# Checks

VibeRegistry is **comparator-primary**. One check establishes an entry; the rest
are extras an entry may switch on.

| Check | Default | What it establishes |
|-------|---------|---------------------|
| `comparator` | **on** | The pinned implementation proves *this* statement. Comparator rebuilds the project in a landrun sandbox, exports the proof term at kernel level, holds the challenge (spec) statement apart from the solution (proof), compares declarations by name and type, and enforces the axiom allowlist. |
| `nanoda` | off | The exported proof is replayed through [nanoda](https://github.com/ammkrn/nanoda_lib), an independently written Lean kernel, as well as Lean's own. A soundness bug in one kernel is unlikely to be shared by the other. |
| `definitions` | off | Spec `def`s are compared through comparator's `definition_names`, not just theorems. |
| `safe_verify` | off | Legacy olean-level spec/impl check (types match, axioms allowed, no `sorry`, no `partial`/`unsafe`). |
| `lean4checker` | off | Legacy kernel re-check of the implementation module. |

## Why comparator is primary

SafeVerify and lean4checker check *oleans that our own build produced*. Comparator
re-derives the proof under its own sandboxed build and checks the exported term,
so it does not have to trust the build that produced the artifact it is checking.
It also enforces the statement/proof separation directly — the property the whole
registry rests on — and it does that against adversarial Lean code, which the
olean-level checks were never designed for.

That makes SafeVerify and lean4checker redundant for the guarantee we publish.
They stay available (an entry can turn them on, and they are cheaper to run), but
they are no longer what a VibeRegistry entry means.

SafeVerify's import-superset limitation (see `CLAUDE.md`) is one more reason: it
constrains how specs may import, and comparator does not have that constraint.

## Configuring an entry

```toml
[checks]
comparator = true
nanoda = false
definitions = false
safe_verify = false
lean4checker = false
```

Omitting `[checks]` gives the defaults in the table above. `nanoda` and
`definitions` are comparator options: switching either on switches comparator on.

`safe_verify` and `lean4checker` need `tools.safe_verify_rev` /
`tools.lean4checker_rev`; the corresponding dependency is only injected into the
implementation's lakefile when its check is enabled, so an entry that does not use
them cannot be broken by them.

## Running

```bash
# Entry defaults
./scripts/verify_entry.sh entries/artificial-theorems.toml

# Add the second kernel (and fail rather than warn if nanoda is missing)
./scripts/verify_entry.sh entries/artificial-theorems.toml --with-nanoda
./scripts/verify_entry.sh entries/artificial-theorems.toml --require-nanoda

# Exactly this set
./scripts/verify_entry.sh entries/aks.toml --checks comparator,definitions

# Everything, across all entries
./scripts/verify_all.sh --with-nanoda --with-safe-verify
```

`--level 1`, `--level 2` and `--skip-level-1` still work as aliases for old
callers: level 1 means lean4checker + SafeVerify, level 2 adds comparator.

nanoda is built by `install_nanoda` in `scripts/lib/install_comparator_tools.sh`
(needs `cargo`). Comparator finds it on `PATH` or via `COMPARATOR_NANODA`. If it
is requested but missing, the run degrades to a Lean-kernel-only comparator run
and records `nanoda: unavailable` — unless `--require-nanoda` was given.

## Results

`results/<entry>/latest.json` records which checks ran and the per-declaration
verdict:

```json
{
  "primary_check": "comparator",
  "checks": { "comparator": true, "nanoda": true, "definitions": false,
              "safe_verify": false, "lean4checker": false },
  "theorems": [
    { "name": "...", "comparator": "pass", "nanoda": "pass",
      "safe_verify": "skip", "lean4checker": "skip" }
  ]
}
```

Per-declaration values: `pass`, `fail`, `skip` (check not enabled),
`not-applicable` (nothing here for this check to look at — e.g. a
definition-only group while `definitions` is off), `unavailable` (requested but
the tool was missing).

**A run where comparator was enabled but returned no verdict for a group fails.**
Before this rule an entry whose comparator never actually ran reported `overall:
pass` with every check `skip` — a green light for something nobody checked.

## CI

- **push / PR** (`verify.yml`) — resolves each changed entry's checks, builds only
  the tools those checks need, runs them.
- **weekly** (`verify_weekly.yml`) — every entry with `--with-nanoda`; commits
  refreshed results.
- Both accept a `checks` input on `workflow_dispatch` to override.
