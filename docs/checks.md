# Checks

VibeRegistry is **comparator-primary**. One check establishes an entry; the rest
are extras an entry may switch on.

| Check | Default | What it establishes |
|-------|---------|---------------------|
| `comparator` | **on** | The pinned implementation proves *this* statement. Comparator rebuilds the project in a landrun sandbox, exports the proof term at kernel level, holds the challenge (spec) statement apart from the solution (proof), compares declarations by name and type, and enforces the axiom allowlist. |
| `nanoda` | off | The exported proof is replayed through [nanoda](https://github.com/ammkrn/nanoda_lib), an independently written Lean kernel, as well as Lean's own. A soundness bug in one kernel is unlikely to be shared by the other. |
| `definitions` | off | Spec `def`s are compared through comparator's `definition_names`, not just theorems. Needs a comparator revision that has that field — see below. |
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

## Definitions need a comparator that has the field

`definition_names` is a recent addition to comparator. The revisions that build
against our entries' Lean versions do not have it:

| comparator | Lean | `definition_names` |
|---|---|---|
| `6d5870e` (stat-learning) | v4.27.0-rc1 | no |
| `2a00b30` (lean-zip) | v4.29.1 | no |
| `master` | v4.34.0-rc2 | yes |

Comparator parses its config with a derived `FromJson`, which reads the fields it
knows and ignores the rest. So passing `definition_names` to an older build is
not an error — it is a no-op. Given `theorem_names: []` and
`definition_names: [...]`, comparator at v4.29's revision prints

```
Lean default kernel accepts the solution
Your solution is okay!          (exit 0)
```

having compared nothing. Enabling `definitions` there would have turned
stat-learning's 12 unchecked definitions into 12 reported as passing.

The pipeline therefore refuses to run when `definitions` is on and the comparator
build lacks the field. Until an entry's Lean version has a comparator that
carries it, its definition-only groups are recorded as **not-applicable**: the
registry says plainly that nothing checked them, rather than implying something did.

## Tool revisions

comparator and lean4export are Lean programs that load the target project's
oleans, so they must be built against the *entry's* Lean version. Their default
branches track whatever Lean release is current, which is usually a different
one — building comparator's master against an older entry fails outright
(`Invalid field 'replay'`).

So the installer picks a revision instead of forcing a toolchain:

1. the newest revision whose `lean-toolchain` is exactly the entry's;
2. otherwise the newest revision in the same minor series, rebuilt against the
   entry's exact toolchain (tools pin releases and skip patch versions —
   comparator pins `v4.29.0` but never `v4.29.1`);
3. otherwise the default branch, with a warning.

lean4export gets a second constraint: comparator reads its output and rejects a
format it does not know, and the two tools are versioned independently. Selecting
each by toolchain alone paired a comparator that reads export format `2.0.0` with
a lean4export that emits `3.0.0`, and every group failed with

```
uncaught exception: Version invalid: '{"meta":{"exporter":...}}'
```

Comparator's own manifest cannot settle it either — at that revision comparator
does not depend on lean4export at all. So the installer reads the format
comparator's parser accepts and picks the newest lean4export revision that both
targets the entry's Lean and emits that format.

An entry pins a tool with `tools.comparator_rev`, `tools.lean4export_rev`,
`tools.nanoda_rev` or `tools.landrun_rev`. Those pins are read by
`verify_entry.sh`, which is also what installs the tools — CI deliberately does
not pre-install them, because installing before the entry is read passed only the
Lean toolchain and the pins never reached the installer. The tool cache is keyed
on the toolchain *and* the requested revisions, so changing a pin rebuilds.

`COMPARATOR_REV`, `LEAN4EXPORT_REV` and `NANODA_REV` override the choice. The log
states which of the three applied, and the resolved revision of every tool is
recorded in the result file:

```json
"tools": {
  "comparator": "2a00b30df5e9173e70c4e4ec669fdf03da3163b9",
  "lean4export": "caccfbe…", "nanoda": "6ae1f0c…", "landrun": "…"
}
```

A verdict is only as meaningful as the tool that produced it, so the revision
that produced it is published with it.

The installer also prefers a tool's committed `lake-manifest.json` over `lake
update`: re-resolving would un-pin the dependencies of a tool whose whole job is
reproducible verification. A tool build that fails is now a hard error — it used
to print "built" and carry on, and the missing binary later surfaced as every
check reporting `skip`.

## Projects whose Lake config needs `-R`

Some projects' compiled Lake configuration is rejected by a plain `lake env` or
`lake build` and accepted only with `-R`, and the reconfigure does not persist.
`build_copy.sh` detects this and sets `LAKE_NEEDS_RECONFIGURE`, after which our
own lake calls pass `-R`. That matters: without it lean4export never ran for such
a project, every declaration's kind came back unknown, and the run failed for a
reason unrelated to the mathematics.

It does not rescue comparator. Comparator runs `lake build <target>` inside its
sandbox with no flags of ours, so for such a project it cannot load the config at
all. The run says so before it starts, so the resulting failure is not read as a
statement or proof failure. lean-zip is the current example: its config is
rejected without `-R` even unpatched, while the entries comparator verifies
successfully load theirs cleanly. Fixing it needs the build restructured so the
spec is a sibling package requiring the implementation, rather than the
implementation's own lakefile being extended.

## Self-test

```bash
tests/run_selftest.sh
```

Builds a throwaway Mathlib-free Lean project with two proved theorems and runs
the real pipeline against `specs/selftest/`, asserting that comparator *and*
nanoda both returned pass and that every tool revision was recorded.

It exists because the failures that matter here do not look like failures. Three
real ones, all found by running it:

- landrun's upgrade to urfave/cli v3 made it swallow the `--` separator
  comparator uses to pass constants to lean4export, so every comparator run died
  with `unknown module prefix 'Nat'`. landrun is now pinned to the commit before
  that (`5283024`), with a preflight that re-checks the separator survives.
- comparator and lean4export speak a protocol that changes between revisions, so
  lean4export is now built at the revision comparator's own manifest pins.
- The theorem filter treated "lean4export could not tell me this declaration's
  kind" as "this is not a theorem", dropped three real theorems, and the run
  reported a pass with nothing checked.

None of those are visible in an ordinary entry, where a pipeline failure and a
real failure look alike. In the fixture the answer is known, so anything but a
pass is a bug in the pipeline. CI runs it on every change to `scripts/`, and
weekly before the full verification run.

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
