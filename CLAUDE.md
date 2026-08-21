# CLAUDE.md — VibeRegistry

## Core Principle

**Specs must be standalone.** They import only from Mathlib and from other spec files within the same entry. Never import from the impl repo's modules.

This is the whole point of VibeRegistry: specs are human-vetted, trusted specifications independent of the implementation. If specs import from impl, they're no longer independently verifiable.

## Spec File Rules

1. Import only from Mathlib and other spec files (`Registry.*`)
2. Replicate any impl definitions needed for theorem statements — use the same namespace so qualified names match
3. Theorem statements end with `:= by sorry`
4. Match the impl's universe variables exactly
5. Avoid `local notation`
6. Each spec module must build cleanly after being copied into the impl repo
7. Human-vetted by a maintainer for mathematical correctness

## Checks: comparator is primary

`comparator` is the check that establishes an entry. `nanoda` (second kernel),
`definitions`, `safe_verify` and `lean4checker` are opt-in extras. Configure per
entry in `[checks]`; see `docs/checks.md`.

Comparator re-derives the proof under its own sandboxed build rather than
trusting oleans our build produced, and enforces statement/proof separation
against adversarial Lean. SafeVerify and lean4checker check artifacts we built,
so they are redundant for the guarantee we publish.

A run whose comparator returns no verdict for a theorem group **fails** — an
all-skipped run used to report `overall: pass`, which was a green light for
something nobody checked.

### The old SafeVerify import-superset pitfall

SafeVerify required the impl's direct imports to be a superset of the spec's,
which broke when a spec imported `Mathlib.*` while the impl imported its own
module tree. **Never solve this by importing impl modules in a spec** — that
violates the standalone principle.

It is now mostly moot: comparator has no such constraint, and SafeVerify is off
by default. Only entries that explicitly enable `safe_verify` still face it.

## Entry Structure

```
entries/<id>.toml          — verification config (repo URL, commit, theorem groups)
specs/<id>/                — self-contained Lean project
  lakefile.lean            — pins Mathlib version
  lean-toolchain           — matches impl repo
  Registry.lean            — root import
  Registry/<Id>/*.lean     — spec files
```

## TOML Config

- `[checks]` — which checks run: `comparator` (default true), `nanoda`,
  `definitions`, `safe_verify`, `lean4checker` (all default false)
- `tools.safe_verify_rev` (not `safe_verify_ref`) — SafeVerify git rev. Only
  injected into the impl lakefile when `checks.safe_verify` is on
- `tools.lean4checker_rev` — lean4checker git rev (should match Lean toolchain);
  likewise gated on `checks.lean4checker`
- `build.targets` — space-separated Lake targets to build (skip unneeded targets)
- `build.strategy` — currently only `"copy"` is implemented
- `[[signoffs]]` — human sign-offs (written by the sign-off Action)
- `[[mathlib_conflict_exemptions]]` — `name` + `reason` for a deliberate
  Mathlib name collision
- `[[spec_import_exemptions]]` — `module` + `reason` for a spec that knowingly
  imports outside Mathlib and the spec tree (`scripts/check_spec_imports.py`)
- `tools.comparator_rev` / `tools.lean4export_rev` — pin a tool revision; by
  default the installer picks the revision matching the entry's Lean toolchain

## Beyond verification

Sign-off is optional and always has been: a comparator-verified statement stands
on its own. These pieces exist so the registry is useful either way.

- **Informal statements** (`docs/signoff.md`) —
  `scripts/fetch_blueprint_statements.py` adopts a project's own prose statements
  from its leanblueprint LaTeX (`\lean{...}` ties prose to declarations) or from
  `formalization.yaml` / LeanPool `projects.yml`, into `informal/<entry>.json`.
  `scripts/generate_signoff_packet.py` then builds a one-file review packet.
- **Overlay** (`docs/overlay.md`) — `scripts/import_upstream.py` mirrors Palomar
  and LeanPool records into `overlay/`. Neither has human sign-off; ours live in
  `overlay/signoffs.toml`, which the importer never writes, and go stale
  automatically when the upstream statement hash changes.
- **Search** (`docs/search.md`) — `scripts/build_search_index.py` writes
  `index/statements.json` plus a static `index/search.html` over our entries and
  every overlaid record.
- **Name collisions** — `scripts/check_mathlib_conflicts.py` flags spec
  declarations that shadow a Mathlib name (and `attribute`/`export` overrides),
  using Mathlib's doc-gen4 declaration list. No Lean toolchain needed.
