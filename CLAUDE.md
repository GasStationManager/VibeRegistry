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

## Common Pitfall: SafeVerify Import Superset Check

SafeVerify requires that the impl's direct imports are a superset of the spec's direct imports. This can fail when:
- Spec imports `Mathlib.*` modules directly
- Impl imports its own modules (e.g., `AKS.*`) which transitively include Mathlib

**Do NOT solve this by importing impl modules in the spec.** That violates the standalone principle.

Current approaches:
- If impl also `import Mathlib`, no issue (spec and impl both import Mathlib)
- If impl uses its own module tree, this is a known SafeVerify limitation that needs a fix (transitive import checking)
- lean4checker provides structural verification independently of SafeVerify

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

- `tools.safe_verify_rev` (not `safe_verify_ref`) — SafeVerify git rev
- `tools.lean4checker_rev` — lean4checker git rev (should match Lean toolchain)
- `build.targets` — space-separated Lake targets to build (skip unneeded targets)
- `build.strategy` — currently only `"copy"` is implemented
