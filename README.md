# VibeRegistry

A registry that catalogs AI-assisted Lean 4 proofs from external repositories, provides human-vetted formal theorem specifications, and runs automated verification to certify that implementations match their specs.

## Core Invariant

The registry itself never contains proof code. It contains:
1. **Theorem specifications** — human-vetted `.lean` files with `sorry`-ed statements
2. **Metadata** — TOML configs pointing to external repos at pinned commits
3. **Automation** — scripts to fetch, build, and verify proofs against the specs

## Registry Entries

| Entry | Theorems | Lean | Verification | Status |
|-------|----------|------|--------------|--------|
| [ArtificialTheorems](https://github.com/GasStationManager/ArtificialTheorems) | Robbins-Siegmund, SGD convergence, Value Iteration | v4.27.0 | Level 1 | Verified |
| [Statistical Learning Theory](https://github.com/YuanheZ/lean-stat-learning-theory) | Gaussian concentration, Dudley's integral, Efron-Stein, Poincare | v4.27.0-rc1 | Level 1 | Verified |

## Verification Levels

**Level 1: SafeVerify** (fast, every PR)
- `lean4checker` — kernel re-checks every declaration
- `safe_verify` — types match, only standard axioms used, no `sorry` remnants

**Level 2: Comparator** (sandboxed, nightly)
- `landrun` sandboxes the build (Linux Landlock filesystem isolation)
- `lean4export` + `comparator` for kernel-level proof export and independent checking

## Repository Structure

```
VibeRegistry/
├── specs/                     # Spec files (self-contained Lean projects per entry)
│   └── artificial-theorems/
│       ├── Registry/          # Lean source tree
│       ├── lakefile.lean      # Pins its own Mathlib version
│       ├── lean-toolchain     # Matches external repo's toolchain
│       └── Registry.lean      # Root import file
├── entries/                   # Per-entry verification configs (TOML)
│   └── artificial-theorems.toml
├── scripts/                   # Verification automation
│   ├── verify_entry.sh        # Verify a single entry
│   ├── verify_all.sh          # Verify all entries
│   └── lib/                   # Shared utilities
├── results/                   # Verification results (JSON)
└── registry.toml              # Central index
```

## Quick Start

### Verify an entry locally

```bash
./scripts/verify_entry.sh entries/artificial-theorems.toml --level 1
```

### Verify all entries

```bash
./scripts/verify_all.sh --level 1
```

### Add a new entry

1. **Identify** the external repo's Lean/Mathlib version
2. **Create** a spec project under `specs/<entry-id>/` with its own `lakefile.lean` and `lean-toolchain`
3. **Write** spec files — theorem statements ending with `:= by sorry`
4. **Create** `entries/<entry-id>.toml` with repo URL, pinned commit, and theorem groups
5. **Update** `registry.toml` with the new entry
6. **Test** locally: `./scripts/verify_entry.sh entries/<entry-id>.toml`
7. **Submit** a PR

### Spec file rules

1. Import from Mathlib and (when using copy strategy) from impl helper modules that provide definitions used in theorem statements
2. Avoid importing the impl module that defines the theorem being spec'd — this would create a name conflict
3. Minimize spec-local definitions; prefer importing them from impl helper modules so SafeVerify sees identical types
4. Theorem statements end with `:= by sorry`
5. Match the impl's universe variables exactly (e.g., `universe u v` if the impl uses explicit universes)
6. Avoid `local notation` — it creates private declarations that won't match the impl's
7. Each spec module must `lake build` cleanly; spec modules are built individually (not combined)
8. Human-vetted by a maintainer for mathematical correctness

## Security Model

**Trusted:** Spec files (human-vetted), Lean kernel, SafeVerify/Comparator tools, CI infrastructure.

**Untrusted:** External repo code — may contain metaprogramming that manipulates the Lean environment.

| Layer | What it catches | Level |
|-------|----------------|-------|
| `lean4checker` | Declarations not accepted by kernel | 1 |
| `safe_verify` | Type mismatches, extra axioms, `sorry`, `partial`/`unsafe` | 1 |
| `landrun` sandbox | Build-time filesystem attacks | 2 |
| `comparator` | Environment manipulation, kernel-level verification | 2 |

## Build Strategies

The registry supports two build strategies for combining spec and impl oleans:

- **copy** (Phase 1): Copies spec files into the cloned external repo, patches its lakefile, and builds everything together. Simple and reliable.
- **workspace** (Phase 2): Uses Lake workspaces to reference both projects. Cleaner separation but trickier Lake semantics.

## License

See [LICENSE](LICENSE).
