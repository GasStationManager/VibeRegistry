# VibeRegistry: Verified Registry of AI-assisted Lean Proofs

VibeRegistry is a registry that catalogs AI-assisted Lean 4 proofs from external repositories, provides human-vetted formal theorem specifications, and runs automated secure verification to certify that implementations match their specs.

As AI-generated / AI-assisted formalizations of mathematical proofs become more common, we hope this registry can:
- increase awareness of tools that check against known pitfalls (comparator, second kernels);
- provide a place for human experts to vett and sign-off on specifications;
- serve as a trusted source of verification status of public repositories;
- promote safe re-use of autoformalized libraries of theorems;
- act as a human sign-off **overlay** on upstream registries that have none ([Palomar](https://palomar-registry.org/), [LeanPool](https://github.com/Vilin97/lean-pool));
- make verified statements **searchable**, whether or not anyone has signed off on them.

## Core Invariant

The registry itself does not contain proof code. It contains:
1. **Theorem specifications** — human-vetted `.lean` files with `sorry`-ed statements
2. **Metadata** — TOML configs pointing to external repos at pinned commits
3. **Automation** — scripts to fetch, build, and verify proofs against the specs

## Registry Entries

<!-- BEGIN REGISTRY TABLE -->
| Entry | Theorems | Lean | Checks | Sign-offs | Status |
|-------|----------|------|--------|-----------|--------|
| [ArtificialTheorems](https://github.com/GasStationManager/ArtificialTheorems) | Robbins-Siegmund, SGD convergence, Value Iteration (8 theorems) | v4.27.0 | comparator | 1 sign-off | Verified |
| [Lean Statistical Learning Theory](https://github.com/YuanheZ/lean-stat-learning-theory) | Gaussian concentration, Dudley's integral, Efron-Stein, Poincare (16 theorems) | v4.27.0-rc1 | comparator | — | Verified |
| [AKS Sorting Networks](https://github.com/girving/aks) | O(log n)-depth sorting networks (1 theorems) | v4.29.0-rc4 | comparator | — | Verified |
| [Archon FirstProof Results](https://github.com/frenzymath/Archon-FirstProof-Results) | Harmonic-mean inequality, epsilon-light graph subsets (2 theorems) | v4.28.0 | comparator | — | Verified |
| [lean-zip](https://github.com/kim-em/lean-zip) | 3 theorems | v4.29.1 | comparator +nanoda | — | Failed |
<!-- END REGISTRY TABLE -->

## Overlay and search

Beyond our own entries, the registry mirrors upstream registries that have no
human sign-off step and indexes everything it knows about:

- `overlay/` — records imported from [Palomar](https://palomar-registry.org/) and
  [LeanPool](https://github.com/Vilin97/lean-pool), with our sign-offs kept
  separately in `overlay/signoffs.toml` so re-importing never clobbers review.
  See [docs/overlay.md](docs/overlay.md).
- `index/` — `statements.json` plus a static `search.html` over every statement,
  ours and overlaid, each tagged with what was checked, who signed off, and any
  Mathlib name collision. Current counts live in `index/meta.json`.
  Published at **https://gasstationmanager.github.io/VibeRegistry/**, rebuilt
  whenever the index changes on `main`. See [docs/search.md](docs/search.md).

## Checks

The registry is **comparator-primary**: one check establishes an entry, the rest
are extras an entry can switch on. Full details in [docs/checks.md](docs/checks.md).

| Check | Default | What it establishes |
|-------|---------|---------------------|
| `comparator` | **on** | Sandboxed rebuild (`landrun`), kernel-level proof export (`lean4export`), statement/proof separation, axiom allowlist |
| `nanoda` | off | The exported proof is replayed through a second, independently written kernel as well as Lean's own |
| `definitions` | off | Spec `def`s compared through comparator's `definition_names` |
| `safe_verify` | off | Legacy olean-level spec/impl check |
| `lean4checker` | off | Legacy kernel re-check of the impl module |

Comparator re-derives the proof under its own sandboxed build instead of trusting
oleans our build produced, and enforces statement/proof separation against
adversarial Lean code. That makes the older checks redundant for the guarantee we
publish — they remain available per entry, but they are no longer what an entry
means.

## Repository Structure

```
VibeRegistry/
├── specs/                     # Spec files (self-contained Lean projects per entry)
│   └── artificial-theorems/
│       ├── Registry/          # Lean source tree
│       ├── lakefile.lean      # Pins its own Mathlib version
│       ├── lean-toolchain     # Matches external repo's toolchain
│       └── Registry.lean      # Root import file
├── entries/                   # Per-entry config: repo, commit, theorems, [checks]
│   └── artificial-theorems.toml
├── scripts/                   # Verification + registry automation
│   ├── verify_entry.sh        # Verify a single entry
│   ├── verify_all.sh          # Verify all entries
│   ├── import_upstream.py     # Mirror Palomar / LeanPool records
│   ├── fetch_blueprint_statements.py  # Adopt informal statements
│   ├── generate_signoff_packet.py     # Reviewer packets
│   ├── check_mathlib_conflicts.py     # Name collisions with Mathlib
│   ├── build_search_index.py          # Statement index + search page
│   └── lib/                   # Shared utilities
├── results/                   # Verification results (JSON)
├── informal/                  # Adopted informal statements, per entry
├── signoff_packets/           # Generated review packets
├── overlay/                   # Mirrored upstream registries + our sign-offs
├── index/                     # statements.json + search.html
├── data/                      # Mathlib name list metadata
├── docs/                      # checks / signoff / overlay / search
└── registry.toml              # Central index
```

## Quick Start

### Verify an entry locally

```bash
./scripts/verify_entry.sh entries/artificial-theorems.toml               # entry defaults
./scripts/verify_entry.sh entries/artificial-theorems.toml --with-nanoda # + second kernel
./scripts/verify_entry.sh entries/aks.toml --checks comparator,definitions
./scripts/verify_all.sh --with-nanoda
```

Tools are auto-installed if missing, or install them yourself:

```bash
source scripts/lib/install_comparator_tools.sh
install_comparator_tools specs/artificial-theorems/lean-toolchain work/tools
install_nanoda work/tools        # needs cargo
```

Or point at existing binaries:

```bash
export COMPARATOR_BIN=/path/to/comparator
export LEAN4EXPORT_BIN=/path/to/lean4export
export LANDRUN_BIN=/path/to/landrun   # optional but recommended
export NANODA_BIN=/path/to/nanoda_bin # optional second kernel
```

### Overlay upstream registries

```bash
python3 scripts/import_upstream.py --all     # Palomar + LeanPool
```

Mirrors their records into `overlay/`, where our human sign-offs
(`overlay/signoffs.toml`) are attached without touching upstream data. See
[docs/overlay.md](docs/overlay.md).

### Search the statements

```bash
python3 scripts/fetch_mathlib_names.py       # once
python3 scripts/build_search_index.py
python3 -m http.server 8000 --directory index    # open /search.html
```

Indexes our entries and every overlaid record, tagging each with what was
checked, who signed off, and any Mathlib name collision. See
[docs/search.md](docs/search.md).

### CI

- **On push/PR**: each changed entry runs its configured checks; only the tools
  those checks need get built
- **Weekly**: every entry, comparator + nanoda, results committed
- **Manual dispatch**: override with the `checks` input

### Add a new entry

1. **Identify** the external repo's Lean/Mathlib version
2. **Create** a spec project under `specs/<entry-id>/` with its own `lakefile.lean` and `lean-toolchain`
3. **Write** spec files — theorem statements ending with `:= by sorry`
4. **Create** `entries/<entry-id>.toml` with repo URL, pinned commit, and theorem groups
5. **Update** `registry.toml` with the new entry
6. **Test** locally: `./scripts/verify_entry.sh entries/<entry-id>.toml`
7. **Submit** a PR

### Self-test

```bash
tests/run_selftest.sh
```

Runs the real pipeline against a Mathlib-free fixture whose answer is known, so a
broken pipeline cannot pass quietly. See [docs/checks.md](docs/checks.md#self-test).

### Sign-off helpers

```bash
python3 scripts/fetch_blueprint_statements.py entries/<id>.toml  # adopt informal statements
python3 scripts/generate_signoff_packet.py --all                 # build review packets
python3 scripts/check_mathlib_conflicts.py --all                 # name-collision check
```

See [docs/signoff.md](docs/signoff.md).

### Spec file rules

1. Import only from Mathlib and other spec files within the same entry
2. Mirror impl module structure: export definitions into separate spec files matching the impl's module layout
3. Spec files for definitions are SafeVerify-checked against their corresponding impl oleans, just like theorem specs
4. Theorem statements end with `:= by sorry` — with one exception, see rule 9
5. Match the impl's universe variables exactly (e.g., `universe u v` if the impl uses explicit universes)
6. Avoid `local notation` — it creates private declarations that won't match the impl's
7. Each spec module must `lake build` cleanly; spec modules are built individually (not combined)
8. Human-vetted by a maintainer for mathematical correctness
9. **Transitive-dep exception**: if a spec definition uses `.choose` (or otherwise references the proof term) of a lemma, the Comparator's Phase 2 check compares that lemma's full `ConstantInfo` including its proof value. A spec `sorry` will never match the impl's real proof, so in that case the lemma's proof must be replicated in the spec. Keep it short and mathematically straightforward — sign-off reviewers need to check the proof manually. Additionally, match the impl's transitive imports (e.g. `Mathlib.RingTheory.SimpleRing.Principal`) so typeclass resolution picks the same instance paths the impl does; otherwise `Expr` terms will differ structurally even when types agree. Example: `extract_ordered_real_roots` in `specs/archon-first-proof/Registry/ArchonFirstProof/Problem4.lean`.

## Security Model

**Trusted:** Spec files (human-vetted), Lean kernel, SafeVerify/Comparator tools, CI infrastructure.

**Untrusted:** External repo code — may contain metaprogramming that manipulates the Lean environment.

| Layer | What it catches | Default |
|-------|----------------|---------|
| `comparator` | Environment manipulation, statement/proof conflation, disallowed axioms, kernel-level verification of an independent export | on |
| `landrun` sandbox | Build-time filesystem attacks (used by comparator) | on |
| `nanoda` | A soundness bug in Lean's own kernel | opt-in |
| `safe_verify` | Type mismatches, extra axioms, `sorry`, `partial`/`unsafe` | opt-in |
| `lean4checker` | Declarations not accepted by the kernel | opt-in |
| `check_mathlib_conflicts.py` | Spec names that shadow Mathlib's, and attribute/export overrides | advisory |

A run whose primary check returns no verdict for a theorem group **fails** rather
than reporting a pass.


## Submitting a Sign-off

Domain experts can attest that spec files faithfully capture the intended mathematics by submitting a sign-off:

1. Open a [new sign-off issue](../../issues/new?template=spec-signoff.yml)
2. Select the entry and list the spec files you reviewed
3. Provide a literature reference and your verdict
4. Submit — a GitHub Action will process the sign-off and create a PR

Sign-offs are recorded in the entry's TOML config and included in verification results. If spec files change after a sign-off, it is automatically marked stale. Run `python3 scripts/check_signoff_staleness.py entries/<entry>.toml` to check.

Before reviewing, generate the packet — it puts the informal statement, the Lean
statement, the checks that ran, and a reviewer checklist in one file:

```bash
python3 scripts/fetch_blueprint_statements.py entries/<entry>.toml
python3 scripts/generate_signoff_packet.py entries/<entry>.toml
```

Sign-off is **optional**. A comparator-verified statement stands on its own; a
sign-off adds a named human vouching for what it says. See
[docs/signoff.md](docs/signoff.md).


