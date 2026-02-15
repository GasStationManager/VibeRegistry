# Lean Proof Registry: Design & Implementation Plan (v2)

## 1. Overview

A registry that catalogs AI-assisted Lean 4 proofs from external repositories, provides human-vetted formal theorem specifications, and runs automated verification (SafeVerify + Comparator) to certify that implementations match their specs without smuggling in extra axioms.

The registry follows the pattern established by [GasStationManager/ArtificialTheorems](https://github.com/GasStationManager/ArtificialTheorems), generalized to reference proofs living in *any* external GitHub repo.

### Core Invariant

The registry itself never contains proof code. It contains:
1. Theorem specifications (human-vetted `.lean` files with `sorry`-ed statements)
2. Metadata pointing to external repos at pinned commits
3. Automation to fetch, build, and verify those proofs against the specs

---

## 2. Repository Structure

```
lean-proof-registry/
├── specs/                             # Spec files, organized per entry
│   ├── stat-learning/                 # Each entry = self-contained Lean project
│   │   ├── Registry/StatLearning/     # Lean source tree (module-path structure)
│   │   │   ├── GaussianConcentration.lean
│   │   │   └── DudleyEntropy.lean
│   │   ├── spec_versions/             # Archived spec snapshots (for sign-off preservation)
│   │   │   └── v1_mathlib-v4.16.0/
│   │   │       ├── GaussianConcentration.lean
│   │   │       └── VERSION.toml
│   │   ├── lakefile.lean              # Pins ITS OWN Mathlib version
│   │   ├── lean-toolchain             # Matches external repo's toolchain
│   │   └── lake-manifest.json         # Locked dependencies
│   │
│   ├── artificial-theorems/
│   │   ├── Registry/ArtificialTheorems/
│   │   │   ├── Opt/
│   │   │   │   ├── RobbinsSiegmund.lean
│   │   │   │   ├── SGD.lean
│   │   │   │   └── SGDUniqueMin.lean
│   │   │   └── RL/
│   │   │       ├── ValueIterationComplete.lean
│   │   │       └── ApproxValueIterationInt.lean
│   │   ├── lakefile.lean
│   │   ├── lean-toolchain
│   │   └── lake-manifest.json
│   └── ...
│
├── entries/                           # Per-entry verification configs
│   ├── stat-learning.toml
│   ├── artificial-theorems.toml
│   └── ...
│
├── scripts/
│   ├── verify_entry.sh                # Verify a single registry entry (main driver)
│   ├── verify_all.sh                  # Verify all entries
│   ├── generate_comparator_configs.py # Auto-generate comparator JSON from entry TOML
│   ├── archive_spec_version.sh        # Snapshot current specs before Mathlib bump
│   └── lib/
│       ├── build_workspace.sh         # Approach A: Lake workspace build
│       ├── build_copy.sh              # Approach B: Copy specs into external repo
│       └── parse_toml.py              # TOML config parser
│
├── .github/workflows/
│   ├── verify_pr.yml                  # PR-triggered Level 1 verification
│   ├── verify_nightly.yml             # Nightly Level 2 (comparator) verification
│   ├── monitor_upstream.yml           # Weekly: check for upstream changes
│   └── process_signoff.yml            # On issue labeled 'signoff': parse & update entry
│
├── .github/ISSUE_TEMPLATE/
│   └── spec-signoff.yml               # Structured template for sign-off issues
│
├── results/                           # Verification results (committed by CI)
│   ├── stat-learning/
│   │   ├── latest.json
│   │   └── history/
│   └── ...
│
├── registry.toml                      # Central index (lightweight, no build logic)
└── README.md
```

### Key structural decision: No central lakefile

Each entry under `specs/` is a self-contained Lean project with its own `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`. This means:

- Different entries can target different Lean/Mathlib versions without conflict
- CI builds each entry independently in its own environment
- Adding a new entry never breaks existing ones
- No global Mathlib dependency to manage

---

## 3. Entry Config Format

### 3.1 Central Index (`registry.toml`)

```toml
[registry]
name = "lean-proof-registry"
description = "Registry of verified AI-assisted Lean 4 proofs"

[[entries]]
id = "stat-learning"
config = "entries/stat-learning.toml"
status = "verified"           # verified | pending | failing

[[entries]]
id = "artificial-theorems"
config = "entries/artificial-theorems.toml"
status = "verified"
```

### 3.2 Entry Config (`entries/stat-learning.toml`)

```toml
[project]
id = "stat-learning"
name = "Lean Statistical Learning Theory"
description = "Gaussian Lipschitz concentration and Dudley's entropy integral"
url = "https://github.com/YuanheZ/lean-stat-learning-theory"
commit = "a1b2c3d4e5f6..."          # Pinned commit SHA (REQUIRED)
branch = "main"                      # Informational only

[lean]
# These MUST match what's in specs/stat-learning/lean-toolchain and lakefile.lean.
# Recorded here for documentation and CI validation.
toolchain = "leanprover/lean4:v4.16.0"
mathlib_tag = "v4.16.0"

# Each [[theorems]] block = one verification unit (one comparator config).
[[theorems]]
spec_module = "Registry.StatLearning.GaussianConcentration"
impl_module = "SLT.GaussianConcentration"
names = ["gaussian_lipschitz_concentration"]
permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]

[[theorems]]
spec_module = "Registry.StatLearning.DudleyEntropy"
impl_module = "SLT.Dudley"
names = ["dudley"]
permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]

# Build approach: "workspace" or "copy" — both to be implemented and tested
[build]
strategy = "copy"

# Human expert sign-offs (populated automatically via GitHub Issues — see Section 8)
# Each sign-off records who reviewed which spec files and when.
[[signoffs]]
github_user = "YuanheZ"
spec_files = ["Registry/StatLearning/GaussianConcentration.lean", "Registry/StatLearning/DudleyEntropy.lean"]
date = "2026-02-20"
issue = 12        # GitHub issue number where sign-off was recorded
comment = "Statements match Boucheron et al. (2013) Theorems 5.6 and Corollary 13.2"

# Tool versions (optional overrides)
[tools]
safe_verify_repo = "https://github.com/GasStationManager/SafeVerify"
safe_verify_ref = "main"
```

---

## 4. Spec Files

### Rules

1. Import only from Mathlib (and other spec files within the same entry).
2. Definitions in theorem statements must be defined in the spec file itself or come from Mathlib — never imported from the external repo.
3. Statements end with `:= by sorry`.
4. Each spec directory is a standalone Lean project that must `lake build` cleanly.
5. Human-vetted by a maintainer for mathematical correctness.

### Example spec lakefile

```lean
-- specs/stat-learning/lakefile.lean
import Lake
open Lake DSL

package registry_stat_learning where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

@[default_target]
lean_lib «Registry» where
  srcDir := "."
```

### Versioning: specs track the external repo's Mathlib version

When an external repo updates Mathlib:
1. Update `specs/<entry>/lean-toolchain` and `lakefile.lean`
2. Run `lake update` to regenerate `lake-manifest.json`
3. Fix any spec compilation breakage from Mathlib API changes
4. Update `entries/<entry>.toml` with new commit SHA
5. Submit PR → CI verifies

---

## 5. Build Strategies

The core challenge: we need spec oleans and impl oleans built in the same Lean/Mathlib environment, but they live in separate repos. Both approaches below will be implemented; per-entry config selects which to use.

### Approach A: Copy specs into external repo ("copy")

During verification:

1. Clone external repo at pinned commit into `work/<entry>/repo/`
2. Copy spec `.lean` files into the cloned repo's source tree
3. Programmatically add the spec library to the repo's `lakefile.lean`
4. `lake build` builds everything in one environment
5. Run SafeVerify on the resulting olean pairs

**Lakefile patching** — append to the external repo's lakefile:

```lean
-- REGISTRY: auto-generated spec library
lean_lib «Registry» where
  srcDir := "."
```

**Pros**: Simple, predictable, inherits external repo's full dependency tree automatically.
**Cons**: Modifies a working copy of the external repo; lakefile patching can break on unusual lakefiles.

### Approach B: Lake workspace ("workspace")

1. Clone external repo into `work/<entry>/repo/`
2. Symlink or copy specs into `work/<entry>/specs/`
3. Generate a workspace lakefile that references both

```
work/<entry>/
├── repo/                    # External repo at pinned commit
├── specs/                   # Copy of specs/<entry>/
└── lakefile.lean            # Generated workspace root
```

Generated workspace lakefile:

```lean
import Lake
open Lake DSL

package verify_workspace

require external from ./"repo"
require registry_specs from ./"specs"
```

**Pros**: Doesn't modify external repo; cleaner conceptual separation.
**Cons**: Lake workspace semantics can be tricky; Mathlib must resolve to same version across both projects.

### Experimental plan

Phase 1 uses **copy** (simpler, known to work in ArtificialTheorems-like setups). Phase 2 experiments with **workspace** on lean-stat-learning-theory. Both are implemented as separate scripts (`build_copy.sh`, `build_workspace.sh`); the entry config's `build.strategy` field selects which runs.

---

## 6. Verification Pipeline

### 6.1 Two Levels

**Level 1: SafeVerify** (fast, every PR)
- `lean4checker` on impl modules — kernel re-checks every declaration
- `safe_verify` on spec ↔ impl olean pairs — types match, only standard axioms used
- See [SafeVerify](https://github.com/GasStationManager/SafeVerify) for full list of checks

**Level 2: Comparator** (sandboxed, nightly)
- `landrun` sandboxes the build (Linux Landlock filesystem isolation)
- `lean4export` + `comparator` for kernel-level proof export and independent checking
- Catches environment manipulation during build, `native_decide` issues, etc.

### 6.2 `verify_entry.sh` Pseudocode

```bash
#!/bin/bash
# Usage: ./scripts/verify_entry.sh entries/<entry>.toml [--level 1|2]

# 1. Parse TOML config → extract repo URL, commit, strategy, theorem groups
# 2. Clone external repo at pinned commit
# 3. Validate lean-toolchain matches spec's toolchain
# 4. Build using chosen strategy (copy or workspace)
#    - For copy: patch lakefile, copy specs, lake build
#    - For workspace: generate workspace lakefile, lake build
# 5. Level 1 verification:
#    For each theorem group:
#      a. lean4checker on impl module
#      b. safe_verify spec.olean impl.olean
# 6. If --level 2:
#    a. Generate comparator JSON configs
#    b. Run comparator (under landrun if available)
# 7. Record results to results/<entry>/
```

### 6.3 SafeVerify Version Compatibility

SafeVerify must be built at a Lean version compatible with the entry. SafeVerify already maintains branches for different Lean versions. The verification script:

1. Reads the entry's Lean toolchain version
2. Clones SafeVerify and checks out the appropriate branch/tag
3. Builds SafeVerify within the entry's environment
4. Runs it on the olean pairs

If SafeVerify is already available as a Lake dependency of the spec project, this simplifies to just `lake exe safe_verify`.

---

## 7. Security Model

### Threat Model

**Trusted**: Spec files (human-vetted, in this repo), Lean kernel, SafeVerify/Comparator tools, CI infrastructure.
**Untrusted**: External repo code — may contain metaprogramming that manipulates the Lean environment, or build-time code that modifies the filesystem.

### Defense Layers

| Layer | What it catches | Level |
|-------|----------------|-------|
| `lean4checker` | Declarations not accepted by kernel after replay | 1 |
| `safe_verify` | Type mismatches, extra axioms, `sorry` remnants, `partial`/`unsafe` | 1 |
| `landrun` sandbox | Build-time filesystem attacks (code execution during compilation) | 2 |
| `comparator` | Environment manipulation, kernel-level proof verification | 2 |

### CI Security (referencing ArtificialTheorems' approach)

ArtificialTheorems has an existing GitHub Action for comparator with landrun. The registry adapts this:

- **Ephemeral runners**: Each entry builds in a fresh container; no shared state.
- **landrun**: Requires Linux kernel ≥5.13 with Landlock support. GitHub-hosted Ubuntu runners support this.
- **No olean caching of untrusted code**: Always build from source for external repos.
- **Mathlib cache is trusted**: `lake exe cache get` for Mathlib oleans is fine (Mathlib is trusted).
- **Isolation between entries**: `LEAN_PATH` must not leak oleans across entries.

### What SafeVerify does NOT check (supplementary checks needed)

Per SafeVerify's README:
- `implemented_by`, `extern`, `noncomputable` keywords — scan source files
- Build-time filesystem attacks — use landrun sandbox
- `native_decide` — SafeVerify rejects it by default (depends on `ofReduceBool` axiom); alternatively use [ReplaceNativeDecide](https://github.com/GasStationManager/ReplaceNativeDecide)

---

## 8. Results Format

```json
{
  "entry_id": "stat-learning",
  "timestamp": "2026-02-15T14:30:00Z",
  "commit": "a1b2c3d4e5f6...",
  "lean_toolchain": "leanprover/lean4:v4.16.0",
  "mathlib_tag": "v4.16.0",
  "verification_level": 2,
  "build_strategy": "copy",
  "theorems": [
    {
      "name": "gaussian_lipschitz_concentration",
      "spec_module": "Registry.StatLearning.GaussianConcentration",
      "impl_module": "SLT.GaussianConcentration",
      "lean4checker": "pass",
      "safe_verify": "pass",
      "comparator": "pass",
      "axioms_used": ["propext", "Quot.sound", "Classical.choice"],
      "extra_axioms": [],
      "signoffs": [
        {"github_user": "YuanheZ", "date": "2026-02-20", "issue": 12}
      ]
    }
  ],
  "overall": "pass",
  "duration_seconds": 1847
}
```

Partial results are recorded per-theorem. If 8/10 pass and 2 fail, `overall` is `"partial"`. Sign-off data is included when available (see Section 9).

---

## 9. Human Expert Sign-off

Automated verification (SafeVerify, Comparator) guarantees that the implementation proves exactly what the spec states. But it cannot guarantee that the spec *faithfully captures the intended mathematics*. A spec might accidentally weaken a hypothesis, strengthen a conclusion, or define a concept differently from the literature. Human expert review bridges this gap.

### Sign-off via GitHub Issues

A human expert signs off on a spec by opening a GitHub Issue in the registry repo with a structured format. Automation parses the issue and updates the entry config.

**Issue format** (template provided by the repo):

```markdown
## Spec Sign-off

**Entry:** stat-learning
**Spec files reviewed:**
- Registry/StatLearning/GaussianConcentration.lean
- Registry/StatLearning/DudleyEntropy.lean

**Reference:** Boucheron, Lugosi, Massart (2013), Theorems 5.6 and Corollary 13.2

**Verdict:** ✅ Approved

**Comments:**
Statements match the referenced theorems. The hypotheses on Lipschitz continuity
and the Gaussian measure are correctly formalized. The definitions of covering
numbers and sub-Gaussian processes align with standard usage.
```

**Labels:** The issue must be labeled `signoff`.

### Automation

A GitHub Action (`process_signoff.yml`) triggers on issues labeled `signoff`:

1. Parses the issue body (entry ID, spec files, verdict)
2. Extracts the issue author's GitHub username
3. If verdict is "Approved":
   - Appends a `[[signoffs]]` block to `entries/<entry>.toml`
   - Commits the change on a branch, opens a PR
   - The PR links back to the sign-off issue
4. A maintainer merges the PR (or the bot auto-merges if configured)

### Sign-off metadata in entry config

```toml
[[signoffs]]
github_user = "YuanheZ"
spec_files = ["Registry/StatLearning/GaussianConcentration.lean",
              "Registry/StatLearning/DudleyEntropy.lean"]
date = "2026-02-20"
issue = 12
comment = "Statements match Boucheron et al. (2013) Theorems 5.6 and Corollary 13.2"

[[signoffs]]
github_user = "expert_reviewer_2"
spec_files = ["Registry/StatLearning/GaussianConcentration.lean"]
date = "2026-03-01"
issue = 17
comment = "Confirmed measurability hypotheses are correct per Wainwright (2019) Ch. 5"
```

### Sign-off display

The registry README and per-entry results show sign-off status:

```
Entry: stat-learning
  Verification: ✅ Level 2 (Comparator)
  Sign-offs:
    📝 @YuanheZ — GaussianConcentration, DudleyEntropy (2026-02-20, #12)
    📝 @expert_reviewer_2 — GaussianConcentration (2026-03-01, #17)
  Unsigned specs: (none)
```

Entries with zero sign-offs still appear in the registry (verification is valuable even without sign-off), but are marked as "unreviewed."

### Trust considerations

- Any GitHub user can open a sign-off issue. The registry records the identity and lets consumers decide how much weight to give each reviewer. No gatekeeping on who can sign off.
- Multiple independent sign-offs on the same spec increase confidence.
- The sign-off issue thread provides a permanent, linkable record of the review discussion.

### Spec versioning and sign-off preservation

Sign-offs attest to the *mathematical content* of a spec, not its Lean syntax. When a spec file changes due to a Mathlib version bump (e.g., API renames, import path changes), the mathematical content is typically unchanged — previous sign-offs should not be lost.

**Mechanism: versioned spec snapshots**

Each entry maintains a `spec_versions/` directory that archives previous spec states alongside their sign-offs:

```
specs/stat-learning/
├── Registry/StatLearning/           # Current spec (for latest Mathlib version)
│   ├── GaussianConcentration.lean
│   └── DudleyEntropy.lean
├── spec_versions/                   # Archived spec versions
│   └── v1_mathlib-v4.16.0/
│       ├── GaussianConcentration.lean
│       ├── DudleyEntropy.lean
│       └── VERSION.toml             # Records mathlib version, date, file hashes
├── lakefile.lean
├── lean-toolchain
└── lake-manifest.json
```

`VERSION.toml` for each snapshot:

```toml
mathlib_tag = "v4.16.0"
lean_toolchain = "leanprover/lean4:v4.16.0"
created = "2026-02-20"
file_hashes = { "GaussianConcentration.lean" = "sha256:abc...", "DudleyEntropy.lean" = "sha256:def..." }
```

**When a spec file changes:**

1. The CI detects the hash change and checks the *reason*:
   - If the entry's `mathlib_tag` also changed → Mathlib version bump. Archive the old spec into `spec_versions/v<N>_mathlib-<old_tag>/` before updating.
   - If only the spec changed (same Mathlib) → substantive mathematical change. Mark existing sign-offs as `stale` and notify reviewers.

2. Sign-offs in the entry config reference a spec version:

```toml
[[signoffs]]
github_user = "YuanheZ"
spec_files = ["Registry/StatLearning/GaussianConcentration.lean"]
spec_version = "v1_mathlib-v4.16.0"    # ties sign-off to a specific snapshot
date = "2026-02-20"
issue = 12
status = "current"                      # "current" | "stale" | "archived"
comment = "Matches Boucheron et al. (2013) Theorem 5.6"
```

3. After a Mathlib bump, the sign-off's `status` stays `"current"` because it was a non-substantive change — the archived snapshot proves the old version was reviewed, and the new version is a mechanical port. A reviewer can optionally re-sign-off on the new version for extra confidence.

4. After a substantive spec change (different hypotheses, different conclusion), the sign-off `status` becomes `"stale"` and the reviewer gets a GitHub notification (via the original issue thread).

**Display logic:**

```
Entry: stat-learning (Mathlib v4.17.0)
  Sign-offs:
    📝 @YuanheZ — GaussianConcentration (2026-02-20, #12)
       ↳ reviewed at Mathlib v4.16.0, current spec is mechanical port
    📝 @expert2 — GaussianConcentration (2026-04-01, #25)
       ↳ reviewed at Mathlib v4.17.0 (current)
```

### Results format (updated with sign-off data)

```json
{
  "entry_id": "stat-learning",
  "timestamp": "2026-02-15T14:30:00Z",
  "commit": "a1b2c3d4e5f6...",
  "lean_toolchain": "leanprover/lean4:v4.16.0",
  "verification_level": 2,
  "theorems": [
    {
      "name": "gaussian_lipschitz_concentration",
      "spec_module": "Registry.StatLearning.GaussianConcentration",
      "impl_module": "SLT.GaussianConcentration",
      "lean4checker": "pass",
      "safe_verify": "pass",
      "comparator": "pass",
      "axioms_used": ["propext", "Quot.sound", "Classical.choice"],
      "signoffs": [
        {"github_user": "YuanheZ", "date": "2026-02-20", "issue": 12},
        {"github_user": "expert_reviewer_2", "date": "2026-03-01", "issue": 17}
      ]
    }
  ],
  "overall": "pass"
}
```

---

## 10. Adding a New Entry: Workflow

### Step 1: Identify external repo's Lean/Mathlib version

```bash
cat lean-toolchain
# → leanprover/lean4:v4.16.0
cat lake-manifest.json | jq '.packages[] | select(.name == "mathlib") | .rev'
```

### Step 2: Create spec project

```bash
mkdir -p specs/my-project/Registry/MyProject/
cd specs/my-project/
echo "leanprover/lean4:v4.16.0" > lean-toolchain

cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL
package registry_my_project where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"
@[default_target]
lean_lib «Registry» where
  srcDir := "."
EOF

lake exe cache get && lake build
```

### Step 3: Write spec files

```lean
-- Registry/MyProject/GaussianConcentration.lean
import Mathlib

theorem gaussian_lipschitz_concentration ... := by sorry
```

### Step 4: Create entry config (`entries/my-project.toml`)

### Step 5: Test locally

```bash
./scripts/verify_entry.sh entries/my-project.toml --level 1
```

### Step 6: Submit PR → CI verifies → maintainer reviews specs → merge

---

## 11. Definition Equivalence

When a spec file defines a structure (like `MDP` in ArtificialTheorems) and the external repo also defines it:

- SafeVerify checks that definitions without `sorry` have *identical bodies* between spec and impl. This ensures structural definitions match exactly.
- Definitions with `sorry` allow different bodies (these are function stubs to be filled).
- Comparator verifies at the kernel level that the impl's proof proves exactly the spec's statement.

**For the registry**: Spec files must define all structures/helpers needed to state the theorems. These definitions must be identical to what the external repo uses. If the external repo uses Mathlib definitions directly, the spec should too. If the external repo defines custom structures, the spec replicates them verbatim.

---

## 12. Implementation Plan

### Phase 1: Skeleton & ArtificialTheorems Entry (Week 1-2)

- [ ] Initialize registry repo with directory structure
- [ ] Port ArtificialTheorems specs into `specs/artificial-theorems/` as standalone project
- [ ] Create `entries/artificial-theorems.toml`
- [ ] Implement `scripts/verify_entry.sh` with copy strategy, Level 1
- [ ] Verify end-to-end against ArtificialTheorems repo
- [ ] Write `README.md`

### Phase 2: lean-stat-learning-theory & Build Experiments (Week 3-4)

- [ ] Study lean-stat-learning-theory: `SLT/` module structure, major theorem names/types
- [ ] Write specs for key results: `gaussian_lipschitz_concentration`, `dudley`, `efronStein`, `gaussianPoincare`
- [ ] Test with copy strategy
- [ ] **Implement and test workspace strategy** on this entry
- [ ] Compare: which is more robust, what breaks, document findings
- [ ] Support both strategies in `verify_entry.sh`

### Phase 3: Level 2 & CI (Week 5-6)

- [ ] Add comparator support, referencing ArtificialTheorems' GitHub Action pattern
- [ ] Implement `generate_comparator_configs.py` (TOML → comparator JSON)
- [ ] Set up GitHub Actions workflows (PR verification, nightly full)
- [ ] landrun setup and security review
- [ ] Results recording and badge generation

### Phase 4: Human Sign-off System (Week 7-8)

- [ ] Create GitHub Issue template (`spec-signoff.yml`) with structured fields
- [ ] Implement `process_signoff.yml` GitHub Action (parse issue → update TOML → open PR)
- [ ] Sign-off staleness detection: hash spec files, mark stale when files change
- [ ] Display sign-off status in README and per-entry results
- [ ] Solicit initial sign-offs for ArtificialTheorems and stat-learning-theory entries

### Phase 5: Polish & Growth (Week 9+)

- [ ] README badges per entry (verification level + sign-off count)
- [ ] Contributor guide with worked example
- [ ] Upstream monitoring workflow
- [ ] Onboard dependency chain: lean-rademacher → CLT → stat-learning-theory
- [ ] Onboard more entries: `ShangtongZhang/rl-theory-in-lean`

---

## 13. Candidate First Entries

| Project | Repo | Key Theorems | Notes |
|---------|------|-------------|-------|
| ArtificialTheorems | GasStationManager/ArtificialTheorems | Robbins-Siegmund, SGD convergence, Value Iteration | Already has SafeVerify + comparator; ideal baseline |
| Rademacher Complexity | auto-res/lean-rademacher | Generalization bound via Rademacher complexity | Dependency of stat-learning; register first |
| CLT | RemyDegenne/CLT | Lévy continuity, char. function inversion | Dependency of stat-learning; register first |
| Stat Learning Theory | YuanheZ/lean-stat-learning-theory | Gaussian Lipschitz, Dudley's integral, Efron-Stein | 30k lines; depends on lean-rademacher + CLT |
| RL Theory | ShangtongZhang/rl-theory-in-lean | Q-Learning convergence | Referenced in ArtificialTheorems wishlist |

**Onboarding order**: ArtificialTheorems → lean-rademacher → CLT → stat-learning-theory → rl-theory-in-lean

---

## 14. Transitive Dependencies Policy

When an external project depends on other Lean packages beyond Mathlib (e.g., lean-stat-learning-theory depends on `lean-rademacher` and `CLT`), the registry treats those dependencies as follows:

**Each dependency that provides theorems should be its own registry entry.** This means:

- `auto-res/lean-rademacher` gets its own entry with specs and verification
- `RemyDegenne/CLT` gets its own entry (if it contains results worth registering)
- `YuanheZ/lean-stat-learning-theory` is then registered as an entry that *builds on top of* verified dependencies

**For the build process**, the external project's lakefile already declares these dependencies, so:
- **Copy strategy**: inherits them automatically (the external lakefile fetches them)
- **Workspace strategy**: the workspace inherits them through the external project's lakefile

**For the registry's integrity**, having each dependency as a separate entry means:
- Each library's theorems are independently verified against their own specs
- A reviewer can assess each component separately
- If lean-rademacher breaks or changes, only its entry (and dependents) need re-verification

**Cross-entry references in specs**: If entry B's spec needs to reference a definition from entry A's library, the spec can either:
1. Redefine it locally (simpler, self-contained)
2. Import from Mathlib if the definition has been upstreamed
3. In the future: import from another entry's spec (requires cross-entry dependency in the spec project's lakefile)

Option 1 is recommended for now to keep entries independent.

---

## 15. Open Questions

1. **Definition drift**: If an external repo refactors a definition (same theorem, different internal structure), the spec needs updating. Should we automate detection? Possible approach: a CI check that compares definition hashes between spec and impl.

2. **Namespace collisions in copy strategy**: If the external repo already has a `Registry` module, copying specs would collide. Mitigation: use a unique prefix like `__RegistryVerify` or generate a UUID-based module name.

3. **CI caching** (future work): Building Mathlib per-entry is expensive (~30 min with cache, hours without). Strategy for later: cache `lake exe cache get` artifacts per `(toolchain, mathlib_tag)` tuple across entries that share the same version.

4. **Spec version diffing**: When archiving a spec snapshot after a Mathlib bump, should we auto-generate a diff showing what changed? This would help reviewers quickly confirm the port is mechanical. Could use `lean --run` to compare ASTs rather than raw text.
