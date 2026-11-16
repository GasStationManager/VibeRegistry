/-
  VibeRegistry spec: Viridis Canon ACC, module Wald

  Source: https://github.com/jdhart81/viridis-canon
  Module: PaperFormalization.Wald (series/ACC)

  Generated from the implementation by copying every definition, instance and
  section variable verbatim and replacing only the proofs of the listed target
  theorems with `sorry`. Lemmas the targets do not need are omitted; lemmas a
  definition's value uses are kept with their proofs (VibeRegistry spec rule 9).
-/

import Registry.ViridisCanon.ACC.Dominance

/-!
# C4: the bounded-overshoot expected-delay corridor

This file formalizes Equations (7)–(8) of `SEALED_paper.tex`:

  `N_a = inf{ m ≥ 1 : ∑_{j=1}^m Z_j ≥ a }`,   `a/D ≤ E₁[N_a] < (a + z_max)/D`.

## Explicit assumptions

The paper says: "let post-change increments `Z_i = log Λ_i` be iid, bounded above by
finite `z_max > 0`, and have mean `D = E₁ Z_i = D(P₁‖P₀) > 0` … assume the usual Wald
integrability conditions".  The hypotheses used here are exactly:

* `hZbdd`  : the increments are bounded, `|Z_j| ≤ B` (the paper's "bounded … increments";
  boundedness is what makes `Z_j` integrable and the dominating function below finite);
* `hZmax`  : `Z_j ≤ z_max` (the paper's overshoot control);
* `hZmean` : every increment has the same mean `D`, and `hD : 0 < D`;
* `hindep` : `Z_j` is independent of the past σ-algebra `𝒢 j` (the "iid increments"
  hypothesis in exactly the form Wald's identity consumes);
* `hNstop` : `N` is a stopping time for `𝒢`;
* `hNint`  : `E[N] < ∞` — this is "the usual Wald integrability condition" that the paper
  assumes rather than derives;
* `hfirst` : `N` is a.s. the first time `m ≥ 1` at which `S_m ≥ a` (Equation 7).

Wald's identity itself (`wald_identity`) is *proved* here, not assumed.
-/

namespace Viridis.Run129.PaperFormalization

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The running evidence `S_m = ∑_{j<m} Z_j` (the paper's `∑_{j=1}^m Z_j`). -/
noncomputable def evidenceSum (Z : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range m, Z j ω

/-- The indicator of `{N > j}`; it is `𝒢 j`-measurable when `N` is a stopping time. -/
noncomputable def stopIndicator (N : Ω → ℕ) (j : ℕ) : Ω → ℝ :=
  Set.indicator {ω | j < N ω} 1

/-- **Wald's identity** for a stopping time with finite mean and bounded increments that
are independent of the past: `E[∑_{j<N} Z_j] = E[Z] · E[N]`. -/
theorem wald_identity {𝒢 : Filtration ℕ m0} {Z : ℕ → Ω → ℝ} {N : Ω → ℕ} {B D : ℝ}
    (hB : 0 ≤ B)
    (hZmeas : ∀ j, Measurable (Z j))
    (hZbdd : ∀ j ω, |Z j ω| ≤ B)
    (hZmean : ∀ j, ∫ ω, Z j ω ∂μ = D)
    (hindep : ∀ j, Indep (MeasurableSpace.comap (Z j) inferInstance) (𝒢 j) μ)
    (hNstop : ∀ j, MeasurableSet[𝒢 j] {ω | N ω ≤ j})
    (hNint : Integrable (fun ω => (N ω : ℝ)) μ) :
    ∫ ω, evidenceSum Z (N ω) ω ∂μ = D * ∫ ω, (N ω : ℝ) ∂μ := by
  sorry

/-- **C4** (`bounded_overshoot_expected_delay`, Equation 8).  For bounded, correctly
specified iid post-change increments with positive mean `D`, under the Wald integrability
condition `E[N_a] < ∞`, the first-crossing time of the boundary `a > 0` satisfies the
bounded-overshoot delay corridor `a/D ≤ E₁[N_a] < (a + z_max)/D`. -/
theorem bounded_overshoot_expected_delay {𝒢 : Filtration ℕ m0} {Z : ℕ → Ω → ℝ} {N : Ω → ℕ}
    {B D zmax a : ℝ}
    (hB : 0 ≤ B)
    (hZmeas : ∀ j, Measurable (Z j))
    (hZbdd : ∀ j ω, |Z j ω| ≤ B)
    (hZmax : ∀ j ω, Z j ω ≤ zmax)
    (hZmean : ∀ j, ∫ ω, Z j ω ∂μ = D)
    (hD : 0 < D)
    (ha : 0 < a)
    (hindep : ∀ j, Indep (MeasurableSpace.comap (Z j) inferInstance) (𝒢 j) μ)
    (hNstop : ∀ j, MeasurableSet[𝒢 j] {ω | N ω ≤ j})
    (hNint : Integrable (fun ω => (N ω : ℝ)) μ)
    (hfirst : ∀ᵐ ω ∂μ, IsLeast {m : ℕ | 1 ≤ m ∧ a ≤ evidenceSum Z m ω} (N ω)) :
    a / D ≤ ∫ ω, (N ω : ℝ) ∂μ ∧ ∫ ω, (N ω : ℝ) ∂μ < (a + zmax) / D := by
  sorry

end Viridis.Run129.PaperFormalization
