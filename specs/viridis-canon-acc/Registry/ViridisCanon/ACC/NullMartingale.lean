/-
  VibeRegistry spec: Viridis Canon ACC, module NullMartingale

  Source: https://github.com/jdhart81/viridis-canon
  Module: PaperFormalization.NullMartingale (series/ACC)

  Generated from the implementation by copying every definition, instance and
  section variable verbatim and replacing only the proofs of the listed target
  theorems with `sorry`. Lemmas the targets do not need are omitted; lemmas a
  definition's value uses are kept with their proofs (VibeRegistry spec rule 9).
-/

import Registry.ViridisCanon.ACC.Mixture

/-!
# C1 and C2: the null martingale property and the anytime (Ville) certificate

This file formalizes the two certificate claims of `SEALED_paper.tex`, §2:

* **C1** `anytime_change_mixture_martingale`: under the declared null, `(M_n)` is a
  nonnegative martingale with `M_0 = 1` and `E₀[M_n] = 1` for all `n`.
* **C2** `anytime_change_ville_certificate` (Equation 4): `P₀(ever alarming) ≤ α`
  when the alarm threshold is `1/α`.

## Explicit assumptions and scope

The paper's null is: `X₁, X₂, …` iid `P₀`, `P₁ ≪ P₀`, and `Λ_n = dP₁/dP₀(X_n)`, from
which it records the only distributional consequence it ever uses, namely

  `E₀[Λ_n ∣ ℱ_{n-1}] = 1`.

We take exactly that consequence (`hcondΛ` below) as the hypothesis, together with
nonnegativity, adaptedness and integrability.  This is a faithful abstraction of the
paper's null: no dependence structure beyond the displayed conditional-mean-one identity
is used anywhere in §2.  `PaperFormalization.Witnesses` exhibits a genuinely iid
Bernoulli likelihood-ratio model satisfying all of these hypotheses, so nothing here is
vacuous.
-/

namespace Viridis.Run129.PaperFormalization

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {Λ : ℕ → Ω → ℝ}

section Martingale

variable
  (hΛmeas : ∀ n, StronglyMeasurable[ℱ n] (Λ n))
  (hΛnonneg : ∀ n ω, 0 ≤ Λ n ω)
  (hΛint : ∀ n, Integrable (Λ n) μ)
  (hAint : ∀ n, Integrable (mixAcc Λ n) μ)
  (hcondΛ : ∀ n, μ[Λ (n + 1) | ℱ n] =ᵐ[μ] fun _ => (1 : ℝ))

include hΛmeas hΛint hAint hcondΛ

include hΛnonneg in
/-- **C1** (`anytime_change_mixture_martingale`).  Under the declared null the
change-time mixture `M_n = A_n + t_n` of Equation (2) is a nonnegative martingale with
`M_0 = 1`, hence a mean-one test martingale: `E₀[M_n] = 1` for every `n`. -/
theorem anytime_change_mixture_martingale :
    Martingale (mixture Λ) ℱ μ ∧ (∀ n ω, 0 ≤ mixture Λ n ω) ∧
      mixture Λ 0 = (fun _ => (1 : ℝ)) ∧ (∀ n, ∫ ω, mixture Λ n ω ∂μ = 1) := by
  sorry

end Martingale

section Ville

/-- **Ville's inequality** for a nonnegative martingale indexed by `ℕ`: the probability of
*ever* reaching the level `c > 0` is at most `E[M₀]/c`.

This is proved from Doob's finite-horizon maximal inequality by monotone convergence of
the crossing events. -/
theorem ville_inequality {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ) (hnonneg : ∀ n ω, 0 ≤ M n ω)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c ≤ M n ω} ≤ ENNReal.ofReal ((∫ ω, M 0 ω ∂μ) / c) := by
  sorry

/-- **Ville's inequality, supremum form.**  This is the literal form of Equation (4):
`P(sup_n M_n ≥ c) ≤ E[M₀]/c`.  The supremum is taken in `ℝ≥0∞` so that it is always
defined; it is a strengthening of `ville_inequality`, whose event is `∃ n, c ≤ M n`. -/
theorem ville_inequality_sup {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hnonneg : ∀ n ω, 0 ≤ M n ω) {c : ℝ} (hc : 0 < c) :
    μ {ω | ENNReal.ofReal c ≤ ⨆ n, ENNReal.ofReal (M n ω)}
      ≤ ENNReal.ofReal ((∫ ω, M 0 ω ∂μ) / c) := by
  sorry

variable
  (hΛmeas : ∀ n, StronglyMeasurable[ℱ n] (Λ n))
  (hΛnonneg : ∀ n ω, 0 ≤ Λ n ω)
  (hΛint : ∀ n, Integrable (Λ n) μ)
  (hAint : ∀ n, Integrable (mixAcc Λ n) μ)
  (hcondΛ : ∀ n, μ[Λ (n + 1) | ℱ n] =ᵐ[μ] fun _ => (1 : ℝ))

include hΛmeas hΛnonneg hΛint hAint hcondΛ

/-- **C2** (`anytime_change_ville_certificate`, Equation 4).  Under the declared null, the
probability that the monitor *ever* alarms at the single threshold `1/α` is at most `α`. -/
theorem anytime_change_ville_certificate {α : ℝ} (hα : 0 < α) :
    μ {ω | ∃ n, 1 / α ≤ mixture Λ n ω} ≤ ENNReal.ofReal α := by
  sorry

/-- **C2, supremum form** (the literal Equation 4): `P₀(sup_{n≥0} M_n ≥ 1/α) ≤ α`.
This strengthens `anytime_change_ville_certificate`. -/
theorem anytime_change_ville_certificate_sup {α : ℝ} (hα : 0 < α) :
    μ {ω | ENNReal.ofReal (1 / α) ≤ ⨆ n, ENNReal.ofReal (mixture Λ n ω)}
      ≤ ENNReal.ofReal α := by
  sorry

end Ville

end Viridis.Run129.PaperFormalization
