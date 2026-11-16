/-
  VibeRegistry spec: Viridis Canon ACC, module Witnesses

  Source: https://github.com/jdhart81/viridis-canon
  Module: PaperFormalization.Witnesses (series/ACC)

  Generated from the implementation by copying every definition, instance and
  section variable verbatim and replacing only the proofs of the listed target
  theorems with `sorry`. Lemmas the targets do not need are omitted; lemmas a
  definition's value uses are kept with their proofs (VibeRegistry spec rule 9).
-/

import Registry.ViridisCanon.ACC.NullMartingale
import Registry.ViridisCanon.ACC.Dominance
import Registry.ViridisCanon.ACC.Wald

/-!
# Non-vacuity witnesses

Every formalized target (C1–C4) is instantiated here at an explicit model, so that none of
the theorem statements is vacuously true.

* `C3Witness`: a deterministic likelihood-ratio path for which the mixture alarm time is
  *strictly* earlier than the embedded component alarm time (`1 < 2`), so the dominance
  claim C3 is non-trivial.
* `C4Witness`: an explicit increment model, stopping time and boundary for which every
  hypothesis of C4 holds and the corridor reads `5/2 ≤ 3 < 7/2`.
* `C12Witness`: the paper's preregistered Bernoulli instance `P₀ = Bern(1/5)`,
  `P₁ = Bern(3/5)` realized as a genuinely iid sequence on `ℕ → Bool` under an infinite
  product measure.  All hypotheses of C1 and C2 hold, the mixture is not identically `1`,
  and the resulting Ville certificate is an instance of C2.
-/

namespace Viridis.Run129.PaperFormalization

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-! ## C3 witness: strict dominance -/

namespace C3Witness

/-- A deterministic likelihood-ratio path with `Λ_i ≡ 3`. -/
noncomputable def Λ : ℕ → Unit → ℝ := fun _ _ => 3

/-- **Non-vacuity for C3**: the dominance conclusion holds and is strict here, so the
statement is not trivially satisfied. -/
theorem c3_nonvacuous :
    (∀ n (ω : Unit), component Λ 1 n ω ≤ mixture Λ n ω) ∧
      firstAlarm (fun n => mixture Λ n ()) 2 < firstAlarm (fun n => component Λ 1 n ()) 2 := by
  sorry

end C3Witness

/-! ## C4 witness: an explicit delay corridor -/

namespace C4Witness

/-- Deterministic unit increments on a one-point probability space. -/
noncomputable def Z : ℕ → Unit → ℝ := fun _ _ => 1

/-- The stopping time: the boundary `a = 5/2` is first crossed at `m = 3`. -/
def N : Unit → ℕ := fun _ => 3

/-- The trivial filtration. -/
def 𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Unit) where
  seq := fun _ => ⊥
  mono' := fun _ _ _ => le_rfl
  le' := fun _ => bot_le

/-- **Non-vacuity for C4**: all hypotheses hold at this model and the corridor is the
non-trivial statement `5/2 ≤ 3 < 7/2`. -/
theorem c4_nonvacuous :
    (5 : ℝ) / 2 / 1 ≤ ∫ ω, (N ω : ℝ) ∂(Measure.dirac ()) ∧
      ∫ ω, (N ω : ℝ) ∂(Measure.dirac ()) < ((5 : ℝ) / 2 + 1) / 1 := by
  sorry

end C4Witness

/-! ## C1/C2 witness: the preregistered iid Bernoulli instance -/

namespace C12Witness

/-- The declared null `P₀ = Bernoulli(1/5)` (the paper's `p₀ = 0.2`). -/
noncomputable def bern : PMF Bool := PMF.bernoulli (1 / 5) (by simp)

/-- `P₀` as a measure on a single observation. -/
noncomputable def μ₀ : Measure Bool := bern.toMeasure

instance : IsProbabilityMeasure μ₀ := by unfold μ₀; infer_instance

/-- The likelihood ratio `dP₁/dP₀` for `P₁ = Bernoulli(3/5)` against `P₀ = Bernoulli(1/5)`:
`(3/5)/(1/5) = 3` on a detection and `(2/5)/(4/5) = 1/2` on a non-detection. -/
noncomputable def LR : Bool → ℝ := fun b => if b then 3 else 1 / 2

lemma LR_meas : Measurable LR := by fun_prop

/-- The iid null on the whole observation stream. -/
noncomputable def μ : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => μ₀)

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- The likelihood ratio process `Λ_j(ω) = dP₁/dP₀(X_j)`. -/
noncomputable def Λ : ℕ → (ℕ → Bool) → ℝ := fun j ω => LR (ω j)

lemma Λ_meas (j : ℕ) : Measurable (Λ j) := LR_meas.comp (measurable_pi_apply j)

lemma Λ_sm (j : ℕ) : StronglyMeasurable (Λ j) := (Λ_meas j).stronglyMeasurable

/-- The natural filtration of the observation stream. -/
noncomputable def ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  Filtration.natural Λ Λ_sm

/-- **Non-vacuity for C1 and C2**: at the preregistered iid Bernoulli instance the mixture
is a mean-one martingale, the anytime certificate at `α = 1/2` holds, and the alarm event
is neither empty nor null. -/
theorem c12_nonvacuous :
    Martingale (mixture Λ) ℱ μ ∧
    (∀ n, ∫ ω, mixture Λ n ω ∂μ = 1) ∧
    μ {ω : ℕ → Bool | ∃ n, (2 : ℝ) ≤ mixture Λ n ω} ≤ ENNReal.ofReal (1 / 2) ∧
    0 < μ {ω : ℕ → Bool | ∃ n, (2 : ℝ) ≤ mixture Λ n ω} := by
  sorry

/-- Non-vacuity for the literal supremum form of Equation (4) at the same instance. -/
theorem c2_sup_nonvacuous :
    μ {ω : ℕ → Bool | ENNReal.ofReal (2 : ℝ) ≤ ⨆ n, ENNReal.ofReal (mixture Λ n ω)}
      ≤ ENNReal.ofReal (1 / 2) := by
  sorry

end C12Witness

end Viridis.Run129.PaperFormalization
