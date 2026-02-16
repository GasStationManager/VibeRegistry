/-
Dudley's Entropy Integral Theorem - Specification
Boucheron et al. (2013), Corollary 13.2
-/

import Mathlib
import Registry.StatLearning.CoveringNumber
import Registry.StatLearning.MetricEntropy
import Registry.StatLearning.SubGaussian

noncomputable section

universe u v

open Set Metric Real MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators ENNReal
open Classical

variable {Ω : Type u} [MeasurableSpace Ω]
variable {A : Type v} [PseudoMetricSpace A]

/-- **Dudley's Entropy Integral Theorem**

For a σ-sub-Gaussian process X indexed by a totally bounded set s with diameter ≤ D,
the expected supremum satisfies:
  E[sup_{t∈s} X_t] ≤ 12√2 · σ · ∫₀^D √(log N(ε, s)) dε -/
theorem dudley {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : A → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : IsSubGaussianProcess μ X σ)
    {s : Set A} (hs : TotallyBounded s)
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam s ≤ D)
    (t₀ : A) (ht₀ : t₀ ∈ s) (hcenter : ∀ ω, X t₀ ω = 0)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_int_exp : ∀ t s : A, ∀ l : ℝ, Integrable (fun ω => Real.exp (l * (X t ω - X s ω))) μ)
    (hfinite : entropyIntegralENNReal s D ≠ ⊤)
    (hcont : ∀ ω, Continuous (fun (t : ↥s) => X t.1 ω)) :
    ∫ ω, ⨆ t ∈ s, X t ω ∂μ ≤ (12 * Real.sqrt 2) * σ * entropyIntegral s D := by
  sorry

end
