/-
Gaussian Lipschitz Concentration - Specification
Boucheron et al. (2013), Theorem 5.6
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory Real Finset BigOperators Function
open scoped ENNReal NNReal

/-! ### Definitions from Registry.StatLearning.GaussianMeasure -/

namespace GaussianMeasure

/-- Standard Gaussian product measure: the product of n independent standard Gaussians N(0,1) -/
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- The standard Gaussian on EuclideanSpace as pushforward of stdGaussianPi via the equivalence. -/
noncomputable def stdGaussianE (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (EuclideanSpace.equiv (Fin n) ℝ).symm (stdGaussianPi n)

end GaussianMeasure

/-! ### GaussianLipConcen spec -/

namespace GaussianLipConcen

variable {n : ℕ}

open GaussianMeasure

/-- **Gaussian Lipschitz Concentration Inequality**

For any L-Lipschitz function f on ℝⁿ equipped with the standard Gaussian measure,
the probability that f deviates from its mean by more than t is at most
2 exp(-t² / (2L²)). -/
theorem gaussian_lipschitz_concentration {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hn : 0 < n) (hL : 0 < L) (hf : LipschitzWith L f) (t : ℝ) (ht : 0 < t) :
    let μ := stdGaussianE n
    (μ {x | t ≤ |f x - ∫ y, f y ∂μ|}).toReal ≤ 2 * exp (-t^2 / (2 * (L : ℝ)^2)) := by
  sorry

end GaussianLipConcen
