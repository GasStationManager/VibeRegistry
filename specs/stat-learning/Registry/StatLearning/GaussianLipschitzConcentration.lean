/-
Gaussian Lipschitz Concentration - Specification
Boucheron et al. (2013), Theorem 5.6
-/

import Mathlib
import SLT.GaussianMeasure

open MeasureTheory ProbabilityTheory Real Finset BigOperators Function GaussianMeasure
open scoped ENNReal NNReal

namespace GaussianLipConcen

variable {n : ℕ}

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
