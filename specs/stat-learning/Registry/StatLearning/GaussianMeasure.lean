/-
Gaussian Measure Definitions - Specification
Definitions from SLT.GaussianMeasure
-/

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace GaussianMeasure

/-- Standard Gaussian product measure: the product of n independent standard Gaussians N(0,1) -/
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- The standard Gaussian on EuclideanSpace as pushforward of stdGaussianPi via the equivalence. -/
noncomputable def stdGaussianE (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (EuclideanSpace.equiv (Fin n) ℝ).symm (stdGaussianPi n)

end GaussianMeasure
