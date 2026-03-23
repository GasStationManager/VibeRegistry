/-
Gaussian Poincaré Inequality - Specification
Boucheron et al. (2013), Theorem 3.20
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set Function Topology Complex
open scoped ENNReal Topology BoundedContinuousFunction

/-! ### Definition from Registry.StatLearning.EfronSteinApp -/

namespace EfronSteinApp

/-- A function is compactly supported and smooth (C²) -/
def CompactlySupportedSmooth (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ HasCompactSupport f

end EfronSteinApp

/-! ### GaussianPoincare spec -/

namespace GaussianPoincare

open EfronSteinApp

/-- The standard real Gaussian N(0,1) as a ProbabilityMeasure. -/
abbrev stdGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- The standard Gaussian measure on ℝ. -/
abbrev stdGaussianMeasure : Measure ℝ := stdGaussian.toMeasure

/-- **Gaussian Poincaré Inequality**

For any f ∈ C²_c(ℝ) and X ~ N(0,1):
  Var(f(X)) ≤ E[f'(X)²] -/
theorem gaussianPoincare {f : ℝ → ℝ} (hf : CompactlySupportedSmooth f) :
    variance (fun x => f x) stdGaussianMeasure ≤
    ∫ x, (deriv f x)^2 ∂stdGaussianMeasure := by
  sorry

end GaussianPoincare

end
