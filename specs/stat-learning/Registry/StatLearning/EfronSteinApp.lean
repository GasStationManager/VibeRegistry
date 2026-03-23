/-
Efron-Stein Application Definitions - Specification
Definition from SLT.GaussianPoincare.EfronSteinApp
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi

namespace EfronSteinApp

/-- A function is compactly supported and smooth (C²) -/
def CompactlySupportedSmooth (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ HasCompactSupport f

end EfronSteinApp
