/-
Efron-Stein Application Definitions - Specification
Definition from SLT.GaussianPoincare.EfronSteinApp
-/

import Mathlib

namespace EfronSteinApp

/-- A function is compactly supported and smooth (C²) -/
def CompactlySupportedSmooth (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ HasCompactSupport f

end EfronSteinApp
