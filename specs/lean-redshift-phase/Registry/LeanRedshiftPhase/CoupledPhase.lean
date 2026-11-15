module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

/-!
# C19 coupled-phase propagating gap

This specification isolates one spectral statement from the staged Redshift
derivation.  The declared phase branch has a positive propagating squared
frequency when both field radii are nonzero and the explicit C19 structure
factor is positive.

The statement is conditional.  It does not establish formation or nonlinear
stability of the branch, a physical photon, Einstein gravity, an SI scale, or
observational agreement.
-/

namespace RedshiftLWFormal

noncomputable section

/-- The C19 Fourier structure factor used by the declared phase branch. -/
def redshiftLWStructureFactor (k0 k1 k2 : ℝ) : ℝ :=
  8 * ((1 - Real.cos k0) + (1 - Real.cos k1) + (1 - Real.cos k2)) +
    8 * ((1 - Real.cos k0 * Real.cos k1) +
      (1 - Real.cos k0 * Real.cos k2) +
      (1 - Real.cos k1 * Real.cos k2))

/-- The phase stiffness after substituting the C19-derived value chi0 = 19. -/
def redshiftLWPhaseStiffness
    (psiRadius chiRadius k0 k1 k2 : ℝ) : ℝ :=
  (psiRadius ^ 2 * chiRadius ^ 2 / (19 : ℝ) ^ 2) *
    redshiftLWStructureFactor k0 k1 k2

/-- The nonzero phase eigenvalue after substituting the C19-derived B = 1197. -/
def redshiftLWPhasePropagatingOmegaSquared
    (psiRadius chiRadius k0 k1 k2 : ℝ) : ℝ :=
  redshiftLWPhaseStiffness psiRadius chiRadius k0 k1 k2 *
    (1 / psiRadius ^ 2 + 1 / ((1197 : ℝ) * chiRadius ^ 2))

/--
The declared coupled phase branch has a strictly positive propagating squared
frequency under explicit nonzero-radius and positive-mode assumptions.
-/
theorem redshiftLW_phase_propagating_gap_positive
    (psiRadius chiRadius k0 k1 k2 : ℝ)
    (hpsi : psiRadius ≠ 0)
    (hchi : chiRadius ≠ 0)
    (hmode : 0 < redshiftLWStructureFactor k0 k1 k2) :
    0 < redshiftLWPhasePropagatingOmegaSquared
      psiRadius chiRadius k0 k1 k2 := by
  sorry

end

end RedshiftLWFormal
