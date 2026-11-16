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

/-- A positively oriented representative of a C19 lattice bond. -/
structure Bond where
  x : Int
  y : Int
  z : Int
  weightSixths : Int
  deriving DecidableEq, Repr

/-- The three positive face bonds followed by the six positive edge bonds. -/
def positiveC19 : List Bond := [
  ⟨1, 0, 0, 2⟩, ⟨0, 1, 0, 2⟩, ⟨0, 0, 1, 2⟩,
  ⟨1, 1, 0, 1⟩, ⟨1, -1, 0, 1⟩,
  ⟨1, 0, 1, 1⟩, ⟨1, 0, -1, 1⟩,
  ⟨0, 1, 1, 1⟩, ⟨0, 1, -1, 1⟩
]

def positiveFaceC19 : List Bond :=
  positiveC19.filter (fun b => b.weightSixths = 2)

def positiveEdgeC19 : List Bond :=
  positiveC19.filter (fun b => b.weightSixths = 1)

def directedFaceModeCount : Nat := 2 * positiveFaceC19.length

def directedEdgeModeCount : Nat := 2 * positiveEdgeC19.length

noncomputable def chi0FromC19 : ℝ :=
  Nat.cast (1 + directedFaceModeCount + directedEdgeModeCount : Nat)

noncomputable def kappaDenominatorFromDimension : ℝ :=
  Nat.cast (4 ^ 3 - 1 : Nat)

noncomputable def kappaFromGeometry : ℝ :=
  1 / kappaDenominatorFromDimension

noncomputable def BFromGeometry : ℝ :=
  chi0FromC19 / kappaFromGeometry

def redshiftLWChi0 : ℝ := chi0FromC19

def redshiftLWB : ℝ := BFromGeometry

/-- The explicit side condition used by Lean's real numeral elaboration. -/
theorem redshiftLWStructureFactor._proof_1 : (7 + 1).AtLeastTwo :=
  Nat.instAtLeastTwoHAddOfNat 7

attribute [local instance] redshiftLWStructureFactor._proof_1

/-- The C19 Fourier structure factor used by the declared phase branch. -/
def redshiftLWStructureFactor (k0 k1 k2 : ℝ) : ℝ :=
  8 * ((1 - Real.cos k0) + (1 - Real.cos k1) + (1 - Real.cos k2)) +
    8 * ((1 - Real.cos k0 * Real.cos k1) +
      (1 - Real.cos k0 * Real.cos k2) +
      (1 - Real.cos k1 * Real.cos k2))

/-- The phase stiffness using the scale derived from the C19 geometry. -/
def redshiftLWPhaseStiffness
    (psiRadius chiRadius k0 k1 k2 : ℝ) : ℝ :=
  (psiRadius ^ 2 * chiRadius ^ 2 / redshiftLWChi0 ^ 2) *
    redshiftLWStructureFactor k0 k1 k2

/-- The nonzero phase eigenvalue using the geometry-derived substrate inertia. -/
def redshiftLWPhasePropagatingOmegaSquared
    (psiRadius chiRadius k0 k1 k2 : ℝ) : ℝ :=
  redshiftLWPhaseStiffness psiRadius chiRadius k0 k1 k2 *
    (1 / psiRadius ^ 2 + 1 / (redshiftLWB * chiRadius ^ 2))

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
