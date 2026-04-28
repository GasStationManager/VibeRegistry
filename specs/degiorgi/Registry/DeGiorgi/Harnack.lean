import DeGiorgi.EllipticCoefficients
import DeGiorgi.WeakFormulation.SolutionInterfaces
import DeGiorgi.MoserIteration.Constants
import DeGiorgi.WeakHarnack
import DeGiorgi.ScaledBallEstimates
import Mathlib.MeasureTheory.Function.EssSup

/-!
# DeGiorgi Harnack — Spec

Sorry'd statement of the Harnack inequality for positive weak solutions on
the unit ball, as proved in `DeGiorgi.Harnack`.

We import the upstream modules that define the supporting structures
(`AmbientSpace`, `NormalizedEllipticCoeff`, `IsSolution`) and the constants
used inside `C_harnack`, but not `DeGiorgi.Harnack` itself — that would
collide with the spec's own declaration of `harnack`. The constant
`C_harnack` is defined inside `DeGiorgi.Harnack`, so we restate it here
verbatim.
-/

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d
local notation "μhalf" => volume.restrict (Metric.ball (0 : E) (1 / 2 : ℝ))

/-- Quantitative constant used to absorb the local-ball Harnack chain into the
final exponential form. -/
noncomputable def C_harnack (d : ℕ) [NeZero d] : ℝ :=
  17 *
    (((d : ℝ) - 2) / ((d : ℝ) - 1) *
        Real.log
          (C_Moser d * (((d : ℝ) - 1) ^ (d : ℝ)) * ((4 : ℝ) ^ (d : ℝ))) +
      (d : ℝ) +
      Real.log (C_weakHarnack_of d * ((d : ℝ) ^ (weak_harnack_decay_exp d))))

/-- Positive weak solutions satisfy Harnack on the unit ball. -/
theorem harnack
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : E) 1))
    {u : E → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : E) 1, 0 < u x)
    (hsol : IsSolution A.1 u) :
    essSup u μhalf ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u μhalf := by
  sorry

end DeGiorgi
