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
(`AmbientSpace`, `NormalizedEllipticCoeff`, `IsSolution`), but not
`DeGiorgi.Harnack` itself — that would collide with the spec's own
declaration of `harnack`. The constant `C_harnack` is defined inside
`DeGiorgi.Harnack`, so we restate its signature here with a `sorry` body.
SafeVerify's `equivDefn` skips value comparison when the spec's def has
`sorryAx` in its axioms (Util.lean:22-31), so the impl's actual numeric
formula is accepted without value-mismatch noise. The verified claim is
therefore existential in the constant: "there exists `C_harnack : ℕ → ℝ`
such that the Harnack inequality holds with that constant" — the standard
textbook formulation. We do not use `local notation` here to avoid
generating spec-private notation declarations that the impl module
doesn't have.
-/

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

/-- Quantitative constant used to absorb the local-ball Harnack chain into the
final exponential form. Body left as `sorry` so SafeVerify skips value
comparison; the impl supplies the explicit formula. -/
noncomputable def C_harnack (d : ℕ) [NeZero d] : ℝ := sorry

/-- Positive weak solutions satisfy Harnack on the unit ball. -/
theorem harnack
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (Metric.ball (0 : AmbientSpace d) 1))
    {u : AmbientSpace d → ℝ}
    (hu_pos : ∀ x ∈ Metric.ball (0 : AmbientSpace d) 1, 0 < u x)
    (hsol : IsSolution A.1 u) :
    essSup u (volume.restrict (Metric.ball (0 : AmbientSpace d) (1 / 2 : ℝ))) ≤
      Real.exp (C_harnack d * A.1.Λ ^ ((1 : ℝ) / 2)) *
        essInf u (volume.restrict (Metric.ball (0 : AmbientSpace d) (1 / 2 : ℝ))) := by
  sorry

end DeGiorgi
