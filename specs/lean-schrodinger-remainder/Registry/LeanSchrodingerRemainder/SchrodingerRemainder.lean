import Mathlib.Analysis.Real.Sqrt

/-!
# Conditional Schrödinger kinetic-energy remainder

This independent specification isolates two algebraic results from the public
LeanSchrodingerDerivation release. Starting from the positive relativistic
energy branch, the rest-energy-removed kinetic energy is the Schrödinger term
plus an explicit remainder, and the remainder has a uniform quartic bound.

The statement is conditional. It does not derive the relativistic mass shell,
an arbitrary-wavefunction position-space equation, Born's rule, or a complete
quantum theory.
-/

namespace SchrodingerFormal

noncomputable section

def relativisticEnergy (mass momentum : ℝ) : ℝ :=
  Real.sqrt (mass ^ 2 + momentum ^ 2)

def restPhaseRemovedEnergy (mass momentum : ℝ) : ℝ :=
  relativisticEnergy mass momentum - mass

def schrodingerEnergy (mass momentum : ℝ) : ℝ :=
  momentum ^ 2 / (2 * mass)

def schrodingerRemainder (mass momentum : ℝ) : ℝ :=
  -(momentum ^ 4) /
    (2 * mass * (relativisticEnergy mass momentum + mass) ^ 2)

theorem rest_phase_removed_energy_eq_schrodinger_plus_remainder
    (mass momentum : ℝ) (hMass : 0 < mass) :
    restPhaseRemovedEnergy mass momentum =
      schrodingerEnergy mass momentum + schrodingerRemainder mass momentum := by
  sorry

theorem schrodinger_remainder_bound
    (mass momentum : ℝ) (hMass : 0 < mass) :
    |schrodingerRemainder mass momentum| ≤ momentum ^ 4 / (8 * mass ^ 3) := by
  sorry

end

end SchrodingerFormal
