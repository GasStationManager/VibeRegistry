module

public import Mathlib

public section

/-!
# Cubical C19 first-order factorization

Eight complex amplitudes live on the corners of a cube. The three signed
corner flips are fixed by cubical incidence and orientation. The theorem
states that the resulting first-order cubical symbol, applied twice, is
exactly the isotropic quadratic C19 continuum symbol.

This is an algebraic operator claim. It does not claim a localized electron,
physical spin, or an exact finite-spacing Dirac equation.
-/

namespace LFMDiracChallenge

noncomputable section

abbrev CubeCorner := Fin 8
abbrev Cell8 := CubeCorner → ℂ

/-- Flip the first parity bit of an eight-corner cube. -/
def cellFlip0 : CubeCorner → CubeCorner
  | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7
  | 4 => 0 | 5 => 1 | 6 => 2 | _ => 3

/-- Flip the second parity bit of an eight-corner cube. -/
def cellFlip1 : CubeCorner → CubeCorner
  | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
  | 4 => 6 | 5 => 7 | 6 => 4 | _ => 5

/-- Flip the third parity bit of an eight-corner cube. -/
def cellFlip2 : CubeCorner → CubeCorner
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  | 4 => 5 | 5 => 4 | 6 => 7 | _ => 6

/-- Read the third parity bit of a cube corner. -/
def cellBit2 : CubeCorner → Nat
  | 0 | 2 | 4 | 6 => 0
  | _ => 1

/-- Read the first parity bit of a cube corner. -/
def cellBit0 : CubeCorner → Nat
  | 0 | 1 | 2 | 3 => 0
  | _ => 1

/-- Read the second parity bit of a cube corner. -/
def cellBit1 : CubeCorner → Nat
  | 0 | 1 | 4 | 5 => 0
  | _ => 1

/-- Select the corner flip associated with one of the three cube axes. -/
def cubeIncidenceFlip (axis : Fin 3) : CubeCorner → CubeCorner :=
  match axis with
  | 0 => cellFlip0
  | 1 => cellFlip1
  | _ => cellFlip2

/-- The orientation sign for an axis crossing at a cube corner. -/
def cubeIncidenceSign (axis : Fin 3) (corner : CubeCorner) : ℂ :=
  match axis with
  | 0 => 1
  | 1 => if cellBit0 corner = 0 then 1 else -1
  | _ => if (cellBit0 corner + cellBit1 corner) % 2 = 0 then 1 else -1

/-- The signed incidence operation along one cube axis. -/
def cubeIncidenceGamma (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    cubeIncidenceSign axis corner *
      amplitude (cubeIncidenceFlip axis corner)

/-- Grade a corner amplitude by even or odd cube parity. -/
def cubeParityBeta (amplitude : Cell8) : Cell8 :=
  fun corner =>
    if (cellBit0 corner + cellBit1 corner + cellBit2 corner) % 2 = 0 then
      amplitude corner
    else
      -amplitude corner

/-- The linear combination of the three signed cube-incidence operations. -/
def cubeIncidenceLinear
    (k0 k1 k2 : ℂ) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    k0 * cubeIncidenceGamma 0 amplitude corner +
    k1 * cubeIncidenceGamma 1 amplitude corner +
    k2 * cubeIncidenceGamma 2 amplitude corner

/-- Add a parity-graded rest coefficient to the cubical incidence symbol. -/
def cubeDiracSymbol
    (mass k0 k1 k2 : ℂ) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    mass * cubeParityBeta amplitude corner +
      cubeIncidenceLinear k0 k1 k2 amplitude corner

/-- The isotropic long-wavelength speed fixed by the C19 stencil moments. -/
def c19ContinuumSpeed : ℝ := Real.sqrt 12

/-- The cube-incidence first-order symbol at C19 continuum normalization. -/
def c19ContinuumDiracSymbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) : Cell8 :=
  cubeDiracSymbol mass
    (c19ContinuumSpeed * momentum 0)
    (c19ContinuumSpeed * momentum 1)
    (c19ContinuumSpeed * momentum 2) amplitude

/-- The isotropic quadratic low-momentum symbol of the C19 stencil. -/
def c19ContinuumScalarSymbol
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    (mass ^ 2 + (12 : ℂ) *
      ((momentum 0 : ℂ) ^ 2 + (momentum 1 : ℂ) ^ 2 +
        (momentum 2 : ℂ) ^ 2)) * amplitude corner

/--
The cubical signed-incidence first-order symbol squares exactly to the
isotropic quadratic symbol obtained from the low-momentum C19 stencil.
-/
theorem main_result
    (mass : ℂ) (momentum : Fin 3 → ℝ) (amplitude : Cell8) :
    c19ContinuumDiracSymbol mass momentum
        (c19ContinuumDiracSymbol mass momentum amplitude) =
      c19ContinuumScalarSymbol mass momentum amplitude := by
  sorry

end

end LFMDiracChallenge
