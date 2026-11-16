import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Independent specification for the C19 spatial-symbol results in
`LeanKleinGordonDerivation` v0.7.0-research.

The scope is deliberately narrow: this specifies the exact isotropic quadratic
moment, its coefficient, and the explicit quartic finite-spacing error. It does
not specify the full seven-stage derivation or a physical continuum-limit claim.
-/

namespace KleinGordonFormal

noncomputable section

abbrev Site := ℤ × ℤ × ℤ
abbrev WaveVector := ℝ × ℝ × ℝ

structure Bond where
  offset : Site
  weight : ℕ
  deriving DecidableEq

def positiveBonds : List Bond :=
  [⟨(1, 0, 0), 2⟩, ⟨(0, 1, 0), 2⟩, ⟨(0, 0, 1), 2⟩,
   ⟨(1, 1, 0), 1⟩, ⟨(1, -1, 0), 1⟩, ⟨(1, 0, 1), 1⟩,
   ⟨(1, 0, -1), 1⟩, ⟨(0, 1, 1), 1⟩, ⟨(0, 1, -1), 1⟩]

def dotSite (k : WaveVector) (s : Site) : ℝ :=
  k.1 * s.1 + k.2.1 * s.2.1 + k.2.2 * s.2.2

def spaceSymbol (k : WaveVector) : ℝ :=
  4 * (positiveBonds.map fun b =>
    (b.weight : ℝ) * (1 - Real.cos (dotSite k b.offset))).sum

def scaleWave (h : ℝ) (k : WaveVector) : WaveVector :=
  (h * k.1, h * k.2.1, h * k.2.2)

def waveNormSq (k : WaveVector) : ℝ :=
  k.1 ^ 2 + k.2.1 ^ 2 + k.2.2 ^ 2

def speedSq : ℝ :=
  2 * (positiveBonds.map fun b =>
    (b.weight : ℝ) * (b.offset.1 : ℝ) ^ 2).sum

def spatialErrorWeight (k : WaveVector) : ℝ :=
  (positiveBonds.map fun b =>
    (b.weight : ℝ) * (dotSite k b.offset) ^ 4).sum / 6

theorem c19_isotropic_moment (k : WaveVector) :
    2 * (positiveBonds.map fun b =>
      (b.weight : ℝ) * (dotSite k b.offset) ^ 2).sum =
      speedSq * waveNormSq k := by sorry

theorem c19_speed_squared : speedSq = 12 := by sorry

theorem c19_spatial_error (h : ℝ) (k : WaveVector) :
    |spaceSymbol (scaleWave h k) - h ^ 2 * (speedSq * waveNormSq k)| ≤
      h ^ 4 * spatialErrorWeight k := by sorry

end
end KleinGordonFormal
