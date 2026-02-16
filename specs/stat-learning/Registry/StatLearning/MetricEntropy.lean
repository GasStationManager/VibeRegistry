/-
Metric Entropy Definitions - Specification
Definitions from SLT.MetricEntropy
-/

import Mathlib
import Registry.StatLearning.CoveringNumber

noncomputable section

open Set Metric Real MeasureTheory
open scoped ENNReal

variable {A : Type*} [PseudoMetricSpace A]

/-- Helper to compute metric entropy given a natural number. -/
def metricEntropyOfNat (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else Real.log n

/-- Metric entropy: log of covering number. -/
def metricEntropy (eps : ℝ) (s : Set A) : ℝ :=
  match _h : coveringNumber eps s with
  | ⊤ => 0
  | (n : ℕ) => metricEntropyOfNat n

/-- Square root of metric entropy. -/
def sqrtEntropy (eps : ℝ) (s : Set A) : ℝ :=
  Real.sqrt (metricEntropy eps s)

/-- Dudley integrand: √(log N(ε, s)) as ENNReal. -/
def dudleyIntegrand (eps : ℝ) (s : Set A) : ℝ≥0∞ :=
  ENNReal.ofReal (sqrtEntropy eps s)

/-- Entropy integral (ENNReal): ∫₀^D √(log N(ε, s)) dε. -/
def entropyIntegralENNReal (s : Set A) (D : ℝ) : ℝ≥0∞ :=
  ∫⁻ eps in Set.Ioc (0 : ℝ) D, dudleyIntegrand eps s

/-- Entropy integral (real-valued wrapper). -/
def entropyIntegral (s : Set A) (D : ℝ) : ℝ :=
  (entropyIntegralENNReal s D).toReal

end
