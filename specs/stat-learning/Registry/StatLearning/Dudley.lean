/-
Dudley's Entropy Integral Theorem - Specification
Boucheron et al. (2013), Corollary 13.2
-/

import Mathlib.Probability.Moments.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Finset.Card

noncomputable section

open Set Metric Real MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators ENNReal
open Classical

/-! ### Definitions from Registry.StatLearning.CoveringNumber -/

section CoveringNumberDefs
variable {A : Type*} [PseudoMetricSpace A]

/-- `t` is an `eps`-net for `s`. -/
def IsENet (t : Finset A) (eps : ℝ) (s : Set A) : Prop :=
  s ⊆ ⋃ x ∈ t, closedBall x eps

/-- Covering number: the minimal cardinality of a finite `eps`-net, as `WithTop Nat`. -/
noncomputable def coveringNumber (eps : ℝ) (s : Set A) : WithTop Nat :=
  sInf {n : WithTop Nat | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop Nat) = n}

end CoveringNumberDefs

/-! ### Definitions from Registry.StatLearning.MetricEntropy -/

section MetricEntropyDefs
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

end MetricEntropyDefs

/-! ### Definition from Registry.StatLearning.SubGaussian -/

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {A : Type v} [PseudoMetricSpace A]

/-- A stochastic process X indexed by a metric space is σ-sub-Gaussian if
the MGF of increments satisfies E[exp(l(X_s - X_t))] ≤ exp(l²σ²d(s,t)²/2). -/
def IsSubGaussianProcess (μ : Measure Ω) (X : A → Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ s t : A, ∀ l : ℝ, μ[fun ω => exp (l * (X s ω - X t ω))] ≤
    exp (l^2 * σ^2 * (dist s t)^2 / 2)

/-! ### Dudley theorem -/

/-- **Dudley's Entropy Integral Theorem**

For a σ-sub-Gaussian process X indexed by a totally bounded set s with diameter ≤ D,
the expected supremum satisfies:
  E[sup_{t∈s} X_t] ≤ 12√2 · σ · ∫₀^D √(log N(ε, s)) dε -/
theorem dudley {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : A → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hX : IsSubGaussianProcess μ X σ)
    {s : Set A} (hs : TotallyBounded s)
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam s ≤ D)
    (t₀ : A) (ht₀ : t₀ ∈ s) (hcenter : ∀ ω, X t₀ ω = 0)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_int_exp : ∀ t s : A, ∀ l : ℝ, Integrable (fun ω => Real.exp (l * (X t ω - X s ω))) μ)
    (hfinite : entropyIntegralENNReal s D ≠ ⊤)
    (hcont : ∀ ω, Continuous (fun (t : ↥s) => X t.1 ω)) :
    ∫ ω, ⨆ t ∈ s, X t ω ∂μ ≤ (12 * Real.sqrt 2) * σ * entropyIntegral s D := by
  sorry

end
