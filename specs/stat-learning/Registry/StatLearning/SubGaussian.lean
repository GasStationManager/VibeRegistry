/-
Sub-Gaussian Process Definition - Specification
Definition from SLT.SubGaussian
-/

import Mathlib

universe u v

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type u} [MeasurableSpace Ω] {A : Type v} [PseudoMetricSpace A]

/-- A stochastic process X indexed by a metric space is σ-sub-Gaussian if
the MGF of increments satisfies E[exp(l(X_s - X_t))] ≤ exp(l²σ²d(s,t)²/2). -/
def IsSubGaussianProcess (μ : Measure Ω) (X : A → Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ s t : A, ∀ l : ℝ, μ[fun ω => exp (l * (X s ω - X t ω))] ≤
    exp (l^2 * σ^2 * (dist s t)^2 / 2)
