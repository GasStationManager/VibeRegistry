/-
Efron-Stein Inequality - Specification
Boucheron et al. (2013), Theorem 3.1
-/

import Mathlib

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μs : Fin n → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]

/-- Conditional expectation of f given all variables except the i-th:
E^{(i)}[f](x) = ∫ f(x₁,...,x_{i-1}, y, x_{i+1},...,xₙ) dμᵢ(y) -/
noncomputable def condExpExceptCoord (i : Fin n) (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ :=
  fun x => ∫ y, f (Function.update x i y) ∂(μs i)

/-- **Efron-Stein Inequality**

For independent random variables X₁,...,Xₙ and a square-integrable function f:
  Var(f) ≤ ∑ᵢ E[(f - E^{(i)}f)²]
where E^{(i)}f is the conditional expectation given all variables except Xᵢ. -/
theorem efronStein (f : (Fin n → Ω) → ℝ) (hf : MemLp f 2 (Measure.pi μs)) :
    variance f (Measure.pi μs) ≤
    ∑ i : Fin n, ∫ x, (f x - condExpExceptCoord (μs := μs) i f x)^2 ∂(Measure.pi μs) := by
  sorry
