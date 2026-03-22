/-
SGD Convergence with Unique Minimizer - Specification

This file specifies the corollary to the SGD convergence theorem
in the case where the drift condition has a unique zero.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set BigOperators
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-! ### Definitions from Registry.ArtificialTheorems.Opt.SGD -/

/-- Assumptions for Theorem 2.3.6.
Encapsulates H1 (Drift), H2 (Perturbations), and step size conditions. -/
structure SGD_Convergence_Assumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM R : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E)
    (ℱ : Filtration ℕ m0) : Prop where

  -- Step Size Conditions (Eq 2.6)
  gamma_pos : ∀ n, 0 < γ n
  gamma_sum_inf : ¬ Summable γ
  gamma_sq_sum_fin : Summable (fun n => (γ n) ^ 2)
  gamma_le_one : ∀ n, γ n ≤ 1

  -- Regularity of V (C² L-smooth / sub-quadratic)
  V_smooth : ContDiff ℝ 2 V
  V_grad_eq : ∀ x, gradient V x = gradV x
  V_grad_lipschitz : ∃ L : ℝ, 0 < L ∧ ∀ x y, ‖gradV x - gradV y‖ ≤ L * ‖x - y‖

  -- (H1) Drift Assumptions
  V_lower_bound : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ V x
  V_coercive : Tendsto V (cocompact E) atTop
  drift_nonneg : ∀ x, 0 ≤ @inner ℝ _ _ (gradV x) (h x)
  growth_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖h x‖^2 + ‖gradV x‖^2 ≤ C * (1 + V x)

  -- Regularity of drift direction
  h_continuous : Continuous h

  -- (H2) Perturbations
  martingale_diff_adapted : Adapted ℱ ΔM
  martingale_diff_condexp : ∀ n, μ[ΔM (n + 1)|ℱ n] =ᵐ[μ] 0
  martingale_condvar_bound : ∃ C : ℝ, 0 < C ∧ ∀ n,
    μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun ω => C * (1 + V (X n ω))
  martingale_diff_L2 : ∀ n, Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ

  remainder_adapted : Adapted ℱ R
  remainder_condvar_bound : ∃ C : ℝ, 0 < C ∧ ∀ n,
    μ[fun ω => ‖R (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun ω => C * (γ (n + 1))^2 * (1 + V (X n ω))
  remainder_L2 : ∀ n, Integrable (fun ω => ‖R (n + 1) ω‖^2) μ

  -- Process adaptedness
  X_adapted : Adapted ℱ X

  -- Initial condition has finite expected energy
  V_X0_integrable : Integrable (fun ω => V (X 0 ω)) μ

/-! ### SGDUniqueMin spec -/

namespace SGDUniqueMin

variable [FiniteDimensional ℝ E]

/-- Simplified SGD assumptions for unbiased gradients with bounded variance. -/
structure SimplifiedAssumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E)
    (ℱ : Filtration ℕ m0)
    (x_star : E) : Prop where

  /-- Base SGD assumptions with R = 0.
      This gives us convergence_stochastic_gradient_method for free. -/
  base : SGD_Convergence_Assumptions μ X γ h ΔM (fun _ _ => 0) V gradV ℱ

  /-- KEY SIMPLIFICATION: Variance bound is CONSTANT, not state-dependent.
      This is stronger than base.martingale_condvar_bound and makes
      the noise summability argument much simpler. -/
  martingale_condvar_bound_const : ∃ σ : ℝ, 0 < σ ∧ ∀ n,
    μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun _ => σ^2

  /-- Recursion matches the StochasticAlgorithm form with R = 0. -/
  recursion : ∀ n ω, X (n + 1) ω = X n ω - (γ (n + 1)) • h (X n ω) + (γ (n + 1)) • ΔM (n + 1) ω

  /-- Unique zero of drift - this is what makes convergence to x* work. -/
  drift_zero_unique : {x : E | @inner ℝ _ _ (gradV x) (h x) = 0} = {x_star}

/-- Simplified Corollary 2.3.1: Almost sure convergence for unbiased SGD with bounded variance.

Under the simplified assumptions (unbiased gradients, constant variance bound), we have:
- X_n → x* almost surely

The proof is simpler because:
1. No remainder term R (so the earlier "line 1375" gap disappears)
2. Constant variance ⟹ E[‖∑ γ_k ΔM_k‖²] ≤ σ² ∑ γ_k² < ∞ directly
3. L²-bounded martingale converges a.s. by Doob's theorem
-/
theorem convergence_simplified
    (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM : ℕ → Ω → E)
    (V : E → ℝ) (gradV : E → E) (ℱ : Filtration ℕ m0) (x_star : E)
    (asm : SimplifiedAssumptions μ X γ h ΔM V gradV ℱ x_star) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds x_star) := by
  sorry

end SGDUniqueMin
