/-
Universal Approximation Theorem (Cybenko 1989) - Registry Spec

Cybenko, G. "Approximation by Superpositions of a Sigmoidal Function."
Mathematics of Control, Signals, and Systems 2 (1989): 303–314.
-/

import Mathlib

open MeasureTheory Topology ContinuousMap Set Filter

noncomputable section

variable {n : ℕ}

def UnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

def neuralNetFun (σ : ℝ → ℝ) (N : ℕ)
    (w : Fin N → (Fin n → ℝ))
    (b : Fin N → ℝ)
    (α : Fin N → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin N, α j * σ (∑ i : Fin n, w j i * x i + b j)

def IsSigmoidal (σ : ℝ → ℝ) : Prop :=
  Tendsto σ atTop (nhds 1) ∧ Tendsto σ atBot (nhds 0)

def IsPositiveLinearFunctional
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : C(↥(UnitCube n), ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f

/-- Jordan decomposition of continuous linear functionals on C(Iₙ,ℝ).
    Classical result (Rudin RCA Thm 6.19 + 6.12; Aliprantis & Border Thms 9.11, 9.14).
    Not in Mathlib v4.27.0. -/
def HasJordanDecomposition (n : ℕ) : Prop :=
  ∀ (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
    ∃ (Lpos Lneg : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
      IsPositiveLinearFunctional Lpos ∧
      IsPositiveLinearFunctional Lneg ∧
      ∀ f, L f = Lpos f - Lneg f

/-- **Cybenko's Universal Approximation Theorem (1989).** -/
theorem universal_approximation_cybenko
    (hJD : HasJordanDecomposition n)
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (f : (Fin n → ℝ) → ℝ) (hf_cont : ContinuousOn f (UnitCube n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
      ∀ x ∈ UnitCube n,
        |f x - neuralNetFun σ N w b α x| < ε := by
  sorry

end
