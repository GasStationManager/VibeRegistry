/-
  VibeRegistry spec: Viridis Canon ACC, module Mixture

  Source: https://github.com/jdhart81/viridis-canon
  Module: PaperFormalization.Mixture (series/ACC)

  Generated from the implementation by copying every definition, instance and
  section variable verbatim and replacing only the proofs of the listed target
  theorems with `sorry`. Lemmas the targets do not need are omitted; lemmas a
  definition's value uses are kept with their proofs (VibeRegistry spec rule 9).
-/

import Registry.ViridisCanon.ACC.Prior

/-!
# The change-time mixture `M_n` of Run-129

This file formalizes the recursion of Equation (2) in `SEALED_paper.tex`:

  `A_0 = 0`,  `A_n = Λ_n (A_{n-1} + π_n)`,  `M_n = A_n + t_n`.

Everything in this file is *pathwise* (no measure theory): the accumulator `mixAcc`,
the mixture `mixture`, nonnegativity, `M_0 = 1`, adaptedness, and the component
dominance bound `M_n ≥ π_ν ∏_{i=ν}^{n} Λ_i` of Equation (5).

`Λ` is the sequence of likelihood ratios `Λ_n = dP₁/dP₀(X_n)`; it is an arbitrary
sequence of functions here, and all distributional assumptions are made where needed.
-/

namespace Viridis.Run129.PaperFormalization

open MeasureTheory

variable {Ω : Type*}

/-- The accumulator `A_n` of Equation (2): `A_0 = 0` and `A_n = Λ_n (A_{n-1} + π_n)`. -/
noncomputable def mixAcc (Λ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => Λ (n + 1) ω * (mixAcc Λ n ω + changePrior (n + 1))

@[simp] lemma mixAcc_zero (Λ : ℕ → Ω → ℝ) : mixAcc Λ 0 = fun _ => 0 := rfl

/-- The change-time mixture `M_n = A_n + t_n` of Equation (2). -/
noncomputable def mixture (Λ : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => mixAcc Λ n ω + priorTail n

/-- `M_0 = 1`. -/
@[simp] lemma mixture_zero (Λ : ℕ → Ω → ℝ) : mixture Λ 0 = fun _ => (1 : ℝ) := by
  funext ω; simp [mixture]

section Nonneg

variable {Λ : ℕ → Ω → ℝ} (hΛ : ∀ n ω, 0 ≤ Λ n ω)
include hΛ

end Nonneg

section Dominance

variable {Λ : ℕ → Ω → ℝ} (hΛ : ∀ n ω, 0 ≤ Λ n ω)
include hΛ

end Dominance

section Adapted

variable {m0 : MeasurableSpace Ω} {Λ : ℕ → Ω → ℝ}

end Adapted

section Integrability

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω} {Λ : ℕ → Ω → ℝ}

end Integrability

end Viridis.Run129.PaperFormalization
