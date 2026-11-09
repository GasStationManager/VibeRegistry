/-
  VibeRegistry spec: Viridis Canon ACC, module Dominance

  Source: https://github.com/jdhart81/viridis-canon
  Module: PaperFormalization.Dominance (series/ACC)

  Generated from the implementation by copying every definition, instance and
  section variable verbatim and replacing only the proofs of the listed target
  theorems with `sorry`. Lemmas the targets do not need are omitted; lemmas a
  definition's value uses are kept with their proofs (VibeRegistry spec rule 9).
-/

import Registry.ViridisCanon.ACC.Mixture

/-!
# C3: component dominance and the late-change evidence penalty

This file formalizes Equations (5)–(6) of `SEALED_paper.tex`:

* `M_n ≥ π_ν ∏_{i=ν}^{n} Λ_i` (Equation 5), hence the mixture alarm time is never later
  than the alarm time of the embedded change-time-`ν` component;
* `a_ν = log(1/(α π_ν)) = log(1/α) + log[ν(ν+1)]` (Equation 6), whose late-change part
  `log[ν(ν+1)]` is asymptotically `2 log ν`.

The alarm time is formalized by `firstAlarm f c`, the first index at which the path `f`
reaches the level `c`, valued in `ℕ∞` so that "never alarms" is represented by `⊤`.
-/

namespace Viridis.Run129.PaperFormalization

open Filter
open scoped Topology

variable {Ω : Type*}

/-- The first index at which the path `f` reaches level `c`, or `⊤` if it never does. -/
noncomputable def firstAlarm (f : ℕ → ℝ) (c : ℝ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n : ℕ | c ≤ f n})

/-- The embedded change-time-`ν` likelihood-ratio component `π_ν ∏_{i=ν}^{n} Λ_i`. -/
noncomputable def component (Λ : ℕ → Ω → ℝ) (ν : ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  changePrior ν * ∏ i ∈ Finset.Icc ν n, Λ i ω

/-- The evidence boundary `a_ν = log(1/(α π_ν))` of Equation (6). -/
noncomputable def evidenceBoundary (α : ℝ) (ν : ℕ) : ℝ := Real.log (1 / (α * changePrior ν))

/-- **C3** (`change_component_dominance_and_penalty`, Equations 5–6).

1. Equation (5): the mixture dominates the embedded change-time-`ν` component pathwise.
2. Consequently the mixture alarm time at threshold `1/α` is never later than the alarm
   time of that component ("the mixture stops no later than the embedded true-change
   component").
3. Equation (6): the evidence the component must accumulate is
   `a_ν = log(1/α) + log[ν(ν+1)]`, exhibiting the late-change penalty `log[ν(ν+1)]`. -/
theorem change_component_dominance_and_penalty (Λ : ℕ → Ω → ℝ) (hΛ : ∀ n ω, 0 ≤ Λ n ω)
    {ν : ℕ} (hν : 1 ≤ ν) {α : ℝ} (hα : 0 < α) :
    (∀ n ω, component Λ ν n ω ≤ mixture Λ n ω) ∧
    (∀ ω, firstAlarm (fun n => mixture Λ n ω) (1 / α)
        ≤ firstAlarm (fun n => component Λ ν n ω) (1 / α)) ∧
    evidenceBoundary α ν = Real.log (1 / α) + Real.log ((ν : ℝ) * ((ν : ℝ) + 1)) := by
  sorry

end Viridis.Run129.PaperFormalization
