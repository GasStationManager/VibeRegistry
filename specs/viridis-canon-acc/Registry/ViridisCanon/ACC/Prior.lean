/-
  VibeRegistry spec: Viridis Canon ACC, module Prior

  Source: https://github.com/jdhart81/viridis-canon
  Module: PaperFormalization.Prior (series/ACC)

  Generated from the implementation by copying every definition, instance and
  section variable verbatim and replacing only the proofs of the listed target
  theorems with `sorry`. Lemmas the targets do not need are omitted; lemmas a
  definition's value uses are kept with their proofs (VibeRegistry spec rule 9).
-/

import Mathlib

/-!
# The heavy-tailed change-time prior of Run-129

This file formalizes Equation (1) of the sealed paper `SEALED_paper.tex`:

  `π_k = 1 / (k (k+1))`,  `t_n = ∑_{k > n} π_k = 1 / (n+1)`.

`changePrior` is `π` and `priorTail` is `t`.  Both are defined for every natural index;
the paper only uses `k ≥ 1` for `π` (and `changePrior 0 = 0` in Lean, which is harmless
since the index `0` never occurs in the recursion).

The two facts that the rest of the development needs are

* `changePrior_add_priorTail`: `π_{n+1} + t_{n+1} = t_n` (the identity `π_n + t_n = t_{n-1}`
  used in the martingale computation), and
* `hasSum_changePrior_tail`: `t_n` really is the tail mass `∑_{k > n} π_k` of the prior,
  so in particular (`hasSum_changePrior`) `π` is a probability distribution on `{1, 2, …}`.
-/

namespace Viridis.Run129.PaperFormalization

open scoped Topology
open Filter

/-- The heavy-tailed change-time prior `π_k = 1 / (k (k+1))` of Equation (1). -/
noncomputable def changePrior (k : ℕ) : ℝ := 1 / ((k : ℝ) * (k + 1))

/-- The prior tail mass `t_n = ∑_{k>n} π_k = 1 / (n+1)` of Equation (1). -/
noncomputable def priorTail (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

@[simp] lemma priorTail_zero : priorTail 0 = 1 := by norm_num [priorTail]

end Viridis.Run129.PaperFormalization
