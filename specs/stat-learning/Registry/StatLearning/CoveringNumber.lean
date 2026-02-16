/-
Covering Number Definitions - Specification
Definitions from SLT.CoveringNumber
-/

import Mathlib

open Set Metric

/-- `t` is an `eps`-net for `s` if every point of `s` lies in a closed ball of radius `eps`
centered at some element of `t`. -/
def IsENet {A : Type*} [PseudoMetricSpace A] (t : Finset A) (eps : ℝ) (s : Set A) : Prop :=
  s ⊆ ⋃ x ∈ t, closedBall x eps

/-- Covering number: the minimal cardinality of a finite `eps`-net, as `WithTop Nat`. -/
noncomputable def coveringNumber {A : Type*} [PseudoMetricSpace A] (eps : ℝ) (s : Set A) : WithTop Nat :=
  sInf {n : WithTop Nat | ∃ t : Finset A, IsENet t eps s ∧ (t.card : WithTop Nat) = n}
