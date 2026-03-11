/-
  # Spec for O(log n)-depth sorting networks (girving/aks)

  Source: https://github.com/girving/aks/blob/main/Challenge.lean
  Theorem: `networks_exist` from `AKS/Seiferas.lean`

  Imports match AKS.Seiferas's direct imports so that SafeVerify's import
  superset check passes. Definitions are restated here for human review;
  SafeVerify checks they match the impl's definitions exactly.
-/

import AKS.Bags.Depth
import AKS.Sort.ZeroOne

/-! **Comparator network definitions (restated for review)** -/

-- These definitions are defined in AKS.Sort.Defs and imported transitively.
-- They are restated here as comments for human reviewers:
--
-- structure Comparator (n : ℕ) where
--   i : Fin n
--   j : Fin n
--   h : i < j
--
-- @[ext] structure ComparatorNetwork (n : ℕ) where
--   comparators : List (Comparator n)
--
-- def ComparatorNetwork.depth (net : ComparatorNetwork n) : ℕ := ...
-- def ComparatorNetwork.size (net : ComparatorNetwork n) : ℕ := ...
-- def ComparatorNetwork.exec (net : ComparatorNetwork n) (v : Fin n → α) : Fin n → α := ...
-- def ComparatorNetwork.Sorts (net : ComparatorNetwork n) : Prop := ...

/-! **O(log n)-depth, O(n log n)-size networks exist** -/

/-- Efficient networks exist -/
theorem networks_exist (n : ℕ) : ∃ net : ComparatorNetwork n, net.Sorts ∧
    net.depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n ∧
    net.size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n := by sorry
