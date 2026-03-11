/-
  # Spec for O(log n)-depth sorting networks (girving/aks)

  Source: https://github.com/girving/aks/blob/main/Challenge.lean
  Theorem: `networks_exist` from `AKS/Seiferas.lean`

  Proves existence of comparator sorting networks with O(log n) depth
  and O(n log n) size, formalizing the AKS sorting network construction.
-/

import AKS.Bags.Depth
import AKS.Sort.ZeroOne

/-! **O(log n)-depth, O(n log n)-size networks exist** -/

/-- Efficient networks exist -/
theorem networks_exist (n : ℕ) : ∃ net : ComparatorNetwork n, net.Sorts ∧
    net.depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n ∧
    net.size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n := by sorry
