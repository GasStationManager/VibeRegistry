/-
  # Spec for O(log n)-depth sorting networks (girving/aks)

  Source: https://github.com/girving/aks/blob/main/Challenge.lean
  Theorem: `networks_exist` from `AKS/Seiferas.lean`

  Imports match AKS.Seiferas's direct imports to satisfy SafeVerify's
  import superset check. All needed defs (ComparatorNetwork, Nat.clog, etc.)
  come in transitively via the AKS module tree.
-/

import AKS.Bags.Depth
import AKS.Sort.ZeroOne

/-! **O(log n)-depth, O(n log n)-size networks exist** -/

/-- Efficient networks exist -/
theorem networks_exist (n : ℕ) : ∃ net : ComparatorNetwork n, net.Sorts ∧
    net.depth ≤ 141 * 10 ^ 62 * Nat.clog 2 n ∧
    net.size ≤ 705 * 10 ^ 61 * n * Nat.clog 2 n := by sorry
