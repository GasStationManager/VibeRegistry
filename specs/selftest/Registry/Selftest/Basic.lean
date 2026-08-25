/-
  Pipeline self-test spec. Standalone: imports nothing but Lean core.
-/

namespace Selftest

/-- Addition on `Nat` is commutative. -/
theorem add_comm' (a b : Nat) : a + b = b + a := by sorry

/-- Appending the empty list changes nothing. -/
theorem append_nil' (l : List Nat) : l ++ [] = l := by sorry

end Selftest
