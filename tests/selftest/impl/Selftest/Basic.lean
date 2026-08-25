namespace Selftest

/-- Addition on `Nat` is commutative. -/
theorem add_comm' (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- Appending the empty list changes nothing. -/
theorem append_nil' (l : List Nat) : l ++ [] = l := List.append_nil l

end Selftest
