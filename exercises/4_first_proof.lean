-- A simple proof showing that adding 0 to any natural number
-- returns that number
theorem add_zero_eq (n : Nat) : n + 0 = n := by
  rfl -- 'rfl' stands for reflexivity (equality by definition)
