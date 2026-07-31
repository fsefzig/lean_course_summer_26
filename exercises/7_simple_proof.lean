
  theorem add_example2 (a b c : Nat) : (a + b) + c = a + (c + b) := by
    -- Swaps (c + b) to (b + c) on the right-hand side first
    rw [Nat.add_comm c b]
    -- Now both sides are (a + b) + c = a + (b + c)
    rw [Nat.add_assoc]


theorem add_example (a b c : Nat) : (a + b) + c = a + (c + b) := by
  -- 1. Regroup LHS from (a + b) + c to a + (b + c)
  rw [Nat.add_assoc]
  -- 2. Swap b + c to c + b
  rw [Nat.add_comm b c]