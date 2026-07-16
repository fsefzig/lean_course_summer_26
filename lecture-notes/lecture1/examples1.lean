import Std -- standard module/library

--on the left hand of the screen is code
--right hand shows what we're doing

#check Nat.add_zero  --objects

#check Nat.mul_succ --aka, these are the peano axioms

#check Nat.mul_zero

--note that we dont need to acc write "#check"
--i think?
--its just for ourselves



-- |- means the goal
-- everything above it is what we can use
-- (if you click on line 18 or 19)

-- Example 1
theorem example1 (n : Nat) : n * Nat.succ 0 = n := by
  rw [Nat.mul_succ]
  -- replace the expression we had with what we got
  -- so the goal changes, from "so n*Nat.succ 0 =n"
  -- to "show n*0+n=n"

  rw[Nat.mul_zero]
  -- goal changes again
  -- replaces n*0 with 0
  -- so goal now is "show 0+n=n"

  sorry
  -- sorry means like if the proof is
  -- too complicated or you dont know how
  -- it accepts it as a proof
  -- and doesnt show up an error (it shows
  -- an error if you dont do it


-- Example 2
theorem example2 (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>   --this is the base case
      exact Nat.zero_add 0 --apply axiom
      --QUESTION: what does exact and rw mean?

  | succ n inductionHypothesis =>
      rw [Nat.add_succ, inductionHypothesis]
  -- inductive step
  --

-- Example 1 - finished
theorem example1' (n : Nat) : n * Nat.succ 0 = n := by
  rw [Nat.mul_succ]
  rw[Nat.mul_zero]
  exact example2 n
  --EXACT means we just plug back n into the
  --now-proven example2
  --exactly example 2 applied to n

  --it ONLY works if the statement is exactly what we have
  --mainly for readability


-- Example 3
theorem example3 (n :Nat) : ∀ m, n + m = m + n := by
  induction n with
  | zero =>
      intro m
      --tell lean "this is supposed to hold for all m"
      --so, we introduce the variable m

      rw [Nat.add_zero]
      --RW means rewrite (replace the old goal with new)

      rw [example2 m]
      --rewrite LHS using example 2, then this goal done
  | succ n inductionHypothesis =>
      intro m
      rw [Nat.succ_add]
      --axiom 4
      rw [inductionHypothesis]
      rw [Nat.add_succ]
      --Felix cheating here lmao
      --because this acc isnt an axiom
      --or defined at all based on our 7 axioms
      --proof is left to the reader


