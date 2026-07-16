import Std

import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite

section

variable {P Q : Prop}

theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      constructor
      · exact hP
      · exact hQ
    · left
      exact hP
  · intro h
    intro hPQ
    cases h with
    | inl hp =>
        exact hp hPQ.left
    | inr hq =>
        exact hq hPQ.right


theorem exercise2 (h : P ∨ Q) (hp : ¬ P) : Q := by
  cases h with
    | inl hp2 =>
        contradiction
    | inr hq =>
        exact hq


end

section -- Quantifiers

variable {T : Type} {P : T → Prop}

/-
Recall a proof of a universally quantified statement ∀ x, P x
is an object of the product type ∏ (x : T), P x. In other words, a proof of ∀ x, P x
is a function that takes an arbitrary element x of type T and returns a proof of P x.
Thus, we can apply h : ∀ x, P x to an arbitrary element x : T to obtain a proof of P x.
-/

theorem exercise3 (h : ∀ x, P x) (x : T) : P x := by
  exact h x


/-
Whenever we want to prove a universally quantified statement ∀ x, P x,
we can use the 'intro' tactic to introduce an element x of type T and change the goal to P x.
-/

theorem theorem_we_want_to_use (x : T) : P x := by
  apply exercise3
  intro x
  sorry
  /- not sure how to do this one -/
  
theorem exercise4 : ∀ x, P x := by
  intro x
  apply theorem_we_want_to_use


/-
Recall a proof of an existentially quantified statement ∃ x, P x
is an object of the sum type ∑ (x : T), P x. In other words, a proof of ∃ x, P x is a pair (x, h)
where x : T and h : P x.
We can use the 'use x' tactic to prove an existentially quantified statement by providing a witness
x : T and changing the goal to P x.
-/

theorem exercise5 (h : ∀ x, P x) (y : T) : ∃ y, P y := by
  use y
  apply theorem_we_want_to_use


/-
Finally, to use a hypothesis h : ∃ x, P x, we can use the 'rcases' tactic to obtain
a witness x : T and a proof h' : P x.
-/

theorem two_mul_two_eq_four : (2 : Nat) * 2 = 4 := by
  rfl

theorem exercise6 (n : Nat) (h : ∃ k, n = 2 * k) : ∃ l, n*n = 4 * l := by
  rcases h with ⟨k, hk⟩
  use k * k
  rw [hk]
  rw[← Nat.mul_assoc]
  rw [Nat.mul_comm 2 k]
  rw [Nat.mul_assoc k 2 2]
  rw [Nat.mul_comm k (2*2)]
  rw [two_mul_two_eq_four]
  rw [Nat.mul_assoc]
end
