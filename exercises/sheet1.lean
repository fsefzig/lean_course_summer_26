import Std

import Mathlib.Tactic.Use

section

variable {P Q : Prop}

theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    --I believe you have to use an import for by_contra but I'm not sure if I should do so since the exercise sheet did not originally include it
    by_cases hp : P
    · right
      intro hq
      apply h
      exact ⟨hp, hq⟩
    · left
      exact hp
  · intro h_or
    intro h_and
    cases h_and with
    | intro hp hq =>
      cases h_or with
      | inl hnot_P => exact hnot_P hp
      | inr hnot_Q => exact hnot_Q hq








theorem exercise2 (h : P ∨ Q) (hp : ¬ P) : Q := by
  cases h with --we must do proof by cases
  | inl hP => --case one where we assume P is true, named hP
    exfalso --exposes the contradiction where P cannot be true and false at the same time
    exact hp hP
  | inr hQ => --assumes Q is true, named hQ
  exact hQ

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
  sorry -- use this theorem to prove exercise4

theorem exercise4 : ∀ x, P x := by
  intro x
  exact theorem_we_want_to_use x


/-
Recall a proof of an existentially quantified statement ∃ x, P x
is an object of the sum type ∑ (x : T), P x. In other words, a proof of ∃ x, P x is a pair (x, h)
where x : T and h : P x.
We can use the 'use x' tactic to prove an existentially quantified statement by providing a witness
x : T and changing the goal to P x.
-/

theorem exercise5 (h : ∀ x, P x) (y : T) : ∃ y, P y := by
  use y
  exact h y


/-
Finally, to use a hypothesis h : ∃ x, P x, we can use the 'rcases' tactic to obtain
a witness x : T and a proof h' : P x.
-/

theorem exercise6 (n : Nat) (h : ∃ k, n = 2 * k) : ∃ l, n*n = 4 * l := by
  rcases h with ⟨k, hk⟩
  rw[hk]
  use k * k
  rw[Nat.mul_assoc]
  rw[Nat.mul_comm k]
  rw[Nat.mul_assoc]
  rw[Nat.mul_assoc 2 2]



end
