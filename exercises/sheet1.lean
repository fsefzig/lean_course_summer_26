import Std

import Mathlib.Tactic.Use

section

variable {P Q : Prop}


theorem glorgth (h : ¬P) : ¬(P ∧ Q) := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  exact h hp


theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  constructor
  · intro h1
    sorry
  · intro h2
    rcases h2 with hnP | hnQ
    · intro hvbv
      rcases hvbv with ⟨hnP, hnQ⟩
      sorry
    sorry
  sorry
sorry


/-
I tried a long time to make a truth table that's like a tree.
I split the problem into a whole bunch of branches, but it got confusing.
I made a "glorgth" theorem in an attempt to see if I could prove one individual branch.
Unfortunately, I was not able to plug it in.

sorry.
-/



theorem exercise2 (h : P ∨ Q) (hp : ¬ P) : Q := by
  rcases h with ha | hb
  · exact False.elim (hp ha)
  exact hb

end

section -- Quantifiers

variable {T : Type} {y₀ : T} {P : T → Prop}

/-
Recall a proof of a universally quantified statement ∀ x, P x
is an object of the product type ∏ (x : T), P x. In other words, a proof of ∀ x, P x
is a function that takes an arbitrary element x of type T and returns a proof of P x.
Thus, we can apply h : ∀ x, P x to an arbitrary element x : T to obtain a proof of P x.
-/



/-
Wait, am I supposed to do anything here to exercise 3? It's "working" with no sorry.
-/

theorem exercise3 (h : ∀ x, P x ) (x : T) : P x := by
  exact h x


/-
Whenever we want to prove a universally quantified statement ∀ x, P x,
we can use the 'intro' tactic to introduce an element x of type T and change the goal to P x.
-/

theorem theorem_we_want_to_use (x : T) : P x := by
  sorry -- use this theorem to prove exercise4

theorem exercise4 : ∀ x, P x := by
  apply theorem_we_want_to_use


/-
Recall a proof of an existentially quantified statement ∃ x, P x
is an object of the sum type ∑ (x : T), P x. In other words, a proof of ∃ x, P x is a pair (x, h)
where x : T and h : P x.
We can use the 'use x' tactic to prove an existentially quantified statement by providing a witness
x : T and changing the goal to P x.
-/

theorem exercise5 (h: ∀ x, P x) : ∃ y, P y := by
  use x
  sorry - /- Why doesn't "use x" just plug in instances of y for x and then we have exact? Right now, it just says P sorry. -/



/-
Finally, to use a hypothesis h : ∃ x, P x, we can use the 'rcases' tactic to obtain
a witness x : T and a proof h' : P x.
-/


/-
I added and named proofs of the next two theorems to make my exercise 6 proof possible.
This part was very natural number game.
-/

theorem fouristwotimestwo : 4 = 2 * 2 := by
  rfl

theorem unscrambling (k : Nat) : 2*2*k*k = 2*k*2*k := by
  rw [Nat.mul_assoc 2 2 k]
  rw [Nat.mul_comm 2 k]
  rw [Nat.mul_left_comm 2 k]
  rw [← Nat.mul_assoc]



theorem exercise6 (n : Nat) (h : ∃ k, n = 2 * k) : ∃ l, n*n = 4 * l := by
  rcases h with ⟨k, hk⟩
  rw[hk]
  rw[← Nat.mul_assoc]
  use k*k
  symm
  rw[fouristwotimestwo]
  rw[← Nat.mul_assoc]
  rw[unscrambling]


end
