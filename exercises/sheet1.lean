import Std

import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.Ring

section

variable {P Q : Prop}

theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases h1 : P
    · by_cases h2 : Q
      · have h3 : P ∧ Q := ⟨h1,h2⟩
        have hf := h h3
        trivial
      right
      exact h2
    left
    exact h1
  intro h
  by_contra
  rcases h with hnp | hnq
  · apply fun a ↦ a.left at this
    apply hnp at this
    trivial
  · apply fun a ↦ a.right at this
    apply hnq at this
    trivial
theorem exercise2 (h : P ∨ Q) (hp : ¬ P) : Q := by
  rcases h with hp1 | hq
  · have h1 := hp hp1
    trivial
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
  sorry
/-I had to ask ChatGPT,
 but apparently I was wasting my time trying to figure out how to prove this cause its impossible.
 I should've known...-/

theorem exercise4 : ∀ x, P x := by
  exact theorem_we_want_to_use


/-
Recall a proof of an existentially quantified statement ∃ x, P x
is an object of the sum type ∑ (x : T), P x. In other words, a proof of ∃ x, P x is a pair (x, h)
where x : T and h : P x.
We can use the 'use x' tactic to prove an existentially quantified statement by providing a witness
x : T and changing the goal to P x.
-/

theorem exercise5 (h : ∀ x, P x) (y : T) : ∃ y, P y := by
  use y
  apply h
/-
Finally, to use a hypothesis h : ∃ x, P x, we can use the 'rcases' tactic to obtain
a witness x : T and a proof h' : P x.
-/
theorem lemma1 (n : Nat) : 2*n*(2*n)=4*n^2 := by ring
/-I figured doing this computation by hand would be tedious and pointless,
so I just used the built in ring tool. Hope that's ok-/

theorem exercise6 (n : Nat) (h : ∃ k, n = 2 * k) : ∃ l, n*n = 4 * l := by
  rcases h with ⟨k, hk⟩
  use k^2
  rw[hk]
  exact lemma1 k
end
