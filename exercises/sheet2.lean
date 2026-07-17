import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- Complete Induction
variable (P : ℕ → Prop)

def complete_induction : Prop :=  (P 0 ∧ (∀ n, (∀ m, m ≤ n → P m) → P (n + 1))) → ∀ n, P n

def Q (P : ℕ → Prop) (n : ℕ) : Prop := ∀ m, m ≤ n → P m

lemma lemma0 : P 0 → Q P 0 := by
  intro h m hmn
  cases hmn
  exact h

lemma lemma1 (n : ℕ) : Q P n -> P n := by
  intro hq
  exact hq n (Nat.le_refl n)

lemma lemma2 (n : ℕ) : (Q P n -> P (n + 1)) -> (Q P n -> Q P (n + 1)) := by
  intro h hq m hm
  rcases Nat.lt_or_ge m (n + 1) with hlt | hge
  · exact hq m (Nat.lt_succ_iff.mp hlt)
  · have heq : m = n + 1 := le_antisymm hm hge
    subst heq
    exact h hq

lemma lemma3 : (∀ n, Q P n) -> ∀ n, P (n) := by
  intro h n
  exact lemma1 P n (h n)

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

variable {I : Finset α} {f : α → ℕ}

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise1 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a s hx ih =>
    rw [Finset.sum_insert hx]
    exact Nat.dvd_add (h a) ih

end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
-/
