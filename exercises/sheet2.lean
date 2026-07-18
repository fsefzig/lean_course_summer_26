import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/
variable (P : ℕ → Prop)

def complete_induction (P : ℕ → Prop) : Prop :=
  (P 0 ∧ (∀ n, (∀ m, m ≤ n → P m) → P (n + 1))) → ∀ n, P n

def Q (P : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ m, m ≤ n → P m

lemma Q_zero_of_P_zero : P 0 → Q P 0 := by
  intro hP0
  intro m
  intro hm
  have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
  rw [hm0]
  exact hP0

lemma P_n_of_Q_n (n : ℕ) : Q P n → P n := by
  intro hQ
  exact hQ n (Nat.le_refl n)

lemma Q_succ_of_Q_n_of_P_succ_of_Q_n
    (n : ℕ) :
    (Q P n → P (n + 1)) →
    (Q P n → Q P (n + 1)) := by
  intro hstep
  intro hQ
  intro m
  intro hm
  rcases Nat.eq_or_lt_of_le hm with heq | hlt
  · rw [heq]
    exact hstep hQ
  · have hmn : m ≤ n := Nat.le_of_lt_succ hlt
    exact hQ m hmn

lemma P_of_Q : (∀ n, Q P n) → ∀ n, P n := by
  intro hQ
  intro n
  exact P_n_of_Q_n P n (hQ n)

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

-- We can sum over finite setsx, using the ∑ notation.
#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise1 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  refine Finset.induction_on I ?_ ?_
  · rw [Finset.sum_empty]
    exact dvd_zero d
  · intro a S ha ih
    rw [Finset.sum_insert ha]
    exact Nat.dvd_add (h a) ih
end
/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?

What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?

Represent Prime factorisation as List ℕ of primes whose product is n,
with uniqueness upto permutation. For every n > 0, there will be a
a list l such that every element of l is prime and l.prod = n;
any two such lists are permutations of each other.
-/
