import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have hdneq0 : d ≠ 0 := by
    intro h
    cases' h with hn
    rw [Nat.zero_mul] at h
    contradiction
  have hd2 : d ≥ 2 := by
    omega
  have hmul : 2 * k ≤ d * k := by
    exact Nat.mul_le_mul_right k hd2
  have hk0 : k ≠ 0 := by
    intro hk
    apply hn
    rw [h, hk]
    rw [Nat.mul_zero]
  have h2k : 2 * k > k := by
    omega
  rw [h]
  exact Nat.lt_of_lt_of_le h2k hmul



theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro h2
  have h3 : d ∣ (n + 1 - n) := by
    exact Nat.dvd_sub h2 h
  have h4 : d ∣ 1 := by
    simpa using h3
  have h5 : d = 1 := by
    exact Nat.dvd_one.mp h4
  contradiction


theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  let m := n.factorial + 1
  have hm : m ≠ 1 := by
    unfold m
    have hfac : 0 < n.factorial := by
      exact Nat.factorial_pos n
    omega
  rcases Nat.exists_prime_and_dvd hm with ⟨p, hp_prime, hp_dvd_m⟩
  refine ⟨p, hp_prime, ?_⟩
  by_contra h
  have hp_le : p ≤ n := Nat.le_of_not_gt h
  have hp_dvd_fac : p ∣ n.factorial := by
    exact (Nat.Prime.dvd_factorial hp_prime).mpr hp_le
  unfold m at hp_dvd_m
  have hp_not_dvd : ¬ (p ∣ n.factorial + 1) := by
    apply exercise1
    intro hp_eq_one
    exact hp_prime.ne_one hp_eq_one
    exact hp_dvd_fac
  contradiction



section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
variable {I : Finset α} {f : α → ℕ}

#check ∑ i ∈ I, f i

#check Finset.dvd_sum

-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  apply Finset.dvd_sum
  intro i hi
  exact h i


/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
