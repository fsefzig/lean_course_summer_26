import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn: n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  cases d with
  | zero =>
  /-d = 0-/
    rw [zero_mul] at h
    contradiction
  | succ d' =>
    cases d' with
    | zero =>
      /-d = 1-/
      rw [zero_add] at hd
      contradiction
    | succ d'' =>
      /-d > 1-/
      rw [add_mul] at h
      rw [add_mul] at h
      rw [one_mul] at h
      rw [h]
      apply Nat.lt_add_left_iff_pos.mpr
      apply Nat.add_pos_right (d'' * k)
      cases k with
      | zero =>
        contradiction
      | succ k =>
        rw [← Nat.succ_eq_add_one]
        apply Nat.succ_pos
/-wasn't sure how to do this without this extra theorem-/
/-problem is I dont know how to subtract two equations(use is not applicable in excercise 1)-/
/-I also dont know how to just add and subtract n-/
/-I probably overcomplicated this-/
theorem needthis (n : ℕ) : n + 1 - n = 1 := by
  rw [add_comm, Nat.add_sub_cancel]

theorem needforexcercise1 {d n : ℕ} (h : d ∣ n) (h1 : d ∣ n + 1) : d ∣ 1 := by
  rcases h1 with ⟨x, hx⟩
  rcases h with ⟨y, hy⟩
  use x-y
  rw [← needthis n]
  rw [hx, hy]
  rw [← Nat.mul_sub]

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  by_contra h2
  have h3:= needforexcercise1 h h2
  have hd1 := Nat.eq_one_of_dvd_one h3
  exact hd hd1


theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  by_contra hp
  push Not at hp
  rcases hp with ⟨n, hn⟩
  let N := n.factorial + 1
  have hN' : 1 ≠  N := by
    unfold N
    by_contra hN1
    nth_rewrite 1 [← Nat.zero_add 1] at hN1
    apply Nat.add_right_cancel at hN1

    exact (Nat.ne_of_gt (Nat.factorial_pos n)) hN1.symm
  rcases Nat.exists_prime_and_dvd hN'.symm with ⟨p, hp_prime, hp_dvd_N⟩
  have hp_le : p ≤ n := hn p hp_prime
  have hp_le_fac : p ∣ n.factorial := by
    exact Nat.dvd_factorial (Nat.Prime.pos hp_prime) hp_le
  unfold N at hp_dvd_N

  have hp_not_dvd : ¬ (p ∣ n.factorial + 1) := by
    apply exercise1
    · exact Nat.Prime.ne_one hp_prime
    · exact hp_le_fac
  contradiction
end

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


-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by

  induction I using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact Nat.dvd_zero d
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      have h1 : d ∣ f a := by
        exact h a
      have h2 : d ∣ ∑ i ∈ s, f i := by
        exact ih
      /-below is exactly the same theorem proved during class-/
      exact Nat.dvd_add h1 h2
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
