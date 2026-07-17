import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Data.Nat.Factorial.Basic

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have hk : k ≠ 0 := by
    intro hk
    rw[hk, Nat.mul_zero] at h
    exact hn h
  have hdneq : d ≠ 0 := by
    intro hd
    rw[hd, Nat.zero_mul] at h
    exact hn h
  by_contra! hkn
  have hmul : d * n ≤ d * k := by
    exact Nat.mul_le_mul_left d hkn
  rw[← h] at hmul
  have hnemul : ¬ (d * n ≤ n) := by
    push Not
    refine (Nat.lt_mul_iff_one_lt_left ?_).mpr ?_
    · exact Nat.zero_lt_of_ne_zero hn
    · exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hdneq, hd⟩
  exact hnemul hmul

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  by_contra hsucc
  have hsub : d ∣ n + 1 - n := by
    exact Nat.dvd_sub hsucc h
  rw[Nat.add_sub_self_left n 1] at hsub
  apply Nat.eq_one_of_dvd_one at hsub
  exact hd hsub


theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  by_contra! h
  rcases h with ⟨n, hn⟩
  have hngt1 : n > 1 := by
    by_contra! hn0
    have h2 : (2 : ℕ).Prime := by
      exact Nat.prime_two
    have hcon : 2 ≤ n := by
      exact hn 2 h2
    have hlt : 2 ≤ 1 := by
      exact Nat.le_trans (hn 2 h2) hn0
    have hlt' : ¬ (2 ≤ 1) := by
      exact Nat.not_le_of_gt (by decide)
    exact hlt' hlt
  let m := Nat.factorial n + 1
  have hmneq : m ≠ 1 := by
    refine (Nat.add_one_ne_add_one_iff.mpr) ?_
    exact Nat.factorial_ne_zero n
  have ⟨p, ⟨hp1,hp2⟩⟩ := Nat.exists_prime_and_dvd (hmneq)
  have hpleqn :=hn p hp1
  have hpdvd : p ∣ Nat.factorial n := by
    exact Nat.dvd_factorial (Nat.Prime.pos hp1) hpleqn
  have hpndvd : ¬ (p ∣ Nat.factorial n + 1):= by
    exact exercise1 (Nat.Prime.ne_one hp1) hpdvd
  exact hpndvd hp2
end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
For more details see: https://leanprover-community.github.io/mathematics_in_lean/C06_Discrete_Mathematics.html
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
variable {I : Finset α} {f : α → ℕ}

#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty => exact Nat.dvd_of_mod_eq_zero rfl
  | @insert a I ha hI =>
  sorry
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
