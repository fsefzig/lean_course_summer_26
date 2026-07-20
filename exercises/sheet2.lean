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
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at h
    exact hn h
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h
    exact hn h
  have hd2 : 2 ≤ d := by
    omega
  calc
    k < 2 * k := by omega
    _ ≤ d * k := Nat.mul_le_mul_right k hd2
    _ = n := h.symm
theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro h1
  have h_diff : d ∣ 1 := by
    exact (Nat.dvd_add_right h).mp h1
  have hd1 : d = 1 := Nat.eq_one_of_dvd_one h_diff
  exact hd hd1

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  have hN : n.factorial + 1 ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hN
  use p
  constructor
  · exact hp
  · by_contra hle
    have hp_dvd_fact : p ∣ n.factorial :=
      Nat.dvd_factorial hp.pos (by omega)
    have hp_dvd_one : p ∣ 1 := by
      exact (Nat.dvd_add_right hp_dvd_fact).mp hpdiv
    exact hp.not_dvd_one hp_dvd_one

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
  induction' I using Finset.induction_on with a s ha ih
  · simp
  · rw [Finset.sum_insert ha]
    exact dvd_add (h a) ih
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
