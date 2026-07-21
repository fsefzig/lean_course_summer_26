import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

/-
example (k n: /n)(h : k+1 = n) : k < n := by
  apply Nat.add_one_le_iff.infinitely_many_primes
  exact Nat.le_of_eq h
-/

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have hd0: d ≠ 0 := by --assumption to prove
    intro hd_zero --suppose d=0 for contradiction
    subst d  --subsituting
    simp at h --simplifying
    exact hn h -- appyling the already known proof hn : n ≠ 0
  have hk0: k ≠ 0 := by --assumption about k
    intro hk_zero
    subst k
    simp at h
    exact hn h
  have hd2 : 2 ≤ d := by
      cases d with
      | zero =>
          exact False.elim (hd0 rfl)
      | succ d =>
          cases d with
          | zero =>
              exact False.elim (hd rfl)
          | succ d =>
              simp

  have hd1 : 1 < d := lt_of_lt_of_le Nat.one_lt_two hd2
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  rw[h]
  calc
    k = 1 * k := by simp
    _ < d * k := Nat.mul_lt_mul_of_pos_right hd1 hkpos


-- k < 2 * k
-- 2 * k <= 2 * d
-- d * k = n


theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1) := by
  by_contra hnot
  have h1 : d ∣ 1 := by
    have hsub : d ∣ (n + 1) - n := by
      exact Nat.dvd_sub hnot h
    simpa using hsub
  have hd1 : d = 1 := by
    exact Nat.dvd_one.mp h1
  exact hd hd1

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  have hlarge : n.factorial + 1 ≠ 1 := by
    have hgt : 1 < n.factorial + 1 := by
      simpa [Nat.succ_eq_add_one] using
        Nat.succ_lt_succ (Nat.factorial_pos n)
    exact Nat.ne_of_gt hgt
  rcases Nat.exists_prime_and_dvd hlarge with
    ⟨p, hpPrime, hpDiv⟩
  use p
  constructor
  · exact hpPrime
  · by_contra hpNotGreater
    have hpLe : p ≤ n := by
      exact Nat.le_of_not_gt hpNotGreater
    have hpFact : p ∣ n.factorial := by
      exact Nat.dvd_factorial hpPrime.pos hpLe
    have hpOne : p ∣ 1 := by
      have hsub : p ∣ ((n.factorial + 1) - n.factorial) := by
        exact Nat.dvd_sub hpDiv hpFact
      simpa using hsub
    have hpEqOne : p = 1 := by
      exact Nat.dvd_one.mp hpOne
    exact hpPrime.ne_one hpEqOne
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
    use 0
    rw [Finset.sum_empty, Nat.mul_zero]
  | insert a s ha ih =>
    rcases ih with ⟨k, hk⟩
    rcases h a with ⟨l, hl⟩
    use l + k
    rw [Finset.sum_insert ha, hl, hk, Nat.mul_add]

end


/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
