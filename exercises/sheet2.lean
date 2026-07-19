import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

-- theorem exactstuff {k n : ℕ} : k+1 ≠ 0 := by
--   exact?

theorem sublemma0 {k n : ℕ} : n * k < k → n = 0 := by
  intro h
  cases k with
  | zero =>
    rw [mul_zero] at h
    apply Nat.not_lt_zero  at h
    trivial
  | succ k1 =>
    apply lt_one_of_mul_lt_left at h
    exact Nat.lt_one_iff.mp h

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  by_contra hc
  apply Nat.le_of_not_lt at hc
  have hok : n = k ∨ n < k  := by
    exact Nat.eq_or_lt_of_le hc
  rcases hok with hleft | hright
  · rw [hleft] at h
    cases k with
    | zero =>
      exact hn hleft
    | succ k1 =>
      have iamnotgoodatnamingvariables := h.symm
      apply mul_left_eq_self₀.mp at iamnotgoodatnamingvariables
      rcases iamnotgoodatnamingvariables with hpls | hpls2
      · exact hd hpls
      · have hpleasefinishthisproofalreadythanks := (Nat.zero_ne_add_one k1)
        exact hpleasefinishthisproofalreadythanks hpls2.symm
  · rw [h] at hright
    apply sublemma0 at hright
    rw [hright, zero_mul] at h
    exact hn h

-- theorem exactstuff1 {n: ℕ} (h : n ∣ 1) : (n = 1) := by
--   exact?

theorem sublemma1 {n m k l : ℕ} (h : n * k + m = l * k) : (k ∣ m) := by
  use (l - n)
  apply Nat.eq_sub_of_add_eq' at h
  rw [← Nat.sub_mul] at h
  rw [mul_comm]
  exact h

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro h1
  rcases h with ⟨k, hk⟩
  rcases h1 with ⟨l, hl⟩
  rw [hk] at hl
  rw [mul_comm] at hl
  nth_rewrite 2 [mul_comm] at hl
  apply sublemma1 at hl
  have hclose : (d = 1) := Nat.eq_one_of_dvd_one hl
  exact hd hclose

-- theorem exactingstuff2 {a b c d : ℕ} (h : 2 ≤ a) : (a ≠ 1) := by
--   exact?

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  cases n with
  | zero =>
    use 3
    constructor
    · trivial
    · trivial
  | succ n1 =>
    by_cases h : ((n1+1).factorial + 1).Prime
    · use ((n1+1).factorial + 1)
      constructor
      · exact h
      · apply Nat.add_lt_add_iff_right.mpr
        have aux := Nat.lt_succ_self n1
        have hok : 1 ≤ n1.factorial := Nat.factorial_pos n1
        have hclose := Nat.self_le_factorial (n1+1)
        exact Nat.lt_of_lt_of_le (aux) hclose
    · use Nat.minFac ((n1+1).factorial + 1)
      have hok : 1 ≤ (n1+1).factorial := Nat.factorial_pos (n1+1)
      have hok1 : 1 ≤ 1 := by decide
      have hok2 := Nat.add_le_add hok hok1
      have hok3 := (Nat.ne_of_lt hok2)
      constructor
      · apply Nat.minFac_prime hok3.symm
      · by_contra h1
        have h2 := Nat.minFac_dvd ((n1+1).factorial + 1)
        have h3 : ((n1 + 1).factorial + 1).minFac ≤ n1 + 1 := by
          linarith
        have h4 := Nat.dvd_factorial (Nat.minFac_pos ((n1+1).factorial + 1)) h3
        have h5 : ((n1+1).factorial + 1).minFac ≠ 1 := by
          by_contra hidk
          apply Nat.minFac_eq_one_iff.mp at hidk
          apply hok3.symm at hidk
          exact hidk
        have h6 := exercise1 h5 h4
        apply h6 at h2
        exact h2

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

#check Finset.sum_insert

-- theorem exactingstuff3 {n : ℕ} : (∑ i ∈ ∅, f i = 0) := by
--   exact?

-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    use 0
    rw [mul_zero]
  | insert x1 s hd1 hd2 =>
    rw [Finset.sum_insert]
    · rcases hd2 with ⟨k1, hk1⟩
      have h1 := h x1
      rcases h1 with ⟨k2, hk2⟩
      use (k2+k1)
      rw [hk1, hk2]
      rw [mul_add]
    · exact hd1
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
