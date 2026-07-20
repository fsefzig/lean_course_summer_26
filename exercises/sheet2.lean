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
  by_contra! hk_ge_n
  /- Lemmas -/
  have hk_ne_zero : k ≠ 0 := by
    intro hk
    subst k
    simp only [mul_zero] at h
    exact hn h
  have hd_ne_zero : d ≠ 0 := by
    intro hd0
    subst d
    simp only [zero_mul] at h
    exact hn h
  /- Main Theorem -/
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
  have hd_gt_one : 1 < d := by
    cases d with
    | zero =>
        exact False.elim (hd_ne_zero rfl)
    | succ d =>
        cases d with
        | zero =>
            exact False.elim (hd rfl)
        | succ d =>
            simp
  have hk_lt_dk : k < d * k := by
    exact (Nat.lt_mul_iff_one_lt_left hk_pos).2 hd_gt_one
  have hn_lt_dk : n < d * k := lt_of_le_of_lt hk_ge_n hk_lt_dk
  rw [← h] at hn_lt_dk
  exact Nat.lt_irrefl n hn_lt_dk

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro h2
  have h_one : d ∣ 1 := by
    have h_sub : d ∣ (n + 1) - n := by
      exact Nat.dvd_sub h2 h
    rw [Nat.add_sub_cancel_left] at h_sub
    exact h_sub
  have hd_one : d = 1 := by
    exact Nat.eq_one_of_dvd_one h_one
  exact hd hd_one

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  let N := n.factorial + 1
  let p := N.minFac
/- Facts -/
  have hN_ne_one : N ≠ 1 := by
    have hfac_pos : 0 < n.factorial := Nat.factorial_pos n
    have hN_gt_one : 1 < N := by
      exact Nat.lt_add_of_pos_left hfac_pos
    exact Nat.ne_of_gt hN_gt_one
/- -/
  have hp_prime : p.Prime := by
    exact Nat.minFac_prime hN_ne_one
/- -/
  have hp_dvd_N : p ∣ N := by
    exact Nat.minFac_dvd N
/- Main Theorem -/
  refine ⟨p, hp_prime, ?_⟩
  by_contra! hp_le_n
/- -/
  have hp_dvd_factorial : p ∣ n.factorial := by
    exact Nat.dvd_factorial hp_prime.pos hp_le_n
/- -/
  have hp_not_dvd_next : ¬ p ∣ n.factorial + 1 := by
    exact exercise1 hp_prime.ne_one hp_dvd_factorial
/- -/
  apply hp_not_dvd_next
  exact hp_dvd_N

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
  refine Finset.induction_on I ?_ ?_
  · exact dvd_zero d
  · intro a S ha ih
    rw [Finset.sum_insert ha]
    exact Nat.dvd_add (h a) ih
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
