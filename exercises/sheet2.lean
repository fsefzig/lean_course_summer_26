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
  cases n with
| zero =>
    contradiction
| succ n' =>
    cases d with
    | zero =>
        simp at h
    | succ d' =>
        cases d' with
        | zero =>
            exact (hd rfl).elim
        | succ d'' =>
            cases k with
            | zero =>
                simp at h
            | succ k' =>
                rw [h]
                have hd_large:
                    1 < Nat.succ (Nat.succ d'') := by
                  exact Nat.succ_lt_succ (Nat.zero_lt_succ d'')
                have hk_positive:
                    0 < Nat.succ k' := by
                  exact Nat.succ_pos k'
                have hmul:
                    1 * Nat.succ k' <
                      Nat.succ (Nat.succ d'') * Nat.succ k' := by
                  exact Nat.mul_lt_mul_of_pos_right
                    hd_large hk_positive
                simp

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro hx
  have hd1 : d ∣ 1 := by
    exact (Nat.dvd_add_iff_right h).mpr hx
  have deq1 : d = 1 := Nat.eq_one_of_dvd_one hd1
  exact hd deq1
--
theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  let p := Nat.minFac (n.factorial + 1)
  have hne: n.factorial + 1 ≠ 1 := by
    exact ne_of_gt (Nat.succ_lt_succ (Nat.factorial_pos n))
  have hp: p.Prime := by
    exact Nat.minFac_prime hne
  have hpn: n < p := by
    apply lt_of_not_ge
    intro hle
    have hpfact:p ∣ n.factorial := by
      exact Nat.dvd_factorial (Nat.minFac_pos _) hle
    have hnot:¬p ∣ n.factorial + 1 := by
      exact exercise1 hp.ne_one hpfact
    apply hnot
    exact Nat.minFac_dvd _
  exact ⟨p, hp, hpn⟩

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
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact Nat.dvd_add (h a) ih

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
