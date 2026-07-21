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
    intro hd_zero
    rw [hd_zero] at h
    simp at h
    exact hn h
  rw [h]
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk] at h
    simp at h
    exact hn h
  have hkpos : k > 0 := by 
    exact Nat.zero_lt_of_ne_zero hk0
  have hd1le : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  have hdpos: 1 < d := by 
    exact Nat.lt_of_le_of_ne hd1le (id (Ne.symm hd))
  have hdk : 1 * k < d * k := by
    exact Nat.mul_lt_mul_of_pos_right hdpos hkpos

  simp at hdk
  exact hdk



    
  
  
  
    
  
    

  sorry

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro hp1
  have hsub : d ∣ (n + 1) - n := by 
    exact Nat.dvd_sub hp1 h
  simp at hsub
  exact hd hsub

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  
  sorry

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
  simp only [Finset.sum_empty, dvd_zero]
  | @insert a I ha ih =>
  
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
