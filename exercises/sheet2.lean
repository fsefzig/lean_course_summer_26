import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  subst h
  have hd0 : d ≠ 0 := by rintro rfl; simp at hn
  have hk0 : k ≠ 0 := by rintro rfl; simp at hn
  have hd2 : 2 ≤ d := by omega
  have hk1 : 1 ≤ k := by omega
  nlinarith

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1) := by
  intro hcontra
  have hdvd : d ∣ (n + 1) - n := Nat.dvd_sub hcontra h
  have heq : (n + 1) - n = 1 := by omega
  rw [heq] at hdvd
  exact hd (Nat.eq_one_of_dvd_one hdvd)

theorem d_not_div_a_plus_one : ∀ (d a : ℕ), d ∣ a → d ∣ a + 1 → d = 1 := by
  intro d a h1 h2
  have hd : d ∣ (a + 1) - a := Nat.dvd_sub h2 h1
  have h_diff : (a + 1) - a = 1 := by omega
  rw [h_diff] at hd
  exact Nat.eq_one_of_dvd_one hd

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  let M := Nat.factorial n + 1
  have hM : M ≠ 1 := by
    intro h
    have : Nat.factorial n = 0 := by omega
    exact Nat.factorial_ne_zero n this
  let p := Nat.minFac M
  have hp_prime : Nat.Prime p := Nat.minFac_prime hM
  use p
  refine ⟨hp_prime, ?_⟩
  by_contra h_le
  simp only [not_lt] at h_le
  have hp_dvd_fact : p ∣ Nat.factorial n := Nat.dvd_factorial (Nat.Prime.pos hp_prime) h_le
  have hp_dvd_M : p ∣ M := Nat.minFac_dvd M
  have hp_dvd_one : p ∣ 1 := (Nat.dvd_add_right hp_dvd_fact).mp hp_dvd_M
  have hp_eq_one : p = 1 := Nat.eq_one_of_dvd_one hp_dvd_one
  exact Nat.Prime.ne_one hp_prime hp_eq_one

end

section -- Finsets

#check Finset ℕ
variable {α : Type} [DecidableEq α]
#check Finset α
#check Finset.induction_on

variable {I : Finset α} {f : α → ℕ}
#check ∑ i ∈ I, f i

theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact dvd_zero d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact dvd_add (h a) ih

end
