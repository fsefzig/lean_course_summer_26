import LectureNotes.lecture6.examples6
import Mathlib.Topology.MetricSpace.IsometricSMul

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le
#check inv_eq_one_div

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · use ⌈1/ε⌉.natAbs
    simp only [one_div, gt_iff_lt, Int.natAbs_pos, ne_eq, Int.ceil_eq_zero_iff, Set.mem_Ioc,
      inv_nonpos, not_and, not_le, Nat.cast_natAbs, Int.cast_abs]
    refine ⟨fun x => hε, ?_⟩
    rw [← Int.cast_abs]
    rw [inv_eq_one_div]
    have hnonneg : 0 ≤ ⌈1/ε⌉ := by
      apply Int.ceil_nonneg ?_
      simp [le_of_lt hε]
    apply one_div_le hε ?_ |>.mp
    · rw [← one_div, abs_of_nonneg hnonneg]
      apply Int.le_ceil (1/ε)
    · rw [← one_div, abs_of_nonneg hnonneg, Int.cast_pos]
      simp only [one_div, Int.ceil_pos, inv_pos]
      exact hε
  push Not at h
  use 1
  simp [lt_iff_le_and_ne.mp h |>.1]

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  sorry

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor <;>
  · unfold isCauchy isCauchyReal RatSeq.toRealSeq
    simp [Rat.dist_cast]

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  unfold tends_toReal at hx
  unfold isCauchyReal
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  use N
  intro m hm n hn
  obtain h := hN m hm
  obtain h' := hN n hn


theorem fiveadd : (5 : ℝ) = @Nat.cast ℝ Real.instNatCast 5 := by
  exact Eq.symm (Real.ext_cauchy rfl)

#check dist_add_left

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n


theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  unfold tends_toReal my_diverging_sequence
  dsimp
  intro ⟨a, ha⟩
  obtain ⟨N, hN⟩ := ha 1 (by simp)
  obtain h₁ := hN (N+1) (by simp)
  obtain h₂ := hN (N+5) (by simp)
  rw [Nat.cast_add] at h₁ h₂
  rw [← fiveadd] at h₂
  rw [Nat.cast_one] at h₁
  have add := add_lt_add_of_lt_of_le h₁ (le_of_lt h₂)
  have tri := dist_triangle (N + 1 : ℝ) a (N + 5)
  rw [dist_comm a] at tri
  have x := lt_of_le_of_lt tri add
  have : IsIsometricVAdd ℝ ℝ := sorry
  rw [dist_add_left] at x
  have rwh : dist (1 : ℝ) 5 = 4 := by
    sorry
  rw [rwh] at x
  rw [show (1 : ℝ) + 1 = 2 by sorry] at x
  sorry

#check dist
