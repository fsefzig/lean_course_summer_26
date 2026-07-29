import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le
#check Int.floor_pos

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  use ⌈1 / ε⌉₊
  constructor
  · positivity
  · have hδ : (0 : ℝ) < ⌈1 / ε⌉₊ := by
      positivity
    apply (one_div_le hδ hε).mpr
    exact Nat.le_ceil (1 / ε)
  use 1
  simp
  have h1 : (1 : ℝ) < ε := by
    exact lt_of_not_ge h
  exact le_of_lt h1

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
#check lt_of_lt_of_le

theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro h h2
  obtain ⟨δ, hδ, hδε⟩ := exercise1 h2
  obtain ⟨N, hN⟩ := hx δ hδ
  use N
  intro n hn
  apply lt_of_lt_of_le (hN n hn)
  exact hδε
/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast
#check one_div_pos
#check lt_of_lt_of_le

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  intro h k hk
  obtain ⟨δ, hδ, hδk⟩ := exercise1 hk
  have h_pos : (0: ℝ ) < δ := by
    exact_mod_cast hδ
  obtain ⟨N, hN⟩ := h (1 / δ) (one_div_pos.mpr h_pos)
  use N
  intro m h2 n h3
  change dist (x m) (x n) < k
  have hmn : dist (x m) (x n) < 1 / δ  := by
    exact hN m h2 n h3
  exact lt_of_lt_of_le hmn hδk
  intro h k hk
  obtain ⟨N, hN⟩ := h k hk
  use N
  intro m hm n hn
  rw [← Rat.dist_cast]
  exact hN m hm n hn


/-
Finally, show that convergent sequences are Cauchy sequences.
-/
#check dist_triangle
#check add_halves
#check add_lt_add

theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro k hk
  obtain ⟨N, hN⟩ := hx (k / 2) (half_pos hk)
  use N
  intro m hm n hn
  have hm_le : dist (x m) a < k / 2 := by
    exact hN m hm
  have hn_le : dist a (x n) < k / 2 := by
    rw [dist_comm]
    exact hN n hn
  have hmn_le : dist (x m) a + dist a (x n) < k /2 + k / 2 := by
    apply add_lt_add
    exact hm_le
    exact hn_le
  have h_dist_le : dist (x.x m) (x.x n) ≤ dist (x.x m) a + dist a (x.x n) := by
    exact dist_triangle (x m) a (x n)
  rw [← add_halves k]
  exact lt_of_le_of_lt h_dist_le hmn_le

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := (-1)^n

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  rintro ⟨a, ha⟩
  have hc : isCauchyReal my_diverging_sequence := by
    exact exercise4 a ha
  obtain ⟨N, hN⟩ := hc 1 (by norm_num)
  have h := hN (2 * N) (by omega) (2 * N + 1) (by omega)
  change dist ((-1)^(2 * N)) ((-1)^(2 * N + 1)) < 1 at h
  have h2 : ((-1: ℝ )^(2 * N)) = 1 := by
   rw [pow_mul]
   norm_num
  have h3 : ((-1: ℝ) ^ (2 * N + 1)) = -1 := by
   rw [pow_succ, h2]
   norm_num
  rw [h2, h3] at h
  change |1 - (-1)| < 1 at h
  norm_num at h
