import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

/-
i spent like two hours on this proof
then i got stuck
then claude said i made a mistake in the second line of my proof by using .natAbs
so uh
ignore this one, i just dont wanna delete it cause i spent so much time on it
-/
theorem exercise1' {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · use (Int.ceil (1 / ε)).natAbs
    have ceil_ge : Int.ceil (1 / ε) > 0 := by
      apply Int.ceil_pos.mpr
      exact one_div_pos.mpr hε
    constructor
    · apply Int.natAbs_pos.mpr
      exact Ne.symm (Int.ne_of_lt ceil_ge)
    · have ceil_nat_ge : (0 : ℝ) < ↑(⌈1 / ε⌉.natAbs) := by
        exact Nat.cast_pos.mpr (Int.natAbs_pos.mpr (ne_of_gt ceil_ge))
      apply (one_div_le ceil_nat_ge hε).mpr
      have simp_cast : ↑⌈1 / ε⌉.natAbs = ⌈1 / ε⌉ := by
        exact Int.natAbs_of_nonneg (Int.le_of_lt ceil_ge)
      rw[← Int.cast_natCast, simp_cast]
      exact Int.le_ceil (1 / ε)
  · rw[not_le] at h
    use (Int.ceil ε).natAbs
    have ceil_gt : ⌈ε⌉ > 1 := Int.lt_ceil.mpr (by exact_mod_cast h)
    -- i used claude to help me prove h : 1 < ε, ⊢ ↑1 < ε cause it was ragebaiting me
    constructor
    · exact Int.natAbs_pos.mpr (Ne.symm (Int.ne_of_lt (Int.ceil_pos.mpr hε)))
    · have lt_one : 1 / ⌈ε⌉ < 1 := by
        exact Int.ediv_lt_self_of_pos_of_ne_one Int.one_pos (Ne.symm (Int.ne_of_lt ceil_gt))
      have natAbs_lt_one : 1 / ((⌈ε⌉.natAbs : ℝ)) < 1 := by
        have gt_zero : ↑⌈ε⌉.natAbs > 0 := by
          refine Int.natAbs_pos.mpr ?_
          by_contra
          rw[this] at ceil_gt
          contradiction
        apply gt_iff_lt.mp at gt_zero
        sorry
      sorry

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · use ⌈1/ε⌉₊ -- nat ceil instead of int ceil, this fixes everything i guess
    constructor
    · exact Nat.ceil_pos.mpr (one_div_pos.mpr hε)
    · have ceil_pos : (0 : ℝ) < (⌈1 / ε⌉₊ : ℝ) :=
        Nat.cast_pos.mpr (Nat.ceil_pos.mpr (one_div_pos.mpr hε))
      exact (one_div_le hε ceil_pos).mp (Nat.le_ceil (1 / ε))
  · use ⌈ε⌉₊
    constructor
    · exact Nat.ceil_pos.mpr hε
    · rw[not_le] at h
      have ε_pos : (0 : ℝ) < (⌈ε⌉₊ : ℝ) := Nat.cast_pos.mpr (Nat.ceil_pos.mpr hε)
      have lh_lt_one : 1 / (↑⌈ε⌉₊ : ℝ) < 1 := by
        refine (div_lt_one₀ ε_pos).mpr (Nat.one_lt_cast.mpr (Nat.lt_ceil.mpr ?_))
        -- look at this full circle moment :)
        exact_mod_cast h
      by_contra hc -- or linarith from here
      rw[not_le] at hc
      have h1 : ε > 1 := gt_iff_lt.mp h
      have h2 : ε < 1 :=  Std.lt_trans hc lh_lt_one
      exact lt_asymm h2 h1

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ hδ
  use N
  have lt_rat : ∃ N, ∀ n ≥ N, dist (x.x n) a < 1 / ↑δ := by
    exact Exists.imp (fun a_1 a ↦ a) (hx δ hδ)
  exact fun n a_1 ↦ Std.lt_of_lt_of_le (hN n a_1) hδε

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro ratX ε hε
    simp only [Rat.dist_cast]
    exact Exists.imp (fun a a_1 ↦ a_1) (ratX ε hε)
  · intro realX ε hε
    simp only [← Rat.dist_cast]
    exact Exists.imp (fun a a_1 ↦ a_1) (realX ε hε)

/-
Finally, show that convergent sequences are Cauchy sequences.
-/


theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  /-
  if threshold of cauchy is ε, we can construct N st the threshold for tends_toReal is 1/2 ε
  if we use that N for the cauchy sequence, the max distance between xm and xn occurs when they
  are on opposite sides, in which case (dist xm a) + (dist xn a) < ε
  -/
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε/2) (half_pos hε)
  use N
  intro m hm n hn
  have max_lt : dist (x m) a + dist (x n) a < ε := by
    have dist_m : dist (x m) a < (ε / 2) := by exact hN m hm
    have dist_n : dist (x n) a < (ε / 2) := by exact hN n hn
    linarith
  have dist_lt_sum : dist (x m) (x n) ≤ dist (x m) a + dist (x n) a := by
    exact dist_triangle_right (x m) (x n) a
  exact Std.lt_of_le_of_lt dist_lt_sum max_lt

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

@[simp]
theorem sequence_simplify (n : ℕ) :
  my_diverging_sequence.x n = (n : ℝ) := rfl

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  by_contra h
  obtain ⟨a, ha⟩ := h
  obtain ⟨N, hN⟩ := ha 1 (by norm_num)
  obtain dist_x := hN N (Nat.le_refl N)
  obtain dist_y := hN (N + 67) (Nat.le_add_right N 67)
  simp only [sequence_simplify, Nat.cast_add, Nat.cast_ofNat] at dist_x dist_y
  have dist_lt_sum : dist (N : ℝ) (N + 67 : ℝ) ≤ dist (N : ℝ) a + dist (N + 67 : ℝ) a := by
    exact dist_triangle_right (N : ℝ) (N + 67 : ℝ) a
  have contr : dist (N : ℝ) (N + 67 : ℝ) < 2 := by linarith
  rw[Real.dist_eq] at contr
  simp only [sub_add_cancel_left, abs_neg, Nat.abs_ofNat] at contr
  linarith
