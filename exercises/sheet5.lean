import LectureNotes.lecture6.examples6

open MySequences
set_option linter.style.longLine false

/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  use ⌈1/ε⌉.toNat
  have h : ⌈1/ε⌉ > 0 := by
    refine Int.ceil_pos.mpr ?_
    exact one_div_pos.mpr hε
  constructor
  · exact Int.pos_iff_toNat_pos.mp h
  have h1 : ⌈1/ε⌉ ≥ 1/ε := by
    exact Int.le_ceil (1 / ε)
  refine (one_div_le hε ?_).mp ?_
  · apply Nat.cast_pos'.mpr
    exact Int.pos_iff_toNat_pos.mp h
  have h2 : ⌈1 / ε⌉ = ⌈1 / ε⌉.toNat := by
    refine Int.eq_natCast_toNat.mpr ?_
    exact Int.le_of_lt h
  have h3 : (⌈1 / ε⌉ : ℝ) = (⌈1 / ε⌉.toNat : ℝ):= Real.ext_cauchy (congrArg Real.cauchy (congrArg Int.cast h2))
  rw[←h3]
  exact Int.le_ceil (1 / ε)
/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ) : tends_toReal x a := by
  intro ε hε
  apply exercise1 at hε
  rcases hε with ⟨δ,hδ⟩
  have hδ1 := hδ.1
  apply hx at hδ1
  rcases hδ1 with ⟨N,hN⟩
  use N
  intro n hn
  apply hN at hn
  calc
  dist (x.x n) a < 1/δ := hn
  _ ≤ ε := hδ.2

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro h ε hε
    apply h at hε
    exact hε
  intro h ε hε
  apply h at hε
  exact hε
-- Both directions are the exact same. It's kinda funny.

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro ε hε
  have ⟨N,hN⟩ := hx (ε/2) (half_pos hε)
  use N
  intro m hm n hn
  calc
  dist (x.x m) (x.x n) ≤ dist (x.x m) a + dist (x.x n) a := dist_triangle_right (x.x m) (x.x n) a
  _ < ε/2 + ε/2 := add_lt_add (hN m hm) (hN n hn)
  _ = ε := by simp only [add_halves]
/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  intro h
  rcases h with ⟨a,ha⟩
  simp only [tends_toReal, gt_iff_lt, ge_iff_le, my_diverging_sequence] at ha
  have h1 : ∃ N, ∀ (n : ℕ), N ≤ n → dist (n : ℝ) a < 1 := by
    apply ha
    exact Real.zero_lt_one
  rcases h1 with ⟨N,hN⟩
  have h2 : ((dist (max N ⌈a+1⌉.toNat) a) : ℝ) < 1 := by
    apply hN (max N ⌈a+1⌉.toNat)
