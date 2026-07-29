import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · use (Nat.ceil (1/ε))
    constructor
    · simp
      linarith
    rw[one_div_le]
    exact (Nat.le_ceil (1/ε))
    positivity
    exact hε
  push Not at h
  use 1
  constructor
  · norm_num
  simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
  exact le_of_lt h

-- Sahasra says 'hi!'
/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/

theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε hε
  obtain ⟨δ, δ_ge_zero, δ_le_ε⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ δ_ge_zero
  use N
  exact fun n a_1 ↦ Std.lt_of_lt_of_le (hN n a_1) δ_le_ε

  -- Note: the last line was written by using _apply ?_

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro h
    unfold isCauchy at h
    unfold isCauchyReal
    intro ε hε
    obtain ⟨N,hN⟩ := h ε hε
    use N
    intro m hm n hn
    rw[Rat.dist_cast (x.x m) (x.x n)]
    exact Metric.mem_ball.mp (hN m hm n hn) -- used _exact?_
  intro h
  unfold isCauchyReal at h
  unfold isCauchy
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  use N
  intro m hm n hn
  rw[← Rat.dist_cast]
  exact Metric.mem_ball.mp (hN m hm n hn)

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  unfold isCauchyReal
  unfold tends_toReal at hx
  intro ε hε
  have ⟨N, hN⟩ := hx (ε/2) (half_pos hε)
  use N
  intro m hm n hn
  have h1 : dist (x.x n) a < ε / 2 := hN n hn
  have h2 : dist (x.x m) a < ε / 2 := hN m hm
  rw[dist_comm (x.x n) a] at h1
  have ha : (dist (x.x m) a) + (dist a (x.x n)) < ε := by linarith
  have ht := dist_triangle (x.x m) a (x.x n)
  have hf : dist (x.x m) (x.x n) ≤ ε := by linarith
  exact Std.lt_of_le_of_lt ht ha

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  intro h
  unfold tends_toReal at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨N, hN⟩ := ha (1) (zero_lt_one)
  set n := N + Nat.ceil(a + 1 : ℝ)
