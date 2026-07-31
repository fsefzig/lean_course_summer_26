import LectureNotes.lecture6.examples6

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
  · use ⌈1 / ε⌉.toNat
    refine ⟨Nat.ceil_pos.mpr (show 0 < ⌈1 / ε⌉ by positivity), ?_⟩
    apply (one_div_le _ _).mpr
    · have h : (⌈1 / ε⌉.toNat : ℝ) = ⌈1 / ε⌉ := by
        exact_mod_cast Int.toNat_of_nonneg (by positivity)
      rw[h]
      exact Int.le_ceil (1 / ε)
    · apply Nat.cast_pos'.mpr
      exact Nat.ceil_pos.mpr (show 0 < ⌈1 / ε⌉ by positivity)
    exact hε
  use 1
  exact ⟨by positivity, by linarith⟩

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_to x a := by
  unfold tends_to
  intro ε hε
  obtain ⟨δ, hδ⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ hδ.1
  use N
  intro n hn
  have h := hN n hn
  exact lt_of_lt_of_le h hδ.2

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
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_to x a) : isCauchyReal x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε / 2) (by positivity)
  use N
  intro m hm n hn
  calc
    dist (x m) (x n) ≤ dist (x m) a + dist a (x n) := dist_triangle (x m) a (x n)
    _ = dist (x m) a + dist (x n) a := by rw[dist_comm a (x n)]
    _ < ε / 2 + ε / 2 := by exact add_lt_add (hN m hm) (hN n hn)
    _ = ε := by exact add_halves ε

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem fiveadd : (5 : ℝ) = @Nat.cast ℝ Real.instNatCast 5 := by
  exact Eq.symm (Real.ext_cauchy rfl)

theorem exercise5 : ¬ ∃ a : ℝ, tends_to my_diverging_sequence a := by
  unfold tends_to my_diverging_sequence
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
  rw [Real.dist_eq] at x
  norm_num at x

#check dist
