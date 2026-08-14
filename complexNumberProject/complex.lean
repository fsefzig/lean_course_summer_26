import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex
noncomputable abbrev π : ℝ := Real.pi

lemma i_even_pow_eq_one_pow (k : ℕ) : I ^ (2 * k) = (-1) ^ k := by
  rw[pow_mul I 2 k]
  simp only [I_sq]

lemma hasSum_exp (z : ℂ) : HasSum (fun n => z ^ n / n.factorial) (exp z) := by
  rw[exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem eulers_theorem (θ : ℝ) : exp (θ * I) = cos θ + I * sin θ := by
  obtain hc := hasSum_cos' θ
  have hs : HasSum (fun n ↦ (↑θ * I) ^ (2 * n + 1) / ↑(2 * n + 1).factorial) (I * sin ↑θ) := by
    obtain sin_mul := HasSum.mul_right I (hasSum_sin' θ)
    simp_rw [div_mul_cancel₀ _ I_ne_zero] at sin_mul
    rw[mul_comm I (sin θ)]
    exact sin_mul
  exact (hasSum_exp (θ * I)).unique (HasSum.even_add_odd hc hs)

theorem eulers_identity : exp (π * I) = -1 := by
  rw[eulers_theorem π]
  simp

theorem de_moivres (θ : ℝ) (n : ℕ) :
  (cos θ + I * sin θ) ^ n = cos (n * θ) + I * sin (n * θ) := by
  rw[(eulers_theorem θ).symm, ← exp_nat_mul, ← mul_assoc]
  have eq : exp (n * θ * I) = cos (n * θ) + I * sin (n * θ) := by
    simpa using eulers_theorem (n * θ)
  rw[eq]

theorem de_moivres_polar (θ r : ℝ) (n : ℕ) :
  (r * (cos θ + I * sin θ))^n = r^n * (cos (n * θ) + I * sin (n * θ)) := by
  rw [mul_pow, de_moivres θ n]

theorem roots_of_unity {n : ℕ} (hn : n ≠ 0) :
  ∀ k : ℕ, (cos (2 * π * k / n) + I * sin (2 * π * k / n)) ^ n = 1 := by
  intro k
  have eq : cos (2 * π * k / n) + I * sin (2 * π * k / n) = exp (2 * π * k / n * I) := by
    obtain eu_2πk_div_n := eulers_theorem (2 * π * k / n)
    push_cast at eu_2πk_div_n
    exact (eu_2πk_div_n).symm
  rw[eq, ← exp_nat_mul, mul_comm, mul_assoc, mul_comm I n, ← mul_assoc,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]
  obtain eq_2πk := eulers_theorem (2 * ↑π * ↑↑k)
  push_cast at eq_2πk
  rw[eq_2πk]
  have cos_eq_one : cos (↑↑k * (2 * ↑π )) = 1 := cos_int_mul_two_pi _
  have sin_eq_zero : sin ((↑↑k * 2) * ↑π ) = 0 := by
    convert sin_int_mul_pi (k * 2)
    push_cast
    rfl
  rw[mul_comm] at cos_eq_one
  rw[mul_assoc, mul_comm] at sin_eq_zero
  rw[cos_eq_one, sin_eq_zero]
  ring

theorem roots_of_unity_distinct {n : ℕ} (j k : Fin n) (hn : n ≠ 0) (hjk : j ≠ k) :
  exp (2 * π * j / n * I) ≠ exp (2 * π * k / n * I) := by
  by_contra hexp
  obtain ⟨b, hb⟩ := exp_eq_exp_iff_exists_int.mp hexp
  replace hb : (j / n) * (2 * π * I) = (k /n + b) * (2 * π * I) := by linear_combination hb
  simp only [mul_eq_mul_right_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero,
    Real.pi_ne_zero, or_self, I_ne_zero, or_false] at hb
  field_simp at hb
  norm_cast at hb
  have habs : |(j : ℤ) - (k : ℤ)| < n := by exact Int.abs_sub_lt_of_lt_lt k.isLt j.isLt
  simp only [Int.sub_eq_iff_eq_add'.mpr hb, abs_mul, Nat.abs_cast] at habs
  nth_rewrite 2 [← mul_one (n : ℤ)] at habs
  have b_eq : b = 0 := Int.abs_lt_one_iff.mp (lt_of_mul_lt_mul_left habs (Int.natCast_nonneg n))
  simp only [b_eq, mul_zero, add_zero, Nat.cast_inj] at hb
  absurd hjk (Fin.eq_of_val_eq hb)
  exact not_false

theorem roots_of_unity_exhaustive {n : ℕ} (z : ℂ) (hn : n ≠ 0) :
  z ^ n = 1 → ∃ k < n, z = exp (2 * π * k / n * I) := by
  intro hz
  have norm_z : ‖z‖ = 1 := by exact norm_eq_one_of_pow_eq_one hz hn
  obtain ⟨θ, hexp⟩ := (norm_eq_one_iff z).mp norm_z
  rw[hexp.symm, (exp_nat_mul (↑θ * I) n).symm, mul_comm] at hz
  obtain ⟨b, hb⟩ := exp_eq_one_iff.mp hz
  field_simp at hb
  replace hb : (θ : ℂ) = ↑b * 2 * π / n := by
    field_simp
    exact hb
  rw[hb] at hexp
  refine ⟨(b % n).toNat, (Int.toNat_lt_of_ne_zero hn).mpr
    (Int.emod_lt_of_pos b (Int.natCast_pos.mpr (Nat.zero_lt_of_ne_zero hn))), ?_⟩
  have mod_eq_sub_int :
    2 * π * (b % n).toNat / n * I = 2 * π * b / n * I - (b / n : ℤ) * (2 * π * I) := by
    field_simp
    have eq : (b % n).toNat = b - n * (b / n) := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg b (Int.ofNat_ne_zero.mpr hn))]
      exact Int.emod_def b ↑n
    exact_mod_cast eq
  simp only [mod_eq_sub_int, exp_sub, exp_int_mul_two_pi_mul_I, div_one]
  rw[mul_assoc, mul_comm (b : ℂ) (2 * π)] at hexp
  exact hexp.symm
