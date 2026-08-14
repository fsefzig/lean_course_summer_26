import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex
noncomputable abbrev π : ℝ := Real.pi

lemma i_even_pow_eq (k : ℕ) : I ^ (2 * k) = (-1) ^ k := by
  rw[pow_mul I 2 k]
  simp only [I_sq]

lemma i_odd_pow_eq (k : ℕ) : I ^ (2 * k + 1) = I * (-1) ^ k := by
  rw[pow_succ' I (2 * k), i_even_pow_eq k]

-- lemma for power series of e^z
lemma hasSum_exp (z : ℂ) : HasSum (fun n => z ^ n / n.factorial) (exp z) := by
  rw[exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem eulers_theorem (θ : ℝ) : exp (θ * I) = cos θ + I * sin θ := by
  -- take cos and I*sin by their respective power series representations
  obtain hc := hasSum_cos' θ
  have hs : HasSum (fun n ↦ (↑θ * I) ^ (2 * n + 1) / ↑(2 * n + 1).factorial) (I * sin ↑θ) := by
    obtain sin_mul := HasSum.mul_right I (hasSum_sin' θ)
    simp_rw [div_mul_cancel₀ _ I_ne_zero] at sin_mul
    rw[mul_comm I (sin θ)]
    exact sin_mul
  -- exp power series matches cos + I*sin power series → exp (θ * I) = cos θ + I * sin θ
  exact (hasSum_exp (θ * I)).unique (HasSum.even_add_odd hc hs)

theorem eulers_identity : exp (π * I) = -1 := by
  rw[eulers_theorem π]
  simp

theorem de_moivres (θ : ℝ) (n : ℕ) :
  (cos θ + I * sin θ) ^ n = cos (n * θ) + I * sin (n * θ) := by
  -- rewrite with exp, multiply powers
  rw[(eulers_theorem θ).symm, ← exp_nat_mul, ← mul_assoc]
  exact_mod_cast eulers_theorem (n * θ)

theorem de_moivres_polar (θ r : ℝ) (n : ℕ) :
  (r * (cos θ + I * sin θ))^n = r^n * (cos (n * θ) + I * sin (n * θ)) := by
  rw [mul_pow, de_moivres θ n]

theorem roots_of_unity {n : ℕ} (hn : n ≠ 0) :
  ∀ k : ℕ, (cos (2 * π * k / n) + I * sin (2 * π * k / n)) ^ n = 1 := by
  intro k
  -- rewrite with exp form and simplify
  have eq : cos (2 * π * k / n) + I * sin (2 * π * k / n) = exp (2 * π * k / n * I) := by
    exact_mod_cast (eulers_theorem (2 * π * k / n)).symm
  rw[eq, ← exp_nat_mul, mul_comm, mul_assoc, mul_comm I n, ← mul_assoc,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]
  -- return to cis form
  obtain eq_2πk := eulers_theorem (2 * ↑π * ↑↑k)
  push_cast at eq_2πk
  rw[eq_2πk]
  -- prove cos(2πk) = 1 and sin(2πk) = 0
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
  -- exp equal implies powers differ by multiple of 2π
  obtain ⟨b, hb⟩ := exp_eq_exp_iff_exists_int.mp hexp
  replace hb : (j / n) * (2 * π * I) = (k /n + b) * (2 * π * I) := by linear_combination hb
  simp only [mul_eq_mul_right_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero,
    Real.pi_ne_zero, or_self, I_ne_zero, or_false] at hb
  field_simp at hb
  norm_cast at hb
  -- (j k : ℕ) < n implies their absoloute difference is less than n
  have habs : |(j : ℤ) - (k : ℤ)| < n := by exact Int.abs_sub_lt_of_lt_lt k.isLt j.isLt
  -- rewrite and simplify with hb, which gives j - k = n * b
  simp only [Int.sub_eq_iff_eq_add'.mpr hb, abs_mul, Nat.abs_cast] at habs
  nth_rewrite 2 [← mul_one (n : ℤ)] at habs
  -- divide both sides by n (with n > 0) → |b| < 1 → b = 0
  have b_eq : b = 0 := Int.abs_lt_one_iff.mp (lt_of_mul_lt_mul_left habs (Int.natCast_nonneg n))
  -- substitute b to get j = k, contradiction
  simp only [b_eq, mul_zero, add_zero, Nat.cast_inj] at hb
  absurd hjk (Fin.eq_of_val_eq hb)
  exact not_false

lemma exists_cosine {a : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) :
  ∃ θ : ℝ, θ ∈ Set.Icc 0 Real.pi ∧ Real.cos θ = a := by
  -- prove ∃ θ between 0 and π such that cos(θ) = a via intermediate value theorem
  obtain hivt := intermediate_value_Icc' Real.pi_nonneg Real.continuous_cos.continuousOn
  rw[Real.cos_pi, Real.cos_zero] at hivt
  obtain ⟨θ, hθ, hcosθ⟩ := hivt (Set.mem_Icc.mpr ha)
  use θ

theorem exp_surj_unit_circle (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ θ : ℝ, exp (θ * I) = z := by
  -- take re(z) and im(z)
  obtain ⟨a, b⟩ := z
  -- a^2 + b^2 = 1 essentially by definition; this allows us to show -1 ≤ a ≤ 1
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simp only [norm, normSq_mk, Real.sqrt_eq_one] at hz
    linarith
  have ha : -1 ≤ a ∧ a ≤ 1 := abs_le_of_sq_le_sq' (by linarith [sq_nonneg b]) (by linarith)
  -- use previous lemma to get θ ∈ [0, π] st cos(θ) = a
  obtain ⟨θ, ⟨hθ, hcosθ⟩⟩ := exists_cosine ha
  -- use pythagorean identity and cos(θ) = a to show sin(θ) = ± b
  have sin_eq_pm : Real.sin θ = b ∨ Real.sin θ = -b := by
    have identity : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
    rw[hcosθ, sub_eq_of_eq_add' hab.symm] at identity
    exact sq_eq_sq_iff_eq_or_eq_neg.mp identity
  by_cases hb : b ≥ 0
  · -- given b ≥ 0, sin(θ) ≥ 0, sin(θ) = ± b, we must have sin(θ) = b
    have hsinθ : Real.sin θ = b := by
      rcases sin_eq_pm with h1 | h2
      · exact h1
      · linarith [Real.sin_nonneg_of_mem_Icc hθ]
    -- use eulers theorem on θ, rewrite sin(θ) and cos(θ)
    obtain eulers := eulers_theorem θ
    rw[(ofReal_cos θ).symm, (ofReal_sin θ).symm, hcosθ, hsinθ] at eulers
    use θ
    rw[eulers]
    apply Complex.ext <;> simp
  · -- given b < 0, sin(θ) ≥ 0, sin(θ) = ± b, we must have sin(θ) = -b
    have hsinθ : Real.sin θ = -b := by
      rcases sin_eq_pm with h1 | h2
      · linarith [Real.sin_nonneg_of_mem_Icc hθ]
      · exact h2
    -- use eulers on -θ, rewrite
    obtain eulers := eulers_theorem (-θ)
    push_cast at eulers
    rw[cos_neg ↑θ, sin_neg ↑θ, (ofReal_cos θ).symm, (ofReal_sin θ).symm, hcosθ, hsinθ] at eulers
    use -θ
    push_cast
    rw[eulers]
    simp only [ofReal_neg, neg_neg]
    apply Complex.ext <;> simp

theorem roots_of_unity_exhaustive {n : ℕ} (z : ℂ) (hn : n ≠ 0) :
  z ^ n = 1 → ∃ k < n, z = exp (2 * π * k / n * I) := by
  intro hz
  -- use surjectivity theorem to place z on unit circle
  obtain ⟨θ, hexp⟩ := exp_surj_unit_circle z (norm_eq_one_of_pow_eq_one hz hn)
  rw[hexp.symm, (exp_nat_mul (↑θ * I) n).symm, mul_comm] at hz
  -- exp(θ * I * n) = 1 implies θ * I * n is a multiple of 2π
  obtain ⟨b, hb⟩ := exp_eq_one_iff.mp hz
  field_simp at hb
  -- solve for and substitute θ
  replace hb : (θ : ℂ) = ↑b * 2 * π / n := by
    field_simp
    exact hb
  rw[hb] at hexp
  -- use k = b mod n, with b mod n < n
  refine ⟨(b % n).toNat, (Int.toNat_lt_of_ne_zero hn).mpr
    (Int.emod_lt_of_pos b (Int.natCast_pos.mpr (Nat.zero_lt_of_ne_zero hn))), ?_⟩
  -- show that result of b % n is the same as (b / n : ℂ) - (b / n : ℤ)
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
