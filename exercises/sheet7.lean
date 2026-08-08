import LectureNotes.lecture8.examples8

open MyFunctions MySequences Function
set_option linter.style.longLine false
/-
Exercise 1: Finish the proof of the Leibniz rule, i.e., `deriv_mul`.
Hint: Calc and limit laws and `continuous_at_iff_tends_to`.
-/

/-
Use exercise1 to show compute the derivative of monomial functions.
Hint: Induction on n.
-/
lemma HasDeriv_x : HasDeriv (fun x ↦ x) (fun _ ↦ 1) := by
  have h : (fun (x : ℝ) ↦ x) = fun x ↦ 1*x + 0 := by simp only [one_mul,add_zero]
  rw[const_def,h]
  exact deriv_affine 1 0

lemma HasDeriv_power (n : ℕ) : HasDeriv (fun x => x ^ n) (fun x : ℝ => n * x ^ (n - 1)) := by
  induction n with
  | zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_tsub, mul_one,const_def]
    exact deriv_const 1
  | succ n hn =>
    by_cases! hn1 : n = 0
    · simp only [hn1, zero_add, pow_one, Nat.cast_one, tsub_self, pow_zero, mul_one]
      exact HasDeriv_x
    simp only [pow_add, pow_one, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right,add_mul,one_mul]
    have h : HasDeriv ((fun x ↦ x^n) * (fun x ↦ x)) (deriv (fun x ↦ x^n) * (fun x ↦ x) + (fun x ↦ x^n) * deriv  (fun x ↦ x)) := by
      refine deriv_mul ?_ ?_
      · use fun x ↦ ↑n * x ^ (n - 1)
      use fun x ↦ 1
      exact HasDeriv_x
    have h1 {x : ℝ} : ↑n * x ^ (n - 1) * x + x ^ n = ↑n * x ^ n + x ^ n := by
      nth_rw 2[←pow_one x]
      rw[mul_assoc,←pow_add x (n-1) 1, Nat.sub_add_cancel]
      exact Nat.one_le_iff_ne_zero.mpr hn1
    simp only [Pi.mul_def, Eq.symm (deriv_of_has_deriv hn), Eq.symm (deriv_of_has_deriv HasDeriv_x), mul_one, Pi.add_def,h1] at h
    exact h
lemma deriv_power (n : ℕ) : deriv (fun x => x ^ n) = (fun x : ℝ => n * x ^ (n - 1)) := by
  exact Eq.symm (deriv_of_has_deriv (HasDeriv_power n))


/-
Prove the fact that the derivate vanishes at a local minimum.
Hint: Use the corresponding fact for a local maximum and the fact that `deriv (-f) = -deriv f`.
-/
theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by sorry

/-
Use the theorem `deriv_at_max_zero` and the theorems below
to prove Rolle's theorem from the lecture.
-/
theorem max_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f) :
    ∃ x ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) x := by
  sorry -- You don't have to prove this! This corresponds to `isCompact_Icc.exists_isMaxOn`.

theorem min_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f) :
    ∃ x ∈ Set.Icc a b, IsMinOn f (Set.Icc a b) x := by
  sorry -- You don't have to prove this! This corresponds to `isCompact_Icc.exists_isMinOn`.

lemma satz_von_rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f) (h : f a = f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = 0 := by
  sorry

/-
Finally, use the lemma above to prove the main theorem.
-/
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
    have h : HasDeriv (fun x ↦ (f x + ((f a - f b) / (b - a) * x + (f b - f a) / (b - a)*a))) ((deriv f) + deriv (fun x ↦ (f a - f b) / (b - a)*x+(f b - f a) / (b - a)*a)) := by
      refine @deriv_add f (fun x ↦ ((f a - f b) / (b - a) * x + (f b - f a) / (b - a)*a)) hf ?_
      use fun _ ↦ (f a - f b)/(b-a)
      exact deriv_affine ((f a - f b)/(b-a)) ((f b - f a)/(b-a)*a)
    have h1 : f b + ((f a - f b) / (b - a) * b + (f b - f a) / (b - a)*a) = f a := by
      calc
        f b + ((f a - f b) / (b - a) * b + (f b - f a) / (b - a) * a) = f b + (f a - f b) * ((b-a) / (b-a)) := by ring
        _ = f b + (f a - f b) := by
          rw[div_self]
          · ring
          linarith
        _ = f a := by ring
    have h2 : deriv (fun x ↦ (f a - f b) / (b - a)*x+(f b - f a) / (b - a)*a) = const _ ((f a - f b) / (b - a)) := by
      refine Eq.symm (deriv_of_has_deriv ?_)
      exact deriv_affine ((f a - f b) / (b - a)) ((f b - f a) / (b - a)*a)
    simp only [h2] at h
    have h2 : f a + ((f a - f b) / (b - a) * a + (f b - f a) / (b - a)*a) = f a := by ring
    have h3 : f a + ((f a - f b) / (b - a) * a + (f b - f a) / (b - a)*a) = f b + ((f a - f b) / (b - a) * b + (f b - f a) / (b - a)*a) := by simp only [h1,h2]
    have hf : Differentiable fun x ↦ f x + ((f a - f b) / (b - a) * x + (f b - f a) / (b - a) * a) := by use deriv f + const ℝ ((f a - f b) / (b - a))
    have h_rolle : ∃x ∈ Set.Ioo a b, deriv (fun x ↦ f x + ((f a - f b) / (b - a) * x + (f b - f a) / (b - a) * a)) x = 0 := satz_von_rolle hab hf h3
    obtain ⟨x,hx⟩ := h_rolle
    apply deriv_of_has_deriv at h
    use x
    constructor
    · exact hx.1
    rw[←h] at hx
    simp only [Pi.add_apply, const_apply] at hx
    grind

/-
Bonus exercise:
1) Show that every sequence with values in a closed interval has a convergent subsequence.
2) Prove the max_value_theorem.
-/

-- We've used this many times. You can leave this for last.
lemma limit_of_nested_intervals {a b : ℕ → ℝ} {x : RealSeq} (hx : ∀ n, x n ∈ Set.Icc (a n) (b n))
    (hnset : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n))
    (hlim : MySequences.TendsTo ⟨(b - a)⟩ 0) :
    ∃ c, TendsTo x c ∧ ∀ n : ℕ, c ∈ Set.Icc (a n) (b n) := by
  sorry

/-
Hint: Try to build a sequence of nested intervals containing a subsequence. Then apply the lemma.
Note a < b is automatic (otherwise you get a contradiction)
-/
theorem convergent_subsequence_of_bounded {x : RealSeq} {a b : ℝ} (hx : ∀ n, x n ∈ Set.Icc a b) :
    ∃ σ : ℕ → ℕ, ∃ c : Set.Icc a b, TendsTo ⟨(x ∘ σ)⟩ c := by
  sorry
