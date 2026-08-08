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
lemma deriv_mul' {f g : ℝ → ℝ} {x f' g' : ℝ} (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    deriv (f * g) x = (deriv f * g  + f  * deriv g) x := by
  sorry -- trivial claim but a lot of work to manually prove (might come back to this)

lemma deriv_const_mul {f : ℝ → ℝ} (a : ℝ) : deriv (f * const _ a) = const _ a * deriv f := by
  ext x
  by_cases hf : ∃f', HasDerivAt f f' x
  · obtain ⟨f',hf⟩ := hf
    simp only [deriv_mul' hf (deriv_const a x), ← deriv_of_has_deriv (deriv_const a), const_zero, mul_comm, mul_zero, Pi.add_apply, Pi.mul_apply, const_apply, Pi.zero_apply, add_zero]
  simp only [deriv, Pi.mul_apply, const_apply, hf, ↓reduceDIte, mul_zero]
  by_cases! h : a = 0
  · rw[←deriv,h,const_zero,mul_zero]
    exact Eq.symm (congrFun (deriv_of_has_deriv (deriv_const 0)) x)
  have h1 : ¬∃ f', HasDerivAt (f * const _ a) f' x := by
    by_contra!
    obtain ⟨f',hf'⟩ := this
    have hf' : MyFunctions.TendsTo (fun y ↦ a * ((f y - f x) / (y - x))) x f' := by
      simp only [HasDerivAt, Pi.mul_apply, const_apply] at hf'
      grind
    have ha :  MyFunctions.TendsTo (fun _ ↦ a⁻¹) x a⁻¹ := tends_to_const a⁻¹ x
    have contra := tends_to_mul_tends_to (fun y ↦ a * ((f y - f x) / (y - x))) ((fun _ ↦ a⁻¹)) x f' a⁻¹ hf' ha
    have h : (fun y ↦ a * ((f y - f x) / (y - x)) * a⁻¹) = fun y ↦ (f y - f x) / (y - x) := by grind
    rw[h,←HasDerivAt] at contra
    grind
  grind

lemma deriv_neg {f : ℝ → ℝ} : deriv (-f) = - deriv f := by
  have h : (-f) = (f * const _ (-1)) := by
    ext x
    simp only [Pi.neg_apply, Pi.mul_apply, const_apply, mul_neg, mul_one]
  rw[h,deriv_const_mul (-1)]
  ext x
  simp only [Pi.mul_apply, const_apply, neg_mul, one_mul, Pi.neg_apply]

theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
    have hf : IsMaxOn (-f) (Set.Ioo (x - ε) (x + ε)) x := by
      intro x1 hx
      simp only [Pi.neg_apply, neg_le_neg_iff, Set.mem_setOf_eq]
      simp only [IsMinOn, IsMinFilter, Filter.eventually_principal, Set.mem_Ioo, and_imp] at hf
      simp only [Set.mem_Ioo] at hx
      specialize hf x1 hx.1 hx.2
      exact hf
    have h : deriv (-f) x = 0 := by
      exact deriv_at_max_zero hε hf
    simp only [deriv_neg, Pi.neg_apply, neg_eq_zero] at h
    exact h


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
    by_cases! h : IsMinOn f (Set.Icc a b) a ∧ ∃ x ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) a
    · have h1 : ∀x ∈ Set.Ioo a b, f x = f a := by
        intro x hx
        by_contra!
        apply lt_or_gt_of_ne at this
        rcases this with h1 | h2
        · have h2 := h.1
          simp [IsMinOn,IsMinFilter] at h2
          grind
        have h1 := h.2
        simp [IsMaxOn,IsMaxFilter] at h1
        grind
      use (a+b)/2
      constructor
      · grind
      have h := Eq.symm (congrFun (deriv_of_has_deriv (deriv_const (f a))) ((a+b)/2))
      simp only [const_apply] at h
/-
Finally, use the lemma above to prove the main theorem.
-/
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
    have h : HasDeriv (fun x ↦ (f x + ((f a - f b) / (b - a) * x + (f b - f a) / (b - a)*a))) ((deriv f) + deriv (fun x ↦ (f a - f b) / (b - a)*x+(f b - f a) / (b - a)*a)) := by
      refine @deriv_add f (fun x ↦ ((f a - f b) / (b - a) * x + (f b - f a) / (b - a)*a)) hf ?_
      use fun _ ↦ (f a - f b)/(b-a)
      exact deriv_affine ((f a - f b)/(b-a)) ((f b - f a)/(b-a)*a)
    have h1 : f b + ((f a - f b) / (b - a) * b + (f b - f a) / (b - a)*a) = f a := by grind
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
