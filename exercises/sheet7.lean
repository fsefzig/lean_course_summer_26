import LectureNotes.lecture8.examples8

open MyFunctions MySequences Function

/-
Exercise 1: Finish the proof of the Leibniz rule, i.e., `deriv_mul`.
Hint: Calc and limit laws and `continuous_at_iff_tends_to`.
-/

/-
Use exercise1 to show compute the derivative of monomial functions.
Hint: Induction on n.
-/
lemma hasDerivExt {f f' f'' : ℝ → ℝ} (hderiv : HasDeriv f f') (heq : f' = f'') : HasDeriv f f'' := by
  rw[heq] at hderiv
  exact hderiv

lemma deriv_power (n : ℕ) : HasDeriv (fun x => x ^ n) (fun x : ℝ => n * x ^ (n - 1)) := by
  induction n with
  | zero => simp only [pow_zero, CharP.cast_eq_zero, zero_tsub, mul_one]
            exact deriv_const 1
  | succ n ih =>
  by_cases hn : n = 0
  · rw[hn]
    have hd := deriv_affine 1 0
    simp only [one_mul, add_zero, const_one, zero_add, pow_one, Nat.cast_one, tsub_self, pow_zero,
      mul_one] at *
    exact hd
  have hprod : (fun x => x ^ (n + 1) : ℝ → ℝ )= (fun x => 1*x + 0) * (fun x => (x ^ n)) :=
    by ext x; rw [Pi.mul_apply]; ring
  have hmul := deriv_mul (⟨fun x => 1, deriv_affine 1 0⟩) (⟨fun x => n * x ^ (n - 1), ih⟩)
  rw[← deriv_of_has_deriv ih, ← deriv_of_has_deriv (deriv_affine 1 0), ← hprod] at hmul
  refine hasDerivExt hmul ?_
  ext x
  simp only [const_one, one_mul, add_zero, Pi.add_apply, Pi.mul_apply, Nat.cast_add, Nat.cast_one,
    add_tsub_cancel_right]
  ring_nf
  rw[add_comm, mul_pow_sub_one hn x]

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
  sorry

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
