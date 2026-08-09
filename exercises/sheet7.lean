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
#check deriv_of_has_deriv
#check deriv_const
#check deriv_affine
#check deriv_mul
#check Differentiable
#check deriv_of_has_deriv

lemma deriv_power (n : ℕ) : deriv (fun x => x ^ n) = fun x : ℝ => n * x ^ (n - 1) := by
  have hpower : ∀ n : ℕ, HasDeriv (fun x : ℝ => x ^ n) (fun x : ℝ => n * x ^ (n - 1)) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact deriv_const 1
    | succ n ih =>
        have hx : HasDeriv (fun x : ℝ => x) (const ℝ 1) := by
          simpa using (deriv_affine (1 : ℝ) 0)
        have hxn : Differentiable (fun x : ℝ => x ^ n) := by
          exact ⟨_, ih⟩
        have hx1 : Differentiable (fun x : ℝ => x) := by
          exact ⟨_, hx⟩
        have hmul := deriv_mul (f := fun x : ℝ => x ^ n) (g := fun x : ℝ => x) hxn hx1
        rw [← deriv_of_has_deriv ih] at hmul
        rw [← deriv_of_has_deriv hx] at hmul
        cases n with
        | zero =>
          ring
          exact hx
        | succ k =>
          convert hmul using 1
          · funext x
            simp [pow_succ]
          · funext x
            simp [pow_succ]
            ring
  apply (deriv_of_has_deriv (hpower n)).symm

/-
Prove the fact that the derivate vanishes at a local minimum.
Hint: Use the corresponding fact for a local maximum and the fact that `deriv (-f) = -deriv f`.
-/
#check deriv_at_max_zero
#check neg_le_neg
#check IsMaxOn.neg
#check tends_to_mul_tends_to

theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
    apply IsMinOn.neg at hf
    have hnegzero : deriv (fun y : ℝ => -f y) x = 0 := by
      apply deriv_at_max_zero hε hf
    by_cases h : ∃ f', HasDerivAt f f' x
    obtain ⟨f', hf'⟩ := h
    have hneg' :
        HasDerivAt (fun y : ℝ => -f y) (-f') x := by
      unfold HasDerivAt
      have hprod : TendsTo (fun y ↦ const ℝ (-1) y * ((f y - f x) / (y - x))) x (-1 * f') := by
        apply tends_to_mul_tends_to
        apply tends_to_const (-1) x
        exact hf'
      convert hprod using 1
      funext y
      simp only [const_apply]
      ring
      ring
    have hf'eq :
        f' = deriv f x :=
      deriv_eq_of_has_deriv f f' x hf'
    have hneg'eq :
        -f' = deriv (fun y : ℝ => -f y) x :=
      deriv_eq_of_has_deriv (fun y : ℝ => -f y) (-f') x hneg'
    rw [← hneg'eq] at hnegzero
    rw [← hf'eq]
    linarith
    simp only [deriv, h, reduceDIte]

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
#check isCompact_Icc.exists_isMaxOn
#check Set.mem_setOf_eq

lemma satz_von_rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f) (h : f a = f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = 0 := by
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
      constructor
      linarith
      linarith
    by_cases hconst : ∀ x ∈ Set.Ioo a b, f x = f a
    use ( a + b ) / 2
    constructor
    exact hmid
    have hderiv : deriv f ((a + b) / 2) = 0 := by
      have hε : (b - a) / 2 > 0 := by
        linarith
      apply deriv_at_min_zero hε
      intro x hx
      rw [show (a + b) / 2 - (b - a) / 2 = a by ring, show (a + b) / 2 + (b - a) / 2 = b by ring] at hx
      rw [hconst]
      have heq : f x = f a := by
        apply hconst
        exact hx
      simp
      rw [heq]
      exact hmid
    exact hderiv
    have hmax := max_value_theorem hab (continuous_of_differentiable hf)
    have hmin := min_value_theorem hab (continuous_of_differentiable hf)
    obtain ⟨xmax, hxmaxIcc, hmaxon⟩ := hmax
    obtain ⟨xmin, hxminIcc, hminon⟩ := hmin
    push_neg at hconst
    obtain ⟨y, hy, hya⟩ := hconst
    rcases lt_or_gt_of_ne hya with hylt | hygt
    have hyIcc : y ∈ Set.Icc a b := by
      constructor
      exact le_of_lt hy.1
      exact le_of_lt hy.2
    have hminy : f xmin ≤ f y := by
      apply hminon
      exact hyIcc
    have hmina : f xmin < f a := by
      linarith
    have hne_a : xmin ≠ a := by
      intro hne
      rw [hne] at hmina
      linarith
    have hne_b : xmin ≠ b := by
      intro hne
      rw [hne] at hmina
      linarith
    have hxopen : xmin ∈ Set.Ioo a b := by
      constructor
      exact lt_of_le_of_ne hxminIcc.1 (Ne.symm hne_a)
      exact lt_of_le_of_ne hxminIcc.2 hne_b
    use xmin
    constructor
    exact hxopen
    let ε : ℝ := min (xmin - a) (b - xmin)
    have hε : ε > 0 := by
      dsimp [ε]
      exact lt_min (sub_pos.mpr hxopen.1) (sub_pos.mpr hxopen.2)
    apply deriv_at_min_zero hε
    intro z hz
    apply hminon
    constructor
    have hεleft : ε ≤ xmin - a := by
      dsimp [ε]
      exact min_le_left _ _
    linarith [hz.1, hεleft]
    have hεright : ε ≤ b - xmin := by
      dsimp [ε]
      exact min_le_right _ _
    linarith [hz.2, hεright]
    have hyIcc : y ∈ Set.Icc a b := by
      constructor
      exact le_of_lt hy.1
      exact le_of_lt hy.2
    have hyIcc : y ∈ Set.Icc a b := by
      constructor
      exact le_of_lt hy.1
      exact le_of_lt hy.2
    have hymax : f y ≤ f xmax := by
      apply hmaxon
      exact hyIcc
    have hamax : f a < f xmax := by
      linarith
    have hne_a : xmax ≠ a := by
      intro hxa
      rw [hxa] at hamax
      exact (lt_irrefl _ hamax)
    have hne_b : xmax ≠ b := by
      intro hxb
      rw [hxb, ← h] at hamax
      exact (lt_irrefl _ hamax)
    have hxmaxIoo : xmax ∈ Set.Ioo a b := by
      constructor
      rcases lt_or_eq_of_le hxmaxIcc.1 with hlt | heq
      exact hlt
      exact False.elim (hne_a heq.symm)
      rcases lt_or_eq_of_le hxmaxIcc.2 with hlt | heq
      exact hlt
      exact False.elim (hne_b heq)
    let ε : ℝ := min (xmax - a) (b - xmax)
    have hε : ε > 0 := by
      dsimp [ε]
      exact lt_min (sub_pos.mpr hxmaxIoo.1) (sub_pos.mpr hxmaxIoo.2)
    have hεleft : ε ≤ xmax - a := by
      dsimp [ε]
      exact min_le_left _ _
    have hεright : ε ≤ b - xmax := by
      dsimp [ε]
      exact min_le_right _ _
    have hmaxlocal : IsMaxOn f (Set.Ioo (xmax - ε) (xmax + ε)) xmax := by
      intro z hz
      apply hmaxon
      constructor
      linarith [hz.1, hεleft]
      linarith [hz.2, hεright]
    exact ⟨xmax, hxmaxIoo, deriv_at_max_zero hε hmaxlocal⟩


/-
Finally, use the lemma above to prove the main theorem.
-/
#check deriv_affine
#check deriv_add
#check congrFun

theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
    let m : ℝ := (f b - f a) / (b - a)
    let g : ℝ → ℝ := f + (fun x : ℝ => -m * (x - a))
    have h : (fun x : ℝ => -m * (x - a)) = (fun x : ℝ => -m * x + m * a) := by
      funext x
      ring
    have haffine : HasDeriv (fun x => -m * (x - a)) (const ℝ (-m)) := by
        rw [h]
        simpa using deriv_affine (-m) (m * a)
    have hdiffmx : Differentiable fun x => -m * (x - a) := by
      exact ⟨_, haffine⟩
    have hdiffg : Differentiable g := by
      refine ⟨deriv f + deriv (fun x : ℝ => -m * (x - a)), ?_⟩
      apply deriv_add hf hdiffmx
    have hne_zero : b - a ≠ 0 := by
        linarith
    have hg : g a = g b := by
      dsimp [g, m]
      simp
      rw [div_mul_cancel₀ (f b - f a) hne_zero]
      simp
    obtain ⟨x, hx, hxzero⟩ := satz_von_rolle hab hdiffg hg
    have hgDeriv : HasDeriv g (deriv f + const ℝ (-m)) := by
      dsimp [g]
      have hadd := deriv_add hf hdiffmx
      rw [← deriv_of_has_deriv haffine] at hadd
      exact hadd
    have heq := deriv_of_has_deriv hgDeriv
    rw [← heq] at hxzero
    rw [Pi.add_apply, const_apply] at hxzero
    use x
    constructor
    exact hx
    have heq : deriv f x = m := by
      linarith
    unfold m at heq
    exact heq

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
