import LectureNotes.lecture8.examples8

open MyFunctions MySequences Function

/-
Exercise 1: Finish the proof of the Leibniz rule, i.e., `deriv_mul`.
Hint: Calc and limit laws and `continuous_at_iff_tends_to`.
-/

lemma deriv_mul {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f * g) (deriv f * g  + f  * deriv g ) := by
  intro x
  have hfx : TendsTo f x (f x) :=
    (continuous_at_iff_tends_to).mp (continuous_of_differentiable hf x)
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  simp only [Pi.mul_apply, Pi.add_apply, ← deriv_of_has_deriv hf', ← deriv_of_has_deriv hg']
  have eq : ∀ y ≠ x, (f y * g y - f x * g x) / (y - x) = (f y - f x) / (y - x) * (g x) + (f y) *
    ((g y - g x)/(y - x)) := by
    intro y hy
    field_simp
    ring
  have h : TendsTo (fun y => (f y - f x)/(y - x) * g x + f y * ((g y - g x) / (y - x))) x
    (f' x * g x + f x * g' x) := tends_to_add_tends_to _ _ _ _ _
      (tends_to_mul_tends_to _ _ _ _ _ (hf' x) (tends_to_const (g x) x))
      (tends_to_mul_tends_to _ _ _ _ _ hfx (hg' x))
  change TendsTo (fun y => ((f * g) y - (f * g) x) / (y - x)) x (f' x * g x + f x * g' x)
  have hfun : (fun y => ((f * g) y - (f * g) x) / (y - x))
    = (fun y => (f y - f x)/(y - x) * g x + f y * ((g y - g x)/(y - x))) := by
    ext y
    by_cases hyx : y = x
    · simp only [hyx, Pi.mul_apply, sub_self, div_zero, zero_mul, mul_zero, add_zero]
    · exact eq y hyx
  rw[hfun]
  exact h

/-
Use exercise1 to show compute the derivative of monomial functions.
Hint: Induction on n.
-/

lemma deriv_mono_lin_eq_one : deriv (fun x ↦ x) = 1 := by
  simpa using Eq.symm (deriv_of_has_deriv (deriv_affine 1 0))

lemma has_deriv_power (n : ℕ) : HasDeriv (fun x : ℝ => x ^ n) (fun x : ℝ => n * x ^ (n - 1)) := by
  induction n with
  | zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_tsub, mul_one]
    exact deriv_const 1
  | succ n ih =>
    simp only [HasDeriv, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    have h1 : Differentiable (fun x ↦ x ^ n) := by exact ⟨_, ih⟩
    have h2 : Differentiable (fun x ↦ x) := by use 1; simpa using deriv_affine 1 0
    have mul := MyFunctions.deriv_mul h1 h2
    rw [deriv_mono_lin_eq_one, mul_one, ← deriv_of_has_deriv ih] at mul
    have eq : (((fun x ↦ (n : ℝ) * x ^ (n - 1)) * fun x ↦ x) + fun x ↦ x ^ n)
    = fun x ↦ ((n : ℝ) + 1) * x ^ n := by
      ext x
      simp only [Pi.add_apply, Pi.mul_apply]
      by_cases hn : n = 0
      · rw[hn]
        ring
      · rw[mul_assoc, pow_sub_one_mul hn x, Eq.symm (add_one_mul (↑n) (x ^ n))]
    rw[eq] at mul; exact mul

lemma deriv_power (n : ℕ) : deriv (fun x => x ^ n) = fun x : ℝ => n * x ^ (n - 1) := by
  exact (deriv_of_has_deriv (has_deriv_power n)).symm

/-
Prove the fact that the derivate vanishes at a local minimum.
Hint: Use the corresponding fact for a local maximum and the fact that `deriv (-f) = -deriv f`.
-/
theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  have deriv_max : deriv (-f) x = 0 := deriv_at_max_zero hε hf.neg
  by_cases h : ∃ f', HasDerivAt f f' x
  · obtain ⟨f', hf'⟩ := h
    rw[← deriv_eq_of_has_deriv f f' x hf']
    have deriv_eq_neg : HasDerivAt (-f) (-f') x := by
      simp only [HasDerivAt, MyFunctions.TendsTo, gt_iff_lt, ne_eq, Pi.neg_apply, sub_neg_eq_add]
      intro ε' hε'
      obtain ⟨δ, hδ, htendsTo⟩ := hf' ε' hε'
      refine ⟨δ, hδ, ?_⟩
      intro y hy hyx
      have eq : (-f y + f x) / (y - x) + f' = f' - (f y - f x) / (y - x) := by ring
      rw[eq]
      exact lt_of_eq_of_lt (abs_sub_comm f' ((f y - f x) / (y - x))) (htendsTo y hy hyx)
    rw[← deriv_eq_of_has_deriv (-f) (-f') x deriv_eq_neg] at deriv_max
    linarith
  simp only [deriv, h, ↓reduceDIte]

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
  -- the german name lol
  have hCont : ContinuousOn f := by exact continuous_of_differentiable hf
  have ⟨x_max, max_in, hmax⟩ := max_value_theorem hab hCont
  have ⟨x_min, min_in, hmin⟩ := min_value_theorem hab hCont
  have y_in : ∀ y ∈ Set.Ioo a b, ∃ ε > 0, Set.Ioo (y - ε) (y + ε) ⊆ Set.Icc a b := by
    intro y hy
    use min (y - a) (b - y)
    obtain ⟨y_gt_a, b_gt_y⟩ := hy
    refine ⟨lt_min (by linarith) (by linarith), ?_⟩
    intro z hz
    have gt_a : a < z := lt_of_le_of_lt (le_sub_comm.mp (min_le_left _ _)) hz.1
    have lt_b : z < b :=
      lt_of_lt_of_le hz.2 (le_sub_iff_add_le.mp (le_sub_comm.mp (min_le_right _ _)))
    constructor <;> linarith
  have max_imp_horiz : ∀ y ∈ Set.Ioo a b, IsMaxOn f (Set.Icc a b) y → deriv f y = 0 := by
    intro y hy hmaxy
    obtain ⟨ε, hε, hsub⟩ := y_in y hy
    exact deriv_at_max_zero hε (IsMaxOn.on_subset hmaxy hsub)
  have min_imp_horiz : ∀ y ∈ Set.Ioo a b, IsMinOn f (Set.Icc a b) y → deriv f y = 0 := by
    intro y hy hminy
    obtain ⟨ε, hε, hsub⟩ := y_in y hy
    exact deriv_at_min_zero hε (IsMinOn.on_subset hminy hsub)
  by_cases max_eq : f x_max = f a
  · by_cases min_eq : f x_min = f a
    · use (a + b) / 2
      have fz_le_max : ∀ z ∈ Set.Icc a b, f z ≤ f x_max := hmax
      have fz_gt_min : ∀ z ∈ Set.Icc a b, f x_min ≤ f z := hmin
      have mid_in : (a + b) / 2 ∈ Set.Icc a b := by constructor <;> linarith
      have mid_in_excl : (a + b) / 2 ∈ Set.Ioo a b := by constructor <;> linarith
      constructor
      · exact mid_in_excl
      · refine max_imp_horiz ((a + b) / 2) mid_in_excl ?_
        intro z hz
        simp
        have z_le_max := fz_le_max z hz
        have mid_gt_min := fz_gt_min ((a + b) / 2) mid_in
        rw[max_eq] at z_le_max
        rw[min_eq] at mid_gt_min
        linarith
    · have fmin_ne_fb : f x_min ≠ f b :=
        (ne_of_eq_of_ne (id (Eq.symm h)) fun hz ↦ min_eq (id (Eq.symm hz))).symm
      have gt_a : a < x_min :=
        lt_of_le_of_ne min_in.1 (Ne.intro fun hz ↦ min_eq (congrArg f hz)).symm
      have lt_b : x_min < b :=
        lt_of_le_of_ne min_in.2 (Ne.intro fun hz ↦ fmin_ne_fb (congrArg f hz))
      use x_min
      have min_in_excl : x_min ∈ Set.Ioo a b := by constructor <;> linarith
      exact ⟨min_in_excl, min_imp_horiz x_min min_in_excl hmin⟩
  · have fmax_ne_fb : f x_max ≠ f b :=
      Ne.symm (ne_of_eq_of_ne (id (Eq.symm h)) fun hz ↦ max_eq (id (Eq.symm hz)))
    have gt_a : a < x_max :=
      lt_of_le_of_ne max_in.1 (Ne.intro fun hz ↦ max_eq (congrArg f (id (Eq.symm hz))))
    have lt_b : x_max < b :=
      lt_of_le_of_ne max_in.2 (Ne.intro fun hz ↦ fmax_ne_fb (congrArg f hz))
    use x_max
    have max_in_excl : x_max ∈ Set.Ioo a b := by constructor <;> linarith
    exact ⟨max_in_excl, max_imp_horiz x_max max_in_excl hmax⟩
  -- probably some much simpler way to prove but this worked so im happy :)

/-
Finally, use the lemma above to prove the main theorem.
-/
noncomputable def g (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := fun x => f x - (f b - f a) / (b - a) * (x - a)

lemma ga_eq_gb (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) : g f a b a = g f a b b := by
  simp only [g, sub_self, mul_zero, sub_zero]
  have cancel : (f b - f a) / (b - a) * (b - a) = (f b - f a) := by
    exact div_mul_cancel₀ (f b - f a) (sub_ne_zero.mpr (ne_of_gt hab))
  rw[cancel]
  simp only [sub_sub_cancel]

lemma g_differentiable (f : ℝ → ℝ) (a b : ℝ) (hf : Differentiable f) :
  Differentiable (g f a b) := by
  simp only [Differentiable]
  have hsplit :
    g f a b = f + (fun x => - ((f b - f a) / (b - a)) * x + (f b - f a) / (b - a) * a) := by
    ext x
    simp only [g, Pi.add_apply]
    ring
  rw [hsplit]
  have affine_diffable : Differentiable fun x ↦ -((f b - f a) / (b - a)) * x +
    (f b - f a) / (b - a) * a := ⟨_, deriv_affine _ _⟩
  have sum_diffable : Differentiable (f + fun x ↦ -((f b - f a) / (b - a)) * x +
    (f b - f a) / (b - a) * a) := ⟨_, deriv_add hf affine_diffable⟩
  exact Exists.imp (fun a_1 a ↦ a) sum_diffable

lemma g_deriv_zero_imp (f : ℝ → ℝ) (a b : ℝ) (hf : Differentiable f) (x₀ : ℝ) :
  deriv (g f a b) x₀ = 0 → deriv f x₀ = (f b - f a) / (b - a) := by
  intro hg
  have hsplit :
    g f a b = f + (fun x => - ((f b - f a) / (b - a)) * x + (f b - f a) / (b - a) * a) := by
    ext x
    simp only [g, Pi.add_apply]
    ring
  rw[hsplit] at hg -- this is repeated from g_diff; i should've probably made this a lemma
  have deriv_split : HasDeriv
    (f + (fun x => - ((f b - f a) / (b - a)) * x + (f b - f a) / (b - a) * a))
    (deriv (f) + deriv ((fun x => - ((f b - f a) / (b - a)) * x + (f b - f a) / (b - a) * a))) := by
    exact deriv_add hf  ⟨_, deriv_affine _ _⟩
  have affine_hasderiv : HasDeriv (fun x ↦ -((f b - f a) / (b - a)) * x +
    (f b - f a) / (b - a) * a) (fun x ↦ -((f b - f a) / (b - a))) := by
    exact deriv_affine _ _
  rw[(deriv_of_has_deriv (affine_hasderiv)).symm] at deriv_split
  rw[(deriv_of_has_deriv deriv_split).symm] at hg
  simp only [Pi.add_apply] at hg
  linarith

theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
  obtain ⟨x₀, hx₀, hderiv⟩ := satz_von_rolle hab (g_differentiable f a b hf) (ga_eq_gb f a b hab)
  refine ⟨x₀, hx₀, ?_⟩
  exact g_deriv_zero_imp f a b hf x₀ hderiv

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
