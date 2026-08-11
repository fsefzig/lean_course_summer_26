import LectureNotes.lecture7.examples7
import Exercises.Sheet5
import Exercises.Sheet6

namespace MyFunctions

open MyFunctions MySequences Function

/-
Convergence of a function `f : ℝ → ℝ` to a limit `a` at a point `x`.
-/
def TendsTo (f : ℝ → ℝ) (x : ℝ) (a : ℝ) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ y ≠ x, |y - x| < δ → |f y - a| < ε


/-
As you can see, there are a few sorry's in the code. Most of these results are similar to things
that we've already proved for sequences. The proofs are completely analogous.
-/
lemma continuous_at_iff_tends_to {f : ℝ → ℝ} {x : ℝ} :
    ContinuousAt f x ↔ TendsTo f x (f x) := by
    constructor
    · intro h ε hε
      obtain ⟨δ, hδ, h'⟩ := h ε hε
      exact ⟨δ, hδ, fun y hy hxy => h' y hxy⟩
    intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    refine ⟨δ, hδ, fun y hxy => ?_⟩
    by_cases h : y = x
    · rw[h, dist_self]
      exact hε
    exact h' y h hxy

lemma tends_to_of_fun_tends_to {f : ℝ → ℝ} {y : RealSeq} {x a : ℝ} (h : TendsTo f x a)
    (hy : MySequences.TendsTo y x) : MySequences.TendsTo ⟨(fun n => f (y n))⟩ a := by
  sorry

lemma tends_to_const (a : ℝ) (x : ℝ) : TendsTo (const _ a) x a := by
  intro ε hε
  refine ⟨1, by positivity, fun y hy hxy => ?_⟩
  simp only [const_apply, sub_self, abs_zero]
  exact hε

lemma tends_to_of_sub {f : ℝ → ℝ} {x a : ℝ} :
    TendsTo f x a ↔ TendsTo (f - const _ a) x 0 := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h'⟩ := h ε hε
    refine ⟨δ, hδ, fun y hy hxy => ?_⟩ -- new trick: refine instead of use
    simp only [Pi.sub_apply, const_apply, sub_zero, h' y hy hxy]
  intro h ε hε
  obtain ⟨δ, hδ, h'⟩ := h ε hε
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  specialize h' y hy hxy
  simp only [Pi.sub_apply, const_apply, sub_zero] at h'
  exact h'

lemma tends_to_add_tends_to {f g : ℝ → ℝ} {x a b : ℝ} :
    TendsTo f x a → TendsTo g x b → TendsTo (fun y => f y + g y) x (a + b) := by
  sorry

lemma tends_to_mul_tends_to {f g : ℝ → ℝ} {x a b : ℝ} :
    TendsTo f x a → TendsTo g x b → TendsTo (fun y => f y * g y) x (a * b) := by
  sorry

/-
We can define the derivative of a function `f` at a point `x` using the above notion of convergence.
-/
def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  TendsTo (fun y => (f y - f x) / (y - x)) x f'

-- Follows directly from the fact that limits are unique in ℝ. See lecture 6 `tends_toReal_unique`.
lemma deriv_unique {f : ℝ → ℝ} {x : ℝ} {f' f'' : ℝ}
    (hf' : HasDerivAt f f' x) (hf'' : HasDerivAt f f'' x) : f' = f'' := by
  sorry

/-
Assertion that `f'` is the derivative of `f` at every point `x : ℝ`
-/
def HasDeriv (f : ℝ → ℝ) (f' : ℝ → ℝ) : Prop :=
    ∀ x, HasDerivAt f (f' x) x

/-
We define the derivate of a function to be the value `f'`
from above if it exists, otherwise `0`.
We have to use the axiom of choice here, so we mark this definition as noncomputable.
-/
open scoped Classical in
noncomputable def deriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ f', HasDerivAt f f' x
    then Classical.choose h
  else 0

-- If `f` is differentiable at `x`, then `deriv f x` is the derivative of `f` at `x`.
lemma deriv_eq_of_has_deriv {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : HasDerivAt f f' x) :
     f' = deriv f x := by
  unfold deriv
  have hex: ∃ f', HasDerivAt f f' x := ⟨f', hf⟩
  simp only [hex, ↓reduceDIte]
  apply deriv_unique (hf) (Classical.choose_spec hex) --access property of choose

-- The same holds globally.
lemma deriv_of_has_deriv {f : ℝ → ℝ} {f' : ℝ → ℝ} (hf : HasDeriv f f') :
    f' = deriv f := by
  ext x --extensionality of functions
  apply deriv_eq_of_has_deriv
  exact hf x

-- Thus, we introduce the notion of a differentiable function.
def Differentiable (f : ℝ → ℝ) : Prop :=
  ∃ f', HasDeriv f f'

-- As a sanity check, we can show that the derivative of a differentiable function is `deriv f`.
lemma has_deriv_of_differentiable {f : ℝ → ℝ} (hf : Differentiable f) :
    HasDeriv f (deriv f) := by
    obtain ⟨f', hf'⟩ := hf
    rw[← deriv_of_has_deriv hf']
    exact hf'

lemma continuous_at_of_deriv_at {f: ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    ContinuousAt f x := by
  rw[continuous_at_iff_tends_to, tends_to_of_sub]
  have h (g : ℝ → ℝ) (hg : g x = 0): g = (fun y => g y / (y - x)) * fun y => y - x := by
      ext y
      by_cases h : y = x
      · simp only [h, hg, Pi.mul_apply, sub_self, div_zero, mul_zero]
      simp only [Pi.mul_apply]
      field_simp -- new tactic!
  rw[h (f - const _ (f x)) (sub_self (f x)), ← mul_zero (f')]
  refine tends_to_mul_tends_to hf ?_
  exact fun ε hε => ⟨ε, hε, fun y hy hxy => by simp only [sub_zero, hxy]⟩


lemma continuous_of_differentiable {f : ℝ → ℝ} (hf : Differentiable f) :
    ContinuousOn f := by
    obtain ⟨f', hf'⟩ := hf
    exact fun x => continuous_at_of_deriv_at (hf' x)

lemma deriv_add_at {f g: ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
  HasDerivAt (f + g) (f' + g') x := sorry

lemma deriv_add {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f + g) (deriv f + deriv g) := by
  sorry

lemma deriv_mul_at {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ} (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (f * g) (f' * g x + f x * g') x := by
  unfold HasDerivAt at ⊢
  have hexpand : (fun y ↦ ((f * g) y - (f * g) x) / (y - x))
    = (fun y => (f y - f x) / (y - x)) * const _ (g x)  + f *  (fun y => (g y - g x) / (y - x)) := by
    ext y
    simp only [Pi.add_apply, Pi.mul_apply, const_apply]
    calc
      (f y * g y - f x * g x) / (y - x) =
          ((f y - f x) * g x + f y * (g y - g x)) / (y - x) := by ring
      _ = (f y - f x) / (y - x) * g x +
          f y * ((g y - g x) / (y - x)) := by ring
  rw[hexpand]
  apply tends_to_add_tends_to ?_ ?_
  · exact tends_to_mul_tends_to hf (tends_to_const (g x) x)
  refine tends_to_mul_tends_to ?_ hg
  apply continuous_at_iff_tends_to.mp (continuous_at_of_deriv_at hf)


lemma deriv_mul {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f * g) (deriv f * g  + f  * deriv g ) := fun x =>
  deriv_mul_at (has_deriv_of_differentiable hf x) (has_deriv_of_differentiable hg x)

lemma deriv_const (c : ℝ) : HasDeriv (const _ c) (const _ 0) := by
    intro x ε hε
    simp only [const_apply, sub_self, zero_div, abs_zero]
    exact ⟨1, by positivity, fun _ _ _ => by positivity⟩

lemma deriv_affine (a b : ℝ) : HasDeriv (fun x => a*x + b) (const _ a) := by
    intro x ε hε
    refine ⟨1, by positivity, fun y hy hxy => ?_⟩
    simp only [add_sub_add_right_eq_sub, const_apply, ← mul_sub a y x]
    field_simp
    rw[sub_self, mul_zero, abs_zero]
    positivity

/-
It is often convenient to restrict functions to intervals.
They are implemented in lean as `Set.Icc a b` for the closed interval `[a, b]`, `Set.Ioo a b` for
the open interval `(a, b)`, and `Set.Ico a b` for the half-open interval `[a, b)`, etc..
-/

#check Set.Ioo _ _ --(a, b) open interval; by defn x ∈ Set.Ioo a b ↔ a < x ∧ x < b.
#check Set.Icc _ _ --[a, b] closed interval
#check Set.Ico _ _ --[a, b) half-open interval

-- The fact that a function has a maximum on a set S is expressed as follows:
#check IsMaxOn

theorem deriv_at_max_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMaxOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  by_cases h : ∃ f' , HasDerivAt f f' x
  · obtain ⟨f', hf'⟩ := h
    obtain ⟨n, hn, hnle⟩ := nat_one_div_le hε
    have hlt : ∀ m : ℕ, ((↑n + ↑m + 1)⁻¹ : ℝ) < 1/n :=
            fun m => (by exact (lt_one_div (by positivity) (by positivity)).mp (by simp; linarith))
    let yu : ℕ → ℝ := fun m => x + 1 / (n + m + 1 : ℝ)
    have hyu : MySequences.TendsTo ⟨yu⟩ x := by
        sorry -- exericse :)
    let yl : ℕ → ℝ := fun m => x - 1 / (n + m + 1 : ℝ)
    have hyl : MySequences.TendsTo ⟨yl⟩ x := by sorry
    have hf'u : f' ≤ 0 := by
        apply tends_to_le_of_le (tends_to_of_fun_tends_to hf' hyu)
        intro m
        apply div_nonpos_of_nonpos_of_nonneg
        · simp only [sub_nonpos]
          refine le_of_eq_of_le rfl (hf ?_)
          simp only [one_div, Set.mem_Ioo, add_lt_add_iff_left, yu]
          exact ⟨lt_add_of_le_of_pos (by linarith) (by positivity), by linarith [hlt m]⟩
        simp only [one_div, add_sub_cancel_left, inv_nonneg, yu]
        linarith
    have hf'l : f' ≥ 0 := by
        apply tends_to_ge_of_ge (tends_to_of_fun_tends_to hf' hyl)
        intro m
        apply div_nonneg_of_nonpos
        · simp only [sub_nonpos]
          refine le_of_eq_of_le rfl (hf (?_))
          simp only [one_div, Set.mem_Ioo, sub_lt_sub_iff_left, yl]
          refine ⟨ by linarith [hlt m], ?_⟩
          calc
            x - (n + m + 1 : ℝ)⁻¹ < x := by simp only [sub_lt_self_iff, inv_pos]; positivity
            _ < x + ε := by linarith
        simp only [one_div, sub_sub_cancel_left, Left.neg_nonpos_iff, inv_nonneg, yl]
        linarith
    rw[← deriv_eq_of_has_deriv hf']
    linarith
  simp only [deriv, h, ↓reduceDIte]


end MyFunctions

--

open MyFunctions MySequences Function

/-
Exercise 1: Finish the proof of the Leibniz rule, i.e., `deriv_mul`.
Hint: Calc and limit laws and `continuous_at_iff_tends_to`.
-/

/-
Use exercise1 to show compute the derivative of monomial functions.
Hint: Induction on n.
-/
lemma deriv_power (n : ℕ) : deriv (fun x => x ^ n) = fun x : ℝ => n * x ^ (n - 1) := by
  sorry

/-
Prove the fact that the derivate vanishes at a local minimum.
Hint: Use the corresponding fact for a local maximum and the fact that `deriv (-f) = -deriv f`.
-/
theorem deriv_at_min_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMinOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  sorry
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
  have hcont : ContinuousOn f := continuous_of_differentiable hf
  obtain ⟨xmax, hxmax, hmax⟩ := max_value_theorem hab hcont
  obtain ⟨xmin, hxmin, hmin⟩ := min_value_theorem hab hcont
  have hmax_interior :
      ∀ {z : ℝ}, z ∈ Set.Ioo a b →
        IsMaxOn f (Set.Icc a b) z →
        deriv f z = 0 := by
    intro z hz hzmax
    have hδ : min (z - a) (b - z) > 0 := by
      exact lt_min (sub_pos.mpr hz.1) (sub_pos.mpr hz.2)
    apply deriv_at_max_zero hδ
    intro y hy
    apply hzmax
    rcases hy with ⟨hy₁, hy₂⟩
    have hleft : min (z - a) (b - z) ≤ z - a :=
      min_le_left _ _
    have hright : min (z - a) (b - z) ≤ b - z :=
      min_le_right _ _
    constructor <;> linarith
  have hmin_interior :
      ∀ {z : ℝ}, z ∈ Set.Ioo a b →
        IsMinOn f (Set.Icc a b) z →
        deriv f z = 0 := by
    intro z hz hzmin
    have hδ : min (z - a) (b - z) > 0 := by
      exact lt_min (sub_pos.mpr hz.1) (sub_pos.mpr hz.2)
    apply deriv_at_min_zero hδ
    intro y hy
    apply hzmin
    rcases hy with ⟨hy₁, hy₂⟩
    have hleft : min (z - a) (b - z) ≤ z - a :=
      min_le_left _ _
    have hright : min (z - a) (b - z) ≤ b - z :=
      min_le_right _ _
    constructor <;> linarith
  by_cases hxmax_int : xmax ∈ Set.Ioo a b
  · exact ⟨xmax, hxmax_int, hmax_interior hxmax_int hmax⟩
  by_cases hxmin_int : xmin ∈ Set.Ioo a b
  · exact ⟨xmin, hxmin_int, hmin_interior hxmin_int hmin⟩
  have hxmax_end : xmax = a ∨ xmax = b := by
    by_cases hxa : xmax = a
    · exact Or.inl hxa
    · right
      have hax : a < xmax := by
        exact lt_of_le_of_ne hxmax.1 (Ne.symm hxa)
      have hxb : ¬ xmax < b := by
        intro hxb
        exact hxmax_int ⟨hax, hxb⟩
      exact le_antisymm hxmax.2 (le_of_not_gt hxb)
  have hxmin_end : xmin = a ∨ xmin = b := by
    by_cases hxa : xmin = a
    · exact Or.inl hxa
    · right
      have hax : a < xmin := by
        exact lt_of_le_of_ne hxmin.1 (Ne.symm hxa)
      have hxb : ¬ xmin < b := by
        intro hxb
        exact hxmin_int ⟨hax, hxb⟩
      exact le_antisymm hxmin.2 (le_of_not_gt hxb)
  have hxmax_val : f xmax = f a := by
    rcases hxmax_end with hx | hx
    · rw [hx]
    · rw [hx]
      exact h.symm
  have hxmin_val : f xmin = f a := by
    rcases hxmin_end with hx | hx
    · rw [hx]
    · rw [hx]
      exact h.symm
  have hconst : ∀ y ∈ Set.Icc a b, f y = f a := by
    intro y hy
    have hu : f y ≤ f xmax := hmax hy
    have hl : f xmin ≤ f y := hmin hy
    rw [hxmax_val] at hu
    rw [hxmin_val] at hl
    exact le_antisymm hu hl
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by
    dsimp [c]
    constructor <;> linarith
  have hc_closed : c ∈ Set.Icc a b :=
    ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  have hcmax : IsMaxOn f (Set.Icc a b) c := by
    intro y hy
    exact le_of_eq ((hconst y hy).trans (hconst c hc_closed).symm)
  exact ⟨c, hc, hmax_interior hc hcmax⟩

/-
Finally, use the lemma above to prove the main theorem.
-/
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Differentiable f)
    : ∃ x ∈ Set.Ioo a b, deriv f x = (f b - f a) / (b - a) := by
  let m : ℝ := (f b - f a) / (b - a)
  let l : ℝ → ℝ := fun y => (-m) * y
  let g : ℝ → ℝ := fun y => f y + l y
  have hl_deriv : HasDeriv l (const ℝ (-m)) := by
    dsimp [l]
    simpa using deriv_affine (-m) 0
  have hl : Differentiable l := by
    exact ⟨const ℝ (-m), hl_deriv⟩
  have hg_deriv :
      HasDeriv g (deriv f + deriv l) := by
    dsimp [g]
    exact deriv_add hf hl
  have hg : Differentiable g := by
    exact ⟨deriv f + deriv l, hg_deriv⟩
  have hgab : g a = g b := by
    dsimp [g, l, m]
    have hba : b - a ≠ 0 := by
      linarith
    field_simp [hba]
    ring
  obtain ⟨x, hx, hxzero⟩ := satz_von_rolle hab hg hgab
  refine ⟨x, hx, ?_⟩
  have hl_eq : deriv l x = -m := by
    have hder := deriv_of_has_deriv hl_deriv
    have hxder := congrFun hder x
    simpa using hxder.symm
  have hg_eq :
      deriv f x + deriv l x = deriv g x := by
    have hder := deriv_of_has_deriv hg_deriv
    have hxder := congrFun hder x
    simpa only [Pi.add_apply] using hxder
  rw [hxzero, hl_eq] at hg_eq
  have hfx : deriv f x = m := by
    linarith
  simpa [m] using hfx

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
  have hnest : ∀ k n, Set.Icc (a (n + k)) (b (n + k)) ⊆ Set.Icc (a n) (b n) := by
    intro k n
    induction k with
    | zero =>
        exact fun _ h => h
    | succ k ih =>
        exact Set.Subset.trans (by simpa [Nat.add_assoc] using hnset (n + k)) ih
  have htail : ∀ {N m}, N ≤ m → x m ∈ Set.Icc (a N) (b N) := by
    intro N m hNm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNm
    exact hnest k N (hx (N + k))
  have hxCauchy : IsCauchyReal x := by
    intro ε hε
    obtain ⟨N, hN⟩ := hlim ε hε
    have hw := hN N (le_refl N)
    change dist (b N - a N) 0 < ε at hw
    rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (sub_nonneg.mpr (le_trans (hx N).1 (hx N).2))] at hw
    use N
    intro m hm n hn
    have hxm := htail hm
    have hxn := htail hn
    rw [Real.dist_eq]
    exact lt_of_le_of_lt
      (abs_le.mpr ⟨by linarith [hxm.1, hxm.2, hxn.1, hxn.2],
        by linarith [hxm.1, hxm.2, hxn.1, hxn.2]⟩) hw
  obtain ⟨c, hc⟩ := real_numbers_complete hxCauchy
  refine ⟨c, hc, ?_⟩
  intro n
  constructor
  · by_contra h
    obtain ⟨N, hN⟩ := hc ((a n - c) / 2) (by linarith)
    have hxM := htail (show n ≤ max n N from le_max_left _ _)
    have hclose := hN (max n N) (le_max_right _ _)
    exact (by linarith [(abs_lt.mp hclose).2, hxM.1])
  · by_contra h
    obtain ⟨N, hN⟩ := hc ((c - b n) / 2) (by linarith)
    have hxM := htail (show n ≤ max n N from le_max_left _ _)
    have hclose := hN (max n N) (le_max_right _ _)
    exact (by linarith [(abs_lt.mp hclose).1, hxM.2])

/-
Hint: Try to build a sequence of nested intervals containing a subsequence. Then apply the lemma.
Note a < b is automatic (otherwise you get a contradiction)
-/
theorem convergent_subsequence_of_bounded {x : RealSeq} {a b : ℝ} (hx : ∀ n, x n ∈ Set.Icc a b) :
    ∃ σ : ℕ → ℕ, ∃ c : Set.Icc a b, TendsTo ⟨(x ∘ σ)⟩ c := by
   classical
  by_cases hab : a = b
  · subst b
    refine ⟨id, ⟨a, le_rfl, le_rfl⟩, ?_⟩
    intro ε hε
    use 0
    intro n hn
    have hxn : x n = a := le_antisymm (hx n).2 (hx n).1
    simpa [hxn] using hε
  have hablt : a < b := lt_of_le_of_ne (le_trans (hx 0).1 (hx 0).2) hab
  let bounds : ℕ → ℝ × ℝ := fun n =>
    Nat.recOn n (a, b) (fun _ p =>
      if Set.Infinite {k : ℕ | x k ∈ Set.Icc p.1 ((p.1 + p.2) / 2)}
      then (p.1, (p.1 + p.2) / 2)
      else ((p.1 + p.2) / 2, p.2))
  have hzero : bounds 0 = (a, b) := by
    simp [bounds]
  have hsucc : ∀ n, bounds (n + 1) =
      if Set.Infinite {k : ℕ | x k ∈ Set.Icc (bounds n).1 (((bounds n).1 + (bounds n).2) / 2)}
      then ((bounds n).1, ((bounds n).1 + (bounds n).2) / 2)
      else (((bounds n).1 + (bounds n).2) / 2, (bounds n).2) := by
    intro n
    simp [bounds]
  have hord : ∀ n, (bounds n).1 ≤ (bounds n).2 := by
    intro n
    induction n with
    | zero =>
        rw [hzero]
        exact le_of_lt hablt
    | succ n ih =>
        rw [show n + 1 = Nat.succ n by omega, ← Nat.add_one, hsucc n]
        split_ifs <;> linarith
  have hInf : ∀ n, Set.Infinite {k : ℕ | x k ∈ Set.Icc (bounds n).1 (bounds n).2} := by
    intro n
    induction n with
    | zero =>
        rw [hzero]
        apply Set.infinite_univ.mono
        intro k hk
        exact hx k
    | succ n ih =>
      rw [hsucc n]
      split_ifs with hl
      · simpa using hl
      · by_contra hr
        apply ih.not_finite
        apply ((Set.not_infinite.mp hl).union (Set.not_infinite.mp hr)).subset
        intro k hk
        by_cases hm : x k ≤ ((bounds n).1 + (bounds n).2) / 2
        · exact Or.inl ⟨hk.1, hm⟩
        · exact Or.inr ⟨le_of_not_ge hm, hk.2⟩
  have hnset : ∀ n,
      Set.Icc (bounds (n + 1)).1 (bounds (n + 1)).2 ⊆
        Set.Icc (bounds n).1 (bounds n).2 := by
    intro n
    rw [hsucc n]
    split_ifs
    · intro y hy
      exact ⟨hy.1, by linarith [hy.2, hord n]⟩
    · intro y hy
      exact ⟨by linarith [hy.1, hord n], hy.2⟩
  have hwidth : ∀ n,
      (bounds n).2 - (bounds n).1 = (b - a) * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
        rw [hzero]
        simp
    | succ n ih =>
        rw [hsucc n]
        split_ifs
        · calc
            ((bounds n).1 + (bounds n).2) / 2 - (bounds n).1
                = ((bounds n).2 - (bounds n).1) / 2 := by ring
            _ = ((b - a) * (1 / 2 : ℝ) ^ n) / 2 := by rw [ih]
            _ = (b - a) * (1 / 2 : ℝ) ^ (n + 1) := by
              rw [pow_succ]
              ring
        · calc
            (bounds n).2 - ((bounds n).1 + (bounds n).2) / 2
                = ((bounds n).2 - (bounds n).1) / 2 := by ring
            _ = ((b - a) * (1 / 2 : ℝ) ^ n) / 2 := by rw [ih]
            _ = (b - a) * (1 / 2 : ℝ) ^ (n + 1) := by
              rw [pow_succ]
              ring
  have hlim : MySequences.TendsTo
    ⟨(fun n => (bounds n).2) - (fun n => (bounds n).1)⟩ 0 := by
    intro ε hε
    obtain ⟨N, hN⟩ :=
      exists_pow_lt_of_lt_one (div_pos hε (sub_pos.mpr hablt))
        (by norm_num : (1 / 2 : ℝ) < 1)
    use N
    intro n hn
    change dist ((bounds n).2 - (bounds n).1) 0 < ε
    rw [hwidth n, Real.dist_eq, sub_zero]
    rw [abs_of_nonneg
      (mul_nonneg
        (sub_nonneg.mpr (le_of_lt hablt))
        (by positivity))]
    have hp : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hn
    calc
      (b - a) * (1 / 2 : ℝ) ^ n
          ≤ (b - a) * (1 / 2 : ℝ) ^ N :=
        mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr (le_of_lt hablt))
      _ < ε := by
        have h := mul_lt_mul_of_pos_left hN (sub_pos.mpr hablt)
        have heq : (b - a) * (ε / (b - a)) = ε := by
          field_simp [sub_ne_zero.mpr (ne_of_gt hablt)]
        rw [heq] at h
        exact h
  let σ : ℕ → ℕ := fun n => Classical.choose (hInf n).nonempty
  have hσ : ∀ n, x (σ n) ∈ Set.Icc (bounds n).1 (bounds n).2 := by
    intro n
    exact Classical.choose_spec (hInf n).nonempty
  obtain ⟨c, hc, hcI⟩ := limit_of_nested_intervals
    (a := fun n => (bounds n).1)
    (b := fun n => (bounds n).2)
    (x := ⟨x ∘ σ⟩)
    hσ hnset hlim
  refine ⟨σ, ⟨c, ?_⟩, hc⟩
  simpa [hzero] using hcI 0
