import LectureNotes.lecture7.examples7
import Exercises.Sheet5
import Exercises.Sheet6

namespace MyFunctions

open MyFunctions MySequences Function


def TendsTo (f : ℝ → ℝ) (x : ℝ) (a : ℝ) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ y ≠ x, |y - x| < δ → |f y - a| < ε


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

/-- **Signature change**: added `hyx : ∀ n, y n ≠ x`, which is necessary
(see note above) and holds at both call sites. -/
lemma tends_to_of_fun_tends_to {f : ℝ → ℝ} {y : RealSeq} {x a : ℝ} (h : TendsTo f x a)
    (hy : MySequences.TendsTo y x) (hyx : ∀ n, y n ≠ x) :
    MySequences.TendsTo ⟨(fun n => f (y n))⟩ a := by
  intro ε hε
  obtain ⟨δ, hδ, h'⟩ := h ε hε
  obtain ⟨N, hN⟩ := hy δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hd : |y n - x| < δ := hN n hn
  exact h' (y n) (hyx n) hd

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
    refine ⟨δ, hδ, fun y hy hxy => ?_⟩
    simp only [Pi.sub_apply, const_apply, sub_zero, h' y hy hxy]
  intro h ε hε
  obtain ⟨δ, hδ, h'⟩ := h ε hε
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  specialize h' y hy hxy
  simp only [Pi.sub_apply, const_apply, sub_zero] at h'
  exact h'

/-- Uniqueness of function limits, proved the same way as
`tends_toReal_unique` in lecture 6: `eq_of_forall_dist_le`, plus a
triangle inequality — but here we don't have a sequence to plug in,
so we build one explicit witness point `y = x + δ/2`. -/
lemma tends_to_unique {f : ℝ → ℝ} {x a b : ℝ} (hx : TendsTo f x a) (hy : TendsTo f x b) :
    a = b := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨δ2, hδ2, h2⟩ := hy (ε / 2) (half_pos hε)
  set δ := min δ1 δ2 with hδdef
  have hδ : δ > 0 := lt_min hδ1 hδ2
  set y := x + δ / 2 with hydef
  have hyx : y ≠ x := by
    rw [hydef]; intro h; have : δ / 2 = 0 := by linarith
    linarith
  have hyabs : |y - x| = δ / 2 := by
    rw [hydef]
    have : x + δ / 2 - x = δ / 2 := by ring
    rw [this, abs_of_pos (by linarith)]
  have hy1 : |y - x| < δ1 := by
    rw [hyabs]; have := min_le_left δ1 δ2; linarith
  have hy2 : |y - x| < δ2 := by
    rw [hyabs]; have := min_le_right δ1 δ2; linarith
  have e1 := h1 y hyx hy1
  have e2 := h2 y hyx hy2
  calc dist a b ≤ dist a (f y) + dist (f y) b := dist_triangle a (f y) b
    _ = |a - f y| + |f y - b| := by rw [Real.dist_eq, Real.dist_eq]
    _ = |f y - a| + |f y - b| := by rw [abs_sub_comm a (f y)]
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := add_halves ε

lemma tends_to_add_tends_to (f g : ℝ → ℝ) (x a b : ℝ) :
    TendsTo f x a → TendsTo g x b → TendsTo (fun y => f y + g y) x (a + b) := by
  intro hf hg ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δ2, hδ2, h2⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy hxy => ?_⟩
  have hxy1 : |y - x| < δ1 := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy2 : |y - x| < δ2 := lt_of_lt_of_le hxy (min_le_right _ _)
  have e1 := h1 y hy hxy1
  have e2 := h2 y hy hxy2
  calc |f y + g y - (a + b)| = |(f y - a) + (g y - b)| := by ring_nf
    _ ≤ |f y - a| + |g y - b| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := add_halves ε

lemma tends_to_mul_tends_to (f g : ℝ → ℝ) (x a b : ℝ) :
    TendsTo f x a → TendsTo g x b → TendsTo (fun y => f y * g y) x (a * b) := by
  intro hf hg ε hε
  obtain ⟨δ0, hδ0, hg0⟩ := hg 1 (by norm_num)
  set M := |b| + 1 with hMdef
  have hMpos : (0:ℝ) < M := by positivity
  have hApos : (0:ℝ) < |a| + 1 := by positivity
  obtain ⟨δ1, hδ1, hf1⟩ := hf (ε / (2 * M)) (by positivity)
  obtain ⟨δ2, hδ2, hg1⟩ := hg (ε / (2 * (|a| + 1))) (by positivity)
  refine ⟨min δ0 (min δ1 δ2), lt_min hδ0 (lt_min hδ1 hδ2), fun y hy hxy => ?_⟩
  have hxy0 : |y - x| < δ0 := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy12 : |y - x| < min δ1 δ2 := lt_of_lt_of_le hxy (min_le_right _ _)
  have hxy1 : |y - x| < δ1 := lt_of_lt_of_le hxy12 (min_le_left _ _)
  have hxy2 : |y - x| < δ2 := lt_of_lt_of_le hxy12 (min_le_right _ _)
  have hgbound : |g y| ≤ M := by
    have hb := hg0 y hy hxy0
    have heq : |g y| = |(g y - b) + b| := by ring_nf
    rw [heq]
    calc |(g y - b) + b| ≤ |g y - b| + |b| := abs_add _ _
      _ < 1 + |b| := by linarith
      _ = M := by rw [hMdef]; ring
  have e1 : |f y - a| < ε / (2 * M) := hf1 y hy hxy1
  have e2 : |g y - b| < ε / (2 * (|a| + 1)) := hg1 y hy hxy2
  have key : f y * g y - a * b = (f y - a) * g y + a * (g y - b) := by ring
  have t1 : |f y - a| * |g y| < (ε / (2 * M)) * M := by
    calc |f y - a| * |g y| ≤ |f y - a| * M :=
          mul_le_mul_of_nonneg_left hgbound (abs_nonneg _)
      _ < (ε / (2 * M)) * M := mul_lt_mul_of_pos_right e1 hMpos
  have t2 : |a| * |g y - b| < (|a| + 1) * (ε / (2 * (|a| + 1))) := by
    calc |a| * |g y - b| ≤ (|a| + 1) * |g y - b| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (|a| + 1) * (ε / (2 * (|a| + 1))) := mul_lt_mul_of_pos_left e2 hApos
  have c1 : (ε / (2 * M)) * M = ε / 2 := by field_simp
  have c2 : (|a| + 1) * (ε / (2 * (|a| + 1))) = ε / 2 := by field_simp
  calc |f y * g y - a * b| = |(f y - a) * g y + a * (g y - b)| := by rw [key]
    _ ≤ |(f y - a) * g y| + |a * (g y - b)| := abs_add _ _
    _ = |f y - a| * |g y| + |a| * |g y - b| := by rw [abs_mul, abs_mul]
    _ < (ε / (2 * M)) * M + (|a| + 1) * (ε / (2 * (|a| + 1))) := add_lt_add t1 t2
    _ = ε / 2 + ε / 2 := by rw [c1, c2]
    _ = ε := add_halves ε

/-
Derivative of a function `f : ℝ → ℝ` at a point `x`.
-/
def HasDerivAt (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
  TendsTo (fun y => (f y - f x) / (y - x)) x f'

lemma deriv_unique {f : ℝ → ℝ} {x : ℝ} {f' f'' : ℝ}
    (hf' : HasDerivAt f f' x) (hf'' : HasDerivAt f f'' x) : f' = f'' :=
  tends_to_unique hf' hf''

def HasDeriv (f : ℝ → ℝ) (f' : ℝ → ℝ) : Prop :=
    ∀ x, HasDerivAt f (f' x) x

open scoped Classical in
noncomputable def deriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ f', HasDerivAt f f' x
    then Classical.choose h
  else 0

lemma deriv_eq_of_has_deriv (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) (hf : HasDerivAt f f' x) :
     f' = deriv f x := by
  unfold deriv
  have hex: ∃ f', HasDerivAt f f' x := ⟨f', hf⟩
  simp only [hex, ↓reduceDIte]
  apply deriv_unique (hf) (Classical.choose_spec hex)

lemma deriv_of_has_deriv {f : ℝ → ℝ} {f' : ℝ → ℝ} (hf : HasDeriv f f') :
    f' = deriv f := by
  ext x
  apply deriv_eq_of_has_deriv f (f' x) x
  exact hf x

def Differentiable (f : ℝ → ℝ) : Prop :=
  ∃ f', HasDeriv f f'

lemma has_deriv_of_differentiable {f : ℝ → ℝ} (hf : Differentiable f) :
    HasDeriv f (deriv f) := by
    obtain ⟨f', hf'⟩ := hf
    rw[← deriv_of_has_deriv hf']
    exact hf'

lemma continuous_of_differentiable {f : ℝ → ℝ} (hf : Differentiable f) :
    ContinuousOn f := by
    obtain ⟨f', hf'⟩ := hf
    intro x
    rw[continuous_at_iff_tends_to, tends_to_of_sub]
    have h (g : ℝ → ℝ) (hg : g x = 0): g = (fun y => g y / (y - x)) * fun y => y - x := by
        ext y
        by_cases h : y = x
        · simp only [h, hg, Pi.mul_apply, sub_self, div_zero, mul_zero]
        simp only [Pi.mul_apply]
        field_simp
    rw[h (f - const _ (f x)) (sub_self (f x)), ← mul_zero (f' x)]
    refine tends_to_mul_tends_to (fun y => (f y - f x) / (y - x)) (fun y => y - x) x
        (f' x) 0 (hf' x) ?_
    exact fun ε hε => ⟨ε, hε, fun y hy hxy => by simp only [sub_zero, hxy]⟩

lemma deriv_add {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f + g) (deriv f + deriv g) := by
  intro x
  have hf' := has_deriv_of_differentiable hf x
  have hg' := has_deriv_of_differentiable hg x
  have hsum := tends_to_add_tends_to _ _ x _ _ hf' hg'
  have heq : (fun y => ((f + g) y - (f + g) x) / (y - x))
      = fun y => (f y - f x) / (y - x) + (g y - g x) / (y - x) := by
    ext y
    by_cases hxy : y = x
    · simp [hxy]
    · rw [Pi.add_apply, Pi.add_apply]
      field_simp
      ring
  show TendsTo (fun y => ((f + g) y - (f + g) x) / (y - x)) x (deriv f x + deriv g x)
  rw [heq]
  simpa [Pi.add_apply] using hsum

lemma deriv_mul {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f * g) (deriv f * g  + f  * deriv g ) := by
  intro x
  have hf' := has_deriv_of_differentiable hf x
  have hg' := has_deriv_of_differentiable hg x
  have hgcont : TendsTo g x (g x) :=
    continuous_at_iff_tends_to.mp (continuous_of_differentiable hg x)
  have hstep : TendsTo
      (fun y => (f y - f x) / (y - x) * g y + f x * ((g y - g x) / (y - x))) x
      (deriv f x * g x + f x * deriv g x) :=
    tends_to_add_tends_to _ _ x _ _
      (tends_to_mul_tends_to _ _ x _ _ hf' hgcont)
      (tends_to_mul_tends_to (const _ (f x)) (fun y => (g y - g x) / (y - x)) x
        (f x) (deriv g x) (tends_to_const (f x) x) hg')
  have heq : (fun y => ((f * g) y - (f * g) x) / (y - x))
      = fun y => (f y - f x) / (y - x) * g y + f x * ((g y - g x) / (y - x)) := by
    ext y
    by_cases hxy : y = x
    · simp [hxy]
    · simp only [Pi.mul_apply]
      field_simp
      ring
  show TendsTo (fun y => ((f * g) y - (f * g) x) / (y - x)) x
      (deriv f x * g x + f x * deriv g x)
  rw [heq]
  simpa [Pi.add_apply, Pi.mul_apply] using hstep

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

#check Set.Ioo _ _
#check Set.Icc _ _
#check Set.Ico _ _
#check IsMaxOn

theorem deriv_at_max_zero {f : ℝ → ℝ} {x ε : ℝ} (hε : ε > 0)
    (hf : IsMaxOn f (Set.Ioo (x - ε) (x + ε)) x) : deriv f x = 0 := by
  by_cases h : ∃ f' , HasDerivAt f f' x
  · obtain ⟨f', hf'⟩ := h
    obtain ⟨n, hn, hnle⟩ := nat_one_div_le hε
    have hlt : ∀ m : ℕ, ((↑n + ↑m + 1)⁻¹ : ℝ) < 1/n :=
            fun m => (by exact (lt_one_div (by positivity) (by positivity)).mp (by simp; linarith))
    let yu : ℕ → ℝ := fun m => x + 1 / (n + m + 1 : ℝ)
    have hyu_ne : ∀ m, yu m ≠ x := fun m h => by
      simp only [yu] at h
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + m + 1) := by positivity
      linarith
    have hyu : MySequences.TendsTo ⟨yu⟩ x := by
      intro ε' hε'
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε')
      refine ⟨N, fun m hm => ?_⟩
      have hpos : (0:ℝ) < (n:ℝ) + m + 1 := by positivity
      have hNm : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hge : (N:ℝ) ≤ (n:ℝ) + m + 1 := by linarith [Nat.cast_nonneg n]
      have hgt : (1 / ε' : ℝ) < (n:ℝ) + m + 1 := lt_of_lt_of_le hN hge
      have hlt' : (1:ℝ) / ((n:ℝ) + m + 1) < ε' := by
        rw [div_lt_iff hpos]
        rw [div_lt_iff hε', mul_comm] at hgt
        linarith
      show dist (yu m) x < ε'
      simp only [yu, Real.dist_eq]
      have heq : x + 1 / ((n:ℝ) + m + 1) - x = 1 / ((n:ℝ) + m + 1) := by ring
      rw [heq, abs_of_pos (by positivity)]
      exact hlt'
    let yl : ℕ → ℝ := fun m => x - 1 / (n + m + 1 : ℝ)
    have hyl_ne : ∀ m, yl m ≠ x := fun m h => by
      simp only [yl] at h
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + m + 1) := by positivity
      linarith
    have hyl : MySequences.TendsTo ⟨yl⟩ x := by
      intro ε' hε'
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε')
      refine ⟨N, fun m hm => ?_⟩
      have hpos : (0:ℝ) < (n:ℝ) + m + 1 := by positivity
      have hNm : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hge : (N:ℝ) ≤ (n:ℝ) + m + 1 := by linarith [Nat.cast_nonneg n]
      have hgt : (1 / ε' : ℝ) < (n:ℝ) + m + 1 := lt_of_lt_of_le hN hge
      have hlt' : (1:ℝ) / ((n:ℝ) + m + 1) < ε' := by
        rw [div_lt_iff hpos]
        rw [div_lt_iff hε', mul_comm] at hgt
        linarith
      show dist (yl m) x < ε'
      simp only [yl, Real.dist_eq]
      have heq : x - 1 / ((n:ℝ) + m + 1) - x = -(1 / ((n:ℝ) + m + 1)) := by ring
      rw [heq, abs_neg, abs_of_pos (by positivity)]
      exact hlt'
    have hf'u : f' ≤ 0 := by
        apply tends_to_le_of_le (tends_to_of_fun_tends_to hf' hyu hyu_ne)
        intro m
        apply div_nonpos_of_nonpos_of_nonneg
        · simp only [sub_nonpos]
          refine le_of_eq_of_le rfl (hf ?_)
          simp only [one_div, Set.mem_Ioo, add_lt_add_iff_left, yu]
          exact ⟨lt_add_of_le_of_pos (by linarith) (by positivity), by linarith [hlt m]⟩
        simp only [one_div, add_sub_cancel_left, inv_nonneg, yu]
        linarith
    have hf'l : f' ≥ 0 := by
        apply tends_to_ge_of_ge (tends_to_of_fun_tends_to hf' hyl hyl_ne)
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
    rw[← deriv_eq_of_has_deriv f f' x hf']
    linarith
  simp only [deriv, h, ↓reduceDIte]


end MyFunctions
