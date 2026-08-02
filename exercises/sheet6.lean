import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ}
    (hx : tends_to x a) (hy : tends_to y b) :
    tends_to ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 2) (by positivity)
  obtain ⟨Ny, hNy⟩ := hy (ε / 2) (by positivity)
  use max Nx Ny
  intro n hn
  calc dist (x n + y n) (a + b) ≤ dist (x n) a + dist (y n) b := dist_add_add_le _ _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hNx n (le_of_max_le_left hn)) (hNy n (le_of_max_le_right hn))
    _ = ε := by exact add_halves ε

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  obtain ⟨N, hN⟩ := hx (a - b) (by linarith)
  have h1 := hN N le_rfl
  have h2 := h N
  rw[Real.dist_eq, abs_lt] at h1 -- a - b > a - x.x N false since b ≥ x.x N
  linarith

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hab
  rw [not_le] at hab
  obtain ⟨N, hN⟩ := hx (b - a) (by linarith)
  have h1 := hN N le_rfl
  have h2 := h N
  rw[Real.dist_eq, abs_lt] at h1
  linarith
-- this is word for word with the previous one lol (except b - a)

end MySequences

/-!
## Exercise 1: continuous functions
-/
namespace MyFunctions

/-
Use `continuousAt_iff_seqContinuousAt` for the exercise.
You may find `Function.comp_apply` useful when simplifying compositions.
-/
lemma continuous_comp_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g (f a)) :
    continuousAt (g ∘ f) a := by
  intro ε hε
  obtain ⟨δ, hδ, hg⟩ := hg ε hε
  obtain ⟨δ', hδ', hf⟩ := hf δ hδ
  /-  Take x : ℝ st |x - a| < δ' → |f(x) - f(a)| < δ (by hf)
      We can use f(x) in hg since |f(x) - f(a)| < δ, this gives |g(f(x)) - g(f(a))| < ε
      Use δ' on goal. |x - a| < δ' → |g(f(x)) - g(f(a))| < ε  -/
  use δ'
  refine ⟨hδ', ?_⟩
  intro x hx
  exact hg (f x) (hf x hx)

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  intro ε hε
  obtain ⟨δ, hδ, hg⟩ := hg (ε / 2) (by linarith)
  obtain ⟨δ', hδ', hf⟩ := hf (ε / 2) (by linarith)
  use (min δ δ')
  refine ⟨lt_min hδ hδ', ?_⟩
  intro x hx
  obtain hgx := hg x (lt_inf_iff.mp hx).1
  obtain hfx := hf x (lt_inf_iff.mp hx).2
  have hsum : dist (f x) (f a) + dist (g x) (g a) < ε := by linarith [add_lt_add hfx hgx]
  simp only [Pi.add_apply, Real.dist_eq, add_sub_add_comm]
  rw [Real.dist_eq, Real.dist_eq] at hsum -- interestingly, repeat rw at hsum doesnt work
  exact lt_of_le_of_lt (abs_add_le _ _) hsum

end MyFunctions

/-!
## Exercise 2: the least-upper-bound property
-/

/-
Do not use `sSup`, `le_csSup`, or `csSup_le` in this exercise. The aim is to
derive the least-upper-bound property from Cauchy completeness.

Use a bisection construction:

1) Choose `l₀ ∈ S` using `hS`, and choose an upper bound `u₀` using `hbdd`.
   Thus `l₀ ≤ u₀`.

2) Recursively bisect the interval `[lₙ, uₙ]`. Let
   `mₙ = (lₙ + uₙ) / 2`.

   * If `mₙ ∈ upperBounds S`, set `lₙ₊₁ = lₙ` and `uₙ₊₁ = mₙ`.
   * Otherwise, there is some `y ∈ S` with `mₙ < y`. Choose such a `y`,
     set `lₙ₊₁ = y`, and keep `uₙ₊₁ = uₙ`.

   You'll need `classical` to make these choices.

3) Prove by induction that:

   * `lₙ ∈ S`;
   * `uₙ ∈ upperBounds S`;
   * the intervals are nested; and
   * `uₙ - lₙ ≤ (u₀ - l₀) / 2^n`.

4) Deduce that `⟨l⟩ : RealSeq` is Cauchy. For sufficiently large `N`,
   every `lₙ` with `n ≥ N` lies in `[l_N, u_N]`, whose length tends to
   zero. The lemmas `exists_pow_lt_of_lt_one` and `one_half_lt_one` may
   help with the powers of `1 / 2`.

5) Apply `MySequences.real_numbers_complete` from last time to obtain a real number `a` to which
   `l` converges. This `a` will be the supremum; do not identify it with
   the library term `sSup S`.

6) Use the two lemmas above about limits to show that `a` satisfied the least-upper-bound property.
Hint: a is also the limit of the sequence `u`.

7) Prove the at least one of the lemmas about limits above.
-/

/-
i spent a few hours on this but i couldn't figure it out ;-;

variable (S : Set ℝ) (l₀ u₀ : ℝ)

section Bisection
variable (hl₀ : l₀ ∈ S) (hu₀ : u₀ ∈ upperBounds S)
include hl₀ hu₀

attribute [local instance] Classical.propDecidable
noncomputable def bisect :
    ℕ → {p : ℝ × ℝ // p.1 ∈ S ∧ p.2 ∈ upperBounds S}
  | 0 => ⟨(l₀, u₀), hl₀, hu₀⟩
  | n + 1 =>
    let prev := bisect n
    let m := (prev.1.1 + prev.1.2) / 2
    if h : m ∈ upperBounds S then
      ⟨(prev.1.1, m), prev.2.1, h⟩
    else
      have hex : ∃ x ∈ S, m < x := by
        rw [mem_upperBounds] at h
        push Not at h
        exact h
      ⟨(Classical.choose hex, prev.1.2), (Classical.choose_spec hex).1, prev.2.2⟩

noncomputable def l (n : ℕ) : ℝ := (bisect S l₀ u₀ hl₀ hu₀ n).1.1
noncomputable def u (n : ℕ) : ℝ := (bisect S l₀ u₀ hl₀ hu₀ n).1.2

local notation "L" => l S l₀ u₀ hl₀ hu₀
local notation "U" => u S l₀ u₀ hl₀ hu₀

lemma l_mem (n : ℕ) : L n ∈ S := (bisect S l₀ u₀ hl₀ hu₀ n).2.1
lemma u_mem (n : ℕ) : U n ∈ upperBounds S := (bisect S l₀ u₀ hl₀ hu₀ n).2.2

lemma L_succ_pos (n) (h : (L n + U n) / 2 ∈ upperBounds S) : L (n+1) = L n := by
  simp only [l, u] at h
  rw [l, bisect, dif_pos h]
  rfl

lemma L_succ_neg (n) (h : (L n + U n) / 2 ∉ upperBounds S) :
    (L n + U n) / 2 < L (n + 1) ∧ U (n + 1) = U n := by
  simp only [l, u] at h ⊢
  constructor
  · sorry
  · sorry

lemma l_inc (n : ℕ) : L n ≤ L (n + 1) := by
  by_cases h : (L n + U n) / 2 ∈ upperBounds S
  · have h_succ := L_succ_pos S l₀ u₀ hl₀ hu₀ n h
    exact le_of_eq (Eq.symm h_succ)
  · have hex : ∃ x ∈ S, (L n + U n) / 2 < x := by
        rw [mem_upperBounds] at h
        push Not at h
        exact h
    have lt_wit : (L n + U n) / 2 < Classical.choose hex := by
      exact (Classical.choose_spec hex).2
    sorry

lemma u_dec (n : ℕ) : U (n + 1) ≤ U n := sorry

end Bisection
-/

-- this is claude's code, not mine :(
variable (S : Set ℝ) (l₀ u₀ : ℝ)

attribute [local instance] Classical.propDecidable

section Bisection

lemma exists_gt_of_not_mem_upperBounds {m : ℝ} (h : m ∉ upperBounds S) :
    ∃ x ∈ S, m < x := by
  rw [mem_upperBounds] at h
  push Not at h
  exact h

noncomputable def step (p : {q : ℝ × ℝ // q.1 ∈ S ∧ q.2 ∈ upperBounds S}) :
    {q : ℝ × ℝ // q.1 ∈ S ∧ q.2 ∈ upperBounds S} :=
  if h : (p.1.1 + p.1.2) / 2 ∈ upperBounds S then
    ⟨(p.1.1, (p.1.1 + p.1.2) / 2), p.2.1, h⟩
  else
    ⟨(Classical.choose (exists_gt_of_not_mem_upperBounds S h), p.1.2),
      (Classical.choose_spec (exists_gt_of_not_mem_upperBounds S h)).1, p.2.2⟩

variable {S}

lemma step_fst_of_pos {p} (h : (p.1.1 + p.1.2) / 2 ∈ upperBounds S) :
    (step S p).1.1 = p.1.1 := by
  simp only [step]; rw [dif_pos h]

lemma step_snd_of_pos {p} (h : (p.1.1 + p.1.2) / 2 ∈ upperBounds S) :
    (step S p).1.2 = (p.1.1 + p.1.2) / 2 := by
  simp only [step]; rw [dif_pos h]

lemma lt_step_fst_of_neg {p} (h : (p.1.1 + p.1.2) / 2 ∉ upperBounds S) :
    (p.1.1 + p.1.2) / 2 < (step S p).1.1 := by
  simp only [step]; rw [dif_neg h]
  exact (Classical.choose_spec (exists_gt_of_not_mem_upperBounds S h)).2

lemma step_snd_of_neg {p} (h : (p.1.1 + p.1.2) / 2 ∉ upperBounds S) :
    (step S p).1.2 = p.1.2 := by
  simp only [step]; rw [dif_neg h]

variable (S)

variable (hl₀ : l₀ ∈ S) (hu₀ : u₀ ∈ upperBounds S)
include hl₀ hu₀

noncomputable def bisect :
    ℕ → {q : ℝ × ℝ // q.1 ∈ S ∧ q.2 ∈ upperBounds S}
  | 0 => ⟨(l₀, u₀), hl₀, hu₀⟩
  | n + 1 => step S (bisect n)

noncomputable def l (n : ℕ) : ℝ := (bisect S l₀ u₀ hl₀ hu₀ n).1.1
noncomputable def u (n : ℕ) : ℝ := (bisect S l₀ u₀ hl₀ hu₀ n).1.2

local notation "L" => l S l₀ u₀ hl₀ hu₀
local notation "U" => u S l₀ u₀ hl₀ hu₀

lemma l_mem (n : ℕ) : L n ∈ S := (bisect S l₀ u₀ hl₀ hu₀ n).2.1
lemma u_mem (n : ℕ) : U n ∈ upperBounds S := (bisect S l₀ u₀ hl₀ hu₀ n).2.2

lemma l_le_u (n : ℕ) : L n ≤ U n :=
  u_mem S l₀ u₀ hl₀ hu₀ n (l_mem S l₀ u₀ hl₀ hu₀ n)

lemma L_succ_of_pos (n) (h : (L n + U n) / 2 ∈ upperBounds S) : L (n+1) = L n := by
  simp only [l, u] at h ⊢; exact step_fst_of_pos h

lemma U_succ_of_pos (n) (h : (L n + U n) / 2 ∈ upperBounds S) :
    U (n+1) = (L n + U n) / 2 := by
  simp only [l, u] at h ⊢; exact step_snd_of_pos h

lemma L_succ_of_neg (n) (h : (L n + U n) / 2 ∉ upperBounds S) :
    (L n + U n) / 2 < L (n+1) := by
  simp only [l, u] at h ⊢; exact lt_step_fst_of_neg h

lemma U_succ_of_neg (n) (h : (L n + U n) / 2 ∉ upperBounds S) : U (n+1) = U n := by
  simp only [l, u] at h ⊢; exact step_snd_of_neg h

lemma L_le_succ (n : ℕ) : L n ≤ L (n+1) := by
  by_cases h : (L n + U n) / 2 ∈ upperBounds S
  · exact (L_succ_of_pos S l₀ u₀ hl₀ hu₀ n h).ge
  · have h1 := L_succ_of_neg S l₀ u₀ hl₀ hu₀ n h
    have h2 := l_le_u S l₀ u₀ hl₀ hu₀ n
    linarith

lemma U_succ_le (n : ℕ) : U (n+1) ≤ U n := by
  by_cases h : (L n + U n) / 2 ∈ upperBounds S
  · rw [U_succ_of_pos S l₀ u₀ hl₀ hu₀ n h]
    have := l_le_u S l₀ u₀ hl₀ hu₀ n
    linarith
  · exact (U_succ_of_neg S l₀ u₀ hl₀ hu₀ n h).le

lemma L_mono : Monotone L := monotone_nat_of_le_succ (L_le_succ S l₀ u₀ hl₀ hu₀)
lemma U_anti : Antitone U := antitone_nat_of_succ_le (U_succ_le S l₀ u₀ hl₀ hu₀)

lemma width_succ (n : ℕ) : U (n+1) - L (n+1) ≤ (U n - L n) / 2 := by
  by_cases h : (L n + U n) / 2 ∈ upperBounds S
  · rw [U_succ_of_pos S l₀ u₀ hl₀ hu₀ n h, L_succ_of_pos S l₀ u₀ hl₀ hu₀ n h]
    linarith
  · rw [U_succ_of_neg S l₀ u₀ hl₀ hu₀ n h]
    have := L_succ_of_neg S l₀ u₀ hl₀ hu₀ n h
    linarith

lemma width_le (n : ℕ) : U n - L n ≤ (u₀ - l₀) / 2 ^ n := by
  induction n with
  | zero => norm_num [l, u, bisect]
  | succ n ih =>
    have hstep := width_succ S l₀ u₀ hl₀ hu₀ n
    have hpow : (u₀ - l₀) / 2 ^ (n+1) = ((u₀ - l₀) / 2 ^ n) / 2 := by
      rw [pow_succ]; ring
    rw [hpow]
    linarith

lemma width_lt_ε : ∀ ε > 0, ∃ N, (u₀ - l₀) / 2^N < ε := by
  intro ε hε
  by_cases h : u₀ - l₀ = 0
  · simp only [h, zero_div, exists_const]; linarith
  · have diff_pos : u₀ - l₀ > 0 := by
        exact sub_pos.mpr (lt_of_le_of_ne (hu₀ hl₀) (Ne.symm (sub_ne_zero.mp h)))
    have pow_lt : ∃ N : ℕ, (1/2) ^ N < ε/(u₀ - l₀) := by
      exact exists_pow_lt_of_lt_one (div_pos hε diff_pos) (by linarith)
    obtain ⟨N, hN⟩ := pow_lt
    use N
    rw [div_eq_mul_inv, ← one_div, ← one_div_pow]
    calc (u₀ - l₀) * (1 / 2) ^ N
      < (u₀ - l₀) * (ε / (u₀ - l₀)) := (mul_lt_mul_iff_of_pos_left diff_pos).mpr hN
      _ = ε := by exact mul_div_cancel₀ ε h

lemma L_cauchy : isCauchyReal ⟨L⟩ := by
  -- L n, L m both in [L N, U N]
  -- width of [L N, U N] ≤ ((u₀ - l₀) / 2 ^ n)
  -- ∃ N st ((u₀ - l₀) / 2 ^ N) < ε
  -- use that N, dist (L m) (L n) ≤ U N - L N ≤ ((u₀ - l₀) / 2 ^ N) < ε
  intro ε hε
  obtain ⟨N, hN⟩ := width_lt_ε S l₀ u₀ hl₀ hu₀ ε hε
  use N
  intro m hm n hn
  have h1 : L N ≤ L m := L_mono S l₀ u₀ hl₀ hu₀ hm
  have h2 : L N ≤ L n := L_mono S l₀ u₀ hl₀ hu₀ hn
  have h3 : L m ≤ U N := u_mem S l₀ u₀ hl₀ hu₀ N (l_mem S l₀ u₀ hl₀ hu₀ m)
  have h4 : L n ≤ U N := u_mem S l₀ u₀ hl₀ hu₀ N (l_mem S l₀ u₀ hl₀ hu₀ n)
  calc dist (L m) (L n) ≤ U N - L N := ?_
    _ ≤ (u₀ - l₀) / 2 ^ N := width_le S l₀ u₀ hl₀ hu₀ N
    _ < ε := hN
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith

lemma gap_tends_to_zero : tends_to ⟨fun n => U n - L n⟩ 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := width_lt_ε S l₀ u₀ hl₀ hu₀ ε hε
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sub_nonneg.mpr (l_le_u S l₀ u₀ hl₀ hu₀ n))]
  have h1 : U n ≤ U N := U_anti S l₀ u₀ hl₀ hu₀ hn
  have h2 : L N ≤ L n := L_mono S l₀ u₀ hl₀ hu₀ hn
  have h3 : U N - L N ≤ (u₀ - l₀) / 2 ^ N := width_le S l₀ u₀ hl₀ hu₀ N
  linarith

end Bisection

#check MySequences.real_numbers_complete
#check tends_to_le_of_le
#check tends_to_ge_of_ge

lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  choose l₀ hl₀ using hS
  obtain ⟨u₀, hu₀⟩ := u
  obtain ⟨a, ha⟩ := real_numbers_complete (L_cauchy S l₀ u₀ hl₀ hu₀)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · have hU : tends_to ⟨u S l₀ u₀ hl₀ hu₀⟩ a := by
      simpa using tends_to_add ha (gap_tends_to_zero S l₀ u₀ hl₀ hu₀)
    intro b hb
    -- All members of U are upper bounds of S → ∀ n, U n ≥ b
    -- By tends_to_ge_of_ge, this implies a ≥ b
    exact tends_to_ge_of_ge hU (fun n => u_mem S l₀ u₀ hl₀ hu₀ n hb)
  · intro b
    -- All members of L are members of S → ∀ n, L n ≤ b
    -- By tends_to_le_of_le, this implies a ≤ b
    exact tends_to_le_of_le ha (fun n => b.2 (l_mem S l₀ u₀ hl₀ hu₀ n))

-- ts was six hours of coding and countless hints from claude

/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
