import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

#check dist_triangle
#check norm_add_le

#check dist_add_add_le
theorem dist_ineq {a b c d : ℝ} : dist (a + b) (c + d) ≤ dist a c + dist b d := by
  repeat rw [Real.dist_eq]
  calc |a + b - (c + d)|
    _ = |a - c + (b - d)| := by
      congr; linarith
  exact norm_add_le (a - c) (b - d)

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ}
    (hx : TendsTo x a) (hy : TendsTo y b) :
    TendsTo ⟨fun n ↦ x n + y n⟩ (a + b) := by
  unfold TendsTo at *
  dsimp at *
  intro ε hε
  obtain ⟨xN, hxN⟩ := hx (ε/2) (by positivity)
  obtain ⟨yN, hyN⟩ := hy (ε/2) (by positivity)
  use max xN yN
  intro n hn
  calc dist (x.x n + y.x n) (a + b)
    _ ≤ dist (x.x n) a + dist (y.x n) b := dist_ineq
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_lt
      (hxN n <| by linarith [le_max_left xN yN, hn])
      (hyN n <| by linarith [le_max_right xN yN, hn])
    _ = ε := by norm_num

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : TendsTo x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  unfold TendsTo at hx
  by_contra! hc
  obtain ⟨N, hN⟩ := hx (a - b) (by positivity)
  have h₁ := hN (N+1) (by simp)
  have h₂ := h (N+1)
  rw [Real.dist_eq] at h₁
  apply sub_lt_of_abs_sub_lt_left at h₁
  linarith

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : TendsTo x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  unfold TendsTo at hx
  by_contra! hc
  obtain ⟨N, hN⟩ := hx (b - a) (by positivity)
  have h₁ := hN (N+1) (by simp)
  have h₂ := h (N+1)
  rw [Real.dist_eq] at h₁
  apply sub_lt_of_abs_sub_lt_right at h₁
  linarith

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
    (hf : ContinuousAt f a) (hg : ContinuousAt g (f a)) :
    ContinuousAt (g ∘ f) a := by
  unfold ContinuousAt at *
  intro ε hε
  obtain ⟨δg, hδg⟩ := hg ε hε
  obtain ⟨δf, hδf⟩ := hf δg hδg.1
  use δf
  refine ⟨hδf.1, ?_⟩
  intro y hy
  repeat rw [Function.comp_apply]
  exact hδg.2 (f y) <| hδf.2 y hy

#check Pi.add_apply
#check min_le_right

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (hg : ContinuousAt g a) :
    ContinuousAt (f + g) a := by
  unfold ContinuousAt at *
  intro ε hε
  obtain ⟨δg, hδg⟩ := hg (ε/2) <| by positivity
  obtain ⟨δf, hδf⟩ := hf (ε/2) <| by positivity
  use min δf δg
  refine ⟨by positivity [hδf.1, hδg.1], ?_⟩
  intro y hy
  repeat rw [Pi.add_apply]
  have h₁ := hδf.2 y <| by linarith [min_le_left δf δg, hy]
  have h₂ := hδg.2 y <| by linarith [min_le_right δf δg, hy]
  calc dist (f y + g y) (f a + g a)
    _ ≤ dist (f y) (f a) + dist (g y) (g a) := dist_ineq
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_lt h₁ h₂
    _ = ε := by norm_num

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

#check sSup {x : ℝ | x > 5}
#print axioms Real.exists_isLUB

noncomputable section
variable {S : Set ℝ} (hS : S.Nonempty) (hbdd : (upperBounds S).Nonempty)

structure SeqEntry : Type where
  l : ℝ
  u : ℝ
  hl : l ∈ S
  hu : u ∈ upperBounds S

def seq : ℕ → @SeqEntry S
| 0 => ⟨
  Classical.choose hS,
  Classical.choose hbdd,
  Classical.choose_spec hS,
  Classical.choose_spec hbdd⟩
| Nat.succ n =>
    let ⟨l, u, hl, hu⟩ := seq n
    let m := l + u / 2
    haveI : Decidable (m ∈ upperBounds S)
      := Classical.dec (m ∈ upperBounds S)
    if h : m ∈ upperBounds S
    then ⟨l, m, hl, h⟩
    else
      have h' : ∃(a : ℝ), a ∈ S ∧ m < a := by
        unfold upperBounds at h; dsimp at h
        push Not at h
        exact h
      ⟨Classical.choose h', u,
      (Classical.choose_spec h').1, hu⟩


abbrev seqL (n : ℕ) : ℝ := (seq hS hbdd n).l
abbrev seqU (n : ℕ) : ℝ := (seq hS hbdd n).u

def intervalOf : @SeqEntry S → Set ℝ
| SeqEntry.mk l u _ _ => Set.Icc l u

theorem elem_lt_ub : Classical.choose hS ≤ Classical.choose hbdd := by
  sorry

theorem incr {a : ℕ} : seqL hS hbdd a ≤ seqL hS hbdd (a+1) := by
  induction a with
  | zero =>
    unfold seqL seq
    dsimp
    by_cases! h : (seq hS hbdd 0).l + (seq hS hbdd 0).u / 2 ∈ upperBounds S
    · simp [h]; unfold seq; dsimp; rfl
    · simp only [if_neg h, h]
      unfold seq; dsimp
      have hc := Classical.choose_spec hS
      have hb := Classical.choose_spec hbdd
      unfold upperBounds at hb
      dsimp at hb
      sorry
  | succ p hp =>
    sorry


lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  sorry


/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
