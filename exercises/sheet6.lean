import LectureNotes.lecture7.examples7
set_option linter.style.longLine false
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
  have hx := hx (ε/2) (half_pos hε)
  have hy := hy (ε/2) (half_pos hε)
  rcases hx with ⟨N,hN⟩
  rcases hy with ⟨M,hM⟩
  use max N M
  intro n hn
  have hN := hN n (le_of_max_le_left hn)
  have hM := hM n (le_of_max_le_right hn)
  calc
     dist (x.x n + y.x n) (a + b) ≤ dist (x.x n) a + dist (y.x n) b := dist_add_add_le (x.x n) (y.x n) a b
     _ < ε/2 + ε/2 := by linarith
     _ = ε  := by ring
-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  contrapose! h
  have h1 : a - b > 0 := by linarith
  apply hx at h1
  rcases h1 with ⟨N,hN⟩
  use N
  have hN1 := Nat.le_refl N
  apply hN at hN1
  have hN : a - (x.x N) < a - b := by
    calc
      a - (x.x N) ≤ dist (x.x N) a := by
        simp only [dist, abs_sub_comm]
        exact le_abs_self (a - x.x N)
      _ < a - b := by linarith
  linarith

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  contrapose! h
  have h1 : b - a > 0 := by linarith
  apply hx at h1
  rcases h1 with ⟨N,hN⟩
  use N
  have hN1 := Nat.le_refl N
  apply hN at hN1
  have hN : (x.x N) - a < b - a := by
    calc
      (x.x N) - a ≤ dist (x.x N) a := Real.sub_le_dist (x.x N) a
      _ < b - a := by linarith
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
    (hf : continuousAt f a) (hg : continuousAt g (f a)) :
    continuousAt (g ∘ f) a := by
      intro ε hε
      have hg := hg ε hε
      rcases hg with ⟨δ1,hδ1⟩
      have hδ := hδ1.1
      apply hf at hδ
      rcases hδ with ⟨δ2,hδ2⟩
      use δ2
      constructor
      · exact hδ2.1
      intro y hy
      simp only [Function.comp_apply]
      apply hδ2.2 at hy
      exact hδ1.2 (f y) hy
/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  intro ε hε
  have hf := hf (ε/2) (half_pos hε)
  have hg := hg (ε/2) (half_pos hε)
  rcases hf with ⟨δ1,hδ1⟩
  rcases hg with ⟨δ2,hδ2⟩
  use min δ1 δ2
  constructor
  · exact lt_min hδ1.1 hδ2.1
  intro y hy
  have hy1 : dist y a < δ1 := by
    calc
      dist y a < min δ1 δ2 := hy
      _ ≤ δ1 := Std.min_le_left
  apply hδ1.2 at hy1
  have hy2 : dist y a < δ2 := by
    calc
      dist y a < min δ1 δ2 := hy
      _ ≤ δ2 := Std.min_le_right
  apply hδ2.2 at hy2
  simp only [Pi.add_apply, gt_iff_lt]
  calc
    dist (f y + g y) (f a + g a) ≤ dist (f y) (f a) + dist (g y) (g a) := dist_add_add_le (f y) (g y) (f a) (g a)
    _ < ε := by linarith

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

6) Use the two lemmas below to show that `a` satisfied the least-upper-bound property.
Hint: a is also the limit of the sequence `u`.

7) Prove the at least one of the lemmas below.
-/
noncomputable section
theorem exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
    classical
    apply Set.nonempty_def.mp at hS
    have hy : ∀ s ∉ upperBounds S, ∃ y ∈ S, y > s := by
      intro s hs
      apply Set.notMem_setOf_iff.mp at hs
      simp only [not_forall, not_le] at hs
      exact bex_def.mp hs
    choose y hy using hy
    rcases hS with ⟨l,hl⟩
    let rec sequences : ℕ → ℝ × ℝ × ℝ
    | 0 => ⟨u,l,(u+l)/2⟩
    | k + 1 =>
      if h : (sequences k).2.2 ∈ upperBounds S then
        ⟨(sequences k).2.2,(sequences k).2.1,((sequences k).2.2+(sequences k).2.1)/2⟩
      else
        ⟨(sequences k).1,y (sequences k).2.2 h,((sequences k).1+y (sequences k).2.2 h)/2⟩
    let f : (ℝ × ℝ × ℝ) → ℝ := fun x ↦ x.1
    let g : (ℝ × ℝ × ℝ) → ℝ := fun x ↦ x.2.1
    have h : ∀ (f : ℕ → ℝ), ∃ u : RealSeq, u = f := by
      exact fun f ↦ exists_apply_eq_apply RealSeq.x { x := f }
    choose h hh using h
    let u1 := h (f ∘ sequences)
    let l1 := h (g ∘ sequences)
    have hl1 : ∀ n, l1 n ∈ S := by
      intro n
      induction n with
      | zero =>
        simp only [hh, Function.comp_apply, l1, g]
        have h : sequences 0 = ⟨u,l,(u+l)/2⟩ := by
          sorry -- I couldn't figure out how to unpack the definition of sequences, sorry. I plan to look at the solution. I tried using dsimp but it failed.
        exact Set.mem_of_eq_of_mem (congrArg Prod.fst (congrArg Prod.snd h)) hl
      | succ => sorry
    sorry
end

/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
