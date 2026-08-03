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
  obtain ⟨N₁, hN₁⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hy (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have h1 : dist (x n) a < ε / 2 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  have h2 : dist (y n) b < ε / 2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
  show dist (x n + y n) (a + b) < ε
  calc dist (x n + y n) (a + b) ≤ dist (x n) a + dist (y n) b := dist_add_add_le _ _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra hcon
  have hba : b < a := not_le.mp hcon
  obtain ⟨N, hN⟩ := hx (a - b) (by linarith)
  have h1 : dist (x N) a < a - b := hN N (le_refl N)
  have h2 : x N ≤ b := h N
  rw [Real.dist_eq, abs_lt] at h1
  linarith [h1.1]

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hcon
  have hab : a < b := not_le.mp hcon
  obtain ⟨N, hN⟩ := hx (b - a) (by linarith)
  have h1 : dist (x N) a < b - a := hN N (le_refl N)
  have h2 : x N ≥ b := h N
  rw [Real.dist_eq, abs_lt] at h1
  linarith [h1.2]

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
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  have h1 : tends_to ⟨fun n ↦ f (x n)⟩ (f a) := hf x hx
  have h2 : tends_to ⟨fun n ↦ g (f (x n))⟩ (g (f a)) := hg ⟨fun n ↦ f (x n)⟩ h1
  simpa only [Function.comp_apply] using h2

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  have h1 : tends_to ⟨fun n ↦ f (x n)⟩ (f a) := hf x hx
  have h2 : tends_to ⟨fun n ↦ g (x n)⟩ (g a) := hg x hx
  simpa only [Pi.add_apply] using tends_to_add h1 h2

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

lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  classical
  -- Step 1: a starting interval `[l₀, u₀]`.
  obtain ⟨l₀, hl₀⟩ := hS
  obtain ⟨u₀, hu₀⟩ := u
  have hl₀u₀ : l₀ ≤ u₀ := hu₀ hl₀
  -- Step 2: choose a point of `S` above any real number that fails to be an upper bound.
  have hex : ∀ m : ℝ, ∃ y : ℝ, m ∉ upperBounds S → y ∈ S ∧ m < y := by
    intro m
    by_cases hm : m ∈ upperBounds S
    · exact ⟨l₀, fun h ↦ absurd hm h⟩
    have hy : ∃ y, y ∈ S ∧ m < y := by
      by_contra hcon
      push Not at hcon
      exact hm fun y hy ↦ hcon y hy
    obtain ⟨y, hy⟩ := hy
    exact ⟨y, fun _ ↦ hy⟩
  choose nxt hnxt using hex
  -- the bisection step, sending an interval `(l, u)` to the next one
  obtain ⟨F, hF⟩ : ∃ F : ℝ × ℝ → ℝ × ℝ, ∀ p : ℝ × ℝ, F p =
      if ((p.1 + p.2) / 2) ∈ upperBounds S then (p.1, (p.1 + p.2) / 2)
      else (nxt ((p.1 + p.2) / 2), p.2) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨P, hP0, hPs⟩ : ∃ P : ℕ → ℝ × ℝ, P 0 = (l₀, u₀) ∧ ∀ n, P (n + 1) = F (P n) :=
    ⟨fun n ↦ Nat.rec (l₀, u₀) (fun _ p ↦ F p) n, rfl, fun _ ↦ rfl⟩
  -- a single step keeps the invariants and at least halves the length
  have hFstep : ∀ p : ℝ × ℝ, p.1 ∈ S → p.2 ∈ upperBounds S → p.1 ≤ p.2 →
      (F p).1 ∈ S ∧ (F p).2 ∈ upperBounds S ∧ (F p).1 ≤ (F p).2 ∧ p.1 ≤ (F p).1 ∧
        (F p).2 ≤ p.2 ∧ (F p).2 - (F p).1 ≤ (p.2 - p.1) / 2 := by
    intro p h1 h2 h3
    rw [hF]
    split_ifs with hm
    · refine ⟨h1, hm, ?_, ?_, ?_, ?_⟩
      · show p.1 ≤ (p.1 + p.2) / 2
        linarith
      · show p.1 ≤ p.1
        linarith
      · show (p.1 + p.2) / 2 ≤ p.2
        linarith
      · show (p.1 + p.2) / 2 - p.1 ≤ (p.2 - p.1) / 2
        linarith
    · obtain ⟨hy1, hy2⟩ := hnxt _ hm
      refine ⟨hy1, h2, ?_, ?_, ?_, ?_⟩
      · show nxt ((p.1 + p.2) / 2) ≤ p.2
        exact h2 hy1
      · show p.1 ≤ nxt ((p.1 + p.2) / 2)
        linarith
      · show p.2 ≤ p.2
        linarith
      · show p.2 - nxt ((p.1 + p.2) / 2) ≤ (p.2 - p.1) / 2
        linarith
  -- Step 3: the invariants, by induction
  have hQ : ∀ n, (P n).1 ∈ S ∧ (P n).2 ∈ upperBounds S ∧ (P n).1 ≤ (P n).2 := by
    intro n
    induction n with
    | zero => rw [hP0]; exact ⟨hl₀, hu₀, hl₀u₀⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨a1, a2, a3, -, -, -⟩ := hFstep (P n) h1 h2 h3
      rw [hPs n]
      exact ⟨a1, a2, a3⟩
  have hmono : ∀ n, (P n).1 ≤ (P (n + 1)).1 ∧ (P (n + 1)).2 ≤ (P n).2 ∧
      (P (n + 1)).2 - (P (n + 1)).1 ≤ ((P n).2 - (P n).1) / 2 := by
    intro n
    obtain ⟨h1, h2, h3⟩ := hQ n
    obtain ⟨-, -, -, b1, b2, b3⟩ := hFstep (P n) h1 h2 h3
    rw [hPs n]
    exact ⟨b1, b2, b3⟩
  have hLmono : Monotone fun n ↦ (P n).1 := monotone_nat_of_le_succ fun n ↦ (hmono n).1
  have hUanti : Antitone fun n ↦ (P n).2 := antitone_nat_of_succ_le fun n ↦ (hmono n).2.1
  have hlen : ∀ n, (P n).2 - (P n).1 ≤ (u₀ - l₀) * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => rw [hP0]; simp
    | succ n ih =>
      have h1 := (hmono n).2.2
      have h2 : (u₀ - l₀) * (1 / 2 : ℝ) ^ (n + 1) = ((u₀ - l₀) * (1 / 2 : ℝ) ^ n) / 2 := by ring
      rw [h2]
      linarith
  -- Step 4: the lengths shrink to zero, so the left endpoints form a Cauchy sequence
  have hlenAnti : Antitone fun n ↦ (P n).2 - (P n).1 := by
    refine antitone_nat_of_succ_le fun n ↦ ?_
    have h1 := (hmono n).2.2
    have h2 : (P n).1 ≤ (P n).2 := (hQ n).2.2
    show (P (n + 1)).2 - (P (n + 1)).1 ≤ (P n).2 - (P n).1
    linarith
  have hsmall : ∀ ε > 0, ∃ N, (P N).2 - (P N).1 < ε := by
    intro ε hε
    have hd : 0 ≤ u₀ - l₀ := by linarith
    have hd1 : (0 : ℝ) < (u₀ - l₀) + 1 := by linarith
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hd1) one_half_lt_one
    refine ⟨N, ?_⟩
    have h1 : (u₀ - l₀) * (1 / 2 : ℝ) ^ N ≤ (u₀ - l₀) * (ε / ((u₀ - l₀) + 1)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hN) hd
    have h2 : (u₀ - l₀) * (ε / ((u₀ - l₀) + 1)) < ε := by
      have hlt : (u₀ - l₀) / ((u₀ - l₀) + 1) < 1 := by
        rw [div_lt_one hd1]; linarith
      calc (u₀ - l₀) * (ε / ((u₀ - l₀) + 1))
          = ((u₀ - l₀) / ((u₀ - l₀) + 1)) * ε := by ring
        _ < 1 * ε := mul_lt_mul_of_pos_right hlt hε
        _ = ε := one_mul ε
    have h3 := hlen N
    linarith
  have hCauchy : isCauchyReal ⟨fun n ↦ (P n).1⟩ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have h1 : (P N).1 ≤ (P m).1 := hLmono hm
    have h2 : (P m).2 ≤ (P N).2 := hUanti hm
    have h3 : (P m).1 ≤ (P m).2 := (hQ m).2.2
    have h4 : (P N).1 ≤ (P n).1 := hLmono hn
    have h5 : (P n).2 ≤ (P N).2 := hUanti hn
    have h6 : (P n).1 ≤ (P n).2 := (hQ n).2.2
    show dist ((P m).1) ((P n).1) < ε
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- Step 5: completeness produces the candidate supremum
  obtain ⟨a, ha⟩ := real_numbers_complete hCauchy
  -- the right endpoints converge to the same limit
  have haU : tends_to ⟨fun n ↦ (P n).2⟩ a := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ := hsmall (ε / 2) (half_pos hε)
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have h1 : dist ((P n).1) a < ε / 2 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    have h2 : (P n).2 - (P n).1 ≤ (P N₂).2 - (P N₂).1 :=
      hlenAnti (le_trans (le_max_right N₁ N₂) hn)
    have h3 : (P n).1 ≤ (P n).2 := (hQ n).2.2
    rw [Real.dist_eq, abs_lt] at h1
    obtain ⟨h1a, h1b⟩ := h1
    show dist ((P n).2) a < ε
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- Step 6: `a` is an upper bound, and it is below every upper bound
  have haUB : a ∈ upperBounds S := by
    intro s hs
    refine tends_to_ge_of_ge haU ?_
    intro n
    exact (hQ n).2.1 hs
  refine ⟨⟨a, haUB⟩, ?_⟩
  rintro ⟨b, hb⟩
  show a ≤ b
  refine tends_to_le_of_le ha ?_
  intro n
  exact hb (hQ n).1


/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
