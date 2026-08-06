import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ} (hx : tends_to x a) (hy : tends_to y b) :
    tends_to ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 2) (by linarith)
  obtain ⟨Ny, hNy⟩ := hy (ε / 2) (by linarith)
  use max Nx Ny
  intro n hn
  have hxn : |x n - a| < ε / 2 := by
    apply hNx n
    exact le_trans (le_max_left Nx Ny) hn
  have hyn : |y n - b| < ε / 2 := by
    apply hNy n
    exact le_trans (le_max_right Nx Ny) hn
  have htriangle :
    |(x n + y n) - (a + b)| ≤ |x n - a| + |y n - b| := by
    rw [show (x n + y n) - (a + b) = (x n - a) + (y n - b) by ring]
    exact abs_add_le (x n - a) (y n - b)
  have hsum : |x n - a| + |y n - b| < ε := by
    calc
      |x n - a| + |y n - b|
          < ε / 2 + ε / 2 := add_lt_add hxn hyn
      _ = ε := by ring
  exact lt_of_le_of_lt htriangle hsum

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hε : 0 < (a - b) / 2 := by
    linarith
  obtain ⟨N, hN⟩ := hx ((a - b) / 2) hε
  have hclose := hN N (le_refl N)
  have habs : -((a - b) / 2) < x N - a := by
    exact (abs_lt.mp hclose).1
  have hxgt : b < x N := by
    linarith
  exact (not_lt_of_ge (h N)) hxgt

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hab
  have hab' : a < b := lt_of_not_ge hab
  have hε : 0 < (b - a) / 2 := by
    linarith
  obtain ⟨N, hN⟩ := hx ((b - a) / 2) hε
  have hclose := hN N (le_refl N)
  have habs : x N - a < (b - a) / 2 := by
    exact (abs_lt.mp hclose).2
  have hxlt : x N < b := by
    linarith
  exact (not_lt_of_ge (h N)) hxlt

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
  have hfx := hf x hx
  have hgfx := hg ⟨fun n ↦ f (x n)⟩ hfx
  simpa [Function.comp_apply] using hgfx

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  have hfx := hf x hx
  have hgx := hg x hx
  simpa using tends_to_add hfx hgx

end MyFunctions

/-!
## Exercise 2: the least-upper-bound property
-/

lemma exists_of_ne_up {S : Set ℝ} {x : ℝ} (hx : x ∉ upperBounds S) : ∃ y ∈ S, x < y := by
  classical
  by_contra h
  apply hx
  intro y hy
  by_cases hle : y ≤ x
  · exact hle
  · exact False.elim (h ⟨y, hy, lt_of_not_ge hle⟩)

lemma choose_mem_of_ne_up {S : Set ℝ} {x : ℝ} (hx : x ∉ upperBounds S) :
    Classical.choose (exists_of_ne_up hx) ∈ S := (Classical.choose_spec (exists_of_ne_up hx)).1

lemma choose_gt_of_ne_up {S : Set ℝ} {x : ℝ} (hx : x ∉ upperBounds S) :
    x < Classical.choose (exists_of_ne_up hx) := (Classical.choose_spec (exists_of_ne_up hx)).2

lemma midpoint_width {l u : ℝ} :
    (l + u) / 2 - l = (u - l) * (1 / 2 : ℝ) := by
  ring

lemma bisect_width_of_gt {l u y : ℝ} (hy : (l + u) / 2 < y) (hyu : y ≤ u) :
    u - y ≤ (u - l) * (1 / 2 : ℝ) := by
  have hyu' : y ≤ u := hyu
  nlinarith [hy, hyu', midpoint_width (l := l) (u := u)]

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

  let l0 : ℝ := Classical.choose hS

  have hl0 : l0 ∈ S := by
    exact Classical.choose_spec hS

  let c : ℝ := (u : ℝ) - l0 + 1

  have hc : 0 < c := by
    dsimp [c]
    linarith [u.2 hl0]

  let bounds : ℕ → ℝ × ℝ := fun n =>
    Nat.recOn n
      ⟨l0, (u : ℝ)⟩
      (fun _ ih =>
        if hm : ((ih.1 + ih.2) / 2) ∈ upperBounds S then
          ⟨ih.1, (ih.1 + ih.2) / 2⟩
        else
          ⟨Classical.choose (exists_of_ne_up hm), ih.2⟩)

  let lSeq : RealSeq := ⟨fun n => (bounds n).1⟩
  let uSeq : RealSeq := ⟨fun n => (bounds n).2⟩

  have hmem :
      ∀ n,
        lSeq n ∈ S ∧
        uSeq n ∈ upperBounds S ∧
        lSeq n ≤ uSeq n := by
    intro n
    induction n with
    | zero =>
        exact ⟨hl0, u.2, u.2 hl0⟩

    | succ n ih =>
        rcases ih with ⟨hl, hu, hlu⟩

        dsimp [bounds, lSeq, uSeq]
        split_ifs with hm

        · refine ⟨hl, hm, ?_⟩
          nlinarith [hlu]

        · refine ⟨choose_mem_of_ne_up hm, by simpa using hu, ?_⟩
          exact hu (choose_mem_of_ne_up hm)

  have hstep_l : ∀ n, lSeq n ≤ lSeq (n + 1) := by
    intro n
    rcases hmem n with ⟨hl, hu, hlu⟩

    dsimp [bounds, lSeq, uSeq]
    split_ifs with hm

    · exact le_rfl

    · nlinarith [choose_gt_of_ne_up hm, hlu]

  have hstep_u : ∀ n, uSeq (n + 1) ≤ uSeq n := by
    intro n
    rcases hmem n with ⟨hl, hu, hlu⟩

    dsimp [bounds, lSeq, uSeq]
    split_ifs with hm

    · nlinarith [hlu]

    · exact le_rfl

  have hlmono : Monotone lSeq := by
    exact monotone_nat_of_le_succ hstep_l

  have huanti : Antitone uSeq := by
    exact antitone_nat_of_succ_le hstep_u

  have hwidth :
      ∀ n, uSeq n - lSeq n ≤ c * (1 / 2 : ℝ)^n := by
    intro n
    induction n with
    | zero =>
        dsimp [c, lSeq, uSeq, bounds, l0]
        linarith [u.2 hl0]

    | succ n ih =>
        have hstep :
            uSeq (n + 1) - lSeq (n + 1)
              ≤ (uSeq n - lSeq n) * (1 / 2 : ℝ) := by
          rcases hmem n with ⟨hl, hu, hlu⟩

          dsimp [bounds, lSeq, uSeq]
          split_ifs with hm

          · nlinarith [
              midpoint_width
                (l := lSeq n)
                (u := uSeq n)
            ]

          · exact bisect_width_of_gt
              (l := lSeq n)
              (u := uSeq n)
              (y := Classical.choose (exists_of_ne_up hm))
              (choose_gt_of_ne_up hm)
              (hu (choose_mem_of_ne_up hm))

        have hmul :
            (uSeq n - lSeq n) * (1 / 2 : ℝ)
              ≤ c * (1 / 2 : ℝ)^(n + 1) := by
          have hhalf : 0 ≤ (1 / 2 : ℝ) := by
            norm_num

          have h :=
            mul_le_mul_of_nonneg_right ih hhalf

          calc
            (uSeq n - lSeq n) * (1 / 2 : ℝ)
                ≤ (c * (1 / 2 : ℝ)^n) * (1 / 2 : ℝ) := h
            _ = c * (1 / 2 : ℝ)^(n + 1) := by
                rw [pow_succ]
                ring

        exact le_trans hstep hmul

  have hlCauchy : isCauchyReal lSeq := by
    intro ε hε

    have hpos : 0 < ε / c := by
      exact div_pos hε hc

    obtain ⟨N, hN⟩ :=
      exists_pow_lt_of_lt_one
        hpos
        (by norm_num : (1 / 2 : ℝ) < 1)

    have hsmall : c * (1 / 2 : ℝ)^N < ε := by
      have htmp := mul_lt_mul_of_pos_left hN hc

      have hEq : c * (ε / c) = ε := by
        field_simp [hc.ne']

      simpa [hEq] using htmp

    have hbound : uSeq N - lSeq N < ε := by
      exact lt_of_le_of_lt (hwidth N) hsmall

    use N

    intro m hm n hn

    by_cases hmn : m ≤ n

    · have hupper : lSeq n ≤ uSeq N := by
        exact le_trans ((hmem n).2.2) (huanti hn)

      have hlower : lSeq N ≤ lSeq m := by
        exact hlmono hm

      have hdist :
          dist (lSeq m) (lSeq n)
            ≤ uSeq N - lSeq N := by
        rw [
          Real.dist_eq,
          abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (hlmono hmn))
        ]
        linarith [hupper, hlower]

      exact lt_of_le_of_lt hdist hbound

    · have hnm : n ≤ m := by
        exact le_of_not_ge hmn

      have hupper : lSeq m ≤ uSeq N := by
        exact le_trans ((hmem m).2.2) (huanti hm)

      have hlower : lSeq N ≤ lSeq n := by
        exact hlmono hn

      have hdist :
          dist (lSeq m) (lSeq n)
            ≤ uSeq N - lSeq N := by
        rw [
          Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (hlmono hnm))
        ]
        linarith [hupper, hlower]

      exact lt_of_le_of_lt hdist hbound

  obtain ⟨a, ha⟩ := real_numbers_complete hlCauchy

  have hu : tends_to uSeq a := by
    intro ε hε

    have hε2 : 0 < ε / 2 := by
      linarith

    obtain ⟨N1, hN1⟩ := ha (ε / 2) hε2

    have hpos : 0 < (ε / 2) / c := by
      exact div_pos hε2 hc

    obtain ⟨N2, hN2⟩ :=
      exists_pow_lt_of_lt_one
        hpos
        (by norm_num : (1 / 2 : ℝ) < 1)

    have hsmall2 : c * (1 / 2 : ℝ)^N2 < ε / 2 := by
      have htmp := mul_lt_mul_of_pos_left hN2 hc

      have hEq : c * ((ε / 2) / c) = ε / 2 := by
        field_simp [hc.ne']

      simpa [hEq] using htmp

    have htail :
        ∀ n, N2 ≤ n →
          uSeq n - lSeq n < ε / 2 := by
      intro n hn

      have hpow :
          (1 / 2 : ℝ)^n ≤ (1 / 2 : ℝ)^N2 := by
        exact pow_le_pow_of_le_one
          (by positivity)
          (by norm_num : (1 / 2 : ℝ) ≤ 1)
          hn

      have hmul :
          c * (1 / 2 : ℝ)^n
            ≤ c * (1 / 2 : ℝ)^N2 := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)

      exact
        lt_of_le_of_lt
          (le_trans (hwidth n) hmul)
          hsmall2

    let N := max N1 N2

    use N

    intro n hn

    have hn1 : N1 ≤ n := by
      exact le_trans (le_max_left _ _) hn

    have hn2 : N2 ≤ n := by
      exact le_trans (le_max_right _ _) hn

    have h1 : dist (uSeq n) (lSeq n) < ε / 2 := by
      rw [
        Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (hmem n).2.2)
      ]
      exact htail n hn2

    have h2 : dist (lSeq n) a < ε / 2 := by
      exact hN1 n hn1

    calc
      dist (uSeq n) a
          ≤ dist (uSeq n) (lSeq n) + dist (lSeq n) a :=
            dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring

  have hsup : a ∈ upperBounds S := by
    intro x hx
    exact tends_to_ge_of_ge
      hu
      (fun n => (hmem n).2.1 hx)

  have hleast : ∀ b : upperBounds S, a ≤ b := by
    intro b
    exact tends_to_le_of_le
      ha
      (fun n => b.2 (hmem n).1)

  exact ⟨⟨a, hsup⟩, hleast⟩

/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
