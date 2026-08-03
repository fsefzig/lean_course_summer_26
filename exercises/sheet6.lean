import LectureNotes.lecture7.examples7

open MyFunctions MySequences

/-!
# Exercise 0 (preliminary lemmas used by Exercises 1 and 2)
-/

namespace MySequences

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ}
    (hx : tends_to x a) (hy : tends_to y b) :
    tends_to ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := hx (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := hy (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn ↦ ?_⟩
  have h1 : |x n - a| < ε / 2 := hN1 n (le_trans (le_max_left N1 N2) hn)
  have h2 : |y n - b| < ε / 2 := hN2 n (le_trans (le_max_right N1 N2) hn)
  change |x n + y n - (a + b)| < ε
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra hab
  push Not at hab
  obtain ⟨N, hN⟩ := hx (a - b) (by linarith)
  have hd : |x N - a| < a - b := hN N le_rfl
  rw [abs_lt] at hd
  linarith [hd.1, h N]

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hab
  push Not at hab
  obtain ⟨N, hN⟩ := hx (b - a) (by linarith)
  have hd : |x N - a| < b - a := hN N le_rfl
  rw [abs_lt] at hd
  linarith [hd.2, h N]

end MySequences

/-!
# Exercise 1: continuous functions
-/
namespace MyFunctions

lemma continuous_comp_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g (f a)) :
    continuousAt (g ∘ f) a := by
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  have hfx := hf x hx
  have hgfx := hg ⟨fun n ↦ f (x n)⟩ hfx
  simpa [Function.comp_apply] using hgfx

lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  rw [continuousAt_iff_seqContinuousAt] at hf hg ⊢
  intro x hx
  have hfx := hf x hx
  have hgx := hg x hx
  have hsum := MySequences.tends_to_add hfx hgx
  simpa [Pi.add_apply] using hsum

end MyFunctions

/-!
# Exercise 2: the least-upper-bound property
-/

namespace MySequences

-- avoids `open Classical`/`open scoped Classical`, which the linter flags;
-- this is the idiomatic way to make `dite` usable on non-decidable props.
attribute [local instance] Classical.propDecidable

variable {S : Set ℝ}

/-- Purely logical fact: a non-upper-bound is beaten by some element of `S`. -/
lemma exists_gt_of_not_upperBounds {m : ℝ} (h : m ∉ upperBounds S) :
    ∃ y ∈ S, m < y := by
  by_contra hc
  apply h
  intro a ha
  by_contra hlt
  exact hc ⟨a, ha, not_le.mp hlt⟩

/-- The bisected `(l, u)` pair after `n` steps. -/
noncomputable def L (S : Set ℝ) (l0 u0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (l0, u0)
  | (n + 1) =>
      let p := L S l0 u0 n
      let m := (p.1 + p.2) / 2
      if h : m ∈ upperBounds S then (p.1, m)
      else ((exists_gt_of_not_upperBounds h).choose, p.2)

noncomputable def lSeq (S : Set ℝ) (l0 u0 : ℝ) (n : ℕ) : ℝ := (L S l0 u0 n).1
noncomputable def uSeq (S : Set ℝ) (l0 u0 : ℝ) (n : ℕ) : ℝ := (L S l0 u0 n).2

/-- Main invariant: membership + orderedness, proved together by induction. -/
lemma inv (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S) (hle0 : l0 ≤ u0) :
    ∀ n, lSeq S l0 u0 n ∈ S ∧ uSeq S l0 u0 n ∈ upperBounds S ∧
      lSeq S l0 u0 n ≤ uSeq S l0 u0 n := by
  intro n
  induction n with
  | zero => simp only [lSeq, uSeq, L]; exact ⟨hl0, hu0, hle0⟩
  | succ n ih =>
    obtain ⟨ihl, ihu, ihle⟩ := ih
    simp only [lSeq, uSeq, L] at ihl ihu ihle ⊢
    split_ifs with h
    · refine ⟨ihl, h, ?_⟩
      dsimp only
      linarith
    · obtain ⟨hyS, hylt⟩ := (exists_gt_of_not_upperBounds h).choose_spec
      dsimp only at hylt ⊢
      have hyu : (exists_gt_of_not_upperBounds h).choose ≤ (L S l0 u0 n).2 := ihu hyS
      refine ⟨hyS, ihu, ?_⟩
      linarith

/-- Consecutive `l` terms increase, consecutive `u` terms decrease, and the gap halves. -/
lemma step_facts (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S)
    (hle0 : l0 ≤ u0) (n : ℕ) :
    lSeq S l0 u0 n ≤ lSeq S l0 u0 (n + 1) ∧
    uSeq S l0 u0 (n + 1) ≤ uSeq S l0 u0 n ∧
    uSeq S l0 u0 (n + 1) - lSeq S l0 u0 (n + 1) ≤ (uSeq S l0 u0 n - lSeq S l0 u0 n) / 2 := by
  obtain ⟨_, _, hle⟩ := inv S l0 u0 hl0 hu0 hle0 n
  simp only [lSeq, uSeq, L] at hle ⊢
  split_ifs with h
  · dsimp only
    refine ⟨le_refl _, by linarith, by linarith⟩
  · obtain ⟨_, hylt⟩ := (exists_gt_of_not_upperBounds h).choose_spec
    dsimp only at hylt ⊢
    refine ⟨by linarith, le_refl _, by linarith⟩

lemma lSeq_mono (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S)
    (hle0 : l0 ≤ u0) : Monotone (lSeq S l0 u0) :=
  monotone_nat_of_le_succ (fun n ↦ (step_facts S l0 u0 hl0 hu0 hle0 n).1)

lemma uSeq_anti (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S)
    (hle0 : l0 ≤ u0) : Antitone (uSeq S l0 u0) :=
  antitone_nat_of_succ_le (fun n ↦ (step_facts S l0 u0 hl0 hu0 hle0 n).2.1)

lemma gap_le (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S)
    (hle0 : l0 ≤ u0) (n : ℕ) :
    uSeq S l0 u0 n - lSeq S l0 u0 n ≤ (u0 - l0) / 2 ^ n := by
  induction n with
  | zero => simp [lSeq, uSeq, L]
  | succ n ih =>
      have hs := (step_facts S l0 u0 hl0 hu0 hle0 n).2.2
      have heq : (u0 - l0) / 2 ^ (n + 1) = ((u0 - l0) / 2 ^ n) / 2 := by
        rw [pow_succ]; ring
      rw [heq]; linarith

lemma initial_gap_nonneg (l0 u0 : ℝ) (hle0 : l0 ≤ u0) : 0 ≤ u0 - l0 := by linarith

/-- `M / 2^n` can be made less than any `ε > 0`, for `n` large. -/
lemma exists_bound (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) : ∃ N : ℕ, M / 2 ^ N < ε := by
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · exact ⟨0, by simp [← hM0, hε]⟩
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < ε / M by positivity) one_half_lt_one
    refine ⟨N, ?_⟩
    have h2 : M * (1 / 2 : ℝ) ^ N < M * (ε / M) := mul_lt_mul_of_pos_left hN hMpos
    rw [mul_div_cancel₀ _ (ne_of_gt hMpos)] at h2
    calc M / 2 ^ N = M * (1 / 2 : ℝ) ^ N := by rw [div_pow]; ring
      _ < ε := h2

lemma bound_mono (M : ℝ) (hM : 0 ≤ M) {N n : ℕ} (hn : N ≤ n) :
    M / 2 ^ n ≤ M / 2 ^ N := by
  have h2N : (0:ℝ) < 2 ^ N := by positivity
  have hpow : (2:ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hone : (1:ℝ) / 2 ^ n ≤ 1 / 2 ^ N := one_div_le_one_div_of_le h2N hpow
  calc M / 2 ^ n = M * (1 / 2 ^ n) := by ring
    _ ≤ M * (1 / 2 ^ N) := mul_le_mul_of_nonneg_left hone hM
    _ = M / 2 ^ N := by ring

lemma lSeq_cauchy (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S)
    (hle0 : l0 ≤ u0) : isCauchyReal ⟨lSeq S l0 u0⟩ := by
  intro ε hε
  set M := u0 - l0 with hMdef
  have hM : 0 ≤ M := initial_gap_nonneg l0 u0 hle0
  obtain ⟨N, hN⟩ := exists_bound M ε hM hε
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  wlog hmn : n ≤ m generalizing m n
  · rw [dist_comm]; exact this n hn m hm (not_le.mp hmn).le
  change |lSeq S l0 u0 m - lSeq S l0 u0 n| < ε
  have hln_lm : lSeq S l0 u0 n ≤ lSeq S l0 u0 m := lSeq_mono S l0 u0 hl0 hu0 hle0 hmn
  have hlm_um : lSeq S l0 u0 m ≤ uSeq S l0 u0 m := (inv S l0 u0 hl0 hu0 hle0 m).2.2
  have hum_un : uSeq S l0 u0 m ≤ uSeq S l0 u0 n := uSeq_anti S l0 u0 hl0 hu0 hle0 hmn
  have hgap : uSeq S l0 u0 n - lSeq S l0 u0 n ≤ M / 2 ^ n := gap_le S l0 u0 hl0 hu0 hle0 n
  have hbnd : M / 2 ^ n ≤ M / 2 ^ N := bound_mono M hM hn
  rw [abs_of_nonneg (by linarith)]
  linarith

lemma uSeq_tends_to_same_limit (S : Set ℝ) (l0 u0 : ℝ) (hl0 : l0 ∈ S) (hu0 : u0 ∈ upperBounds S)
    (hle0 : l0 ≤ u0) {a : ℝ} (hl : tends_to ⟨lSeq S l0 u0⟩ a) :
    tends_to ⟨uSeq S l0 u0⟩ a := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := hl (ε / 2) (by linarith)
  set M := u0 - l0 with hMdef
  have hM : 0 ≤ M := initial_gap_nonneg l0 u0 hle0
  obtain ⟨N2, hN2⟩ := exists_bound M (ε / 2) hM (by linarith)
  refine ⟨max N1 N2, fun n hn ↦ ?_⟩
  have h1 : |lSeq S l0 u0 n - a| < ε / 2 := hN1 n (le_trans (le_max_left N1 N2) hn)
  have h2 : n ≥ N2 := le_trans (le_max_right N1 N2) hn
  have hgap : uSeq S l0 u0 n - lSeq S l0 u0 n ≤ M / 2 ^ n := gap_le S l0 u0 hl0 hu0 hle0 n
  have hbnd : M / 2 ^ n ≤ M / 2 ^ N2 := bound_mono M hM h2
  have hlu : lSeq S l0 u0 n ≤ uSeq S l0 u0 n := (inv S l0 u0 hl0 hu0 hle0 n).2.2
  have hbound : uSeq S l0 u0 n - lSeq S l0 u0 n < ε / 2 := by linarith
  change |uSeq S l0 u0 n - a| < ε
  rw [abs_lt] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end MySequences

lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  set l0 := hS.choose with hl0def
  have hl0 : l0 ∈ S := hS.choose_spec
  set u0 : ℝ := (u : ℝ) with hu0def
  have hu0 : u0 ∈ upperBounds S := u.2
  have hle0 : l0 ≤ u0 := hu0 hl0
  obtain ⟨a, ha⟩ :=
    MySequences.real_numbers_complete (MySequences.lSeq_cauchy S l0 u0 hl0 hu0 hle0)
  have haU := MySequences.uSeq_tends_to_same_limit S l0 u0 hl0 hu0 hle0 ha
  have ha_upper : a ∈ upperBounds S := by
    intro y hy
    exact MySequences.tends_to_ge_of_ge haU
      (fun n ↦ (MySequences.inv S l0 u0 hl0 hu0 hle0 n).2.1 hy)
  refine ⟨⟨a, ha_upper⟩, fun b ↦ ?_⟩
  change a ≤ (b : ℝ)
  exact MySequences.tends_to_le_of_le ha
    (fun n ↦ b.2 (MySequences.inv S l0 u0 hl0 hu0 hle0 n).1)

/-!
# Bonus (not required)

Every real number has a decimal expansion — use `Int.floor`/`Nat.floor` at each scale
`10^{-n}`, showing the resulting series `Σ' n, dₙ / 10^n` `HasSum`s to the target real
number, by squeezing it between the truncated sum and the truncated sum plus `10^{-N}`.
-/
