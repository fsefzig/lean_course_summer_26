import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

-- The sum of two convergent sequences converges to the sum of their limits.
--abbrev tends_to (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε
lemma tends_to_add {x y : RealSeq} {a b : ℝ} (hx : tends_to x a) (hy : tends_to y b) :
  tends_to ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  have ha : ∃ N, ∀ n≥ N, dist (x n) a < ε/2 := by
    apply hx (ε / 2)
    linarith
  have hb : ∃ N, ∀ n≥ N, dist (y n) b < ε/2 := by
    apply hy (ε / 2)
    linarith
  obtain ⟨N1, h1⟩ := ha
  obtain ⟨N2, h2⟩ := hb
  use max N1 N2
  intro n hn
  have hn1 : dist (x n) a < ε / 2 := h1 n (le_of_max_le_left hn)
  have hn2 : dist (y n) b < ε / 2 := h2 n (le_of_max_le_right hn)
  have hadd : dist (x n) a + dist (y n) b < ε := by
    linarith
  exact Std.lt_of_le_of_lt (dist_add_add_le (x.x n) (y.x n) a b) hadd



-- For exercise 2
--abbrev tends_to (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
    --contradiction, suppose a>b
    --take epsilon = (a-b)/2
    -- xn would have to lie in interval (a-(a-b)/2, a+(a-b)/2)
    -- an interval all strictly greater than b
    -- but x n ≤ b
    by_contra hab
    apply Std.not_le.mp at hab
    have h3 : (a-b)/2 >0 := by linarith
    obtain ⟨N, hn⟩ := (hx ((a-b)/2) h3)
    have hcont : a-(a-b)/2 > b := by linarith
    let n:=N+1
    have husethis2 : n≥N := by omega
    exact (not_lt_of_ge (RCLike.ofReal_le_ofReal.mp (h n))) ((fun n a_1 ↦ Std.lt_trans hcont
        ((fun n a_1 ↦ sub_lt_of_abs_sub_lt_left (hn n a_1)) n a_1)) n husethis2)



-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hab
  apply Std.not_le.mp at hab
  have h3 : (b-a)/2 >0 := by linarith
  obtain ⟨N, hn⟩ := (hx ((b-a)/2) h3)
  have hcont : b-(b-a)/2 > a := by linarith
  let n:=N+1
  have husethis2 : n≥N := by omega
  have hxn : x n < b := by
    have habs := abs_sub_lt_iff.mp (hn n husethis2)
    linarith
  exact (not_lt_of_ge (h n)) hxn


end MySequences

/-!
## Exercise 1: continuous functions
-/
namespace MyFunctions

/-
Use `continuousAt_iff_seqContinuousAt` for the exercise.
You may find `Function.comp_apply` useful when simplifying compositions.
-/

#check Function.comp_apply

--def continuousAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
--    ∀ ε > 0, ∃ δ > 0, ∀ y, dist y a < δ → dist (f y) (f a) < ε

lemma continuous_comp_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g (f a)) :
    continuousAt (g ∘ f) a := by
  intro ε he
  obtain ⟨δ1, hd0, hdel⟩ :=  hg ε he  --hdel : ∀y, |y-f(a)|<δ2 => |g(y)-g(f(a))|<ε
  obtain ⟨δ2, hd20, hdelt⟩ := hf δ1 hd0  --hdelt : ∀x, |x-a|<δ1 => |f(x)-f(a)|<ε
  use δ2
  constructor
  · exact hd20
  · intro x hx
    simpa [Function.comp_apply] using (Metric.mem_ball.mp (hdel (f x) (hdelt x hx)))


/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
--huh

--is the intended proof to turn the sum into a composition??



--def continuousAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
--    ∀ ε > 0, ∃ δ > 0, ∀ y, dist y a < δ → dist (f y) (f a) < ε
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  intro ε he
  have he : ε/2 > 0:= by linarith
  obtain ⟨δ1, hd1, hdel⟩ := hf (ε/2) he
  obtain ⟨δ2, hd2, hdelt⟩ := hg (ε/2) he
  let δ3 := min δ1 δ2
  use δ3
  constructor
  · exact lt_min hd1 hd2
  · intro y hy
    rw[Pi.add_apply f g a]
    rw[Pi.add_apply f g y]
    calc
      dist (f y + g y) (f a + g a) = abs (f y + g y -f a - g a):= by
        rw [Real.dist_eq]
        congr 1
        ring --gpted last two lines
      _ = abs (f y -f a + (g y - g a)) := by
        congr 1
        ring
    have heps :  |f y - f a|+|g y - g a|< ε := by
      rw[Eq.symm (add_halves ε)]
      exact add_lt_add (hdel y (Std.lt_of_lt_of_le hy (Std.min_le_left)))
        (hdelt y (Std.lt_of_lt_of_le hy (Std.min_le_right)))
    exact Std.lt_of_le_of_lt (abs_add_le (f y - f a) (g y - g a)) heps







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

#check upperBounds


--incomplete problem; step 4 and beyond didn't get to
lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by

  obtain ⟨l0, hl⟩ := hS
  obtain ⟨u0, hu⟩ := u

  have h0 : l0≤u0 := by
    exact RCLike.ofReal_le_ofReal.mp (hu hl)--l0∈S and u0 is an upper bound

  classical
  let f : ℕ → ℝ × ℝ × ℝ := fun n =>
    Nat.rec (motive := fun _ => ℝ × ℝ × ℝ) (l0, u0, 0)
      (fun n ih =>
        let ln := ih.1
        let un := ih.2.1
        let m := (ln + un) / 2
        if hm : m ∈ upperBounds S then
          (ln, m, 0)
        else
          have hy : ∃ y, y ∈ S ∧ m < y := by
            rw [mem_upperBounds] at hm
            push Not at hm
            exact hm
          let y := Classical.choose hy
          (y, un, 1))
      n

  --apparantly i should have this (claude)
  have f_succ : ∀ k, f (k + 1) =
    (let ln := (f k).1
     let un := (f k).2.1
     let m := (ln + un) / 2
     if hm : m ∈ upperBounds S then
       (ln, m, 0)
     else
       let y := Classical.choose (show ∃ y, y ∈ S ∧ m < y by
         rw [mem_upperBounds] at hm; push Not at hm; exact hm)
       (y, un, 1)) := fun k => rfl

  have h0 : ∀n, (f (n+1)).2.2 = 0 → (f (n)).1 = (f (n+1)).1 := by
    intro n
    let ln := (f n).1
    let un := (f n).2.1
    let m := (ln + un) / 2
    have h0 : (f (n+1)).2.2 = 0 → m ∈ upperBounds S := by
      contrapose!
      --have hnm : m ∉ upperBounds S → (f (n+1)).2.2 ≠ 0 := by
      intro hnm
      rw [f_succ n]
      simp [ln, un, m, hnm]
    have hm : m ∈ upperBounds S → (f (n+1)).1 = (f n).1 := by
      intro hm
      rw [f_succ n]
      simp only [ln, un, m, hm, dif_pos]
    exact fun a ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (hm (h0 a))))


  have h1 : ∀n, (f (n+1)).2.2 = 1 → (f (n)).2.1 = (f (n+1)).2.1 := by
    intro n
    let ln := (f n).1
    let un := (f n).2.1
    let m := (ln + un) / 2

    have h0 : (f (n+1)).2.2 = 1 → m ∉ upperBounds S := by
      contrapose! --have hnm : m ∈ upperBounds S → (f (n+1)).2.2 ≠ 1 := by
      intro hnm
      rw [f_succ n]
      simp [ln, un, m, hnm]

    have hm : m ∉ upperBounds S → (f (n+1)).2.1 = (f n).2.1 := by
      intro hm --claude wrote these next 5 lines, i couldnt figure out
      rw [f_succ n]
      dsimp only
      split
      · next h => exact absurd h hm
      · rfl
    exact fun a ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (hm (h0 a))))

  have hf0 : f 0 = (l0, u0, 0) := by
    rfl


  --lₙ ∈ S
  have hl (n : ℕ): (f n).1 ∈ S := by
    induction n with
    | zero =>
      rw[hf0]
      exact hl
    | succ n ih =>
      let ln := (f n).1
      let un := (f n).2.1
      let m := (ln + un) / 2
      if hm : m ∈ upperBounds S then
        have hidek : f (n+1) = (ln, m, 0) := by
          exact (Ne.dite_eq_left_iff fun h a ↦ h hm).mpr hm
        rw[hidek]
        exact ih
      else
        have hy : ∃ y, y ∈ S ∧ m < y := by
            rw [mem_upperBounds] at hm
            push Not at hm
            exact hm
        let y := Classical.choose hy
        have idek : f (n + 1) = (y, un, 1) := by
          rw [f_succ n]
          simp [ln, un, m, hm, y]
        rw[idek]
        exact (Classical.choose_spec hy).1 --hyS





  --un ∈ upperBounds S
  have huu (n : ℕ): (f n).2.1 ∈ upperBounds S := by
    induction n with
    | zero =>
      rw[hf0]
      exact hu
    | succ n ih =>
      let ln := (f n).1
      let un := (f n).2.1
      let m := (ln + un) / 2
      if hm : m ∈ upperBounds S then
        have hidek : f (n+1) = (ln, m, 0) := (Ne.dite_eq_left_iff fun h a ↦ h hm).mpr hm
        rw [hidek]
        exact hm
      else
        have hy : ∃ y, y ∈ S ∧ m < y := by
          rw [mem_upperBounds] at hm
          push Not at hm
          exact hm
        let y := Classical.choose hy
        have idek : f (n + 1) = (y, un, 1) := by
          rw [f_succ n]
          simp [ln, un, m, hm, y]
        rw[idek]
        exact ih



  --nested
  have hlnest (n : ℕ): (f n).1 ≤ (f (n+1)).1 := by
    let ln := (f n).1
    let un := (f n).2.1
    let m := (ln + un) / 2
    have hlun : ln ≤ un := RCLike.ofReal_le_ofReal.mp (huu n (hl n))



    have hlm : ln ≤ m := by --disgusting
      have hlun : ln/2 ≤ un/2 := by linarith
      have hlun : ln/2+ln/2 ≤ ln/2+un/2 := by linarith
      have hlun : ln ≤ ln/2+un/2 := by linarith
      have hlun : ln/2+un/2 = (ln +un)/2 := Eq.symm (add_div ln un 2)
      (expose_names; exact le_of_le_of_eq hlun_4 hlun)
    if hm : m ∈ upperBounds S then
      have hidek : f (n+1) = (ln, m, 0) := (Ne.dite_eq_left_iff fun h a ↦ h hm).mpr hm
      have hidke : (f (n+1)).1 = ln := by rw[hidek]
      exact Std.le_of_eq (id (Eq.symm hidke)) -- ln≤ln
    else
      have hy : ∃ y, y ∈ S ∧ m < y := by
          rw [mem_upperBounds] at hm
          push Not at hm
          exact hm
      let y := Classical.choose hy
      have idek : f (n + 1) = (y, un, 1) := by
        rw [f_succ n]
        simp [ln, un, m, hm, y]
      rw[idek]
      have hwhatever : (y, un, 1).1 = y := Classical.choose.congr_simp rfl hy
      rw[hwhatever]
      exact Std.le_of_lt (Std.lt_of_le_of_lt hlm ((Classical.choose_spec hy).2))


  have hrnest (n : ℕ): (f n).2.1 ≥ (f (n+1)).2.1 := by
    let ln := (f n).1
    let un := (f n).2.1
    let m := (ln + un) / 2
    --same as above
    sorry


  --uₙ - lₙ ≤ (u₀ - l₀) / 2^n
  have hhalves (n : ℕ) : (f n).2.1 - (f n).1 ≤ ((f 0).2.1 - (f 0).1) / 2^n := by
    induction n with
    | zero =>
      linarith

    | succ n ih =>

      let ln := (f n).1
      let un := (f n).2.1
      let m := (ln + un) / 2

      if hm : m ∈ upperBounds S then

        have hidek : f (n+1) = (ln, m, 0) := (Ne.dite_eq_left_iff fun h a ↦ h hm).mpr hm

        have hidke1 : (f (n+1)).1 = ln := by
          rw[hidek]

        have hidke : (f (n+1)).2.1 = m := by
          rw[hidek]

        -- sts m-ln ≤ (un - ln)/2

        --i ran out of good names to call them
        have hhuh : m-ln = (un - ln)/2 := by ring

        have huhhhh : (f (n+1)).2.1 - (f (n+1)).1 ≤ ((f n).2.1 - (f n).1)/2 := by
          calc
            (f (n+1)).2.1 - (f (n+1)).1 = m - (f (n+1)).1 := by rw[hidke]
            _= m-ln := by rw[hidke1]

          exact Std.le_of_eq hhuh


        have huhhhhh : ((f n).2.1 - (f n).1)/2 ≤ (((f 0).2.1 - (f 0).1) / 2 ^ n)/2 := by
          linarith

        have huhhhhhh : (((f 0).2.1 - (f 0).1) / 2 ^ n)/2 = (((f 0).2.1 - (f 0).1) / 2 ^ (n+1))
          := by ring

        exact le_of_le_of_eq (Std.IsPreorder.le_trans ((f (n + 1)).2.1 - (f (n + 1)).1)
          (((f n).2.1 - (f n).1) / 2) (((f 0).2.1 - (f 0).1) / 2 ^ n / 2) huhhhh huhhhhh) huhhhhhh


      else
      -- ih : (f n).2.1 - (f n).1 ≤ ((f 0).2.1 - (f 0).1) / 2 ^ n
          --  un - ln ≤ (u0 - l0)/2^n

      -- ⊢ (f (n + 1)).2.1 - (f (n + 1)).1 ≤ ((f 0).2.1 - (f 0).1) / 2 ^ (n + 1)
      --which becomes
      -- ⊢ (y, un, 1).2.1 - (y, un, 1).1 ≤ ((f 0).2.1 - (f 0).1) / 2 ^ (n + 1)
      --  un - y ≤ (u0 - l0)/2^(n+1)

      -- sts u(n)-y ≤ (un - ln)/2

        have hy : ∃ y, y ∈ S ∧ m < y := by
            rw [mem_upperBounds] at hm
            push Not at hm
            exact hm
        let y := Classical.choose hy
        have hyM : m≤y:=  Std.le_of_lt (Classical.choose_spec hy).2
        have idek : f (n + 1) = (y, un, 1) := by
          rw [f_succ n]
          simp [ln, un, m, hm, y]
        rw[idek]
        have hrewrite : (y, un, 1).2.1 = un := Real.ext_cauchy rfl
        have hrewrite2 : (y, un, 1).1 = y := Real.ext_cauchy rfl
        rw[hrewrite]
        rw[hrewrite2]
        have huh : un - y ≤ (un-ln)/2 := by
          have huhhh : un -m = (un-ln)/2 := by
            calc
              un -m = un - (ln + un) / 2 := by ring
              _ = (un - ln) / 2 := by ring
          exact le_of_le_of_eq (tsub_le_tsub_left hyM un) huhhh
        have huhhhh : (un-ln)/2 ≤ (((f 0).2.1 - (f 0).1) / 2 ^ (n))/2 := by
          linarith [ih]
        have huhhhhh : (((f 0).2.1 - (f 0).1) / 2 ^ (n))/2 =
          (((f 0).2.1 - (f 0).1) / 2 ^ (n+1)) := by
          ring
        exact le_of_le_of_eq (Std.IsPreorder.le_trans (un - y) ((un - ln) / 2)
            (((f 0).2.1 - (f 0).1) / 2 ^ n / 2) huh huhhhh) huhhhhh


  --abbrev tends_to (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε

  have heps : ∀ ε>0, ∃ n, (f n).2.1 - (f n).1 <ε := by
    intro ε he


    have hmid : ∀n, ((f n).2.1 - (f n).1) =0 ∨ ((f n).2.1 - (f n).1) / 2^n/2 <
      (((f n).2.1 - (f n).1) / 2^(n)) := by
      intro n
      by_cases h : ((f n).2.1 - (f n).1) = 0
      · left
        exact h
      · have h :  (f n).2.1 ≠ (f n).1:= by
          exact sub_ne_zero.mp h

        right
        refine div_two_lt_of_pos ?_

        --0 < ((f n).2.1 - (f n).1) / 2 ^ n
        let ln := (f n).1
        let un := (f n).2.1
        let m := (ln + un) / 2

        have hlnS : ln ∈ S := by
          exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) (hl n)

        have hunS : un ∈ upperBounds S := by
          exact mem_upperBounds_iff_subset_Iic.mpr (huu n)

        have hlun : ln ≤ un := by
          exact RCLike.ofReal_le_ofReal.mp (huu n (hl n))

        have huh : 0≤ (f n).2.1 - (f n).1 := by
          exact sub_nonneg_of_le (huu n (hl n))

        have huhh : (f n).2.1 - (f n).1≠0 := by
          exact sub_ne_zero.mpr h

        have huhhh : 0≠(f n).2.1 - (f n).1 := by
          exact huhh.symm

        have huhhhh : 0< (f n).2.1 - (f n).1 := by
          exact Std.lt_of_le_of_ne huh huhhh

        have huhhhhh : 0<2^n := by
          exact Nat.two_pow_pos n

        have huhhhhhh : (0:ℝ) <(2^n : ℝ) := by
          exact_mod_cast huhhhhh

        have huhhhhhh : 0 < ((f n).2.1 - (f n).1) / 2 ^ n := by
          exact div_pos huhhhh huhhhhhh


        exact huhhhhhh
    sorry




  --(f n).2.1 - (f n).1 ≤ ((f 0).2.1 - (f 0).1) / 2^n < eps
  --(f n).2.1 - (f n).1 < ((f 0).2.1 - (f 0).1) / 2^(n+1) < eps




/-
4) Deduce that `⟨l⟩ : RealSeq` is Cauchy. For sufficiently large `N`,
   every `lₙ` with `n ≥ N` lies in `[l_N, u_N]`, whose length tends to
   zero. The lemmas `exists_pow_lt_of_lt_one` and `one_half_lt_one` may
   help with the powers of `1 / 2`.

5) Apply `MySequences.real_numbers_complete` from last time to obtain a real number `a` to which
   `l` converges. This `a` will be the supremum; do not identify it with
   the library term `sSup S`.

6) Use the two lemmas above about limits to show that `a` satisfied the least-upper-bound property.
Hint: a is also the limit of the sequence `u`.

7) Prove the at least one of the lemmas about limits above.-/





  sorry









/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/
