import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le


#check Int.toNat_of_nonneg


lemma lemma1point5 {a b : ℝ} (hab : a = b) : (1/a = 1/b) := by
  exact (div_eq_div_iff_comm a 1 b).mp (congrFun (congrArg HDiv.hDiv hab) 1)


theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · --sketch
    --

    -- 1/δ ≤ ε < 1/(δ-1)
    -- δ-1< 1/ε ≤ δ
    -- take δ := ⌈x⌉
    use ⌈1/ε⌉.toNat
    have hcpos : ⌈1/ε⌉ >0 := by
      exact Int.ceil_pos.mpr (one_div_pos.mpr hε)
    --had gpt do hcasting i couldnt figure it out
    have hcasting : (⌈1/ε⌉:ℝ ) = (⌈1/ε⌉.toNat : ℝ ) := by
      norm_cast
      exact (Int.toNat_of_nonneg (le_of_lt (Int.ceil_pos.mpr (one_div_pos.mpr hε)))).symm
    constructor
    · omega
    · --rw [Nat.add_zero (Nat.div 1 ⌈1 / ε⌉.toNat)] failed
      have hineq : (1 / ⌈1 / ε⌉) ≤ (1/(1/ε)) := by
        refine (one_div_le ?_ ?_).mp ?_
        · rw[one_div_one_div ε]
          linarith
        · exact Int.cast_pos.mpr (Int.ceil_pos.mpr (one_div_pos.mpr hε))
        · rw[one_div_one_div ε]
          exact Int.le_ceil (1 / ε)
      rw[one_div_one_div ε] at hineq
      rw[lemma1point5 (Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm hcasting))))]
      --lemma1poitn5 could be rewritten out of existence as well
      exact hineq
  · let y := 1
    have h : ε > 1:= by
      exact Std.not_le.mp h
    have hpos : y>0 := by
      omega
    have halg : (1 : ℝ) / (↑y : ℝ) = 1 := by
      ring
    have hineq : (1/y)≤ε := by
      rw[halg]
      (expose_names; exact Std.le_of_not_ge h_1)
    use y






/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/

--dist (x n) a = |x_n -a|

#check tends_toReal

--def tends_toReal (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε he
  obtain ⟨δ, hd⟩ := exercise1 he
  obtain ⟨N, hN⟩ := hx δ hd.1
  have hj : ∀ n ≥ N, dist (x.x n) a < ε := fun n a_1 ↦ Std.lt_of_lt_of_le (hN n a_1) (hd.2)
  use N


/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/


#check Rat.dist_cast
--distance is preserved from mapping from rationals to reals

--convert every rational number to its real form
--coercsion pretty much

--


--def isCauchy (x : RatSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε
--def isCauchyReal (x : RealSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε
--abbrev RatSeq.toRealSeq (f : RatSeq) : RealSeq where x n := (f.x n : ℝ)
--    aka, every term is turned from its rational form to its real form

--lemma2 is unecessary
lemma lemma2 {m n : ℕ} {x : RatSeq} : dist (x.toRealSeq.x m) (x.toRealSeq.x n)
  = dist (x.x m) (x.x n) := by
  exact Rat.dist_cast (x.x m) (x.x n)


theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro hx ε he
    obtain ⟨N, hN⟩ := Exists.imp (fun a a_1 ↦ a_1) (hx ε he)
    exact Exists.intro N hN
  · intro hx ε he
    obtain ⟨N, hN⟩ := Exists.imp (fun a a_1 ↦ a_1) (hx ε he)
    exact Exists.intro N hN




/-
Finally, show that convergent sequences are Cauchy sequences.
-/

--def tends_toReal (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε
--def isCauchyReal (x : RealSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro ε he
  have he : ε/2 >0 := half_pos he
  obtain ⟨N, hN⟩ := Exists.imp (fun a_1 a ↦ a) (hx (ε/2) he)
  use N
  intro m hm n hn
  have hdn : dist (x n) a < ε/2 := Metric.mem_ball.mp (hN n hn)
  have hdm : dist (x m) a < ε/2 := Metric.mem_ball.mp (hN m hm)
  have hdrfl : dist (x n) a = dist a (x n) := PseudoMetricSpace.dist_comm (x.x n) a
  have hcalc : dist (x m) a + dist a (x n) < ε := by
    linarith --uses hdn and hdm and hdrfl so cant get rid of those
  exact Std.lt_of_le_of_lt (dist_triangle (x m) a (x n)) hcalc

/-
Finally, define a sequence of real numbers that does not converge.
-/

--do whatever i want
def divseq : RealSeq where
  x n := (-1)^n

--is this overkill? [yes almost 100%]
lemma oddpow : ∀ n, Odd n → (-1)^n = -1 := by
  intro n hn
  rcases hn with ⟨k, rfl⟩
  induction k with
  | zero =>
    ring
  | succ n ih =>
    calc
      (-1) ^ (2 * (n + 1) + 1) = (-1) ^ (2 * n + 3) := Int.neg_inj.mp rfl
      _ = (-1)^(2 * n+1 + 2) := Int.neg_inj.mp rfl
      _ = (-1)^(2 * n+1) * (-1)^2 := Int.pow_add (-1) (2 * n + 1) 2
      _ = (-1)^(2 * n+1 ) * 1 := by ring
      _ = (-1)^(2 * n+1 ) := by rw[mul_one]
      _ = -1 := ih

lemma evenpow : ∀ n, Even n → (-1)^n = 1 := by
  intro n hn
  rcases hn with ⟨k, rfl⟩
  induction k with
  | zero =>
    ring
  | succ n ih =>
    calc
      (-1) ^ (n + 1 + (n + 1)) = (-1) ^ (n + 1 + n + 1) := by
        exact Int.neg_inj.mp rfl
      _ = (-1)^ (n+n+1+1) := by ring
      _ = (-1)^ (2*n+2) := by ring
      _ = (-1)^(2*n)* (-1)^2:= Int.pow_add (-1) (2 * n) 2
      _ = (-1)^(2*n) * 1 := by ring
      _ = (-1)^(2*n) := by rw[mul_one]
      _ = (-1)^(n+n) := by ring
      _ = 1 := ih


--fyi the following oddp2 those 4 gpt did for me
lemma oddp2 (x : ℕ) (h : Odd x) : Odd (x + 2) := by
  rcases h with ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  omega

lemma evenp2 (x : ℕ) (h : Even x) : Even (x + 2) := by
  rcases h with ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  omega

lemma evenp1 (x : ℕ) (h : Even x) : Odd (x + 1) := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  omega

lemma oddp1 (x : ℕ) (h : Odd x) : Even (x + 1) := by
  rcases h with ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  omega

lemma stupid (x y : ℝ) (hxy : x > y) : dist x y = x-y := by
  rw [Real.dist_eq]
  rw [abs_of_pos]
  linarith


--def tends_toReal (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε
--sorry in advance lol
theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal divseq a := by
  by_contra
  obtain ⟨a, hA⟩ := this
  have hdef : ∀ ε > 0, ∃ N, ∀ n≥ N, dist (divseq n) a < ε :=
    fun ε a_1 ↦ Exists.imp (fun a_2 a ↦ a) (hA ε a_1)
  --couldnt figure out how to simplify this/get rid of hdef and collapse it all into line 225
  let ε := 1
  obtain ⟨N, hN⟩ := hdef (1) (by norm_num)
  have hodd : ∀ n, Odd n → divseq n = -1 := by
    intro n hodd
    simp only [divseq]
    exact_mod_cast oddpow n hodd
  have heven : ∀ n, Even n → divseq n = 1 := by
    intro n heven
    simp only [divseq]
    exact_mod_cast  evenpow n heven
  by_cases ha : a>0
  · by_cases hNp : Odd N
    · let x := N +2
      have hx : x≥ N := by omega
      have hseqx : divseq x = -1 := Real.ext_cauchy (congrArg Real.cauchy (hodd x (oddp2 N hNp)))
      have ignorets : divseq x <0 := by linarith
      have htsid : dist (divseq x) a > 1:= by
        rw[(PseudoMetricSpace.dist_comm (divseq.x x) a)]
        rw[stupid]
        linarith
        exact Std.lt_trans ignorets ha
      have hcont : dist (divseq.x x) a < 1 := hN x hx
      linarith
----------------------------------------------------------------------------------------------------
    · let x := N +1
      have hx : x≥ N := by omega
      have hseqx : divseq x = -1 :=
        Real.ext_cauchy (congrArg Real.cauchy (hodd x (evenp1 N (Nat.not_odd_iff_even.mp hNp))))
      have ignorets : divseq x <0 := by
        linarith --hseqx implies this
      have htsid : dist (divseq x) a > 1:= by
        rw[(PseudoMetricSpace.dist_comm (divseq.x x) a)]
        rw[stupid]
        linarith
        exact Std.lt_trans ignorets ha
      have hcont : dist (divseq.x x) a < 1 := by
        exact hN x hx --same as above
      linarith
  · by_cases hNp : Odd N
    · let x := N +1
      have ha : 0≥a := Std.not_lt.mp ha
      have haq : 1-a ≥ 1 := by linarith
      have hx : x≥ N := by omega

      have hseqx : divseq x = 1 := by
        exact Real.ext_cauchy (congrArg Real.cauchy (heven x (oddp1 N hNp)))
      have ignorets : divseq x >0 := by linarith
      have hxa : divseq x > a := by linarith
      have hdist : dist (divseq x) a≥ 1 := by
        rw[stupid]
        rw[hseqx]
        exact haq
        exact hxa --no idea why i need to do this
        --again, super sloppy. it works tho shrug emoji
      have hcont : dist (divseq.x x) a < 1 := hN x hx
      linarith
    · let x := N +2
      have ha : 0≥a := Std.not_lt.mp ha
      have haq : 1-a ≥ 1 := by linarith
      have hx : x≥ N := by omega
      have hxEven : Even x := by
        exact evenp2 N (Nat.not_odd_iff_even.mp hNp)
      have hseqx : divseq x = 1 := by
        exact Real.ext_cauchy
          (congrArg Real.cauchy (heven x (evenp2 N (Nat.not_odd_iff_even.mp hNp))))
      have ignorets : divseq x >0 := by linarith
      have hxa : divseq x > a := by linarith
      have hdist : dist (divseq x) a≥ 1 := by
        rw[stupid]
        rw[hseqx]
        exact haq
        exact hxa --no idea why i need to do this
        --again, super sloppy. it works tho shrug emoji
      have hcont : dist (divseq.x x) a < 1 :=  hN x hx
      linarith
