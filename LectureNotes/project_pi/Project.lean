import Mathlib
import Mathlib.Tactic

open Real
open intervalIntegral

noncomputable section

/- STEP 1-3: DEFINITIONS-/
/-
  Assume π = a / b.
  Define
      f(x) = x^n (a - bx)^n / n!
-/

def f (a b n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * ((a : ℝ) - (b : ℝ) * x) ^ n /
    (n.factorial : ℝ)

/-
  Define: even derivatives
  F(x) = f(x) - f''(x) + f⁽⁴⁾(x) - ... + (-1)^n f⁽²ⁿ⁾(x)
-/
def F (a b n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ k *
      iteratedDeriv (2 * k) (f a b n) x
/-
  Define the integral, riemman sum
      I = ∫₀^π f(x) sin(x) dx
-/
def I (a b n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi,
    f a b n x * Real.sin x
/-
  Constant used for the upper bound.
      Cₙ = π^n a^n / n!
-/
def C (a n : ℕ) : ℝ :=
  Real.pi ^ n * (a : ℝ) ^ n /
    (n.factorial : ℝ)

/- KNOWN FACTS-/

lemma pi_positive :
    0 < Real.pi := by
  exact Real.pi_pos

lemma sin_pi :
    Real.sin Real.pi = 0 := by
  simp

lemma cos_pi :
    Real.cos Real.pi = -1 := by
  simp

lemma sin_zero :
    Real.sin 0 = 0 := by
  simp

lemma cos_zero :
    Real.cos 0 = 1 := by
  simp

lemma sin_positive_between_zero_pi
    {x : ℝ}
    (hx0 : 0 < x)
    (hxpi : x < Real.pi) :
    0 < Real.sin x := by
  exact Real.sin_pos_of_pos_of_lt_pi hx0 hxpi

/-
   STEP 4
   Prove: F''(x) + F(x) = f(x)
   Lean mustmanipulate iterated derivatives and the finite sum.
-/

lemma F_identity
    (a b n : ℕ) (x : ℝ) :
    iteratedDeriv 2 (F a b n) x +
      F a b n x = f a b n x := by
    sorry

/- STEP 5
   Differentiate
        F'(x) sin x - F(x) cos x
   Its derivative is
        f(x) sin x
-/

lemma derivative_identity
    (a b n : ℕ)
    (x : ℝ)
    (hF : HasDerivAt
        (F a b n)
        (deriv (F a b n) x)
        x)
    (hF' : HasDerivAt
        (fun y => deriv (F a b n) y)
        (iteratedDeriv 2 (F a b n) x)
        x) :
      HasDerivAt
      (fun y =>
        deriv (F a b n) y * Real.sin y
          - F a b n y * Real.cos y)
      (f a b n x * Real.sin x)
      x := by

  have hsin :
      HasDerivAt Real.sin (Real.cos x) x := by
    exact Real.hasDerivAt_sin x

  have hcos :
      HasDerivAt Real.cos (-Real.sin x) x := by
    exact Real.hasDerivAt_cos x

  have h :=
    hF'.mul hsin |>.sub (hF.mul hcos)

  convert h using 1 <;> try { rfl }
  rw [← F_identity a b n x]
  ring

/-
   STEP 6
   Fundamental Theorem of Calculus
      I = F(π) + F(0)
   The derivative identity above gives the integrand.
   The remaining work is supplying all of the differentiability
   and integrability hypotheses required by Lean.
    -/

lemma integral_identity
    (a b n : ℕ) :
    I a b n =
      F a b n Real.pi +
      F a b n 0 := by
  sorry
/-
   STEP 7
   Prove F(0) and F(π) are integers so related to I. -/

/-
  Niven proves that the derivatives of f at 0 have integer
  values.
  In Lean state "x is an integer" as
      ∃ z : ℤ, (z : ℝ) = x
-/
lemma F_zero_integer
    (a b n : ℕ) :
    ∃ z : ℤ,
      (z : ℝ) = F a b n 0 := by
  sorry
/-
  If π = a/b, symmetry gives the same result at π.
-/

lemma F_pi_integer
    (a b n : ℕ)
    (hb : 0 < b)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    ∃ z : ℤ,
      (z : ℝ) = F a b n Real.pi := by
  sorry

/-
  Now we can prove that I itself is an integer.

  This part is easy once the previous two lemmas are known.
-/

lemma I_integer
    (a b n : ℕ)
    (hb : 0 < b)
    (hpi : Real.pi = (a : ℝ) / (b : ℝ)) :
    ∃ z : ℤ,
      (z : ℝ) = I a b n := by
  obtain ⟨z₁, hz₁⟩ := F_pi_integer a b n hb hpi
  obtain ⟨z₂, hz₂⟩ := F_zero_integer a b n
  use z₁ + z₂
  rw [integral_identity]
  rw [← hz₁, ← hz₂]

  norm_num

/-
   STEP 8
   Prove
      0 < f(x) sin(x)
   for 0 < x < π.
-/
/-
  First prove
      a - bx > 0.
-/

lemma inside_factor_positive
    (a b : ℕ)
    {x : ℝ}
    (hb : 0 < b)
    (hxpi : x < Real.pi)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    0 < (a : ℝ) - (b : ℝ) * x := by
  have hbR : 0 < (b : ℝ) := by
    exact_mod_cast hb
  rw [hpi] at hxpi
  have h :
      (b : ℝ) * x < (a : ℝ) := by
    have h2 :
        x * (b : ℝ) < (a : ℝ) := by
      exact (lt_div_iff₀ hbR).mp hxpi
    simpa [mul_comm] using h2
  linarith

/- f(x) itself is positive. -/

lemma f_positive
    (a b n : ℕ)
    {x : ℝ}
    (hn : 0 < n)
    (hb : 0 < b)
    (hx0 : 0 < x)
    (hxpi : x < Real.pi)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    0 < f a b n x := by

  have hinside :
      0 < (a : ℝ) - (b : ℝ) * x := by
    exact inside_factor_positive
      a b hb hxpi hpi
  unfold f
  positivity

/- Therefore f(x) sin(x) > 0. -/

lemma integrand_positive
    (a b n : ℕ)
    {x : ℝ}
    (hn : 0 < n)
    (hb : 0 < b)
    (hx0 : 0 < x)
    (hxpi : x < Real.pi)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    0 < f a b n x * Real.sin x := by

  have hf :
      0 < f a b n x := by
    exact f_positive
      a b n
      hn hb hx0 hxpi hpi
  have hs :
      0 < Real.sin x := by
    exact sin_positive_between_zero_pi
      hx0 hxpi
  positivity

/-
   Show the whole integral is positive.

   Mathematically this follows because the integrand is
   continuous, nonnegative on [0,π], and strictly positive
   inside the interval.

   Lean needs the integral positivity theorem and continuity
   details, so this is left as a technical lemma.
    -/

lemma I_positive
    (a b n : ℕ)
    (hn : 0 < n)
    (hb : 0 < b)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    0 < I a b n := by
  sorry

/-
   STEPS 9-10
   Bound f(x) sin(x).
   Niven's bound is
       f(x) sin(x) ≤ π^n a^n / n!
   which is C a n.
    -/

lemma integrand_upper_bound
    (a b n : ℕ)
    {x : ℝ}
    (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi)
    (hb : 0 < b)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    f a b n x * Real.sin x
      ≤
    C a n := by
  sorry

/-
   By monotonicity of the integral,
      I ≤ ∫₀^π Cₙ dx
        = π Cₙ
    -/

lemma integral_upper_bound
    (a b n : ℕ)
    (hb : 0 < b)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    I a b n ≤ Real.pi * C a n := by
  sorry

/-
   STEP 1
   Factorial eventually grows fast enough that
      π Cₙ < 1.
   This is another technical asymptotic result.
  -/

lemma choose_large_n
    (a : ℕ) :
    ∃ n : ℕ,
      0 < n ∧
      Real.pi * C a n < 1 := by
  sorry

/-
   Once n is chosen, prove I < 1.

   This follows very easily from the two bounds.
   -/

lemma I_less_than_one
    (a b n : ℕ)
    (hb : 0 < b)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ))
    (hbound :
      Real.pi * C a n < 1) :
    I a b n < 1 := by
  have hI :
      I a b n ≤ Real.pi * C a n := by
    exact integral_upper_bound a b n hb hpi
  linarith

/-
   There is no integer strictly between 0 and 1.
  -/

lemma no_integer_between_zero_one
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1)
    (hxint :
      ∃ z : ℤ,
        (z : ℝ) = x) :
    False := by
  obtain ⟨z, hz⟩ := hxint
  rw [← hz] at hx0 hx1
  have hz0 :
      0 < z := by
    exact_mod_cast hx0
  have hz1 :
      z < 1 := by
    exact_mod_cast hx1
  omega
/-
   The final contradiction for a fixed rational representation
   π = a/b.
   -/

lemma contradiction_if_pi_eq_fraction
    (a b : ℕ)
    (hb : 0 < b)
    (hpi :
      Real.pi = (a : ℝ) / (b : ℝ)) :
    False := by
  obtain ⟨n, hn, hnsmall⟩ :=
    choose_large_n a

  have hpositive :
      0 < I a b n := by
    exact I_positive a b n hn hb hpi

  have hsmall :
      I a b n < 1 := by
    exact I_less_than_one
      a b n hb hpi hnsmall

  have hinteger :
      ∃ z : ℤ,
        (z : ℝ) = I a b n := by
    exact I_integer a b n hb hpi
  exact no_integer_between_zero_one
    hpositive hsmall hinteger

/-
   STEP 1
   Convert "π is rational" into
       π = a / b
   with a,b natural numbers and b > 0.
   This is bookkeeping about Rational / Irrational in Mathlib,
   rather than the main Niven argument.
  -/

 lemma rational_pi_gives_fraction
    (h : ¬ Irrational Real.pi) :
    ∃ a b : ℕ,
      0 < b ∧
      Real.pi = (a : ℝ) / (b : ℝ) := by

  obtain ⟨q, hq⟩ :=
    exists_rat_of_not_irrational h

  have hqpos : 0 < (q : ℝ) := by
    rw [← hq]
    exact Real.pi_pos

  have hden : 0 < (q.den : ℝ) := by
    exact_mod_cast q.pos

  have hnumR : 0 < (q.num : ℝ) := by
    rw [Rat.cast_def] at hqpos
    rcases (div_pos_iff.mp hqpos) with hpos | hneg
    · exact hpos.1
    · linarith [hden, hneg.2]

  have hnum : 0 < q.num := by
    exact_mod_cast hnumR

  use q.num.natAbs
  use q.den

  constructor
  · exact q.pos

  · rw [hq]
    rw [Rat.cast_def]

    have hnum_nonneg : 0 ≤ q.num := by
      exact le_of_lt hnum

    have ha_int : ((q.num.natAbs : ℕ) : ℤ) = q.num := by
      exact Int.natAbs_of_nonneg hnum_nonneg

    have ha :
        ((q.num.natAbs : ℕ) : ℝ) =
          (q.num : ℝ) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ)) ha_int
    rw [ha]

theorem pi_irrational_project :
    Irrational Real.pi := by
  by_contra h
  obtain ⟨a, b, hb, hpi⟩ :=
    rational_pi_gives_fraction h
  exact contradiction_if_pi_eq_fraction
    a b hb hpi
