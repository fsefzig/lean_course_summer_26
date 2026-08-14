import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic --def of π. Note that here, π : ℝ s.t. 2 * Classical.choose exists_cos_eq_zero
import Mathlib.Analysis.Complex.Trigonometric -- def of trig fns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series -- sin as a continued fraction, Complex.hasSum_sin should be what we need
import Mathlib.NumberTheory.Real.Irrational -- def irrationality
import Mathlib.Data.Nat.Factorial.Basic -- factorials
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts -- integration by parts formula
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic -- summation in F(x)
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs -- nth deriv
import Mathlib.Order.Interval.Finset.Defs

import Std
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.style.whitespace false


/-
definitions we need:
n!      imported!

integration by parts formula        imported!

sin x := x - (x^3 / 3!) + (x^5 / 5!) - (x^7 / 7!) + ...     imported!


π = smallest ℝ st. π > 0 ∧ sin π = 0        π is defined as something a little different, but we can prove this. See lemma piDefInIven_Details.

f(x) = x^n (a-bx)^n / n!
F(x) = f(x) - f''(x) + f''''(x) - f''''''(x) + ...


Steps:
For integers a, b, n with b ≠ 0 and n ≥ 0, let f(x) = x^n(a − bx)^n, and F(x) =
f(x) − f''(x) + f''''(x) − · · · .
    Show: F(0)/n! and b^n F(a/b)/n! are integers
        see corollary 2 in (Chow, 8)

    Show: integral_statement : the integral over Icc [0, π] of f(x) sin x dx = F(π) + F(0)
            see integration by parts in Chow's equation 7.7

    Show: new_statement : this is equivalent to that equation multiplied by b^n / n! on both sides
        literally just algebra



    Show: π is irrational
        by_contra to assume π CAN be written as a / b.
        Turn the there exists into a form where we can do stuff to a and b.

        have left hand side of new_statement is always positive, but < 1 for really large n
            n! outpaces exponents. Not sure how to say that in lean.
        have right hand side of new_statement is an integer
            exact corollary 2

        contradiction, since there are no integers within (0, 1) by fundamental theorem of transcendental number theory

    EDIT: Felix said it's better to prove a bunch of lemmas than to have a MASSIVE block of haves!
-/
open Real

lemma piDefInIven_Details {a : ℝ} (ha : a > 0) (hasin : Real.sin a = 0) : a ≥ Real.pi := by
    rw [Real.sin_eq_zero_iff] at hasin
    rcases hasin with ⟨n, hn⟩
    subst hn
    have h_n_pos : (n : ℝ) > 0 := by
        simp only [gt_iff_lt] at ha
        rw[mul_comm] at ha
        exact pos_of_mul_pos_right ha Real.pi_nonneg
    have h_n_ge_one : n ≥ 1 := by
        exact_mod_cast h_n_pos
    have h_n_cast_ge_one : (n : ℝ) ≥ 1 := by exact_mod_cast h_n_ge_one
    nlinarith [Real.pi_pos]


/-
Old definitions for f and F:

def f (a : ℤ) (b : ℤ) : ℕ → ℝ → ℝ := fun n x ↦ x^n * (a - b * x)^n / n.factorial -- f(x)

def F (a : ℤ) (b : ℤ) (n : ℕ) : ℝ → ℝ :=
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * (iteratedDeriv (2*i) (f a b n))

Unfortunately Lean says they're noncomputable, so we're going to define them as polynomials.

Then, we switched from division to scalar multiplication since polynomial division is bad for some reason.
Then, we turned all the real number stuff into integer stuff, but that still didn't work.
So it got changed back and we still have noncomputable functions!

open Polynomial

noncomputable def f (a b : ℤ) (n : ℕ) : Polynomial ℝ :=
  (1 / (n.factorial : ℝ)) • (X ^ n * (C (a : ℝ) - C (b : ℝ) * X) ^ n)

noncomputable def F (a b : ℤ) (n : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1), ((-1 : ℝ) ^ i) • ((derivative^[2 * i]) (f a b n))

Also that messed up the other work I've tried to do, so we're going back to the old definitions for now.
-/

open Polynomial

noncomputable def P (a b : ℤ) (n : ℕ) : Polynomial ℝ := -- without the factorial since that might make integerness easier to prove
  X ^ n * (C (a : ℝ) - C (b : ℝ) * X) ^ n

noncomputable def f (a b : ℤ) (n : ℕ) : ℝ → ℝ := -- f(x)
  fun x ↦ (P a b n).eval x / (n.factorial : ℝ)

noncomputable def F (a : ℤ) (b : ℤ) (n : ℕ) : ℝ → ℝ :=
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * (iteratedDeriv (2*i) (f a b n))



lemma fzeroisint (a b : ℤ) (n : ℕ) : ∃ (z : ℤ), z = (f a b n) 0 := by
    unfold f
    unfold P
    simp only [map_intCast, eval_mul, eval_pow, eval_X, eval_sub, eval_intCast,
      mul_zero, sub_zero]
    rcases n with _ | k -- splitting between n = 0 and n ≠ 0.
    · use 1
      simp only [Int.cast_one, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, ne_eq,
        one_ne_zero, not_false_eq_true, div_self]
    use 0
    simp only [Int.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, zero_mul, zero_div]


lemma bnfadivbisint (a b : ℤ) (n : ℕ) {hb : b ≠ 0}: ∃ (z : ℤ), z = b^n * (f a b n) ((a : ℝ) / (b : ℝ)) := by
    unfold f
    unfold P
    simp only [map_intCast, eval_mul, eval_pow, eval_X, eval_sub, eval_intCast]
    rw [div_pow] -- when simp stops making progress, it's time for a bunch of rewrites! I'm not grouping these since I like to see the steps line by line. We're back at the "natural number game" rewrites!
    rw [← mul_div_assoc]
    rw [mul_div_left_comm]
    rw [div_self]
    · rw [mul_one]
      rw [sub_self]
      rcases n with _ | k
      · simp only [pow_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, mul_one,
        Nat.factorial_zero, Nat.cast_one, Int.cast_eq_one, exists_eq]
      · rw[zero_pow]
        · simp only [mul_zero, zero_div, Int.cast_eq_zero, exists_eq]
        exact Ne.symm (Nat.zero_ne_add_one k)
    exact Int.cast_ne_zero.mpr hb

lemma Fzeroisint (a b : ℤ) (n : ℕ) : ∃ (z : ℤ), z = (F a b n) 0:= by
    unfold F
    induction n
    · unfold f
      unfold P
      simp only [zero_add, Finset.range_one, Int.reduceNeg, Int.cast_neg, Int.cast_one, pow_zero,
        map_intCast, mul_one, eval_one, Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero,
        not_false_eq_true, div_self, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.one_apply, Finset.sum_singleton, mul_zero, iteratedDeriv_zero, Int.cast_eq_one,
        exists_eq]
    sorry -- oh no, finsets! How do I get rid of the sum thing? I want to just show that since f(0) is an integer, f''(0) is also an integer, and so on.


lemma Chow_Corollary_2 (a b : ℤ) (n : ℕ) : -- F(0) + F(a/b) is an integer
    ∃ k : ℤ , k = (F a b n) 0 + b^n * (F a b n) (a/b) := by

    sorry

lemma integral_statement (a b : ℤ) (n : ℕ) : -- Chow's equation 7.7
    ∫ x in Set.Icc 0 Real.pi, (f a b n) x * sin x = (F a b n) Real.pi + (F a b n) 0 := by
    sorry -- define some new functions, then use integration by parts formula

lemma new_statement (a b : ℤ) (n : ℕ) : -- Chow's equation 7.8
    b^n / n.factorial * ∫ x in Set.Icc 0 Real.pi, (f a b n) x * sin x = b^n * (F a b n) Real.pi / n.factorial + b^n * (F a b n) 0 / n.factorial := by
    sorry

theorem irrationalpi (n : ℕ) : Irrational Real.pi := by
    rw [irrational_iff_ne_rational]
    intro a b h_bnotzero
    by_contra hcon
    have Chow_Corollary_2forpi : -- F(0) + F(π) is an integer
    ∃ k : ℤ , k = (F a b n) 0 + b^n * (F a b n) Real.pi := by
        rw[hcon]
        exact Chow_Corollary_2 a b n

    sorry
