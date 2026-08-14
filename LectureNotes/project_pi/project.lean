
/-
Definitions:
1.) Pi
2.) Sin
3.) Cos
4.) Factorial

Theorems/Results:

Known results:
1.) Product rule for derivatives
2.) Fundamental Theorem of Calculus


Unknown results:
1.) Integral is monotone
2.) Positive integrand ⇒ positive integral
3.) Polynomials are infinitely differentiable

Proof Structure
  Step 1: Assert we are proving via contradiction (D)
  Step 2: Get a hypothesis h: π = a/b (D)
  Step 3: Prove that a,b : ℕ (in particular, a,b ≠ 0)
  Step 4: Define the functions f, F.
  Step 5: Show that f^(j)(π) and f^(j)(0) are integers
    · Show that the coefficients of Niven polynomials are integers
    · Not really sure how to prove this!
  Step 6: Show that F is infinitely differentiable
    · There should be a lemma that says polynomials are infinitely differentiable
  Step 7: Define the function g(x):= F'(x)sin(x)-F(x)cos(x)
  Step 8: Compute derivative of g(x)
    · Use product rule on F'(x)sin(x) and F(x)cos(x)
    · Use _linarith_ to get g'(x) = F''(x)sin(x)+F(x)sin(x)
  Step 9: Show g'(x)=f(x)sin(x)
  Step 10: Define I = integral_{0}^{π} f(x)sin(x)
  Step 11: Evaluate I to be F(π)+F(0)
    · Use FTC to get into the form [F'(x)sin(x)-F(x)cos(x)]_0^{π}
  Step 12: Show that I : ℕ
    · Show that F(π) : ℕ because sum of integers (thanks to Step X) is an integer
    · Similarly show that F(0) : ℕ
    · Then, we obviously have F(π)+F(0) : ℕ
  Step 13: Show that I>0
    · 13.1: Show that f(x)sin(x)>0 on 0<x<π
    · Perhaps _simp ?_ will show this automatically once prove have 13.1
  Step 14: Show on 0<x<π we have (0 < f(x)sin(x)) ∧ (f(x)sin(x) < (πa)^n/n!)
    · We can prove each individually
    · The left side is just 13.1
    · The right side might be some _simp ?_ work
      · We might need to also show that x^n < π^n, a-bx < a, and (a-bx)^n < a^n
  Step 15: Show that integral_{0}^{π} (πa)^n/n! = π^{n+1}/(n+1)! * a^n
  Step 16: Show that I < π^{n+1}/(n+1)! * a^n
    · Use the monotonicity property of integrals
    · We need to show that f(x)sin(x) and π^{n+1}/(n+1)! * a^n are monotone
  Step 17: Show that π^{n+1}/(n+1)! * a^n tends to 1
  Step 19: Show that I<1
  Step 19: Contradiction! I : N but 0 < I < 1 !!!

DONE

-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import LectureNotes.lecture8.examples8
import LectureNotes.lecture9.examples9
import Mathlib.Analysis.BoxIntegral.Basic
import Mathlib.Analysis.BoxIntegral.Partition.Tagged
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open BoxIntegral MyFunctions
open scoped BigOperators
open Real
open scoped ContDiff

#check sin
#check cos

noncomputable def pi : ℝ :=
  2 * Classical.choose Real.exists_cos_eq_zero

noncomputable def iterPolyDeriv (p : Polynomial ℝ) (k : ℕ) : Polynomial ℝ :=
  (Polynomial.derivative^[k]) p

-- the identification of `Fin 1 (= {0}) → ℝ` with `ℝ`
noncomputable abbrev ev := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

/- THIS IS MULTIPLICATION RULE FOR DERIVATIES (FROM LECTURE 8)
lemma deriv_mul {f g : ℝ → ℝ} (hf : Differentiable f) (hg : Differentiable g) :
    HasDeriv (f * g) (deriv f * g  + f  * deriv g ) := fun x =>
  deriv_mul_at (has_deriv_of_differentiable hf x) (has_deriv_of_differentiable hg x)
-/

abbrev intervalToBox (a b : ℝ) (h : a < b) : Box (Fin 1) :=
  Box.mk (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (fun _ => h)

-- map: Intervals × ℝ -> ℝ which is additive in the boxes and linear in the real variable.
noncomputable abbrev riemannVolume : (Fin 1 →ᵇᵃ[⊤] ℝ →L[ℝ] ℝ) :=
  BoxAdditiveMap.volume

def HasIntegral {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) (α : ℝ) : Prop :=
  BoxIntegral.HasIntegral (intervalToBox a b hab) (IntegrationParams.Riemann)
  (fun g => f (ev g)) (riemannVolume) α

def Integrable {a b : ℝ} (f : ℝ → ℝ) (hab : a < b) : Prop :=
  ∃ α, HasIntegral f hab α

theorem integral_of_differentiable_Interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : Differentiable ℝ f)
    (hf' : Integrable (MyFunctions.deriv f) hab) :
    HasIntegral (MyFunctions.deriv f) hab (f b - f a) := by
  sorry

lemma integral_monotone {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfg : ∀ x ∈ Set.Icc a b, f x < g x)
    (hf : Integrable f hab) (hg : Integrable g hab) :
    ∀ {If Ig : ℝ}, HasIntegral f hab If → HasIntegral g hab Ig → If < Ig := by
  sorry

lemma poly_infty_differentiable (p : Polynomial ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
    sorry
  --exact p.analytic.contDiff -It's giving me issues

theorem iven_niven_pi {a b : ℕ+} (hab : b < a) : ¬(pi = (a : ℝ)/(b : ℝ)) := by
    by_contra h
    let n : ℕ := 10000 -- a value that is significantly large
    let f : Polynomial ℝ := (Polynomial.X ^ n * (Polynomial.C (a : ℝ) - Polynomial.C (b : ℝ) * Polynomial.X) ^ n) *
    Polynomial.C ((Nat.factorial n : ℝ)⁻¹) -- New notation learned!
    -- let f : ℝ → ℝ := fun x => f.eval x
    let D : ℕ → Polynomial ℝ :=
      fun k => (Polynomial.derivative^[k]) f
    let F : Polynomial ℝ :=
      Finset.sum (Finset.range (n + 1)) (fun k => (-1 : ℝ) ^ k • D (2 * k))
    -- helper polynomial for step 5
    let P : Polynomial ℤ := Polynomial.X ^ n *
      (Polynomial.C ((a : ℕ) : ℤ) -
        Polynomial.C ((b : ℕ) : ℤ) * Polynomial.X) ^ n
    have hfP : f = --step 5
      (P.map (Int.castRingHom ℝ)) *
        Polynomial.C ((Nat.factorial n : ℝ)⁻¹) := by
        dsimp [f, P]
        simp only [Polynomial.map_mul,
        Polynomial.map_pow,
        Polynomial.map_sub,
        Polynomial.map_C,
        Polynomial.map_X]
        norm_num
    have hF_smooth : ContDiff ℝ ∞ (fun x : ℝ => F.eval x) := by --step 6
       exact poly_infty_differentiable F
    let g : ℝ → ℝ := fun x => --step 7
    (Polynomial.derivative F).eval x * sin x - F.eval x * cos x
    have hg_deriv (x : ℝ) : --step 8
      MyFunctions.HasDerivAt g (((Polynomial.derivative^[2]) F).eval x * sin x + F.eval x * sin x) x := by
      dsimp [g]
      convert
        ((Polynomial.hasDerivAt (Polynomial.derivative F) x).mul
          (hasDerivAt_sin x)).sub -- Mathlib definition of HasDerivAt. Defines derivatices for sin & cos.
        ((Polynomial.hasDerivAt F x).mul
          (hasDerivAt_cos x))
        using 1 <;> ring
    have hg_deriv_eq (x : ℝ) : MyFunctions.deriv g x = (((Polynomial.derivative^[2]) F).eval x + F.eval x) * sin x := by
      rw [← MyFunctions.deriv_eq_of_has_deriv (hg_deriv x)]
      ring
    have g_deriv_eq_fsin (x : ℝ) : MyFunctions.deriv g x = f.eval x * sin x := by --step 9
      rw [hg_deriv_eq]
      dsimp [f]
      ring_nf
    have h0pi : (0 : ℝ) < pi := by --step 10
      sorry
    have hIntegrable : Integrable (fun x => f.eval x * Real.sin x) h0pi := by
      sorry
    obtain ⟨I, hI⟩ := hIntegrable
    have hI_eval : I = F.eval pi + F.eval 0 := by --step 11
      sorry
