
/-
change!!
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
  Step 1: Assert we are proving via contradiction
  Step 2: Get a hypothesis h: π = a/b
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
