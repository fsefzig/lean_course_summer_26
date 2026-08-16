/-
Definition:
1) Pi
2) Assume pi is rational
  Pi = a/b, where a b : N and b>0
3)Define f(x) construction
  f(x) = x ^ n (a - b∗x) ^ n / n!
4) Define F(x) construction
  F(x) = f(x) - f ‘ ‘ (x) + f (4)(x) - … + (-1) ^ n f (2n)(x)
5) Define the integral
  I = int x in 0 .. pi, f x ∗ sin x

Known results:
Rules of differentiation:
Derivative of addition
Derivative of subtraction
Product rule
Derivative of sin
Derivative of cos

Trigonometric facts:
Sin pi = 0
Cos pi = -1
Sin 0 = 0
Cos 0 = 1

Pi is positive
  0 < pi

Sin is positive between 0 and pi:
0 < x ∧  x < pi → 0 < sin x

Fundamental theorem of calculus

Integral of a constant
  ∫ x in a..b, C = C ∗ (b-a)
Monotonicity of integrals:
  If f(x) ≤ g(x) on [a,b]
  Then ∫ f ≤ ∫ g
Basic facts about powers and factorials


Unknown results:
1) F"(x) sin x + F(x) sin x = f(x) sin x
2) d/dx F'(x) sin x — F(x) cos x = f(x) sin x
3) ∫ x in 0..pi , f(x) ∗ sin(x) = F(pi) + F(0)
4) F(pi) and F(0) are integer
  ∫ x in 0..pi , f(x) ∗ sin(x)   this becomes an integer
5) For 0 < x < pi, 0 < f(x) ∗  sin(x)
  0 < I
6) Upper bound for f(x)
  For 0 ≤ x ≤ pi:
  0 ≤ f(x) ≤ som_constant(n)
7)Bound on f and sin(x) ≤ 1 to get
0 ≤ f(x) ∗ sin(x) ≤ some_constant(n)
8)By monotonicity of the integral
  I ≤ ∫ x in 0..π, some_constant(n)
9) Integrate the constant: I ≤ π ∗ some_constant(n)
10)Show this upper bound tends to 0 as n gets large
  So choose n large enough that: I < 1

Proof Structure:
Step 1: Assume for contradiction that pi is rational
	Write pi = a/b
Step 2: Choose n and define f
Step 3: Define F from the even derivative of f
Step 4: Prove F ‘ ‘ + F = f
Step 5: Differentiate: F ‘ ∗ sin - F ∗  cos
	Show its derivative is: f ∗  sin
Step 6: Fundamental theorem of calculus
	I = int x in 0 .. pi, f x ∗ sin x  = F(pi) + F(0)
Step 7: Prove F (pi) and F (0) are integers
	I is an integer
Step 8: Prove 0 < f(x) ∗ sin(x) for 0 < x < pi
Step 9: Bound the integral from above
	f(x) ∗ sin(x) ≤ Cn
Step 10: Use monotonicity of the integral:
	I ≤ ∫ x in 0..π, some_constant(n) = pi ∗ Cn
Step 11: Choose n sufficiently large
	Pi ∗ Cn < 1
	0 < I < 1
Step 12: I is an integer
	There is no integer strictly between 0 and 1
	Contradiction
Therefore, pi is irrational
-/
