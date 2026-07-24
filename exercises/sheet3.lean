import Mathlib.Tactic --Imports Lean proof tactics
import Mathlib.Data.Nat.Factorization.Defs --Imports definitions about prime factorization of natural numbers

/-!
# Exercise sheet 3: removing one prime power

In `examples4.lean`, `PExp n p` is the exponent of `p` in `n`.  The two
definitions below give names to the corresponding entries of
`Nat.maxPowDvdDiv`.  Thus `primeExponent n p` is the exponent of `p`, while
`remainder n p` is what remains after the full power of `p` has been removed.

The four exercises isolate the number-theoretic input needed for lemmas 1--4
in the lecture notes. You may find the results in `Nat.MaxPowDiv` useful.
-/

namespace Sheet3 --Everything below goes in here

open Nat -- Open Natural number namespace, so you do not need to write Nat.maxPowDvdDiv

abbrev primeExponent (n p : ℕ) : ℕ := (maxPowDvdDiv p n).1
/-
Defines an abbreviation called primeExponent
primeExponent - how many times p divides n
  n = 72        72 = 2 x 2 x 2 x 9
  p = 2         primeExponent 72 2 = 3
n and p are natural numbers, n is the exponent of p
maxPowDvdDiv p n : returns a pair of natural numbers (exponent, remainder)
  For 72 and 2 --> (3,9)
.1 selects the first entry of that pair
  first entry is largest exponent k such that p ^ k occurs as a factor n
  For 72 and 2 --> 3


-/

abbrev remainder (n p : ℕ) : ℕ := (maxPowDvdDiv p n).2
/-
n = 72    72 = 2^3 x 9
p = 2
maxPowDvdDiv p n     gives the pair (3,9)
.2 selects the second entry of the pair returned by maxPowDvdDiv p n
  remainder 72 2 = 9
  remove all factors of 2 from 72 and 9 is left
-/



/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/
lemma product_of_primeExponent (n p : ℕ) : n = p ^ primeExponent n p * remainder n p := by
/-
Every natural number n is equal to the largest power of p contain in it,
multiplied by what reamin after that power is removed.
  n = 72      72 = 2^3 x 9
  p = 2       2^3 = 8   72 = 8 x 9
-/
-- Goal: 72 = 2 ^ primeExponent 72 2 * remainder 72 2
 simp only [fst_maxPowDvdDiv, -- rewrites the primeExponent 72 2 into padicValNat 2 72 = 3
            snd_maxPowDvdDiv, -- changes remainder 72 2 into 72.divMaxPow 2 = 9
            -- Goal becomes 72 = 2^3 * 9
            pow_padicValNat_mul_divMaxPow] -- proves the above goal



theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
/-
The largest power of p inside n divides n
n = 72, p = 2
primeExponent 72 2 = 3
2 ^ 3 ∣ 72
8 ∣ 72 true because 72 = 8 * 9
-/
  use remainder n p
  exact product_of_primeExponent n p


/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/
theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
/-
p is prime.
q is prime.
q divides n. n/q
We remove every factor of q from n.
Then any prime p dividing n must either:
be q, or
divide the remainder.

72 = 2^3 x 9
remainder 72 2 = 9
prime divisors of 72: 2 and 3
p = 2, p = q
p = 3, 9/3 so p divides the remainder
p ∣ 72 ↔ p = 2 ∨ p ∣ 9
↔ if and only if       v or

p divides n exactly when p is q, or p divides the remainder.
-/
  constructor
  · intro hpn
      rw [product_of_primeExponent n q] at hpn
      rcases hp.dvd_mul.mp hpn with hpow | hrem

    · left
        apply (hq.dvd_iff_eq hp).mp
        exact hp.dvd_of_dvd_pow hpow

      · right
        exact hrem

    · rintro (rfl | hrem)

      · exact hqn

      · rw [product_of_primeExponent n q]
        exact dvd_mul_of_dvd_right hrem _

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  simp only [remainder, snd_maxPowDvdDiv]
  exact Nat.Prime.not_dvd_divMaxPow hp hn



/-
Lecture lemma 4: removing the largest power of `q` does not change the exponent
of a different prime `p`.
-/

/-
Start by using the first lemma to prove the other lemmas. (You can use simp? and exact?)
-/

lemma padicValNat_mul (n m p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
  padicValNat p (m * n) = padicValNat p m + padicValNat p n := by
  refine @padicValNat.mul _ _ _ ?_ hm hn
  exact { out := hp }

lemma primeExponent_mul {n m p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
    primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
  simp only [primeExponent, fst_maxPowDvdDiv]
  exact padicValNat.mul hp hm hn

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  simp only [primeExponent, fst_maxPowDvdDiv]
  exact Nat.factorization_eq_zero_of_not_dvd hcoprime

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have hqpow_ne :
      q ^ primeExponent n q ≠ 0 := by
    exact pow_ne_zero _ hq.ne_zero

  have hrem_ne :
      remainder n q ≠ 0 := by
    intro hrem
    apply hn
    rw [product_of_primeExponent n q, hrem]
    simp

  have hnotdvd :
      ¬p ∣ q ^ primeExponent n q := by
    intro hdiv
    have hpdivq : p ∣ q := hp.dvd_of_dvd_pow hdiv
    have hpeq : p = q := (hq.dvd_iff_eq hp).mp hpdivq
    exact hpq hpeq

  calc
    primeExponent n p =
        primeExponent
          (q ^ primeExponent n q * remainder n q) p := by
            rw [← product_of_primeExponent n q]
    _ = primeExponent (q ^ primeExponent n q) p +
        primeExponent (remainder n q) p := by
          exact primeExponent_mul hqpow_ne hrem_ne hp
    _ = 0 + primeExponent (remainder n q) p := by
          rw [primeExponent_coprime hnotdvd]
    _ = primeExponent (remainder n q) p := by simp


/-!
## Applications of prime factorization

For these exercises we use Mathlib's built-in `Nat.factorization`.  Its
support is the finite set of prime divisors, just like the support of `PExp`
constructed in the lecture.

The greatest common divisor `Nat.gcd n m` is the largest natural number that
divides both `n` and `m`.

The least common multiple `Nat.lcm n m` is the smallest natural number
divisible by both `n` and `m`.
-/

/-
Start by writing down the proofs on paper, and start by formalizing the key mathematical
facts you used in the proof as lemmas.
We will discuss set operations during the exercise class tomorrow!
-/

/- Every prime dividing both `n` and `m` also divides `n + m`. -/
theorem exercise5 (n m : ℕ) :
    (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
  intro p hp
  have hp_prime : p.Prime := by
    exact Nat.prime_of_mem_factorization hp

  have hp_gcd : p ∣ Nat.gcd n m := by
    exact Nat.dvd_of_mem_factorization hp

  have hp_n : p ∣ n := by
    exact dvd_trans hp_gcd (Nat.gcd_dvd_left n m)

  have hp_m : p ∣ m := by
    exact dvd_trans hp_gcd (Nat.gcd_dvd_right n m)

  have hp_add : p ∣ n + m := by
    exact Nat.dvd_add hp_n hp_m

  rw [Nat.support_factorization]
  exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_add⟩

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
    rw [Nat.factorization_lcm hn hm]
    ext p
    simp

end Sheet3
