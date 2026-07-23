import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Basic /- for Nat.Prime.dvd_of_dvd_mul_left -/
import Mathlib.Data.Nat.GCD.Prime /- for Nat.Prime.dvd_or_dvd_of_dvd_lcm -/

/-!
# Exercise sheet 3: removing one prime power

In `examples4.lean`, `PExp n p` is the exponent of `p` in `n`.  The two
definitions below give names to the corresponding entries of
`Nat.maxPowDvdDiv`.  Thus `primeExponent n p` is the exponent of `p`, while
`remainder n p` is what remains after the full power of `p` has been removed.

The four exercises isolate the number-theoretic input needed for lemmas 1--4
in the lecture notes. You may find the results in `Nat.MaxPowDiv` useful.
-/

namespace Sheet3

open Nat

abbrev primeExponent (n p : ℕ) : ℕ := (maxPowDvdDiv p n).1

abbrev remainder (n p : ℕ) : ℕ := (maxPowDvdDiv p n).2

/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/
lemma product_of_primeExponent (n p : ℕ) :
    n = p ^ primeExponent n p * remainder n p := by
  exact (Nat.pow_padicValNat_mul_divMaxPow p n).symm


theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
  exact ⟨remainder n p, product_of_primeExponent n p⟩

/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/
theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
  constructor
  · intro hpn
    by_cases hpq : p = q
    · left
      exact hpq
    · right
      rw [← q.pow_padicValNat_mul_divMaxPow n] at hpn
      exact not_imp_not.mp (hp.not_dvd_mul (hpq ∘ prime_eq_prime_of_dvd_pow hp hq)) hpn
  · rintro (hpq | hpdivnq)
    · exact hpq ▸ hqn
    · rw [← q.pow_padicValNat_mul_divMaxPow n]
      exact Nat.dvd_mul_left_of_dvd hpdivnq _

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  exact Nat.not_dvd_divMaxPow hp.one_lt hn

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
  exact padicValNat_mul _ _ _ hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  rw [primeExponent, Nat.maxPowDvdDiv_of_not_dvd hcoprime]

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have ⟨hqPEneq0, hrqneq0⟩ :=
    ne_zero_and_ne_zero_of_mul (ne_of_ne_of_eq' hn (product_of_primeExponent n q))
  nth_rewrite 1 [product_of_primeExponent n q, primeExponent_mul hqPEneq0 hrqneq0 hp, add_eq_right]
  exact primeExponent_coprime (hpq ∘ (prime_eq_prime_of_dvd_pow hp hq))

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
  rw [Finset.subset_iff]
  intro p
  repeat rw [support_factorization, mem_primeFactors, ne_eq]
  rw [Nat.gcd_eq_zero_iff, not_and, ← not_and, Nat.add_eq_zero_iff]
  intro ⟨hp, hpdvd, hnm⟩
  have ⟨pdvdn, pdvdm⟩ := Nat.dvd_gcd_iff.mp hpdvd
  exact ⟨hp, Nat.dvd_add pdvdn pdvdm, hnm⟩

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  ext p
  rw [support_factorization, support_factorization, support_factorization,
    Finset.mem_union, mem_primeFactors, mem_primeFactors, mem_primeFactors,
    ne_eq, ne_eq, ne_eq, Nat.lcm_eq_zero_iff, not_or]
  constructor
  · rintro (⟨hp, hpdvd, _⟩ | ⟨hp, hpdvd, _⟩)
    · exact ⟨hp, Nat.dvd_lcm_of_dvd_left hpdvd m, hn, hm⟩
    · exact ⟨hp, Nat.dvd_lcm_of_dvd_right hpdvd n, hn, hm⟩
  · intro ⟨hp, hpdvd, _, _⟩
    rcases hp.dvd_or_dvd_of_dvd_lcm hpdvd with hpdvdn | hpdvdm
    · left
      exact ⟨hp, hpdvdn, hn⟩
    · right
      exact ⟨hp, hpdvdm, hm⟩

end Sheet3
