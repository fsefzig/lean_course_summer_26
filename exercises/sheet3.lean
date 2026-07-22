import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Defs

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
     unfold remainder primeExponent
     rw [Nat.snd_maxPowDvdDiv, Nat.fst_maxPowDvdDiv]
     symm
     rw [Nat.mul_comm]
     exact Nat.divMaxPow_mul_pow_padicValNat p n


theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
    unfold primeExponent
    exact Nat.maxPowDiv.pow_dvd

/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/

#check Nat.coprime_primes
#check Coprime.pow_right
#check Coprime.dvd_of_dvd_mul_right

theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
    constructor
    intro h
    by_cases hpq : p = q
    left
    exact hpq
    right
    have h_p_coprime_q : p.Coprime q := by
      exact (Nat.coprime_primes hp hq).2 hpq
    have h_p_coprime_q_pow : p.Coprime (q ^ primeExponent n q) := by
      exact h_p_coprime_q.pow_right (primeExponent n q)
    apply h_p_coprime_q_pow.dvd_of_dvd_mul_right
    have h_mul : q ^ primeExponent n q * remainder n q = n := by
      unfold remainder primeExponent
      rw [Nat.snd_maxPowDvdDiv, Nat.fst_maxPowDvdDiv]
      rw [mul_comm]
      exact Nat.divMaxPow_mul_pow_padicValNat q n
    rw [mul_comm, h_mul]
    exact h
    intro h
    rcases h with h3 | h4
    symm at h3
    rw [h3] at hqn
    exact hqn
    apply Nat.dvd_trans h4
    have h_mul : n = remainder n q * q ^ primeExponent n q   := by
      unfold remainder primeExponent
      rw [Nat.snd_maxPowDvdDiv, Nat.fst_maxPowDvdDiv]
      symm
      exact Nat.divMaxPow_mul_pow_padicValNat q n
    nth_rw 2 [h_mul]
    exact ⟨q ^ primeExponent n q, rfl⟩

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/

#check Nat.div_eq_of_eq_mul_left
#check Nat.not_dvd_ordCompl
#check Nat.factorization_def

theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
    have h_mul : n = p ^ primeExponent n p * remainder n p := by
      exact product_of_primeExponent n p
    have hp_pos : 0 < p := hp.pos
    have hpow_pos : 0 < p ^ primeExponent n p := by
      exact pow_pos hp_pos _
    have h_remainder : remainder n p = n / p^ primeExponent n p := by
      exact (Nat.div_eq_of_eq_mul_right hpow_pos h_mul).symm
    rw [h_remainder]
    have h_exp_eq_fac : primeExponent n p = (n.factorization p) := by
      unfold primeExponent
      rw [Nat.fst_maxPowDvdDiv]
      exact (Nat.factorization_def n hp).symm
    rw [h_exp_eq_fac]
    exact Nat.not_dvd_ordCompl hp hn

/-
Lecture lemma 4: removing the largest power of `q` does not change the exponent
of a different prime `p`.
-/

/-
Start by using the first lemma to prove the other lemmas. (You can use simp? and exact?)
-/

#check Nat.fst_maxPowDvdDiv

lemma padicValNat_mul (n m p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
  padicValNat p (m * n) = padicValNat p m + padicValNat p n := by
  refine @padicValNat.mul _ _ _ ?_ hm hn
  exact { out := hp }

lemma primeExponent_mul {n m p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
    primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
    unfold primeExponent
    rw [Nat.fst_maxPowDvdDiv]
    rw [Nat.fst_maxPowDvdDiv]
    rw [Nat.fst_maxPowDvdDiv]
    exact padicValNat_mul n m p hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
    unfold primeExponent
    rw [Nat.maxPowDvdDiv_of_not_dvd]
    exact hcoprime

#check Nat.maxPowDvdDiv_of_not_dvd
/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat
#check Nat.add_comm
#check Nat.Prime.dvd_iff_eq
#check Nat.ne_one_iff_exists_prime_dvd
#check Nat.ne_add_one

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
    nth_rw 1 [product_of_primeExponent n q]
    rw [primeExponent_mul]
    rw [Nat.add_eq_right]
    rw [primeExponent_coprime]
    intro h
    have hp_dvd_q : p ∣ q := by
      exact hp.dvd_of_dvd_pow h
    have hp_ne_one : p ≠ 1 := by
      exact hp.ne_one
    have h_p_eq_q : p = q := by
      symm
      exact (Nat.Prime.dvd_iff_eq hq hp.ne_one).mp hp_dvd_q
    contradiction
    rw [product_of_primeExponent n q] at hn
    by_contra h2
    rw [h2] at hn
    rw [zero_mul] at hn
    omega
    rw [product_of_primeExponent n q] at hn
    by_contra h2
    rw [h2] at hn
    rw [mul_zero] at hn
    omega
    exact hp

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
#check Nat.eq_zero_of_add_eq_zero_right
#check Nat.dvd_add
#check Nat.gcd_dvd_left
#check Nat.gcd_dvd_right
/- Every prime dividing both `n` and `m` also divides `n + m`. -/
theorem exercise5 (n m : ℕ) :
    (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
    rw [Nat.support_factorization]
    rw [Nat.support_factorization]
    by_cases hnm : n + m = 0
    have hn : n = 0 := Nat.eq_zero_of_add_eq_zero_right hnm
    have hm : m = 0 := Nat.eq_zero_of_add_eq_zero_left hnm
    rw [hn]
    rw [hm]
    simp
    apply Nat.primeFactors_mono
    apply Nat.dvd_add
    exact Nat.gcd_dvd_left n m
    exact Nat.gcd_dvd_right n m
    intro h
    contradiction

#check Nat.factorization_lcm
#check Finsupp.support_sup
/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
    rw [Nat.factorization_lcm hn hm]
    rw [← Finsupp.support_sup]

end Sheet3
