import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Algebra.GCDMonoid.Basic

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
-/

lemma product_of_primeExponent (n p : ℕ) :
    n = p ^ primeExponent n p * remainder n p := by
  simp only [fst_maxPowDvdDiv, snd_maxPowDvdDiv, pow_padicValNat_mul_divMaxPow]

theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
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
  constructor
  · intro h
    by_cases hqeq : p = q
    · exact Or.inl hqeq
    · rw [product_of_primeExponent n q] at h
      apply Nat.Prime.dvd_or_dvd hp at h
      rcases h with hpdvdq | hqdvdr
      · apply Nat.Prime.dvd_of_dvd_pow hp at hpdvdq
        have hpq : p = q := by exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpdvdq
        contradiction
      · exact Or.inr hqdvdr
  rintro (heq | hdiv)
  · rw[heq]
    exact hqn
  obtain ⟨k, hk⟩ := hdiv
  rw [product_of_primeExponent n q, hk]
  use q ^ primeExponent n q * k
  group

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/

theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
    intro h
    obtain ⟨k, hk⟩ := h
    have hdvd : p ^ ((primeExponent n p) + 1)  ∣ n := by
      use k
      rw [pow_succ, mul_assoc, ← hk]
      exact product_of_primeExponent n p
    have hcon : primeExponent n p + 1 ≤ primeExponent n p := by
      rw[primeExponent] at *
      refine (pow_dvd_iff_le_padicValNat ?_ ?_).mp hdvd
      · exact Nat.Prime.ne_one hp
      exact hn
    exact Nat.not_succ_le_self (primeExponent n p) hcon

/-
Lecture lemma 4: removing the largest power of `q` does not change the exponent
of a different prime `p`.
-/

lemma padicValNat_mul (n m p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
  padicValNat p (m * n) = padicValNat p m + padicValNat p n := by
  refine @padicValNat.mul _ _ _ ?_ hm hn
  exact { out := hp }

lemma primeExponent_mul {n m p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
    primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
  simp only [primeExponent, fst_maxPowDvdDiv]
  exact padicValNat_mul n m p hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  simp only [primeExponent, fst_maxPowDvdDiv]
  exact padicValNat.eq_zero_of_not_dvd hcoprime

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
  primeExponent n p = primeExponent (remainder n q) p := by
  by_cases hpdvd: p ∣ n
  · by_cases hqdvd : q ∣ n
    · have hmul : primeExponent n p =
        primeExponent (q ^ primeExponent n q) p + primeExponent (remainder n q) p := by
        nth_rewrite 1 [product_of_primeExponent n q]
        refine primeExponent_mul ?_ ?_ hp
        · apply pow_ne_zero
          exact Nat.Prime.ne_zero hq
        exact Nat.ne_zero_of_mul_ne_zero_right (product_of_primeExponent n q ▸ hn)
      have hzero : primeExponent (q ^ primeExponent n q) p = 0 := by
        simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
        right
        right
        intro h
        apply Nat.Prime.dvd_of_dvd_pow hp at h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
      rw[hmul , hzero]
      exact Nat.zero_add (primeExponent (remainder n q) p)
    have hrem : remainder n q = n := by
      rw[remainder, maxPowDvdDiv_of_not_dvd hqdvd]
    rw[hrem]
  have hlhs : primeExponent n p = 0 := by
    simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpdvd)
  have hpndvdr : ¬(p ∣ remainder n q) := by
    intro h
    have hdvd : p ∣ n := by
      rw[product_of_primeExponent n q]
      exact Nat.dvd_mul_left_of_dvd h (q ^ primeExponent n q)
    contradiction
  have hrhs : primeExponent (remainder n q) p = 0 := by
    simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpndvdr)
  rw[hlhs, hrhs]

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
  intro p
  simp only [support_factorization, mem_primeFactors, ne_eq, Nat.gcd_eq_zero_iff, not_and,
    Nat.add_eq_zero_iff, and_imp]
  intro hprime hdvd hne
  constructor
  · exact hprime
  constructor
  · refine (Nat.dvd_add_iff_right ?_).mp ?_
    · exact Nat.dvd_trans hdvd (Nat.gcd_dvd_left n m)
    exact Nat.dvd_trans hdvd (Nat.gcd_dvd_right n m)
  exact hne


/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  ext p
  constructor
  · simp only [support_factorization, Finset.mem_union, mem_primeFactors, ne_eq,
    Nat.lcm_eq_zero_iff, not_or]
    rintro (⟨hprime, hdvdn,hne⟩ | ⟨hprime, hdvdm,hme⟩)
    · refine ⟨hprime, ?_, hne, hm⟩
      exact Nat.dvd_lcm_of_dvd_left hdvdn m
    refine ⟨hprime, ?_, hn, hme⟩
    exact Nat.dvd_lcm_of_dvd_right hdvdm n
  simp only [support_factorization, mem_primeFactors, ne_eq, Nat.lcm_eq_zero_iff, not_or,
    Finset.mem_union, and_imp]
  intro hprime hdvdlcm hne hme
  have hpdvdor : p ∣ n ∨ p ∣ m := by
    exact (Prime.dvd_lcm (prime_iff.mp hprime)).mp hdvdlcm
  rcases hpdvdor with hpdvdn | hpdvdm
  · exact Or.inl ⟨hprime, hpdvdn, hne⟩
  exact Or.inr ⟨hprime, hpdvdm, hme⟩

end Sheet3
