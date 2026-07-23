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
#check (maxPowDvdDiv)

lemma product_of_primeExponent (n p : ℕ) :
    n = p ^ primeExponent n p * remainder n p := by
  simp only [fst_maxPowDvdDiv, snd_maxPowDvdDiv, pow_padicValNat_mul_divMaxPow]

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
  · intro h
    by_cases hpeq : p = q
    · left
      exact hpeq
    · right
      rw[product_of_primeExponent n q] at h
      /- prove primality -/
      have hcases :
        p ∣ q ^ primeExponent n q ∨ p ∣ remainder n q :=
        (hp.dvd_mul).mp h
      cases hcases with
          | inl hpow =>
              have hpq : p = q :=
              Nat.prime_eq_prime_of_dvd_pow hp hq hpow
              exact False.elim (hpeq hpq)
          | inr hrem =>
            exact hrem
  · intro h
    rcases h with hpeq | hrem
    · rw[hpeq]
      exact hqn
    · rw [product_of_primeExponent n q]
      exact dvd_mul_of_dvd_right hrem _
/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  exact Nat.not_dvd_divMaxPow hp.one_lt hn

#check maxPowDvdDiv
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
  simpa [primeExponent, fst_maxPowDvdDiv] using
    (padicValNat_mul n m p hm hn hp)

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  simp [primeExponent, Nat.maxPowDvdDiv_of_not_dvd hcoprime]

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have hqne : q ≠ 0 := hq.ne_zero
  have hpowne : q ^ primeExponent n q ≠ 0 := by
    exact pow_ne_zero _ hqne
  have hremne : remainder n q ≠ 0 := by
    intro hrem
    have hfactor := product_of_primeExponent n q
    rw [hrem, Nat.mul_zero] at hfactor
    exact hn hfactor
  have hnotdvd : ¬ p ∣ q ^ primeExponent n q := by
    intro hdvd
    have hpq' : p = q := Nat.prime_eq_prime_of_dvd_pow hp hq hdvd
    exact hpq hpq'
  /- -/
  nth_rewrite 1 [product_of_primeExponent n q]
  rw [primeExponent_mul
  (m := q ^ primeExponent n q)
  (n := remainder n q)
  hpowne
  hremne
  hp]
  rw [primeExponent_coprime hnotdvd]
  simp
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
  simp only [Nat.support_factorization] at hp ⊢
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpgcd : p ∣ Nat.gcd n m := (Nat.mem_primeFactors.mp hp).2.1
  have hgcd_ne : Nat.gcd n m ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  apply Nat.mem_primeFactors.mpr
  constructor
  · exact hpprime
  · constructor
    · exact Nat.dvd_add
        (dvd_trans hpgcd (Nat.gcd_dvd_left n m))
        (dvd_trans hpgcd (Nat.gcd_dvd_right n m))
    · intro hsum
      have hnm : n = 0 ∧ m = 0 := Nat.add_eq_zero_iff.mp hsum
      rw [hnm.1, hnm.2] at hgcd_ne
      exact hgcd_ne rfl

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
