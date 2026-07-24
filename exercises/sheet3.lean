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
    set k := remainder n q with hk

    sorry
  · intro h
    sorry
#check Subtype

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  refine not_dvd_divMaxPow ?_ ?_
  · exact Prime.one_lt hp
  · exact hn

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
    primeExponent (m * n) p = primeExponent m p + primeExponent n p
    := by
  exact padicValNat_mul n m p hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
  right; right; exact hcoprime

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  sorry

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
  refine Finset.subset_iff.mpr ?_
  intro x hx
  simp only [support_factorization, mem_primeFactors, ne_eq, Nat.add_eq_zero_iff, not_and] at *
  have ⟨hn, hm⟩ := Nat.gcd_dvd n m
  refine ⟨hx.1, ⟨?_, ?_⟩⟩
  · exact Nat.dvd_add
      (Nat.dvd_trans hx.2.1 hn)
      (Nat.dvd_trans hx.2.1 hm)
  · intro h₁ h₂
    refine hx.2.2 ?_
    rw [h₁, h₂]
    simp

#check Or.resolve_right
#check Nat.prime_dvd_prime_iff_eq

#check Coprime
#check Prime.coprime_iff_not_dvd

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  ext _
  simp only [support_factorization, Finset.mem_union, mem_primeFactors, ne_eq, Nat.lcm_eq_zero_iff,
    not_or]
  constructor
  · intro h
    cases h with
    | inl hl =>
      refine ⟨hl.1, ⟨?_, ⟨hl.2.2, hm⟩⟩⟩
      exact Nat.dvd_lcm_of_dvd_left hl.2.1 m
    | inr hr =>
      refine ⟨hr.1, ⟨?_, ⟨hn, hr.2.2⟩⟩⟩
      exact Nat.dvd_lcm_of_dvd_right hr.2.1 n
  · intro h
    cases Prime.dvd_or_dvd_of_dvd_lcm (prime_iff.mp h.1) h.2.1 with
    | inl hl =>
      exact Or.inl ⟨h.1, ⟨hl, hn⟩⟩
    | inr hr =>
      exact Or.inr ⟨h.1, ⟨hr, hm⟩⟩

#check Coprime.lcm_eq_mul
#check Finsupp.prod
#check Nat.irreducible_iff_nat_prime
#check _root_.Prime

/-
Nat.factorization 10 : ℕ →₀ ℕ

5 ↦ 1
2 ↦ 1
x ↦ 0
-/

end Sheet3
