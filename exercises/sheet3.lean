import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Defs
set_option linter.style.longLine false
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
lemma product_of_primeExponent (n p : ℕ) : n = p ^ primeExponent n p * remainder n p := by
  simp only [fst_maxPowDvdDiv, snd_maxPowDvdDiv, pow_padicValNat_mul_divMaxPow]


theorem exercise1 (p n : ℕ) : p ^ primeExponent n p ∣ n := by
  use remainder n p
  exact product_of_primeExponent n p

/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/
theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) : p ∣ n ↔ p = q ∨ p ∣ n.divMaxPow q := by
  constructor
  · intro h
    by_cases h1 : p = q
    · left
      exact h1
    right
    rcases hqn with ⟨k,hk⟩
    rw[hk]
    have h2 : q ≠ 0 := by
      exact Nat.Prime.ne_zero hq
    rw[divMaxPow_base_mul h2 k]
  sorry
/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : ¬p ∣ (maxPowDvdDiv p n).2 := by
  exact Nat.not_dvd_divMaxPow (Prime.one_lt hp) hn

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
  sorry

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  sorry

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
theorem exercise5 (n m : ℕ) : (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
  intro x hx
  rw[support_factorization] at hx
  rw[support_factorization]
  apply mem_primeFactors.mp at hx
  apply mem_primeFactors.mpr
  constructor
  · exact hx.1
  constructor
  · have hxl := hx.2.1
    apply dvd_gcd_iff.mp at hxl
    refine (Nat.dvd_add_iff_right ?_).mp ?_
    · exact hxl.1
    exact hxl.2
  have hxl := hx.2.2
  have imp : n ≠ 0 ∨ m ≠ 0 := by
    by_contra
    apply Decidable.and_iff_not_not_or_not.mpr at this
    rw[this.1,this.2,gcd_zero_right] at hxl
    contradiction
  exact AddRightCancelMonoid.add_ne_zero.mpr imp


/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) : n.factorization.support ∪ m.factorization.support = (Nat.lcm n m).factorization.support := by
  repeat rw[support_factorization]
  refine Finset.ext_iff.mpr ?_
  intro x
  constructor
  · intro h
    apply Finset.mem_union.mp at h
    refine mem_primeFactors.mpr ?_
    constructor
    · rcases h with h1 | h2
      · exact prime_of_mem_primeFactors h1
      exact prime_of_mem_primeFactors h2
    constructor
    · rcases h with h1 | h2
      · exact Nat.dvd_lcm_of_dvd_left (mem_primeFactors.mp h1).2.1 m
      exact Nat.dvd_lcm_of_dvd_right (mem_primeFactors.mp h2).2.1 n
    exact lcm_ne_zero hn hm
  intro h
  apply mem_primeFactors.mp at h
  apply Finset.mem_union.mpr
  have hlcm : x ∣ n ∨ x ∣ m := by
    exact Nat.Prime.dvd_or_dvd h.1 (Nat.dvd_trans h.2.1 (Nat.lcm_dvd_mul n m))
  rcases hlcm with h1 | h2
  · left
    exact mem_primeFactors.mpr ⟨h.1, ⟨h1, hn⟩⟩
  right
  exact mem_primeFactors.mpr ⟨h.1, ⟨h2, hm⟩⟩
end Sheet3
