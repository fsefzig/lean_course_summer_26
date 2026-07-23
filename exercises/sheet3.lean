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

lemma primeExponent_mul {n m p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) : primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
  simp only [fst_maxPowDvdDiv]
  exact padicValNat_mul n m p hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) : primeExponent n p = 0 := by
  simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
  refine padicValNat.eq_zero_iff.mp ?_
  exact padicValNat.eq_zero_of_not_dvd hcoprime

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : primeExponent n p = primeExponent (remainder n q) p := by
  simp only [fst_maxPowDvdDiv, snd_maxPowDvdDiv]
  have h3 : n.divMaxPow q = n/(q^padicValNat q n) := by
    refine Nat.eq_div_of_mul_eq_right ?_ ?_
    · refine pow_ne_zero (padicValNat q n) ?_
      exact Nat.Prime.ne_zero hq
    exact pow_padicValNat_mul_divMaxPow q n
  rw[h3]
  have h4 : q^padicValNat q n ∣ n := pow_padicValNat_dvd
  have h5 : (padicValNat p (n/q^padicValNat q n)) = padicValNat p n - padicValNat p (q^padicValNat q n) := by
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    apply padicValNat.div_of_dvd h4
  rw[h5]
  have h6 : padicValNat p (q^padicValNat q n) = 0 :=  by
    apply padicValNat.eq_zero_iff.mpr
    right
    right
    by_contra
    have h7 : p.primeFactors ⊆ (q^padicValNat q n).primeFactors := by
      refine primeFactors_mono this ?_
      refine pow_ne_zero (padicValNat q n) ?_
      exact Nat.Prime.ne_zero hq
    have h8 : p.primeFactors = {p} := Prime.primeFactors hp
    have h9 : (q^padicValNat q n).primeFactors = {q} ∨ (q^padicValNat q n).primeFactors = ∅ := by
      by_cases h10 : padicValNat q n ≠ 0
      · left
        exact primeFactors_prime_pow h10 hq
      right
      refine primeFactors_eq_empty.mpr ?_
      right
      refine Nat.pow_eq_one.mpr ?_
      right
      exact Function.notMem_support.mp h10
    have h10 : p ∉ (q^padicValNat q n).primeFactors := by
      rcases h9 with h11 | h12
      · rw[h11]
        exact Finset.notMem_singleton.mpr hpq
      rw[h12]
      tauto
    have h11 : p ∈ p.primeFactors := Prime.mem_primeFactors_self hp
    tauto
  rw[h6,Nat.sub_zero]

theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) : p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
  simp only [snd_maxPowDvdDiv]
  constructor
  · intro h
    by_cases h1 : p = q
    · left
      exact h1
    right
    have h2 : padicValNat p n = padicValNat p (n.divMaxPow q) := add_right_cancel (congrFun (congrArg HAdd.hAdd (exercise4 hp hq h1)) p)
    have h3 : n ≠ 0 → 1 ≤ padicValNat p (n.divMaxPow q) := by
      rw[←h2]
      letI : Fact (p.Prime) := ⟨hp⟩
      exact fun a ↦ one_le_padicValNat_of_dvd a h
    by_cases h4 : n ≠ 0
    · apply h3 at h4
      exact dvd_of_one_le_padicValNat h4
    have h5 : n = 0 := by tauto
    simp only [h5,divMaxPow_zero_left, dvd_zero]
  intro h
  rcases h with h1 | h2
  · rw[h1]
    exact hqn
  have h3 : n.divMaxPow q = n/(q^padicValNat q n) := by
    refine Nat.eq_div_of_mul_eq_right ?_ ?_
    · refine pow_ne_zero (padicValNat q n) ?_
      exact Nat.Prime.ne_zero hq
    exact pow_padicValNat_mul_divMaxPow q n
  rw[h3] at h2
  have h4 : n/(q^padicValNat q n) ∣ n := by
    refine div_dvd_of_dvd ?_
    exact pow_padicValNat_dvd
  exact Nat.dvd_trans h2 h4
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
