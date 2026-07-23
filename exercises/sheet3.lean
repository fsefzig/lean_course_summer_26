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
    simp only [fst_maxPowDvdDiv,
    snd_maxPowDvdDiv,
    pow_padicValNat_mul_divMaxPow]




theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
  use (remainder n p)
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
    by_cases eq : p = q
    · left
      exact eq
    · right
      rw [product_of_primeExponent n q] at h
      rcases hp.dvd_mul.mp h with hdivq|hdivr
      · exfalso
        apply eq
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp
          (hp.dvd_of_dvd_pow hdivq)

      · exact hdivr

  · intro h
    rcases h with eq|div
    · rw [eq]
      exact hqn
    · have k : remainder n q ∣ n := by
        use q ^ primeExponent n q
        rw [Nat.mul_comm]
        exact product_of_primeExponent n q
      exact Nat.dvd_trans div k









/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  rw [remainder]
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
  simp only [fst_maxPowDvdDiv]
  exact padicValNat_mul n m p hm hn hp


lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
  right
  right
  exact hcoprime

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have eq : n =  q^primeExponent n q * remainder n q := by
    exact product_of_primeExponent n q

  have rm : remainder n q ≠ 0 := by
    by_contra
    rw [this] at eq
    rw [Nat.mul_zero] at eq
    exact hn eq

  have qn : q ^ primeExponent n q ≠ 0 := by
    by_contra
    rw [this] at eq
    rw [Nat.zero_mul] at eq
    exact hn eq

  have eeq : primeExponent n p = primeExponent (q^primeExponent n q) p + primeExponent (remainder n q) p := by
    nth_rw 1 [eq]
    exact primeExponent_mul qn rm hp

  have q0 : primeExponent (q ^ primeExponent n q) p = 0 := by
    refine primeExponent_coprime ?_
    intro h
    have peq: p = q := Nat.prime_eq_prime_of_dvd_pow hp hq h
    exact hpq peq

  rw [q0, Nat.zero_add] at eeq
  exact eeq






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
    simp only [support_factorization]
    intro x hx
    simp only [mem_primeFactors, ne_eq, Nat.add_eq_zero_iff, not_and]
    constructor
    · exact prime_of_mem_primeFactors hx
    · constructor
      · have div_gcd : x ∣ (n.gcd m) := by
          exact dvd_of_mem_primeFactors hx
        have div_n : (n.gcd m) ∣ n := Nat.gcd_dvd_left n m
        have div_m : (n.gcd m) ∣ m := Nat.gcd_dvd_right n m
        refine (Nat.dvd_add_iff_right ?_).mp ?_
        · exact Nat.dvd_trans div_gcd div_n
        · exact Nat.dvd_trans div_gcd div_m
      · intro hn
        intro hm
        rw [hn, hm] at hx
        simp only [gcd_self, primeFactors_zero, Finset.notMem_empty] at hx




/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  simp only [support_factorization]
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_union, mem_primeFactors, ne_eq] at hx
    simp only [mem_primeFactors, ne_eq, Nat.lcm_eq_zero_iff, not_or]
    rcases hx with hx | hx
    constructor
    · exact hx.1
    · constructor
      · refine Nat.dvd_lcm_of_dvd_left ?_ m
        exact hx.2.1
      · constructor
        · exact hx.2.2
        ·exact hm
    · constructor
      · exact hx.1
      · constructor
        · refine Nat.dvd_lcm_of_dvd_right ?_ n
          exact hx.2.1
        · exact ⟨hn, hm⟩
  · intro hx
    rw [Finset.mem_union]
    by_cases facn : x ∈ n.primeFactors
    · left
      exact facn
    · right
      have xp : Nat.Prime x := prime_of_mem_primeFactors hx
      refine Prime.mem_primeFactors ?_ ?_ hm
      · exact xp
      · have lcmprod : (n.lcm m) ∣(n * m) := by
          exact Nat.lcm_dvd_mul n m
        have xlcm : x ∣ (n.lcm m) := by
          exact dvd_of_mem_primeFactors hx
        have xprod : x ∣ n*m := by
          exact Nat.dvd_trans xlcm lcmprod
        #check dvd_mul
        rcases xp.dvd_mul.mp xprod with xn|xm
        · exfalso
          apply facn
          exact Nat.Prime.mem_primeFactors xp xn hn
        · exact xm

end Sheet3
