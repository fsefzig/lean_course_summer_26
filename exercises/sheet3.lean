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

-- actual definition of prime number
theorem lemmaprime {p a b : ℕ} (hp : p.Prime) (h : p ∣ a * b) : (p ∣ a ∨ p ∣ b) := by
  exact Nat.Prime.dvd_or_dvd hp h

theorem lemmasub {p q n : ℕ} (hm : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
  ¬ p ∣ q ^ primeExponent n q := by
  intro htemp
  by_cases hcheese : (primeExponent n q = 0)
  · rw [hcheese] at htemp
    rw [pow_zero] at htemp
    have hcontra : ¬ p ∣ 1 := by
      exact Nat.Prime.not_dvd_one hp
    exact hcontra htemp
  · have hokok : ∃(k : ℕ), (primeExponent n q = succ k) := by
      exact exists_eq_succ_of_ne_zero hcheese
    rcases hokok with ⟨k1, hk⟩
    rw [hk] at htemp
    have hpls : p ∣ q := by
      exact Nat.Prime.dvd_of_dvd_pow hp htemp
    have halmost : p ≠ 1 := by
      exact Nat.Prime.ne_one hp
    have hthere : p = q := by
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpls
    exact hm hthere

theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
  constructor
  · intro h
    by_cases hm : p = q
    · left
      exact hm
    · right
      rw [product_of_primeExponent n q] at h
      have hok : ¬ p ∣ q ^ primeExponent n q := by
        exact lemmasub hm hp hq
      apply lemmaprime at h
      exact Or.resolve_right (id (Or.symm h)) hok
      exact hp
  · intro h
    rcases h with h1 | h2
    · rw [← h1] at hqn
      exact hqn
    · have hok := product_of_primeExponent n q
      rcases h2 with ⟨k, hk⟩
      use (k * q ^ primeExponent n q)
      rw [hk] at hok
      rw [mul_comm] at hok
      rw [mul_assoc] at hok
      exact hok



/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  simp only [snd_maxPowDvdDiv]
  have hok : 1 < p := by
    exact Prime.one_lt hp
  exact Nat.not_dvd_divMaxPow hok hn


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
  have hok := product_of_primeExponent n q
  nth_rewrite 1 [hok]
  rw [primeExponent_mul]
  have hok1 : ¬ p ∣ q ^ primeExponent n q := by
    exact lemmasub hpq hp hq
  rw [primeExponent_coprime]
  rw [zero_add]
  exact hok1
  have hqn : q ≠ 0 := by
    exact Nat.Prime.ne_zero hq
  exact pow_ne_zero (primeExponent n q) hqn
  by_contra hbruh
  rw [hbruh] at hok
  rw [mul_zero] at hok
  exact hn hok
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

/- Every prime dividing both `n` and `m` also divides `n + m`. -/
theorem exercise5 (n m : ℕ) :
    (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
  intro p
  simp only [support_factorization, mem_primeFactors, ne_eq, Nat.gcd_eq_zero_iff, not_and, Nat.add_eq_zero_iff,
    and_imp]
  intro hp h hnm
  constructor
  · exact hp
  · constructor
    · have h1 : n.gcd m ∣ n := by
        exact Nat.gcd_dvd_left n m
      have h2 := Nat.gcd_dvd_right n m
      rcases h1 with ⟨k1, hk1⟩
      rcases h2 with ⟨k2, hk2⟩
      rcases h with ⟨k, hk⟩
      use k * (k1 + k2)
      rw [hk1]
      nth_rewrite 2 [hk2]
      rw [hk]
      calc
        p * k * k1 + p * k * k2 = p * k * (k1 + k2) := by exact Eq.symm (Nat.mul_add (p * k) k1 k2)
        p * k * (k1 + k2) = p * (k * (k1 + k2)) := by exact Nat.mul_assoc p k (k1 + k2)
    · exact hnm


/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  simp only [support_factorization]
  ext p -- W axiom of extensionality
  simp only [Finset.mem_union, mem_primeFactors, ne_eq, Nat.lcm_eq_zero_iff, not_or]
  have hnm : ¬n = 0 ∧ ¬m = 0 := by
    exact ⟨hn, hm⟩
  constructor
  · intro h
    rcases h with hl | hr
    · constructor
      · exact hl.left
      · constructor
        · have hfunny := hl.right.left
          exact Nat.dvd_lcm_of_dvd_left hfunny m
        · exact hnm
    · constructor
      · exact hr.left
      · constructor
        · have hfunny := hr.right.left
          exact Nat.dvd_lcm_of_dvd_right hfunny n
        · exact hnm
  · intro h
    by_cases harg : p ∣ n
    · left
      constructor
      · exact h.left
      · constructor
        · exact harg
        · exact hn
    · right
      constructor
      · exact h.left
      · constructor
        · have hyay : (n.lcm m) * (n.gcd m) = n * m := by
            exact lcm_mul_gcd n m
          have huseful : p ∣ n.lcm m := by
            exact h.right.left
          have hok : p ∣ n * m := by
            rcases huseful with ⟨k, hk⟩
            use k * n.gcd m
            rw [hk] at hyay
            rw [← hyay]
            rw [mul_assoc]
          apply lemmaprime at hok
          exact Or.resolve_right (id (Or.symm hok)) harg
          exact h.left
        · exact hm

end Sheet3
