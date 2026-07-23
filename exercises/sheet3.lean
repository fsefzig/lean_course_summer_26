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
    simp only [primeExponent, remainder, fst_maxPowDvdDiv, snd_maxPowDvdDiv]
    exact (pow_padicValNat_mul_divMaxPow p n).symm


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
  have hn : n = q ^ primeExponent n q * remainder n q := product_of_primeExponent n q
  constructor
  · intro hpn
    rw [hn] at hpn
    rcases hp.dvd_mul.mp hpn with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]; exact hqn
    · rw [hn]; exact h.mul_left _

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  exact not_dvd_divMaxPow hp.one_lt hn

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
  exact padicValNat_mul n m p hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  simp [primeExponent, maxPowDvdDiv_of_not_dvd hcoprime]

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have hfact : n = q ^ primeExponent n q * remainder n q := product_of_primeExponent n q
  have hrne : remainder n q ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hfact
    exact hn hfact
  have hqpow : q ^ primeExponent n q ≠ 0 := by
    intro h
    rw [h, Nat.zero_mul] at hfact
    exact hn hfact
  have hpq_pow : ¬p ∣ q ^ primeExponent n q := fun hdvd =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))
  calc primeExponent n p
      = primeExponent (q ^ primeExponent n q * remainder n q) p := by rw [← hfact]
    _ = primeExponent (q ^ primeExponent n q) p + primeExponent (remainder n q) p :=
        primeExponent_mul hqpow hrne hp
    _ = 0 + primeExponent (remainder n q) p := by rw [primeExponent_coprime hpq_pow]
    _ = primeExponent (remainder n q) p := by rw [Nat.zero_add]

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
  simp only [Nat.support_factorization]
  intro p hp
  rw [Nat.mem_primeFactors] at hp ⊢
  obtain ⟨hpp, hpd, hg⟩ := hp
  refine ⟨hpp, dvd_add (hpd.trans (Nat.gcd_dvd_left n m))
    (hpd.trans (Nat.gcd_dvd_right n m)), ?_⟩
  intro h
  obtain ⟨hn0, hm0⟩ := Nat.add_eq_zero_iff.mp h
  exact hg (by rw [hn0, hm0, Nat.gcd_zero_left])

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  have hlcm : Nat.lcm n m ≠ 0 := Nat.lcm_ne_zero hn hm
  simp only [Nat.support_factorization]
  ext p
  simp only [Finset.mem_union, Nat.mem_primeFactors_of_ne_zero hn,
    Nat.mem_primeFactors_of_ne_zero hm, Nat.mem_primeFactors_of_ne_zero hlcm]
  constructor
  · rintro (⟨hpp, hpd⟩ | ⟨hpp, hpd⟩)
    · exact ⟨hpp, hpd.trans (Nat.dvd_lcm_left n m)⟩
    · exact ⟨hpp, hpd.trans (Nat.dvd_lcm_right n m)⟩
  · rintro ⟨hpp, hpd⟩
    have hnm : p ∣ n * m :=
      hpd.trans (Nat.lcm_dvd (dvd_mul_right n m) (dvd_mul_left m n))
    rcases hpp.dvd_mul.mp hnm with h | h
    · exact Or.inl ⟨hpp, h⟩
    · exact Or.inr ⟨hpp, h⟩

end Sheet3
