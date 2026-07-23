import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Padics.PadicVal.Basic

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
notation "ordProj[" p "] " n:arg => p ^ Nat.factorization n p

/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/


/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/

lemma product_of_primeExponent (n p : ℕ) :
    n = p ^ primeExponent n p * remainder n p := by
    simp
theorem q_div_n_div_p_pow (n p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h_pq : p ≠ q) (hqn : q ∣ n) : q ∣ remainder n p := by
  by_cases hn : n = 0
  · subst hn
    simp [remainder, maxPowDvdDiv]
  · have hq_dvd_mul : q ∣ p ^ primeExponent n p * remainder n p := by
      rw [← product_of_primeExponent n p]
      exact hqn
    cases hq.dvd_mul.mp hq_dvd_mul with
    | inl h_qp_pow =>
      have h_qp : q ∣ p := hq.dvd_of_dvd_pow h_qp_pow
      have h_eq : q = p := (hp.eq_one_or_self_of_dvd q h_qp).resolve_left hq.ne_one
      exact (h_pq h_eq.symm).elim
    | inr h_q_goal =>
      exact h_q_goal




theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
    use remainder n p
    conv => lhs; rw [product_of_primeExponent n p]

/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/

theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
  constructor
  · intro mp
    by_cases hpq : p = q
    · exact Or.inl hpq
    · right
      exact q_div_n_div_p_pow n q p hq hp (Ne.symm hpq) mp
  · intro mpr
    rcases mpr with heq | hdvd
    · rw [heq]; exact hqn
    · have hdvd' : remainder n q ∣ n := by
        refine ⟨q ^ primeExponent n q, ?_⟩
        conv_lhs => rw [product_of_primeExponent n q]
        ring
      exact hdvd.trans hdvd'

theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  have he : primeExponent n p = n.factorization p := by
    rw [Nat.factorization_def n hp]
    exact congrFun (congrFun padicValNat.padicValNat_eq_maxPowDiv p) n
  intro hdvd
  obtain ⟨m, hm⟩ := hdvd
  apply Nat.pow_succ_factorization_not_dvd hn hp
  refine ⟨m, ?_⟩
  have h1 := product_of_primeExponent n p
  rw [he] at h1
  calc n = p ^ n.factorization p * remainder n p := h1
    _ = p ^ n.factorization p * (p * m) := by rw [hm]
    _ = p ^ (n.factorization p + 1) * m := by rw [pow_succ]; ring

lemma primeExponent_mul {n m p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
    primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
  have key : ∀ a : ℕ, primeExponent a p = a.factorization p := fun a => by
    rw [Nat.factorization_def a hp]
    exact congrFun (congrFun padicValNat.padicValNat_eq_maxPowDiv p) a
  rw [key, key, key, Nat.factorization_mul hm hn]
  rfl

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  by_cases hp : p.Prime
  · have he : primeExponent n p = n.factorization p := by
      rw [Nat.factorization_def n hp]
      exact congrFun (congrFun padicValNat.padicValNat_eq_maxPowDiv p) n
    rw [he]
    exact Nat.factorization_eq_zero_of_not_dvd hcoprime
  · sorry -- non-prime p case: depends on what maxPowDvdDiv does for non-prime p; need the actual def
theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have hr : remainder n q ≠ 0 := by
    intro h0
    apply hn
    have h1 := product_of_primeExponent n q
    rw [h0, mul_zero] at h1
    exact h1
  have hqk : q ^ primeExponent n q ≠ 0 := pow_ne_zero _ hq.pos.ne'
  have hsplit : primeExponent n p
      = primeExponent (q ^ primeExponent n q) p + primeExponent (remainder n q) p := by
    have h1 := product_of_primeExponent n q
    calc primeExponent n p
        = primeExponent (q ^ primeExponent n q * remainder n q) p := by rw [← h1]
      _ = primeExponent (q ^ primeExponent n q) p + primeExponent (remainder n q) p :=
          primeExponent_mul hqk hr hp
  have hzero : primeExponent (q ^ primeExponent n q) p = 0 := by
    apply primeExponent_coprime
    intro hpdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hpdvd))
  rw [hsplit, hzero, zero_add]

theorem exercise5 (n m : ℕ) :
    (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
  intro p hp
  rw [Nat.support_factorization] at hp ⊢
  simp only [Nat.mem_primeFactors] at hp ⊢
  obtain ⟨hpp, hpdvd, hgcdne⟩ := hp
  have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_left n m)
  have hpm : p ∣ m := hpdvd.trans (Nat.gcd_dvd_right n m)
  refine ⟨hpp, Nat.dvd_add hpn hpm, ?_⟩
  intro hcontra
  apply hgcdne
  rcases Nat.add_eq_zero.mp hcontra with ⟨hn0, hm0⟩
  simp [hn0, hm0]

theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  ext p
  simp only [Finset.mem_union, Nat.support_factorization, Nat.mem_primeFactors]
  constructor
  · rintro (⟨hpp, hpn, -⟩ | ⟨hpp, hpm, -⟩)
    · exact ⟨hpp, hpn.trans (Nat.dvd_lcm_left n m), Nat.lcm_ne_zero hn hm⟩
    · exact ⟨hpp, hpm.trans (Nat.dvd_lcm_right n m), Nat.lcm_ne_zero hn hm⟩
  · rintro ⟨hpp, hpdvd, -⟩
    have hlcm_dvd : Nat.lcm n m ∣ n * m := Nat.lcm_dvd ⟨m, rfl⟩ ⟨n, mul_comm n m⟩
    rcases (Nat.Prime.dvd_mul hpp).mp (hpdvd.trans hlcm_dvd) with h | h
    · exact Or.inl ⟨hpp, h, hn⟩
    · exact Or.inr ⟨hpp, h, hm⟩
end Sheet3
