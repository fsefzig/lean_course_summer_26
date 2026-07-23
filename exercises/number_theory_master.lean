import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.Divisors


-- Start with the set {k : ℕ | k < n ∧ Nat.gcd k n = 1} (abbrev means U is notation for the rhs)
abbrev U n := ((Finset.range n).filter (fun k => Nat.gcd k n = 1))

def φ : ℕ → ℕ := fun n => ((Finset.range n).filter (fun k => Nat.gcd k n = 1)).card

theorem φ_product {n : ℕ} (h : n ≠ 0) : φ n =
  n * ∏ p ∈ (n.factorization.support), (1 - (1/p : ℚ)) := by
  sorry

theorem φ_sum_divisors {n : ℕ} (h : n ≠ 0) : ∑ d ∈ Nat.divisors n, φ d = n := by
  sorry

lemma φ_prime_power {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : φ (p ^ k) = p ^ k - p ^ (k - 1) := by
  sorry

lemma φ_mul_coprime {m n : ℕ} (h1 : m ≠ 0) (h2 : n ≠ 0) (h3 : Nat.gcd m n = 1) :
    φ (m * n) = φ m * φ n := by
  sorry

lemma bezout {a b : ℤ} (h : Int.gcd a b = (1 : ℤ)) : ∃ x y, a * x + b * y = 1 := by
  use Int.gcdA a b, Int.gcdB a b
  calc
    a * Int.gcdA a b + b * Int.gcdB a b = Int.gcd a b := by
      exact (Int.gcd_eq_gcd_ab a b).symm
    _ = 1 := by
      exact h

lemma crt_corr {n m x : ℤ} (hcoprime : Int.gcd n m = 1) (hn : ∃ a, a * x % m = 1)
  (hm : ∃ b, b * x % n = 1) : ∃ c, c % m * n = 1 := by  sorry
