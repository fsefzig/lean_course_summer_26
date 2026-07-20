import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  nth_rewrite 1 [h, ← one_mul k, Nat.mul_lt_mul_right]
  · exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨fun hd' => hn (mul_eq_zero_of_left hd' k ▸ h), hd⟩
  · exact Nat.zero_lt_of_ne_zero fun hk' => hn (mul_eq_zero_of_right d hk' ▸ h)

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  exact fun hd' => hd (Nat.eq_one_of_dvd_one (Nat.add_sub_cancel_left n 1 ▸ Nat.dvd_sub hd' h))

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  by_cases hnp : (Nat.factorial n + 1).Prime
  · exact ⟨Nat.factorial n + 1, ⟨hnp, Nat.lt_add_one_of_le (Nat.self_le_factorial n)⟩⟩
  · use Nat.minFac (Nat.factorial n + 1)
    constructor
    · exact Nat.minFac_prime (Nat.add_one_ne_add_one_iff.mpr (Nat.factorial_ne_zero n))
    · by_contra h
      impossible by simp
      /-
        to not lean on simp:
        say (n.factorial + 1).minFac ≤ n
        and then say (n.factorial + 1).minFac + c = n
        so minFac is n - c
        show that 2 ≤ n - c ≤ n, and then that m | n.factorial when 2 ≤ m ≤ n
        use exercise1 to show ¬(n - c | n.factorial + 1) and get contradiction
      -/

end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
variable {I : Finset α} {f : α → ℕ}

#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact Eq.substr Finset.sum_empty (dvd_zero d)
  | insert a s hs f => exact Eq.substr (Finset.sum_insert hs) (Nat.dvd_add (h a) f)

end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
  A decent guess is I : Finset ℕ, I would assume.
  A multiset of naturals is just a function from ℕ -> ℕ, so that's another way of looking at it.
How can you state the theorem that every natural number has a (unique) prime factorization?
  It's easier to state it in two parts: existence and uniqueness.
  For existence, it would be a theorem with input n : ℕ and output I : Finset ℕ.
  For uniqueness, it would be a theorem with inputs n : ℕ, n : ℕ -> I : Finset ℕ,
    n : ℕ -> J : Finset ℕ and output I : Finset ℕ = J : Finset ℕ .
  Of course, I haven't checked if this works, but it seems like it would be something like this.
How would you prove it?
  I think I would try to follow the standard proof; go through prime/nonprime
    cases for existence and use contradiction for uniqueness.
  Maybe there's a more straightforward way in Lean, but familiarity is worth it, I feel.
-/
