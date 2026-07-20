import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

/-
Exercise 0:

Word proof (before I turn it into Lean):

For natural numbers d, k, n, with n ≠ 0 and d ≠ 1, and n = d * k, prove that k < n.

Let's first assume that k ≥ n. That means n ≤ k. For n = d * k to hold,
that means when d is multiplied by k, the result is smaller than or
equal to k.

Zero_one_idea: Since d is a natural number, d must be either 0 or 1,
because when any natural number k is multiplied by a natural number
2 or greater, the result is greater than k.
  Case d = 0:
    n = 0 * k
    n = 0
    contradiction, since we were given n ≠ 0
  Case d = 1:
    contradiction, since we were given d ≠ 1
Since it is not possible that k ≥ n, it must be true that k < n.

Actually, it might be easier to do the Zero_one_idea backwards. Having d ≠ 0, d ≠ 1, k ≠ 0, k < dk.

So I guess we need to show k ≠ 0 first, so k > 0. Then, we can split cases on d.

I had to do outside research to find the stuff I needed, so yippee!


-/

#check Nat.succ_mul
#check Nat.lt_add_of_pos_left
#check Nat.le_add_left

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have hk : k ≠ 0 := by
    intro hk
    rw [hk] at h
    rw [mul_zero] at h
    exact hn h
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  rcases d with _ | d
  · -- zero case
    rw [h] at hn
    rw [Nat.zero_mul] at hn
    contradiction
  · -- successor case. Must split again since d ≠ 1
    rcases d with _ | d
    · -- d = 0 + 1 (obviously false)
      rw [Nat.zero_add] at hd
      contradiction
    · -- the + 1 + 1 case
      rw [h]
      rw [Nat.succ_mul]
      rw [Nat.succ_mul] -- Now we have a very obviously true statement but we have to prove it.
      have hkk : k < k + k := by
        exact Nat.lt_add_of_pos_left hkpos
      have hI'velostmymind : k < d * k + k + k := by -- If k<k+k, k < something bigger than k + k
        apply lt_of_lt_of_le hkk
        rw [Nat.add_assoc]
        exact Nat.le_add_left (n := k + k) (m := d * k)
      exact hI'velostmymind


/-
Exercise 1:

Word proof (before I turn it into Lean):

Given natural numbers d, n, with d ≠ 1, and that d divides n, prove that
d does not divide n + 1.

If d does divide n + 1, since it also divides n, it must divide their difference
(n + 1) - n. That means d must divide 1. The only divisor of 1 is 1. Therefore,
d = 1. But we were given d ≠ 1, so that is a contradiction.

Since with the given constraints, is not possible that d divides n + 1,
we can conclude ¬ (d ∣ n + 1).


-/


theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  by_contra hcon --assuming d divides both n + 1 and n
  have hdiff : d ∣ (n + 1) - n := by
    exact Nat.dvd_sub hcon h -- d divdes (n + 1) - n
  have hone : d ∣ 1 := by
    simpa using hdiff
  have : d = 1 := Nat.dvd_one.mp hone --d has to be 1 since d | 1
  exact hd this -- d = 1 and d ≠ 1 contradict


/-
Infinitely_many_primes:

Recall: Theorems I've already proved earlier in the document:

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n
theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1)

Word proof (before I turn it into Lean):

For all natural numbers n, there exists a natural number p that is prime and greater than n.

Let's assume there is some finite natural number n that is greater than every prime number.
That means the amount of prime numbers is finite because it is less than or equal to n.
We can list all the prime numbers p1, p2, p3 ... pk, where pk is the biggest prime in existence.
Consider the product of this finite set of prime numbers. Call that result j.

Since j + 1 is larger than pk, it cannot be prime. It must be composite.
By the definition of composite, j + 1 has a prime factor pm. Since the list p1 ... pk
contains every prime number, pm must be part of that list. And since j is the product
of every element in that list, pm divides j. Since pm ≠ 1, if pm divides j, it cannot
divide j + 1, by exercise 1. That is a contradiction.

Since there does not exist a natural number n such that there is no prime
greater than n, for every natural number n, there has got to be a prime greater than n.


WAIT!!! Computers HATE the infinite set of all primes. That is NOT type theory!!
I guess we can use factorials?!?!?!?!!??

-/


theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  let N := Nat.factorial n + 1
  by_contra hcon -- assume there does NOT exist a prime p that's greater than n

  sorry
  /-
  I have no clue what to do next. I guess we have to say p ≤ n, and that should come from
  ¬ p > n. But the "∃" symbol caused a ton of problems and it turned p into a sorry.
  So idk???
  -/

end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

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

/-
In type alpha, we are given I is a finite subset
of alpha. f is a function from type alpha to natural numbers. d is a natural number.
Given hypothesis h: For all x, d divides f of x.
Prove: d divides the sum of all natural-numberified (by f) elements i in I

IN HUMAN WORDS: If d divides every natural number in a set, it divides
the sum of all the natural numbers in that set.


Anyway, I wonder if dvd_add is cheating because it literally says that if a|b
and a|c, a|b+c. But guess what? I used it, lol.

-/

set_option linter.flexible false
set_option linter.unusedDecidableInType false

theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih => -- show that when you insert an element, it still works
      simp [ha]
      exact dvd_add (h a) ih


end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?


We can say:

For a natural number n such that n ≠ 0, and n ≠ 1, with a prime factorization j = p1 * p2 * ... pk,
where p1 through pk are listed in order from smallest to greatest (ie 120 = 2 * 2 * 2 * 3 * 5),
¬ ∃ a natural number k such that k ≠ 0, and k ≠ 1, whose prime factoriation is also j.

We can prove this by creating a bijection from each natural number to its prime factorization.
Probably use functions or something.
Since this is a rule, it works in type theory. Yippee!

-/
