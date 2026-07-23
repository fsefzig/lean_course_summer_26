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

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

open Nat

abbrev primeExponent (n p : ℕ) : ℕ := (maxPowDvdDiv p n).1

abbrev remainder (n p : ℕ) : ℕ := (maxPowDvdDiv p n).2

#print maxPowDvdDiv

/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/

#check fst_maxPowDvdDiv


lemma product_of_primeExponent (n p : ℕ) :
    n = p ^ primeExponent n p * remainder n p := by
    simp only [fst_maxPowDvdDiv, snd_maxPowDvdDiv, pow_padicValNat_mul_divMaxPow] -- Haha, the power of simp? !


theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
    simp only [fst_maxPowDvdDiv]
    exact pow_padicValNat_dvd


/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.


Why it works in regular words:

I guess we should look at what remainder n q means.
By definition, if we "factorize" n into n = q ^ k * r, where k is the max power and r is the remainder n q,
it returns r. That step was really annoying since I had to go to the Lean library and scroll through all
maxPowDvdDiv theorems until I found pow_padicValNat_mul_divMaxPow which basically does that.

So I guess we should constructor and split the forward and backwards case up:

Forward: If p divides n, that means p divides q^k * r. Since p is prime, it divides q^k or r.
Let's call this point Checkpoint A so I can remember where in the proof I'm at.
We can split the cases:
• If p divides q^k, since p is prime, p divides q. Since q is prime, for p to divide q, p either equals 1 or q. But 1 is not prime, so p = q
• If p divides r, that goes immediately to the p divides remainder n q we are trying to prove.

Backward: (Let's call this Checkpoint B.)
If p = q, since we have q divides n, by substitution, p divides n.

If p divides remainder n q, we use that n = q^k * r which tells us r divides n.
So if p divides r and r divides n, p divides n (transitivity).

-/



theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
  constructor
  · intro hpn
    have hfac : q ^ padicValNat q n * remainder n q = n := by
      simpa [remainder] using pow_padicValNat_mul_divMaxPow q n
    rw [← hfac] at hpn
    apply hp.dvd_mul.mp at hpn -- Checkpoint A
    rcases hpn with hpqpow | hprem
    · left
      exact prime_eq_prime_of_dvd_pow hp hq hpqpow
    · right
      exact hprem
  · intro h -- Checkpoint B
    cases h with
    | inl hpq =>
      rw [hpq]
      exact hqn
    | inr hprem =>
      have hfac : q ^ padicValNat q n * remainder n q = n := by -- Haha, again
        simpa [remainder] using pow_padicValNat_mul_divMaxPow q n
      have hremdiv : remainder n q ∣ n:= by
        exact Dvd.intro_left (q ^ padicValNat q n) hfac
      exact Nat.dvd_trans hprem hremdiv


/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/

/-

Basically we're saying that if n = p ^ padic value * remainder, p cannot divide the remainder.

If p does divide the remainder, then the remainder is p * k for some natural number k.

Then, we can simplify as  n = p ^ ("padic value" + 1) * k, which is definitionally not acceptable.


-/

#check padicValNat


theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  by_contra hcon
  rcases hcon with ⟨k, hk⟩ -- breaking up the remainder as p * k
  · have hfac : p ^ padicValNat p n * remainder n p = n := by -- Haha, again!!
      simpa [remainder] using pow_padicValNat_mul_divMaxPow p n
    rw [hk] at hfac

    have hcombineexp : p ^ (padicValNat p n + 1) * k = n := by -- p raised to power higher than "padic value"
      rw [← mul_assoc] at hfac
      rw [← pow_succ] at hfac
      exact hfac

    have hpowdvd : p ^ (padicValNat p n + 1) ∣ n := by -- turning it into divisibility so it thinks the number is larger than itself
      use k
      exact Eq.symm (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd hcombineexp) p))

    sorry -- It was at this point when I went to the library to search for a theorem that says "padic value is the MAXIMUM power!!!!"

#check not_dvd_divMaxPow -- OH WAIT THERE'S SOMETHING IN THE LIBRARY I CAN USE!!!!!!!

theorem exercise3new {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by

  have hexprem : n.divMaxPow p = remainder n p := by
    exact Eq.symm (snd_maxPowDvdDiv p n)

  have honeltp : 1 < p := by
    exact Prime.one_lt hp
  apply not_dvd_divMaxPow
  · exact honeltp
  exact hn



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
  simpa [primeExponent] using padicValNat_mul n m p hm hn hp -- Prime exponent is padic value, just plug it in


#check padicValNat_eq_zero_of_mem_Ioo


lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by

  unfold primeExponent
  have hpvzero : padicValNat p n = 0 := by
    exact padicValNat.eq_zero_of_not_dvd hcoprime
  exact Eq.symm (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm hpvzero))) n))


/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/


/-
q ^ padic value * remainder n q = n (just like what we had before)

Then I guess we plug in earlier lemmas?
-/


#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have hfac : p ^ padicValNat p n * remainder n p = n := by -- Haha, again!!
    simpa [remainder] using pow_padicValNat_mul_divMaxPow p n

  rw [← hfac]
  rw [primeExponent_mul] -- Four goals, because certain things have to be true to apply primeExponent_mul. But I'm not sure what to do now.
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
 sorry

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  sorry

end Sheet3
