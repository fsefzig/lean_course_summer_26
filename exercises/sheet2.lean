import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

#check Nat.factorial
#check Nat.factorial 5
#check (5 : ℕ).factorial


/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  --fix some k
  --if d≠1 and d : Nat then d≥2
  -- d≥2>1
  -- n=dk ≥2k > 1*k => k<n
  -- do this last step by contradiction?

  by_contra hnot
  rw [Nat.not_lt] at hnot
  rw [h] at hnot
  --note that division doesnt exist in natural numbers

  --goal: show d>1
  --then multiply both sides by k

  by_cases hs: d=0
  · rw[hs] at h
    rw [zero_mul] at h
    contradiction
  · have hd0 : d > 0 := Nat.pos_of_ne_zero hs
    --

    by_cases hk : k=0
    · rw[hk] at h
      rw [mul_zero] at h
      contradiction
    · have hk0 : k > 0 := Nat.pos_of_ne_zero hk
      have hd1 : d ≥ 1 := Nat.succ_le_of_lt hd0

      by_cases hdg1 : d=1
      · contradiction
      · have hdgt1 : d > 1 := Nat.lt_of_le_of_ne hd1 (Ne.symm hdg1)

        have h' : 1 * k < d * k := mul_lt_mul_of_pos_right hdgt1 hk0
        rw[one_mul] at h'

        contradiction
        --contradiction doesn't work here for some reason, even though
        --h' and hnot are literal opposites of each other
        --I checked it and everything else should be fine, why isn't this working?

        --note: contradiction only works for EXACTLY h and ¬ h
        --omega and linarith can do this fine

        omega





    --have h : d * k < 0 * k := mul_lt_mul_of_pos_right hd0 hc

  --mul_lt_mul_of_pos_right
  --b<c and 0<a -> b times a < c time a

lemma lemma1 {a b : Nat} : 1 = a * b  →  a=1 ∧ b =1:= by
  intro h
  constructor
  · have ha : a ∣ 1 := by
      rw [h]
      exact Nat.dvd_mul_right a b
    exact Nat.eq_one_of_dvd_one ha
  · rw[mul_comm] at h
    have hb : b ∣ 1 := by
      rw [h]
      exact Nat.dvd_mul_right b a
    exact Nat.eq_one_of_dvd_one hb



theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  by_contra hn1
  obtain ⟨k1, hk1⟩ := h
  obtain ⟨k2, hk2⟩ := hn1
  rw [hk1] at hk2


  by_cases hg : k1≥k2
  · let k3 := k1-k2

    have hc : k1 = k2 + k3 := by
      change k1 = k2 + (k1 - k2)
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel hg).symm

    rw [hc] at hk2

    rw[mul_add] at hk2

    nth_rewrite 2 [← Nat.add_zero (d * k2)] at hk2
    rw [Nat.add_assoc] at hk2
    have h' : d * k3 + 1 = 0 := Nat.add_left_cancel hk2
    have hdk3 : d*k3≥0 := Nat.zero_le (d*k3)
    have hneg : d*k3 + 1 ≠ 0 := Nat.succ_ne_zero (d*k3)
    contradiction


  · rw[not_le] at hg
    let k3 := k2-k1


    have hk3 : k3 = k2-k1 := by
      omega --i gave up trying to prove this technically
      --since i searched up the one for above
      --but it didnt work here since i need like k1.succ instead of k1 ig
      --i lowkey dont want to spend all my time on these annoying addition things

    have hkadd : k2 = k1+k3 := by
      omega --same deal

    rw [hkadd] at hk2
    rw [mul_add] at hk2

    have hk2' : 1 = d*k3 := Nat.add_left_cancel hk2
    have hnew : d=1 ∧ k3=1 := lemma1 hk2'

    have hd1 : d=1 := hnew.1
    have hk31 : k3=1 := hnew.2

    contradiction

#check Nat.dvd_factorial

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  --look at the number n!+1

  --note that k | n! (by definition) forall k=1,2...n
  --thus, not k|n! forall k=1...n
  --by definition, either n!+1 is prime (done) or there's a prime that divides it
  --in the second case, the prime cannot be any of 1,2,...n
  --thus, that prime is >n+1
  intro n
  --imported mathlib for ts

  have h : ∀ k, 1<k ∧ k ≤ n → ¬ (k ∣ n.factorial +1) := by
    intro k hkn
  --  by_cases h0 : n=0
  --  · sorry
    --· --have hn : n > 0 := Nat.pos_of_ne_zero h0
      --have hfac : n ∣ n.factorial := Nat.dvd_factorial hn (Nat.le_refl n)

    have hk1 := hkn.1
    have hkpos : 0 < k := by
      omega --same deal with omega as before

    have hknot1 : k≠1 := by
      omega

    have hdiv : k ∣ n.factorial := by
      exact Nat.dvd_factorial hkpos hkn.2

    --need to show k≠1
    have hnot : ¬ k ∣ n.factorial+1 := exercise1 (d := k) (n := n.factorial) hknot1 hdiv

    exact hnot


  --logic: we showed that n!+1 has no factors among 1,2,...,n
  --now, two cases. first case is if n!+1 is prime. then we're done
  --if it's not prime, then it must have a prime factor.
  --what we need to show now is that no prime factor of N can be ≤n

  have hprimes_bigger_than_n  {k : ℕ} : k.Prime ∧ k ∣ n.factorial + 1 → n<k := by
    intro hkprime
    by_cases hle : k≤n
    · have hpgt1 : 1 < k := Nat.Prime.one_lt hkprime.1

      have hcontra : ¬ (k ∣ n.factorial +1) := h k ⟨hpgt1, hle⟩

      have hcontraotherthing : k ∣ n.factorial +1 := hkprime.2
      contradiction
    · rw[not_le] at hle
      exact hle


  let x := n.factorial + 1

  by_cases hxprime : (n.factorial + 1).Prime
  · have hnfac : n.factorial ≥ n := by
      have hfactorialbiggerthan0 : (n-1).factorial > 0 := by
        exact Nat.factorial_pos (n-1)

      have hfactorialge0 : (n-1).factorial ≥1 := by
        exact Nat.succ_le_of_lt hfactorialbiggerthan0

      have completedthingy : n.factorial ≥ n := by
        --exact Nat.mul_le_mul_right n hfactorialge0
        sorry
        --I DONT GET WHY THIS DOESNT WORK???
        --Some help please
        --this should be the only questionable part of the proof
        --everything else seems fine-ish

      exact completedthingy





      --n!≥1
      --(n+1)!≥n+1

      /-
      induction n with
      | zero =>
        rw [Nat.factorial_zero]
        exact Nat.zero_le 1

      | succ n ih =>
        have hnisbiggerthan1 : n! ≥1 := by

        sorry
        --suppose n!≥n
        --then (n+1)!≥n+1

        -- n!≥n≥1
        -- (n+1)!≥(n+1)!
      -/

    have hnfacg : n.factorial +1 > n := by
      exact Nat.lt_succ_of_le hnfac
    use n.factorial+1

  · by_cases hn1 : n=1 --btw this is completely useless
    --i think
    --but i dont wanna remove it and risk breaking it
    · rw[hn1] at hxprime
      contradiction
    ·--section not written by me
      have hfacne : n.factorial ≠ 0 := Nat.ne_of_gt (Nat.factorial_pos n)

      have hfac1 : n.factorial + 1 ≠ 1 := by
        intro h
        have hzero : n.factorial = 0 := by
          exact Nat.add_right_cancel h
        exact hfacne hzero
      --end section

      have hprime : Nat.Prime (Nat.minFac (n.factorial + 1)) := by
        exact Nat.minFac_prime hfac1

      --current status:
      --assumed n≠1
      --lowkey never used that
      --chat got that n.factorial+1 ≠1
      --so now we can apply
      --this is a nightmare lmao


      have thisprimeisbigerthan_n : n< Nat.minFac (n.factorial+1) := by

        have hkdiv : Nat.minFac (n.factorial+1) ∣ n.factorial + 1 := by
          exact Nat.minFac_dvd (n.factorial + 1)
        have hkn : n < Nat.minFac (n.factorial+1) := hprimes_bigger_than_n ⟨hprime, hkdiv⟩
        exact hkn

      --uhh where tf are we now

      --hprime : Nat.Prime (n.factorial + 1).minFac
      --min factor of n.factorial+1 is known as prime

      --thisprimeisbigerthan_n : n < (n.factorial + 1).minFac
      --that prime is bigger than n

      --so just use that then

      use (n.factorial + 1).minFac

      --done!!!!





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

#check Finset.sum_empty

-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty =>
    rw[Finset.sum_empty]
    exact Nat.dvd_zero d
  | @insert a s ha hs =>
    have hdividess : d ∣ (f a) := h a
    rw [Finset.sum_insert ha]
    exact Nat.dvd_add hdividess hs

end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?

idk
-/
