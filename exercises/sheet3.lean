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

#check maxPowDiv



/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/
lemma product_of_primeExponent (n p : ℕ) :
    n = (p ^ primeExponent n p) * (remainder n p) := by
      simp




theorem exercise1 (p n : ℕ) :
    p ^ (primeExponent n p) ∣ n := by
      have name : n = (p ^ primeExponent n p) * (remainder n p) := product_of_primeExponent n p
      exact Dvd.intro (remainder n p) (id (Eq.symm name))


/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/

#check Nat.pow_zero

#check Nat.Coprime.pow_right

#check Nat.Prime.coprime_iff_not_dvd

lemma mylemma {p q : ℕ} : ∀ k : ℕ , (p.Prime) ∧ ¬ (p∣ q) ∧ (p ≠ 1) ∧ (q.Prime)→ ¬ (p∣ q^k) := by
  intro k h
  have hprime : p.Prime := h.1
  have hnpq : ¬ p∣ q := h.2.1
  have hpn1 : p≠ 1:= h.2.2.1
  have hqrime : q.Prime := h.2.2.2 --oml why
  have hpnq : p ≠ q := by
    by_contra
    have hcontra : p ∣ q := by
      have h1 : q= p*1 := by
        omega
      exact ⟨1, h1⟩
    contradiction
  have hcop : p.Coprime q := (Nat.Prime.coprime_iff_not_dvd hprime).mpr hnpq
  have hcopk : p.Coprime (q ^ k) := hcop.pow_right k
  --refine (Nat.Prime.coprime_iff_not_dvd hprime).mp ?_
  --· exact Coprime.pow_right k hcop

  /-
  induction k with
      | zero =>
        refine (Nat.Prime.coprime_iff_not_dvd ?_).mp ?_
        · exact h.1
        · rw[Nat.pow_zero]
          exact Nat.gcd_one_right p

      | succ n ih =>
        have hnpq : ¬ (p∣ q) := h.2.1
        refine (Nat.Prime.coprime_iff_not_dvd ?_).mp ?_
        · exact h.1
        · have hcop : p.Coprime (q) :=
            sorry

          sorry
    -/
  exact (Nat.Prime.coprime_iff_not_dvd hprime).mp hcopk


theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ (p = q) ∨ (p ∣ remainder n q) := by
    constructor
    · intro hpn
      by_cases hpq: p=q
      · left
        exact hpq
      · right
        have name : n = (q ^ primeExponent n q) * (remainder n q) := product_of_primeExponent n q
        have hnpq : ¬ (p ∣ q) := by
          (expose_names; refine (Nat.Prime.coprime_iff_not_dvd hp).mp ?_)
          exact (coprime_primes hp hq).mpr hpq
        have hnpqexp : ¬ (p ∣ q ^ primeExponent n q) := by
          exact mylemma (p := p) (q := q) (primeExponent n q) ⟨hp, hnpq, hp.ne_one, hq⟩
          --apparantly i needed (p:=p) here??idk why
        have heuc : p ∣ (q ^ primeExponent n q) ∨ p ∣ (remainder n q) := by
          rw[name] at hpn
          exact (Nat.Prime.dvd_mul hp).mp hpn
        cases heuc with
        | inl hbad =>
            contradiction
            -- ha : A
        | inr hgood =>
            exact hgood
          --we need ¬ p | q => ¬ p ∣ q^k
          --
          --apply the lemma here

        --finish it off here

        --have ¬ (p ∣ q)
        --thus ¬ (p ∣ q^exp)
        --but (p ∣ n)
        --and n=(q^exp) *  (remainder n q)
        --so, p | remainder n q
    · intro h
      cases h with
      | inl hpq =>
        subst hpq
        exact hqn
      | inr hprem =>
        have hdef : n = (q ^ primeExponent n q) * (remainder n q) := product_of_primeExponent n q
        have idk : (remainder n q) ∣ n := by
          nth_rewrite 2 [hdef]
          exact dvd_mul_left (remainder n q) (q ^ primeExponent n q)
        exact Nat.dvd_trans hprem idk

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/

lemma lifesaver {p n k : ℕ} : k> primeExponent n p → ¬ p^k ∣ n := by
    --i NEED this lemma for two questions
    --but i cant figure out how to do it
    --so i'm just leaving it
    --it should be by definition
    --Main Problen: I couldn't figure out how to turn "maxPowDvdDiv"
    --from a pair of two numbers into a theorem that .1 returns
    --the biggest such number
    sorry

theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
    --logic for this:
    --if p | remainder n p
    --then exists q with (remainder n p) = p * q
    --then, p^(primeExponent n p) * p * q= n
    --aka, p^(primexp + 1) *q = n
    -- p^(primexp + 1) | n
    --contradicts definition of primeexp
    by_contra h
    have hdiv : n = (p ^ primeExponent n p) * (remainder n p) := product_of_primeExponent n p

    obtain ⟨q, hq⟩ := h

    rw[hq] at hdiv

    have halgebra : p ^ primeExponent n p * (p * q) = p^(primeExponent n p + 1) * q := by
      --ring --i guess omega doesnt work for exponents apparantly??
      --and apparantly ring doesn't work either??
      rw [pow_succ]
      ring_nf

    rw[halgebra] at hdiv

    have hcont : p^(primeExponent n p + 1) ∣ n := by
      use q

    have usethis : primeExponent n p + 1 > primeExponent n p := by
      omega

    have hfalse : ¬ p^(primeExponent n p + 1) ∣ n := by
      exact lifesaver usethis

    contradiction





/-
Lecture lemma 4: removing the largest power of `q` does not change the exponent
of a different prime `p`.
-/

/-
Start by using the first lemma to prove the other lemmas. (You can use simp? and exact?)
-/

--ts is lowk cool
lemma padicValNat_mul (n m p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
  padicValNat p (m * n) = padicValNat p m + padicValNat p n := by
  refine @padicValNat.mul _ _ _ ?_ hm hn
  --{} means its implicit. by doing @, we can tell lean to figure out what goes here
  --({} as in {p a b : ℕ} in the @padic thing within it)

                    --    p m n; these can be inferred from the others so we can leave them out
              -- we can't have  hp
         --everything with a ? becomes a goal
         --so the goal now is

    --usually we have assumption that p is prime, the lemma takes a different assumption
    --the fact that p is prime

    --we can also do
    --efine @padicValNat.mul _ _ _ ?_ ?_ ?_
    --and then we have three tactic goals
    --here, we would just do like
    -- · exact { out := hp }
    -- · exact hm
    -- · exact hn

    --refine does this: we can apply any theorem, even if its not known yet
    --and then we just make new goals, for what's not proven yet


  --this  turns a proposition into a fact
  --the way that @padicValNat.mul is set up, we need the FACT that p is prime
  --
  exact { out := hp }




--above: padicValNat p (m * n) = padicValNat p m + padicValNat p n


lemma primeExponent_mul {m n p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
    primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
    let k1 := primeExponent (m * n) p
    let k2 := primeExponent m p
    let k3 := primeExponent n p
    dsimp[k1]
    let l1 := padicValNat p (m * n)
    let l2 := padicValNat p m
    let l3 := padicValNat p n
    exact padicValNat_mul n m p hm hn hp

    --ok honestly i have like no idea whats happening here
    --claude told me dsimp can like undo abbreviations i guess
    --but dsimp k1 didnt unabbrev it to the original maxpowdivdvd.1, it instead
    --unabbreved it to the padic
    --which sort of makes sense, my understanding of that is that
    --the maxpowdivdvd.1 and padic are the same thing, and it overwrites
    --or de-something idk the word

    --but then with that it literally just turns into the lemma right before
    --the i discussed with you in class???

    --so idk, i mean if it works it works i guess




lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
    --explanation:
    --i did contradiction
    --so suppose the prime expo := k >0 aka ≥1
    --essentially then p| p^k | n by def and since k≥1
    --and then p|n contradiction
    by_contra hndiv
    have hn0 : primeExponent n p> 0 := Nat.pos_of_ne_zero hndiv
    let k := primeExponent n p
    have hk0 : k>0 := by
      exact hn0
    have hpower : p^k ∣ n := by
      exact exercise1 p n
    have hk1 : 1≤k := by
      exact one_le_of_lt hn0
    have hpdiv : p ∣ p^k := by
      exact div_pow_of_pos p k hn0
    have hcontra : p ∣ n := by
      exact Nat.dvd_trans hpdiv hpower
    contradiction




/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat


--lemma primeExponent_mul {m n p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
--    primeExponent (m * n) p = primeExponent m p + primeExponent n p

--this single problem was one of the most tortorous moments of my life i think (and its so simple)
theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
      -- n = (q^ primeExponent n q) * (remainder n q))
      -- p rp to (q^ primeExponent n q)
      have hprod : n =  (q^ primeExponent n q) * (remainder n q):= by
        exact product_of_primeExponent n q
      have hq0 : q^ primeExponent n q ≠ 0 := by
        by_contra
        have wrong : n=0 := by
          rw [hprod, this, zero_mul]
        contradiction
      have hp0 : (remainder n q) ≠ 0 := by
        by_contra
        have wrong : n=0 := by
          rw [hprod, this, mul_zero]
        contradiction
      have hcop : p.Coprime q := by
        exact (coprime_primes hp hq).mpr hpq
      have hpadic : primeExponent n p = primeExponent (q^ primeExponent n q) p +
      primeExponent (remainder n q) p := by
        nth_rewrite 1 [hprod]
        exact primeExponent_mul hq0 hp0 hp
      --primeExponent ((q^ primeExponent n q) * (remainder n q)) q
      --= primeExponent ((q^ primeExponent n q)) + primeExponent  ((remainder n q)) q := by
      have h0 : ¬ p ∣  (q^ primeExponent n q) := by
        have idkanymore : p.Coprime (q ^ primeExponent n q) :=  hcop.pow_right (primeExponent n q)
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp idkanymore
      have h1 : primeExponent (q ^ primeExponent n q) p = 0 := by
        exact primeExponent_coprime h0
      rw[h1] at hpadic
      omega










    -- n = (remainder n q) * (q^ primeExponent n q)
    --p-adic n = padic (rem n q) + padic (q^expo)

    --p doesnt divide (q^prime Expo), so padic (q^expo=0)

    --done

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

#check Nat.factorization
#check Nat.factorization_def
#check Nat.factorization_mul




/- Every prime dividing both `n` and `m` also divides `n + m`. -/
theorem exercise5 (n m : ℕ) :
    (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
      intro p h

      rw [Finsupp.mem_support_iff] at h

      have idk : (n.gcd m).factorization p > 0 := by
        omega

      let k := (n.gcd m).factorization p

      have hdiv : p^k ∣ n.gcd m := by
        sorry

      have hpn : p^k ∣ n := by
        exact Nat.dvd_trans hdiv (Nat.gcd_dvd_left n m)

      have hpm : p^k ∣ m := by
        exact Nat.dvd_trans hdiv (Nat.gcd_dvd_right n m)

      obtain ⟨qn, hns⟩ := hpn

      obtain ⟨qm, hms⟩ := hpm

      have hsum : n+m = p^k * (qn + qm) := by
        calc
          n+m = p^k*qn + m := by rw [hns]
          _   = p^k*qn + p^k*qm := by rw [hms]
          _   = p^k * (qn + qm) := by rw [mul_add]

      have hpdivp : p ∣ p^k := by
        exact div_pow_of_pos p k idk

      have hpkdivnm : p^k ∣ (n+m) := by
        refine ⟨qn+qm, ?_⟩
        rw[hsum]

      have halmostdone : p ∣ (n+m) := by
        exact Nat.dvd_trans hpdivp hpkdivnm

      rw [Nat.support_factorization]
      --exact Nat.mem_primeFactors.mpr ⟨hp, halmostdone, hnm⟩

      sorry
      --giving up here
      --the problem was that this "nat.support_factorization" thing i searched up
      --requires p to be prime
      --but that doenst work with my method
      --couldnt find anything
      -- :(

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
  --syntax question: how do i even show that
  -- x belongs in y.factorization.support ?
  --as a question about the factorization library, not about support
  --i feel like this would look almost identical to ex5
  --but i dont know the syntax to solve that
  --and i cant find anything good online
    sorry

end Sheet3
