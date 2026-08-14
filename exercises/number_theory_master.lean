import Mathlib.Tactic
import Mathlib.Data.Int.DivMod
import exercises.sheet4
/-
This is a bonus exercise sheet. You can submit it at any point, I do not expect you to finish it by
Monday! You can work on it at your own pace, and you can choose which exercise to do.
The topic of this exercise sheet is Euler's totient function. You can prove two fundamental
relations involving the totient function.
Proving the theorems on paper is already a good exercise, I encourage you to send me your
'normal' proof before you start formalizing it.
The formalization will require you to use essentially all the tools we have developed so far!
-/

noncomputable def ϕ : ℕ → ℕ := fun n => Nat.card {k : Fin n | Nat.Coprime (k : ℕ) n}


--For future reference, we call the set of integers smaller than n and coprime to n, U(n).
abbrev U (n : ℕ) := {k : Fin n | Nat.Coprime (k : ℕ) n}

/-
The first relation expresses the totient function as a product over the prime factors of `n`.
I wrote the statement in this elegant form, however, formulated like this it involves rational numbers,
so it will be helpful to expand the product and write it in terms of natural numbers.
-/
theorem product_formula (n : ℕ) : ϕ n = n * ∏ p ∈ (Nat.primeFactors n), (1 - (1 / p) : ℚ) := by
  sorry

/-
The second relation expresses a number `n` as a sum of the totient values of all its divisors.
-/
theorem sum_formula (n : ℕ) : n = ∑ d ∈ (Nat.divisors n), ϕ d := by
  sorry

/-
The proof of both relations involves the following properties of the totient function.
-/

--PRIME
abbrev badPrimePower (p k : ℕ) :=
  {x : Fin (p ^ k) | p ∣ (x : ℕ)}

lemma coprime_prime_power_iff {p k x : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.Coprime x (p ^ k) ↔ ¬ p ∣ x := by
  rw [Nat.coprime_pow_right_iff hk]
  rw [Nat.coprime_comm]
  exact hp.coprime_iff_not_dvd

def badPrimePowerMap {p k : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) :
    Fin (p ^ (k - 1)) → badPrimePower p k := by
  intro j
  refine ⟨⟨p * j, ?_⟩, ?_⟩
  · have hk' : k = (k - 1) + 1 := by
      omega
    calc
      p * j < p * p ^ (k - 1) :=
        (Nat.mul_lt_mul_left hp.pos).2 j.isLt
      _ = p ^ k := by
        rw [hk', pow_succ]
        exact Nat.mul_comm _ _
  · exact dvd_mul_right p j

lemma badPrimePowerMap_injective {p k : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) :
    Function.Injective (badPrimePowerMap hp hk) := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg
    (fun z : badPrimePower p k => (z.1 : ℕ)) hxy
  change p * (x : ℕ) = p * (y : ℕ) at hval
  exact Nat.mul_left_cancel hval

lemma badPrimePowerMap_surjective {p k : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) :
    Function.Surjective (badPrimePowerMap hp hk) := by
  intro x
  obtain ⟨j, hj⟩ := x.property
  have hk' : k = (k - 1) + 1 := by
    omega
  have hjlt : j < p ^ (k - 1) := by
    apply Nat.lt_of_mul_lt_mul_left
    calc
      p * j = (x : ℕ) := hj.symm
      _ < p ^ k := x.1.isLt
      _ = p * p ^ (k - 1) := by
        rw [hk', pow_succ]
        exact Nat.mul_comm _ _
  refine ⟨⟨j, hjlt⟩, ?_⟩
  apply Subtype.ext
  apply Fin.ext
  change p * j = (x : ℕ)
  exact hj.symm

lemma badPrimePower_card {p k : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.card (badPrimePower p k) = p ^ (k - 1) := by
  have hbij :
      Function.Bijective (badPrimePowerMap hp hk) :=
    ⟨badPrimePowerMap_injective hp hk,
      badPrimePowerMap_surjective hp hk⟩
  calc
    Nat.card (badPrimePower p k)
        = Nat.card (Fin (p ^ (k - 1))) := by
            symm
            exact Nat.card_eq_of_bijective
              (badPrimePowerMap hp hk) hbij
    _ = p ^ (k - 1) := Nat.card_fin _

lemma ϕ_prime_power {p k : ℕ} (hp : Nat.Prime p) (hk : k > 0) : ϕ (p ^ k) = p ^ k - p ^ (k - 1) := by
  unfold ϕ
  have hbad :
      Fintype.card (badPrimePower p k) = p ^ (k - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact badPrimePower_card hp hk
  have hcop :
      ∀ x : Fin (p ^ k),
        Nat.Coprime (x : ℕ) (p ^ k) ↔ ¬ p ∣ (x : ℕ) := by
    intro x
    exact coprime_prime_power_iff hp hk
  let e :
      {x : Fin (p ^ k) | Nat.Coprime (x : ℕ) (p ^ k)}
        ≃
      {x : Fin (p ^ k) | ¬ p ∣ (x : ℕ)} :=
    {
      toFun := fun x => ⟨x.1, (hcop x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hcop x.1).mpr x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
    }
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl
    (fun x : Fin (p ^ k) => p ∣ (x : ℕ))]
  rw [hbad]
  simp

lemma ϕ_multiplicative {m n : ℕ} (h : Nat.Coprime m n) : ϕ (m * n) = ϕ m * ϕ n := by
  unfold ϕ
  have hcard :
      Nat.card (U (m * n)) = Nat.card (U n × U m) := by
    exact Nat.card_eq_of_bijective (f n m) (f_bijective h)
  rw [hcard]
  rw [Nat.card_prod]
  ring

/-
To prove multiplicativity, we construct a map f: U n*m → U n × U m, k ↦ (k mod n, k mod m).
Then use the Chinese remainder theorem and the map q_res from the lecture to show it f is bijective.
If you are familar with rings, you may notice that the proof approach below is somewhat pedestrian,
If you know about rings, you may use ZMod.chineseRemainder to prove multiplicativity.
I suggest to leave this proof for last!
-/

/-
The first step to define the values of the map f.
-/
def f_fst_val {n m : ℕ} (k : U (m * n)) : Fin n where
  val := k % n
  isLt := by
    by_cases hn : n = 0
      · subst n
        exact Fin.elim0 k.1
      · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)

def f_snd_val {n m : ℕ} (k : U (m * n)) : Fin m where
  val := k % m
  isLt := by
    by_cases hm : m = 0
    · subst m
      exact Fin.elim0 k.1
    · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)

/-
The second step is to show that f(k) lands in U n × U m,
i.e. that the values of f are coprime to n and m respectively.
-/
lemma f_fst_well_defined {n m : ℕ} (k : U (m * n)) : f_fst_val k ∈ U n := by
  change Nat.Coprime ((k : ℕ) % n) n
  have hk : Nat.Coprime (k : ℕ) (m * n) := k.property
  have hkn : Nat.Coprime (k : ℕ) n :=
    (Nat.coprime_mul_iff_right.mp hk).2
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [(Nat.mod_modEq (k : ℕ) n).gcd_eq]
  exact hkn.gcd_eq_one

lemma f_snd_well_defined {n m : ℕ} (k : U (m * n)) : f_snd_val k ∈ U m := by
  change Nat.Coprime ((k : ℕ) % m) m
  have hk : Nat.Coprime (k : ℕ) (m * n) := k.property
  have hkm : Nat.Coprime (k : ℕ) m :=
    (Nat.coprime_mul_iff_right.mp hk).1
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [(Nat.mod_modEq (k : ℕ) m).gcd_eq]
  exact hkm.gcd_eq_one


/-
Finally we can combine the previous definitions to define the map f.
-/
def f (n m : ℕ) : U (m * n) → U n × U m := by exact
  fun k => (⟨f_fst_val k, f_fst_well_defined k⟩, ⟨f_snd_val k, f_snd_well_defined k⟩)

/-
Proceed by expressing the map f as a composition of the CRT map C and the maps q_res from the lecture.
-/

/-
Record explicitly the two coordinates of f.
-/
lemma f_fst_apply {n m : ℕ} (k : U (m * n)) :
    (((f n m k).1 : U n) : ℕ) = (k : ℕ) % n := by
  rfl

lemma f_snd_apply {n m : ℕ} (k : U (m * n)) :
    (((f n m k).2 : U m) : ℕ) = (k : ℕ) % m := by
  rfl

lemma f_injective {m n : ℕ} (h : Nat.Coprime m n) :
    Function.Injective (f n m) := by
  intro x y hxy
  have hfst := congrArg (fun z => (((z.1 : U n) : Fin n) : ℕ)) hxy
  have hsnd := congrArg (fun z => (((z.2 : U m) : Fin m) : ℕ)) hxy
  change (x : ℕ) % n = (y : ℕ) % n at hfst
  change (x : ℕ) % m = (y : ℕ) % m at hsnd
  have hnmod : (x : ℕ) ≡ (y : ℕ) [MOD n] := hfst
  have hmmod : (x : ℕ) ≡ (y : ℕ) [MOD m] := hsnd
  have hmnmod : (x : ℕ) ≡ (y : ℕ) [MOD m * n] := by
    exact (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hmmod, hnmod⟩
  have hval : (x : ℕ) = (y : ℕ) := by
    apply hmnmod.eq_of_lt_of_lt
    · exact x.1.isLt
    · exact y.1.isLt
  apply Subtype.ext
  exact Fin.ext hval


lemma f_surjectiveq {m n : ℕ} (h : Nat.Coprime m n) :
    Function.Surjective (f n m) := by
  intro z
  rcases z with ⟨z₁, z₂⟩
  by_cases hm : m = 0
  · subst m
    exact Fin.elim0 z₂.1
  · by_cases hn : n = 0
    · subst n
      exact Fin.elim0 z₁.1
    ·
      have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm
      have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn

      have hcopZ : IsCoprime (m : ℤ) (n : ℤ) := by
        rw [isCoprime_iff_gcd_eq_one]
        exact_mod_cast h.gcd_eq_one

      have hCRT :
          Function.Surjective (C (m : ℤ) (n : ℤ)) :=
        (chinese_remainder_theorem hmZ hnZ hcopZ).2

      let zn : ℤ_mod (n : ℤ) :=
        q_res (n : ℤ) ⟨z₁.1, by simpa using z₁.1.isLt⟩

      let zm : ℤ_mod (m : ℤ) :=
        q_res (m : ℤ) ⟨z₂.1, by simpa using z₂.1.isLt⟩

      obtain ⟨r, hr⟩ := hCRT (zm, zn)

      have hqsur :
          Function.Surjective (q_res ((m * n : ℕ) : ℤ)) :=
        (Z_mod_n_fin_n_bijection
          (by
            exact_mod_cast Nat.mul_ne_zero hm hn)).2

      obtain ⟨k, hk⟩ := hqsur r

      have hklt : k.val < m * n := by
        simpa using k.isLt

      have hC :
          C (m : ℤ) (n : ℤ)
            (q_res ((m * n : ℕ) : ℤ) k) = (zm, zn) := by
        rw [hk]
        exact hr

      have hkmq :
          q (m : ℤ) k.val = q (m : ℤ) z₂.1 := by
        exact congrArg Prod.fst hC

      have hknq :
          q (n : ℤ) k.val = q (n : ℤ) z₁.1 := by
        exact congrArg Prod.snd hC

      have hkmdiv :
          (m : ℤ) ∣ (k.val : ℤ) - (z₂.1 : ℤ) := by
        exact q_equality.mp hkmq

      have hkndiv :
          (n : ℤ) ∣ (k.val : ℤ) - (z₁.1 : ℤ) := by
        exact q_equality.mp hknq

      have hkm_mod : k.val % m = z₂.1 := by
        have hmod : k.val % m = z₂.1 % m := by
          apply Nat.ModEq.eq_iff_dvd.mpr
          exact_mod_cast hkmdiv
        rw [Nat.mod_eq_of_lt z₂.1.isLt] at hmod
        exact hmod

      have hkn_mod : k.val % n = z₁.1 := by
        have hmod : k.val % n = z₁.1 % n := by
          apply Nat.ModEq.eq_iff_dvd.mpr
          exact_mod_cast hkndiv
        rw [Nat.mod_eq_of_lt z₁.1.isLt] at hmod
        exact hmod

      have hkmcop : Nat.Coprime k.val m := by
        rw [← Nat.coprime_mod_left_iff]
        rw [hkm_mod]
        exact z₂.property

      have hkncop : Nat.Coprime k.val n := by
        rw [← Nat.coprime_mod_left_iff]
        rw [hkn_mod]
        exact z₁.property

      have hkcop : Nat.Coprime k.val (m * n) := by
        rw [Nat.coprime_mul_iff_right]
        exact ⟨hkmcop, hkncop⟩

      let ku : U (m * n) :=
        ⟨⟨k.val, hklt⟩, hkcop⟩

      refine ⟨ku, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        apply Fin.ext
        exact hkn_mod
      · apply Subtype.ext
        apply Fin.ext
        exact hkm_mod

lemma f_bijective {m n : ℕ} (h : Nat.Coprime m n) :
    Function.Bijective (f n m) := by
  constructor
  · exact f_injective h
  · exact f_surjective h



/-
PLAN FOR ϕ_prime_power

Goal:
    ϕ (p^k) = p^k - p^(k-1).

Step A:
Show that for x : Fin (p^k),

    Nat.Coprime (x : ℕ) (p^k)
      ↔ ¬ p ∣ (x : ℕ).

Because k > 0, coprimality with p^k is equivalent to coprimality with p,
and because p is prime, coprimality with p is equivalent to p not dividing x.

Step B:
Count the bad elements:
    {x : Fin (p^k) | p ∣ x}.

Construct a bijection

    Fin (p^(k-1))
      ≃
    {x : Fin (p^k) | p ∣ x}

by
    j ↦ p*j.

The key bound follows from
    j < p^(k-1)
⇒   p*j < p*p^(k-1)
 =  p^k.

Step C:
Fin (p^k) has p^k elements, and the bad subset has p^(k-1) elements.
The remaining elements are U(p^k).

Hence:
    ϕ(p^k) = p^k - p^(k-1).
-/

/-
PLAN FOR product_formula

1. Factor n into prime powers using Nat.factorization / Nat.primeFactors.
2. Distinct prime powers are pairwise coprime.
3. Repeatedly apply ϕ_multiplicative:
4. Substitute ϕ_prime_power.
..

-/

/-
PLAN FOR sum_formula

Let
    S(n) = ∑ d ∈ Nat.divisors n, ϕ d.

1. Prove S is multiplicative.

2. Compute S on prime powers:
   This is a telescoping sum.

3. Since both S and the identity function n ↦ n are multiplicative and
   agree on all prime powers, conclude:
       S(n) = n.
-/
