import Mathlib.Tactic
import Mathlib.Data.Int.DivMod

/-
This is a bonus exercise sheet. You can submit it at any point, I do not expect you to finish it by
Monday! You can work on it at your own pace, and you can choose which exercise to do.
The topic of this exercise sheet is Euler's totient function. You can prove two fundamental
relations involving the totient function.
Proving the theorems on paper is already a good exercise, I encourage you to send me your
'normal' proof before you start formalizing it.
The formalization will require you to use essentially all the tools we have developed so far!
-/

noncomputable def ϕ :ℕ →  ℕ := fun n => Nat.card {k : Fin n | IsCoprime (k : ℕ) n}

--For future reference, we call the set of integers smaller than n and coprime to n, U(n).
abbrev U (n : ℕ) := {k : Fin n | IsCoprime (k : ℕ) n}

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
lemma ϕ_prime_power {p : ℕ} (hp : Nat.Prime p) (k : ℕ) : ϕ (p ^ k) = p ^ k - p ^ (k - 1) := by
  have h : ϕ (p^k) = Nat.card (Fin (p^k)) - Nat.card {x : Fin (p^k) | ¬ IsCoprime x.val (p^k)} := by
    dsimp only [ϕ]
    have h1 : U (p^k) = {x : Fin (p^k) | x < p^k} \ {x : Fin (p^k) | ¬ IsCoprime x.val (p^k)} := by
      dsimp only [U]
      refine Set.ext ?_
      intro x
      constructor
      · intro hx
        refine (Set.mem_sdiff x).mpr ?_
        constructor
        · refine Set.mem_setOf.mpr ?_
          exact x.2
        intro h
        contradiction
      intro hx
      apply (Set.mem_sdiff x).mp at hx
      have hx2 := hx.2
      refine Set.mem_setOf.mpr ?_
      apply Set.notMem_setOf_iff.mp at hx2
      tauto
    dsimp[U] at h1
    rw[h1]
    simp only [Nat.isCoprime_iff, Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard]
    rw[Set.ncard_sdiff]
    · simp only [Fin.is_lt, Set.setOf_true, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, pow_eq_one_iff, not_or]
    intro x hx
    refine Set.mem_setOf.mpr ?_
    exact x.2
  have h1 : ϕ (p^k) = p^k - Nat.card {x : Fin (p^k) | ¬ IsCoprime x.val (p^k)} := by
    rw[h]
    refine Nat.sub_eq_of_eq_add ?_
    rw[Nat.sub_add_cancel]
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    sorry
  sorry
lemma ϕ_multiplicative {m n : ℕ} (h : IsCoprime m n) : ϕ (m * n) = ϕ m * ϕ n := by
  sorry

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
  isLt := sorry -- note that the proof is trivial if one of the two numbers is 0!

def f_snd_val {n m : ℕ} (k : U (m * n)) : Fin m where
  val := k % m
  isLt := sorry

/-
The second step is to show that f(k) lands in U n × U m,
i.e. that the values of f are coprime to n and m respectively.
-/
lemma f_fst_well_defined {n m : ℕ} (k : U (m * n)) : f_fst_val k ∈ U n := by
  sorry

lemma f_snd_well_defined {n m : ℕ} (k : U (m * n)) : f_snd_val k ∈ U m := by
  sorry

/-
Finally we can combine the previous definitions to define the map f.
-/
def f (n m : ℕ) : U (m * n) → U n × U m := by exact
  fun k => (⟨f_fst_val k, f_fst_well_defined k⟩, ⟨f_snd_val k, f_snd_well_defined k⟩)

/-
Proceed by expressing the map f as a composition of the CRT map C and the maps q_res from the lecture.
-/
