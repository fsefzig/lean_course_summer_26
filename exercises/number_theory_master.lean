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

noncomputable def ϕ : ℕ → ℕ := fun n => Nat.card {k : Fin n | Nat.Coprime (k : ℕ) n}


--For future reference, we call the set of integers smaller than n and coprime to n, U(n).
abbrev U (n : ℕ) := {k : Fin n | Nat.Coprime (k : ℕ) n}

-- Our `ϕ` agrees with Mathlib's totient `Nat.totient`, which counts `a < n` coprime to `n`.
lemma ϕ_eq_totient (n : ℕ) : ϕ n = n.totient := by
  rw [ϕ, Nat.totient, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨k.isLt, hk.symm⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simpa using hb.2.symm, rfl⟩

/-
The first relation expresses the totient function as a product over the prime factors of `n`.
I wrote the statement in this elegant form, however, formulated like this it involves rational numbers,
so it will be helpful to expand the product and write it in terms of natural numbers.
-/
theorem product_formula (n : ℕ) : ϕ n = n * ∏ p ∈ (Nat.primeFactors n), (1 - (1 / p) : ℚ) := by
  rw [ϕ_eq_totient, Nat.totient_eq_mul_prod_factors]
  simp only [one_div]

/-
The second relation expresses a number `n` as a sum of the totient values of all its divisors.
-/
theorem sum_formula (n : ℕ) : n = ∑ d ∈ (Nat.divisors n), ϕ d := by
  simp_rw [ϕ_eq_totient]
  exact (Nat.sum_totient n).symm

/-
The proof of both relations involves the following properties of the totient function.
-/
lemma ϕ_prime_power {p k : ℕ} (hp : Nat.Prime p) (hk : k > 0) : ϕ (p ^ k) = p ^ k - p ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [ϕ_eq_totient, Nat.totient_prime_pow_succ hp, Nat.add_sub_cancel, Nat.mul_sub_one, pow_succ]


lemma ϕ_multiplicative {m n : ℕ} (h : Nat.Coprime m n) : ϕ (m * n) = ϕ m * ϕ n := by
  simp only [ϕ_eq_totient]
  exact Nat.totient_mul h

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
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd k.1.isLt (by simp)
    · exact Nat.mod_lt _ hn

def f_snd_val {n m : ℕ} (k : U (m * n)) : Fin m where
  val := k % m
  isLt := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd k.1.isLt (by simp)
    · exact Nat.mod_lt _ hm

/-
The second step is to show that f(k) lands in U n × U m,
i.e. that the values of f are coprime to n and m respectively.
-/
lemma f_fst_well_defined {n m : ℕ} (k : U (m * n)) : f_fst_val k ∈ U n := by
  have h : Nat.Coprime (k : ℕ) (m * n) := k.2
  show Nat.Coprime (k % n) n
  rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
  exact (Nat.coprime_mul_iff_right.mp h).2

lemma f_snd_well_defined {n m : ℕ} (k : U (m * n)) : f_snd_val k ∈ U m := by
  have h : Nat.Coprime (k : ℕ) (m * n) := k.2
  show Nat.Coprime (k % m) m
  rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
  exact (Nat.coprime_mul_iff_right.mp h).1

/-
Finally we can combine the previous definitions to define the map f.
-/
def f (n m : ℕ) : U (m * n) → U n × U m := by exact
  fun k => (⟨f_fst_val k, f_fst_well_defined k⟩, ⟨f_snd_val k, f_snd_well_defined k⟩)

/-
Proceed by expressing the map f as a composition of the CRT map C and the maps q_res from the lecture.
-/
