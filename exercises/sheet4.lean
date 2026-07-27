import lecture5.examples5
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Algebra.GCDMonoid.Basic


open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder mod `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (_hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  simp only [q_equality, mod_relation]
  constructor
  · intro hdvd
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    exact Int.emod_eq_zero_of_dvd hdvd
  · intro hmod
    exact Int.ModEq.dvd (Eq.symm hmod)
  -- idk if i cheated at some point because i didnt use hn and i didn't use modulo_eq_rest

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro h --hint: use x ∈ {z : α | R x z}
    -- R y y holds by refl
    -- sets are same means y member of {z | R y z} => y member of {z | R x z} => R x y
    have hy : y ∈ {z | R y z} := hR.refl y
    exact (Eq.to_iff (congrFun h y)).mpr hy
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  simp only [Set.setOf_subset_setOf] at *
  constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
  · intro z hz
    have hyx : R y x := by exact hR.symm hRxy
    exact hR.trans hyx hz
  · intro z hz
    exact hR.trans hRxy hz

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun x => q n (k * x)) ?_
  intro a b h
  simp only [q_equality, mod_relation, ← mul_sub] at *
  exact Int.dvd_mul_of_dvd_right h

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro a₁ a₂ hf -- i learned you can write subscripts with \ and a number :)
  have ghf : g (f a₁) = g (f a₂) → a₁ = a₂ := by
    simp only [h a₁, h a₂, imp_self]
  exact (ghf ∘ congrArg g) hf

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro b
  use g b
  exact h b

lemma add_mul_zero_eq_val (k n : ℤ) : k = n * 0 + k := by simp only [mul_zero, zero_add]

lemma fin_mod_eq_val {n : ℤ} (a : Fin n.natAbs) (hn : n ≠ 0) : a.val % n = a.val := (modulo_eq_rest
  n a 0 a hn ⟨Nat.cast_nonneg a, Nat.cast_lt.mpr a.isLt⟩ (add_mul_zero_eq_val a n))

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩ -- takes apart by injective/surjective
  · intro a₁ a₂ hq
    have hmod := (exercise0 hn).mp hq
    rw [fin_mod_eq_val a₁ hn, fin_mod_eq_val a₂ hn] at hmod
    exact Fin.eq_of_val_eq (Int.ofNat_inj.mp hmod)
  · intro b
    obtain ⟨x, hx⟩ := Quotient.exists_rep b
    -- to make something of type Fin n.natAbs we need the value and proof that its le n
    have mod_le_n : (x % n).toNat < n.natAbs := by
      refine (Int.toNat_lt ?_).mpr ?_
      · exact Int.emod_nonneg x hn
      · exact Int.emod_lt x hn
    use ⟨(x % n).toNat, mod_le_n⟩
    simp only [q_res, q, ← hx]
    apply (exercise0 hn).mpr
    rw[Int.toNat_of_nonneg (Int.emod_nonneg x hn)]
    exact Int.emod_emod x n

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.

lemma ab_prime_exp_le_c {a b c p : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) :
    padicValNat p (a * b) ≤ padicValNat p c := by
  haveI : Fact p.Prime := ⟨hp⟩ -- idk why but padicValNat.mul requires this
  rw [padicValNat.mul ha hb]
  have pa : padicValNat p a ≤ padicValNat p c :=
    (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hc).mp (dvd_trans pow_padicValNat_dvd h1)
  have pb : padicValNat p b ≤ padicValNat p c :=
    (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hc).mp (dvd_trans pow_padicValNat_dvd h2)
  by_cases hdvd : p ∣ a
  · have hzero : padicValNat p b = 0 :=
      padicValNat.eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left hdvd h3))
    rw [hzero, add_zero]
    exact pa
  · rw [padicValNat.eq_zero_of_not_dvd hdvd, zero_add]
    exact pb

lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  /-
  1. let p | a. since a and b are coprime, the exponent of p in the factorization of b is 0.
  2. in the factorization of a*b, the exp of p must be the exp of p in the factorization of a
  3. we can apply similar logic for p | b
  4. ⇒ for each prime, exp(p in factorization(a)) + exp(p in factorization(b)) ≤ exp(p in c)
  5. since this is true for all primes in a and b ∧ a | c and b | c, a * b | c

  i cant use apply? or exact? cause it only gives Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2 lol
  -/
  by_cases hc : c = 0
  · subst hc
    exact Nat.dvd_zero (a * b)
  · have ha : a ≠ 0 := by exact ne_zero_of_dvd_ne_zero hc h1
    have hb : b ≠ 0 := by exact ne_zero_of_dvd_ne_zero hc h2
    apply (Nat.factorization_le_iff_dvd (mul_ne_zero ha hb) hc).mp
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_def (a*b) hp, Nat.factorization_def c hp]
      apply ab_prime_exp_le_c hp ha hb hc h1 h2 h3
    · rw[Nat.factorization_eq_zero_of_not_prime (a*b) hp,
          Nat.factorization_eq_zero_of_not_prime c hp]
  -- wow this was hard, is there any easier way to do it?
