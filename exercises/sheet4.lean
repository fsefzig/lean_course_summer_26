import lecture5.examples5
open MyQuotient
#check Int.emod_eq_emod_iff_emod_sub_eq_zero
#check Int.emod_eq_zero_of_dvd
-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  have hq_eq : (q n m1) = q n m2 →  (m1 ∼[n] m2) := by
    exact (q_equality).mp
  constructor
  intro h
  apply hq_eq at h
  have hdiv : n ∣  m1 - m2 := by
    exact h
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr
  apply Int.emod_eq_zero_of_dvd at hdiv
  exact hdiv
  intro h
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp at h
  apply (q_equality).mpr
  apply Int.dvd_of_emod_eq_zero
  exact h

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/


lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  intro h
  have hx : x ∈ {z : α | R x z} := by
    exact hR.refl x
  rw [h] at hx
  apply hR.symm
  exact hx
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
  intro h
  intro h2
  apply hR.symm at hRxy
  exact hR.trans hRxy h2
  intro h
  intro h2
  exact hR.trans hRxy h2


#check dvd_mul_of_dvd_right
-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun x : ℤ => q n (k * x)) ?_
  intro a b hab
  apply q_equality.mpr
  change n ∣ k*a - k*b
  rw [← mul_sub]
  change n ∣ a - b at hab
  exact dvd_mul_of_dvd_right hab k

#check congrArg
-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
    intro x
    intro y
    intro hxy
    apply congrArg g at hxy
    rw [h] at hxy
    rw [h] at hxy
    exact hxy

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
    intro x
    use g x
    rw [h]

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
#check Fin.ext
#check Fin.isLt
#check Quotient.exists_rep
#check Int.emod_lt
#check Int.toNat_lt

theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  intro x
  intro y
  intro hq
  apply Fin.ext
  change q n x.val = q n y.val at hq
  have heq : x.val % n = y.val % n := by
    exact (exercise0 hn).mp hq
  have hx : x.val % n = x.val := by
    apply modulo_eq_rest (k := 0)
    exact hn
    constructor
    omega
    exact_mod_cast x.isLt
    omega
  have hy : y.val % n = y.val := by
    apply modulo_eq_rest (k := 0)
    exact hn
    constructor
    omega
    exact_mod_cast y.isLt
    omega
  rw [hx, hy] at heq
  exact_mod_cast heq
  intro x
  rcases Quotient.exists_rep x with ⟨m, hm⟩
  have ha_nezero : 0 ≤ m % n := by
    exact Int.emod_nonneg m hn
  have ha_le_abs : m % n < n.natAbs := by
    exact Int.emod_lt m hn
  let a : Fin n.natAbs := ⟨(m % n).toNat, (Int.toNat_lt ha_nezero).mpr ha_le_abs⟩
  use a
  rw [← hm]
  change q n a.val = q n m
  apply (exercise0 hn).mpr
  have ha_val : a.val = m % n := by
    simp [a]
    exact ha_nezero
  rw [ha_val]
  simp

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
#check Nat.Coprime.dvd_of_dvd_mul_left
#check mul_dvd_mul_left

lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  have hab : Nat.Coprime a b := by
    exact h3
  obtain ⟨k, hk⟩  := h1
  rw [hk]
  rw [hk] at h2
  have hb : b ∣ k := by
    apply Nat.Coprime.dvd_of_dvd_mul_left hab.symm
    exact h2
  apply mul_dvd_mul_left
  exact hb
