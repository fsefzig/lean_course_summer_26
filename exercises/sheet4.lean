import LectureNotes.lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · intro hq
    obtain ⟨k, hk⟩ := q_equality.mp hq
    have hr : 0 ≤ m2 % n ∧ m2 % n < n.natAbs := by
      exact ⟨Int.emod_nonneg m2 hn, Int.emod_lt m2 hn⟩
    have hm2 : m2 = n * (m2 / n) + m2 % n := by
      exact (Int.mul_ediv_add_emod m2 n).symm
    have hm1 : m1 = n * (k + m2 / n) + m2 % n := by
      calc
        m1 = n * k + m2 := by omega
        _ = n * k + (n * (m2 / n) + m2 % n) := by rw [← hm2]
        _ = n * (k + m2 / n) + m2 % n := by ring
    exact modulo_eq_rest n m1 (k + m2 / n) (m2 % n) hn hr hm1
  · intro hmod
    apply q_equality.mpr
    change n ∣ m1 - m2
    use m1 / n - m2 / n
    calc
      m1 - m2 =
          (n * (m1 / n) + m1 % n) - (n * (m2 / n) + m2 % n) := by
            rw [Int.mul_ediv_add_emod, Int.mul_ediv_add_emod]
      _ = n * (m1 / n - m2 / n) := by rw [hmod]; ring

/- Look at exercise_class.lean in LectureNotes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro heq
    have hx : x ∈ {z : α | R x z} := by
      exact hR.refl x
    rw[heq] at hx
    exact hR.symm hx
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
  · intro z hz
    exact hR.trans (hR.symm hRxy) hz
  intro z hz
  exact hR.trans hRxy hz

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  apply Quotient.lift (fun x => q n (k * x))
  intro a b h
  simp only [ℤ_mod, ℤ_mod_setoid, q]
  apply Quotient.eq.mpr
  change n ∣ (k * a) - (k * b)
  obtain ⟨l, hl⟩ := h
  use k * l
  rw[← mul_assoc, mul_comm n k, mul_assoc, ← hl]
  group


-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  rw[← h x,←  h y, hxy]

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro y
  use g y
  exact h y

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  constructor
  · intro x y hxy
    have hdvd : n ∣ (x : ℤ) - (y : ℤ) := Quotient.exact hxy
    have habs : ((x : ℤ) - (y : ℤ)).natAbs < n.natAbs := by
      omega
    have h0 : ((x : ℤ) - (y : ℤ)).natAbs = 0 := by
      exact Nat.eq_zero_of_dvd_of_lt (Int.natAbs_dvd_natAbs.mpr hdvd) habs
    omega
  · intro x
    obtain ⟨m, hm⟩ := Quotient.exists_rep x
    have hr0 : 0 ≤ m % n := Int.emod_nonneg m hn
    have hrlt : m % n < (n.natAbs : ℤ) := Int.emod_lt m hn
    have hfin : (m % n).toNat < n.natAbs := by
      omega
    use ⟨(m % n).toNat, hfin⟩
    rw [← hm]
    apply Quotient.eq.mpr
    change n ∣ ((m % n).toNat : ℤ) - m
    rw [Int.toNat_of_nonneg hr0]
    exact Int.dvd_emod_sub_self

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  sorry
