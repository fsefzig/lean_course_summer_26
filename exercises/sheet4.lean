import LectureNotes.lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  rw [q_eq]
  have h1 := (Int.emod_eq_iff hn).mp (rfl : m1 % n = m1 % n)
  have h2 := (Int.emod_eq_iff hn).mp (rfl : m2 % n = m2 % n)
  constructor
  · intro h
    refine (Int.emod_eq_iff hn).mpr ⟨h2.1, h2.2.1, ?_⟩
    have hsplit : m2 % n - m1 = (m2 % n - m2) + (m2 - m1) := by ring
    rw [hsplit]
    exact dvd_add h2.2.2 (dvd_sub_comm.mp h)
  intro h
  show n ∣ m1 - m2
  have hsplit : m1 - m2 = (m1 - m1 % n) + (m2 % n - m2) := by rw [← h]; ring
  rw [hsplit]
  exact dvd_add (dvd_sub_comm.mp h1.2.2) h2.2.2

/- Look at exercise_class.lean in LectureNotes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro h --hint: use x ∈ {z : α | R x z}
    have hx : x ∈ {z : α | R x z} := hR.refl x
    rw [h] at hx
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
  refine Quotient.lift (fun m => q n (k * m)) ?_
  intro a b h
  have hd : n ∣ a - b := h
  show q n (k * a) = q n (k * b)
  apply q_eq.mpr
  show n ∣ k * a - k * b
  have hkab : k * a - k * b = k * (a - b) := by ring
  rw [hkab]
  exact hd.mul_left k

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro a b hab
  have hg : g (f a) = g (f b) := by rw [hab]
  rwa [h a, h b] at hg

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro y
  exact ⟨g y, h y⟩

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    have h : ((i.val : ℤ)) % n = ((j.val : ℤ)) % n := (exercise0 hn).mp hij
    have hi : ((i.val : ℤ)) % n = (i.val : ℤ) :=
      modulo_eq_rest n i.val 0 i.val hn ⟨by omega, by exact_mod_cast i.isLt⟩ (by ring)
    have hj : ((j.val : ℤ)) % n = (j.val : ℤ) :=
      modulo_eq_rest n j.val 0 j.val hn ⟨by omega, by exact_mod_cast j.isLt⟩ (by ring)
    have hval : (i.val : ℤ) = (j.val : ℤ) := by rw [← hi, ← hj, h]
    have hnat : i.val = j.val := by exact_mod_cast hval
    exact Fin.ext hnat
  intro x
  obtain ⟨m, hm⟩ := Quotient.exists_rep x
  obtain ⟨hnn, hlt, hdvd⟩ := (Int.emod_eq_iff hn).mp (rfl : m % n = m % n)
  refine ⟨⟨(m % n).toNat, by omega⟩, ?_⟩
  show q n ((m % n).toNat : ℤ) = x
  rw [Int.toNat_of_nonneg hnn, ← hm]
  exact q_eq.mpr hdvd

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2
