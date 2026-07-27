import LectureNotes.lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  sorry

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
    have hdvd : n ∣ x - y := by
      exact Quotient.exact hxy
    have habs : ((x: ℤ) - (y: ℤ)).natAbs < n.natAbs := by
      omega
    apply Int.natAbs_dvd_natAbs.mpr at hdvd
    have h0 : (x - (y : ℤ)).natAbs = 0 := by
      exact Nat.eq_zero_of_dvd_of_lt hdvd habs
    omega
  intro x
  obtain ⟨m, hm⟩ := Quotient.exists_rep x
  have hr : m.natAbs % n.natAbs < n.natAbs := by
    apply Nat.mod_lt
    exact Int.natAbs_pos.mpr hn
  by_cases h : m ≥ 0
  · use ⟨m.natAbs % n.natAbs, hr⟩
    simp only [ℤ_mod, ℤ_mod_setoid, q_res, q, Int.natCast_emod, Nat.cast_natAbs, Int.cast_abs,
      Int.cast_eq, Int.emod_abs]
    rw[← hm]
    apply Quotient.eq.mpr
    simp only [mod_relation]
    have habs : |m| = m := by exact abs_of_nonneg h
    rw[habs]
    exact Int.dvd_emod_sub_self
  by_cases hrzero : m.natAbs % n.natAbs = 0
  · use ⟨0, by omega⟩
    simp only [ℤ_mod, ℤ_mod_setoid, q_res, q, CharP.cast_eq_zero]
    rw[← hm]
    apply Quotient.eq.mpr
    simp only [mod_relation, zero_sub, dvd_neg]
    apply Int.natAbs_dvd_natAbs.mp
    exact Nat.dvd_of_mod_eq_zero hrzero
  use ⟨n.natAbs - m.natAbs % n.natAbs, by omega⟩
  rw[← hm]
  simp only [ℤ_mod, ℤ_mod_setoid, q_res, q]
  apply Quotient.eq.mpr
  simp only [mod_relation]
  rw[Nat.mod_def]
  have hm : m = -m.natAbs := by
    push Not at h
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq]
    exact Int.eq_neg_comm.mp (abs_of_neg h)
  --rw[hm]
  --group
  --simp
  by_cases hn0 : 0 ≤ n
  · have hnabs : n.natAbs = n := by
      simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, abs_eq_self]
      exact hn0
    use 1 - (m.natAbs / n)
    apply Eq.symm
    simp
    calc n * (1 - |m| / n) = n.natAbs - n.natAbs * (|m| / n.natAbs) := by rw[← hnabs]; simp; group
    _ = n.natAbs - (-m.natAbs + m.natAbs + n.natAbs * (|m| / n.natAbs)) := by group
    _ = n.natAbs + m.natAbs -(m.natAbs + n.natAbs * (|m| / n.natAbs)) := by group
    _ = n.natAbs + m.natAbs - (m.natAbs + n.natAbs * (m.natAbs / n.natAbs)) := by
      simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, ]
    _ = ↑(n.natAbs - (m.natAbs - n.natAbs * (m.natAbs / n.natAbs))) + m.natAbs := by sorry_nf
    _ =↑(n.natAbs - (m.natAbs - n.natAbs * (m.natAbs / n.natAbs))) - m := by
      rw[hm]
      simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Int.natAbs_neg, abs_abs,
        sub_neg_eq_add]

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  sorry
