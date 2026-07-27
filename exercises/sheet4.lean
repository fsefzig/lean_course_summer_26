import lecture5.examples5

open MyQuotient



lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  rw [q_equality]
  simp only [mod_relation]
  constructor
  · intro h
    have : m2 ≡ m1 [ZMOD n] := Int.modEq_iff_dvd.mpr h
    exact this.symm
  · intro h
    have : m2 ≡ m1 [ZMOD n] := h.symm
    exact Int.modEq_iff_dvd.mp this

lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro h
    have hx : x ∈ {z : α | R x z} := hR.refl x
    simp [h] at hx
    exact hR.symm hx
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · intro z hz
    simp only [Set.mem_setOf_eq] at *
    exact hR.trans (hR.symm hRxy) hz
  · intro z hz
    simp only [Set.mem_setOf_eq] at *
    exact hR.trans hRxy hz

def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun m => q n (k * m)) ?_
  intro m1 m2 h
  simp only [q_equality, mod_relation] at *
  have heq : k * m1 - k * m2 = k * (m1 - m2) := by ring
  rw [heq]
  exact Dvd.dvd.mul_left h k

lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x1 x2 hx
  have hgx := congrArg g hx
  rwa [h, h] at hgx

lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro y
  exact ⟨g y, h y⟩

theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · intro i1 i2 h
    unfold q_res at h
    rw [q_equality] at h
    simp only [mod_relation] at h
    have hdvd_natAbs : n.natAbs ∣ ((i1.val : ℤ) - i2.val).natAbs := Int.natAbs_dvd_natAbs.mpr h
    have h1 : (i1.val : ℕ) < n.natAbs := i1.isLt
    have h2 : (i2.val : ℕ) < n.natAbs := i2.isLt
    have hlt : ((i1.val : ℤ) - i2.val).natAbs < n.natAbs := by omega
    have heq0 : ((i1.val : ℤ) - i2.val).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_natAbs hlt
    have hdiff0 : (i1.val : ℤ) - i2.val = 0 := Int.natAbs_eq_zero.mp heq0
    have : i1.val = i2.val := by omega
    exact Fin.ext this
  · intro y
    obtain ⟨m, hm⟩ := Quotient.exists_rep y
    have hNpos : (0 : ℤ) < (n.natAbs : ℤ) := by exact_mod_cast Int.natAbs_pos.mpr hn
    have hNne : (n.natAbs : ℤ) ≠ 0 := ne_of_gt hNpos
    have hr_nonneg : 0 ≤ m % (n.natAbs : ℤ) := Int.emod_nonneg m hNne
    have hr_lt : m % (n.natAbs : ℤ) < (n.natAbs : ℤ) := Int.emod_lt_of_pos m hNpos
    have hdvd : (n.natAbs : ℤ) ∣ (m - m % (n.natAbs : ℤ)) := by
      refine ⟨m / (n.natAbs : ℤ), ?_⟩
      have := Int.emod_add_ediv_mul m (n.natAbs : ℤ)
      linarith
    have hdvd' : n ∣ (m - m % (n.natAbs : ℤ)) := Int.natAbs_dvd.mp hdvd
    have hri : (m % (n.natAbs : ℤ)).toNat < n.natAbs := by
      have heq := Int.toNat_of_nonneg hr_nonneg
      have : ((m % (n.natAbs : ℤ)).toNat : ℤ) < (n.natAbs : ℤ) := by rw [heq]; exact hr_lt
      exact_mod_cast this
    refine ⟨⟨(m % (n.natAbs : ℤ)).toNat, hri⟩, ?_⟩
    show q n ((((m % (n.natAbs : ℤ)).toNat : ℕ) : ℤ)) = y
    rw [Int.toNat_of_nonneg hr_nonneg, ← hm]
    apply q_equality.mpr
    have hrm : n ∣ -(m - m % (n.natAbs : ℤ)) := (dvd_neg).mpr hdvd'
    rwa [neg_sub] at hrm

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2
