import lecture5.examples5
import Init.Data.Cast
set_option linter.style.longLine false
open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
--I believe that exercise0 does not need to have the hypothesis that n \ne 0
lemma exercise0 {n m1 m2 : ℤ} : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  simp only [q,Quotient,ℤ_mod, ℤ_mod_setoid]
  constructor
  · intro h
    apply Quotient.eq.mp at h
    simp only [mod_relation] at h
    refine (Int.emod_sub_cancel_right m1).mp ?_
    simp only [sub_self, EuclideanDomain.zero_mod]
    exact Eq.symm (Int.emod_eq_zero_of_dvd (dvd_sub_comm.mp h))
  intro h
  have h1 : n ∣ m1 - m2 := by
    exact Int.ModEq.dvd (Eq.symm h)
  apply Quotient.eq.mpr
  simp only [mod_relation]
  exact h1



/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro h
    have h1 : y ∈ {z | R y z} := by
      exact hR.refl y
    exact (Eq.to_iff (congrFun h y)).mpr h1
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  constructor
  · intro z h
    refine Set.mem_setOf.mpr ?_
    apply Set.mem_setOf.mp at h
    exact hR.trans (hR.symm hRxy) h
  intro z h
  refine Set.mem_setOf.mpr ?_
  apply Set.mem_setOf.mp at h
  exact hR.trans hRxy h


-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun m => q n (k*m)) ?_
  intro x y h
  simp only [ℤ_mod, ℤ_mod_setoid, q]
  refine Quotient.sound ?_
  refine (Setoid.comm' { r := mod_relation n, iseqv := mod_equivalence n }).mpr ?_
  simp only [mod_relation]
  apply (Setoid.comm' { r := mod_relation n, iseqv := mod_equivalence n }).mp at h
  simp only [mod_relation] at h
  rw[←mul_sub]
  exact Int.dvd_mul_of_dvd_right h

example : mul_k 2 2 ⟦1⟧ = ⟦0⟧ := by
  simp only [ℤ_mod, ℤ_mod_setoid,mul_k]
  simp only [q, ℤ_mod_setoid, Quotient.lift_mk, mul_one]
  refine Quotient.sound ?_
  refine Setoid.symm' { r := mod_relation 2, iseqv := mod_equivalence 2 } ?_
  simp only [mod_relation, zero_sub, Int.reduceNeg, dvd_neg, dvd_refl]

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y h1
  have hx : g (f x) = x := h x
  have hy : g (f y) = y := h y
  rw[h1,hy] at hx
  exact hx.symm

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro y
  use g y
  exact h y

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    dsimp only [q_res, q] at h
    apply exercise0.mp at h
    have h1 : n ∣ x-y := by
      exact Int.ModEq.dvd (Eq.symm h)
    have h2 : |↑↑x - ↑↑y| < |n| := by
      refine abs_sub_lt_iff.mpr ?_
      constructor
      · refine Int.sub_lt_iff.mpr ?_
        calc
          x < |n| := by
            refine Int.lt_toNat.mp ?_
            refine Fin.val_lt_of_le x ?_
            simp only [abs_nonneg, Int.le_toNat, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Std.le_refl]
          _ ≤ |n| + y := by omega
      refine Int.sub_lt_iff.mpr ?_
      calc
        y < |n| := by
          refine Int.lt_toNat.mp ?_
          refine Fin.val_lt_of_le y ?_
          simp only [abs_nonneg, Int.le_toNat, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq,
            Std.le_refl]
        _ ≤ |n| + x := by omega
    rcases h1 with ⟨k,hk⟩
    rw[hk] at h2
    have h3 : k = 0 := by
      by_contra!
      have h3 : |k| ≥ 1 := by
        exact Int.one_le_abs this
      rw[abs_mul] at h2
      nth_rw 2[←mul_one |n|] at h2
      have h4 : 0 < |n| := by
        exact abs_pos.mpr hn
      apply Int.mul_lt_mul_left at h4
      apply h4.mp at h2
      have h4 : 1 < 1 := by
        exact lt_imp_lt_of_le_imp_le (fun a ↦ h3) h2
      contradiction
    rw[h3,mul_zero] at hk
    apply Int.sub_eq_zero.mp at hk
    refine Fin.eq_of_val_eq ?_
    exact Int.ofNat_inj.mp hk
  intro x1
  obtain ⟨x2,h⟩ := Quotient.exists_rep x1
  dsimp only [ℤ_mod, ℤ_mod_setoid, q_res, q]
  have h1 : ∃ k r : ℤ, 0 ≤ r ∧ r < n.natAbs ∧  x2 = n.natAbs*k + r := by
    use x2/n.natAbs
    use (x2 % n.natAbs)
    constructor
    · refine Int.emod_nonneg x2 ?_
      refine Int.ofNat_ne_zero.mpr ?_
      exact Int.natAbs_ne_zero.mpr hn
    constructor
    · refine Int.emod_lt x2 ?_
      refine Int.ofNat_ne_zero.mpr ?_
      exact Int.natAbs_ne_zero.mpr hn
    exact Eq.symm (Int.mul_ediv_add_emod x2 ↑n.natAbs)
  rcases h1 with ⟨k,hk⟩
  rcases hk with ⟨r,hr⟩
  have r.toNat : Fin n.natAbs := by
    refine Fin.Internal.ofNat n.natAbs ?_ ?_
    · exact Int.natAbs_pos.mpr hn
    exact USize.size



-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  rcases h1 with ⟨k,hk⟩
  rw[hk] at h2
  sorry
