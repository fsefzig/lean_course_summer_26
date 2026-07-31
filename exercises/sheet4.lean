import LectureNotes.lecture5.examples5
import Mathlib.Data.Nat.Factorization.Basic

open MyQuotient

theorem Int.dvd_sub_iff_emod_eq_emod_of_ne_zero {n a b : ℤ}
    : n ∣ a - b ↔ a % n = b % n := by
  constructor
  · intro h
    exact Int.modEq_iff_dvd.mpr <| dvd_sub_comm.mp h
  · intro h
    exact Int.modEq_iff_dvd.mp <| Eq.symm h

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · unfold q
    intro h
    apply Quotient.eq.mp at h
    unfold ℤ_mod_setoid at h
    dsimp at h
    exact Int.dvd_sub_iff_emod_eq_emod_of_ne_zero |>.mp h
  intro h
  unfold q
  refine Quotient.sound ?_
  change n ∣ m1 - m2
  exact Int.dvd_sub_iff_emod_eq_emod_of_ne_zero |>.mpr h

/- Look at exercise_class.lean in LectureNotes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · --hint: use x ∈ {z : α | R x z}
    intro h
    have helem : x ∈ {z : α | R x z} := hR.refl x
    rw [h] at helem
    change R y x at helem
    exact hR.symm helem
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
  · intro e he
    apply hR.symm at he
    change R y e
    exact hR.symm <| hR.trans he hRxy
  intro e he
  exact hR.trans hRxy he

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := Quotient.lift
    (fun m => Quotient.mk (ℤ_mod_setoid n) (k*m)) <| by
  intro a b h
  refine Quotient.eq.mpr ?_
  unfold ℤ_mod_setoid
  simp only [mod_relation]
  rw [← mul_sub]
  refine dvd_mul_of_dvd_right ?_ k
  exact h

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  rw[← h x,← h y, hxy]

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  unfold Function.Surjective
  intro b
  use g b
  exact h b

abbrev finmod (n : ℤ) (hnez : n ≠ 0) : ℤ → Fin n.natAbs := fun x => Fin.mk (x % n).natAbs <| by
  have hmodlt : x % n < n.natAbs := Int.emod_lt x hnez
  have hnonneg : 0 ≤ x % n := Int.emod_nonneg x hnez
  have test := Int.natAbs_of_nonneg hnonneg
  rw [← test] at hmodlt
  exact Int.ofNat_lt.mp hmodlt

def q_res_inv (n : ℤ) (hnez : n ≠ 0) : ℤ_mod n → Fin n.natAbs := Quotient.lift (finmod n hnez) <| by
  intro a b heq
  unfold finmod
  ext; dsimp
  rw [Int.dvd_sub_iff_emod_eq_emod_of_ne_zero.mp heq]

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · refine f_injective_of_left_inverse (q_res n) (q_res_inv n hn) ?_
    intro x
    obtain ⟨x, hx⟩ := x
    unfold q_res_inv q_res
    simp only [ℤ_mod_setoid, q, Quotient.lift_mk]
    ext; dsimp
    have heqself : (x : ℤ) % n = (x : ℤ) := (Int.emod_eq_iff hn).mpr <|
      ⟨Int.natCast_nonneg x, ⟨Int.ofNat_lt.mpr hx, by simp⟩⟩
    rw [heqself]
    simp
  refine f_surjective_of_right_inverse (q_res n) (q_res_inv n hn) ?_
  intro b
  refine Quotient.recOn b ?_ (fun a b p => rfl)
  intro a
  unfold q_res q_res_inv
  simp only [ℤ_mod, ℤ_mod_setoid, q, Quotient.lift_mk, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq]
  apply Quotient.sound
  change n ∣ |a%n| - a
  rw [abs_of_nonneg <| Int.emod_nonneg a hn]
  exact Int.dvd_emod_sub_self

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma prime_power_case {p k b c : ℕ} (hp : Nat.Prime p)
    (h1 : p ^ k ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd (p ^ k) b = 1) :
    p ^ k * b ∣ c := by
  obtain ⟨l,hl⟩ := h2
  rw[hl, mul_comm]
  rw[hl] at h1
  apply Nat.mul_dvd_mul (Nat.dvd_refl b)
  cases k with
  | zero =>
    rw [pow_zero]
    exact one_dvd l
  | succ k =>
    refine (Nat.prime_iff.mp hp).pow_dvd_of_dvd_mul_left (k + 1) ?_ h1
    apply hp.coprime_iff_not_dvd.mp
    exact Nat.Coprime.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero k)) h3


lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  induction a using Nat.strong_induction_on generalizing b c with
  | h a ih =>
      by_cases ha0 : a = 0
      · simpa [ha0] using h1
      by_cases ha1 : a = 1
      · simpa [ha1] using h2
      obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
      let k := a.factorization p
      let r := a / p ^ k
      have hprod : p ^ k * r = a := Nat.ordProj_mul_ordCompl_eq_self a p
      have hr_dvd_a : r ∣ a := by
        use p ^ k
        rw [mul_comm]
        exact hprod.symm
      rw[← hprod, mul_assoc]
      refine prime_power_case hp ?_ ?_ ?_
      · rw[← hprod] at h1
        exact dvd_of_mul_right_dvd h1
      · refine ih r ?_ ?_ h2 (Nat.Coprime.coprime_dvd_left hr_dvd_a h3)
        · apply Nat.div_lt_self (Nat.zero_lt_of_ne_zero ha0)
          refine Nat.one_lt_pow ?_ (Nat.Prime.one_lt hp)
          exact Nat.ne_zero_of_lt (hp.factorization_pos_of_dvd ha0 hpa)
        rw[← hprod] at h1
        exact dvd_of_mul_left_dvd h1
      apply Nat.Coprime.pow_left k
      refine Nat.Coprime.mul_right ?_ ?_
      · exact Nat.coprime_ordCompl hp ha0
      exact Nat.Coprime.coprime_dvd_left hpa h3
