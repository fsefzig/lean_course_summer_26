import lecture5.examples5
import Mathlib.Data.Int.Basic

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · -- Forward Direction
    intro h1
    simp[Quotient.eq] at h1
    rcases h1 with ⟨k, hk⟩
    have h_eq: m1 = n*k + m2 := by omega
    rw[h_eq]
    simp only [Int.mul_add_emod_self_left]
  · -- Reverse Direction
    intro h1
    apply q_equality.mpr
    unfold mod_relation
    use (m1/n - m2/n)
    set r := m1 % n
    have hm1: m1 = n * (m1/n) + r := (Int.ediv_add_emod m1 n).symm
    have hm2: m2 = n * (m2/n) + r := (Int.ediv_add_emod m2 n).symm
    nth_rewrite 1 [hm1]
    nth_rewrite 1 [hm2]
    linarith

    -- Question: I have no idea why Int.ediv_add_emod is not working...

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · --hint: use x ∈ {z : α | R x z}
    intro h
    have hx : x ∈ {z : α | R x z} := hR.refl x
    rw[h] at hx
    exact hR.symm hx
  · --other direction
    intro hRxy
    have hRyx: R y x := hR.symm hRxy
    apply Set.Subset.antisymm_iff.mpr -- show both inclusions
    constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
    · -- Prove that {z | R x z} ⊆ {z | R y z}
      intro a ha
      have hxa: R x a := ha
      have hax: R a x := hR.symm ha
      have hay: R a y := hR.trans hax hRxy
      have hya: R y a := hR.symm hay
      exact hya
    · -- Prove that {z | R y z} ⊆ {z | R x z}
      intro a ha
      have hya: R y a := ha
      have hay: R a y := hR.symm ha
      have hax: R a x := hR.trans hay hRyx
      have hxa: R x a := hR.symm hax
      exact hxa

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  sorry

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  sorry

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  sorry

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine⟨?_, ?_⟩
  · --Injective
    intro i j h
    unfold q_res at h
    rw[q_equality] at h
    unfold mod_relation at h
    ext
    have hi := i.is_lt
    have hj := j.is_lt
    rcases h with ⟨k,hk⟩
    omega -- Question: I am not sure why omega is not working :(
  · --Surjective
    intro y
    obtain ⟨m, hm⟩ := Quotient.exists_rep y
    rw [← hm]
    sorry


-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  sorry
  -- Wasn't able to get enough time to think about this problem before due date. Will work on it!
