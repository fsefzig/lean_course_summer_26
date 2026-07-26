import lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.

lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · intro hq
    have hdiv : n ∣ m1 - m2 := by
      exact q_equality.mp hq
    obtain ⟨k, hk⟩ := hdiv
    have hm1 : m1 = n * (k + m2 / n) + m2 % n := by
      calc
        m1 = n * k + m2 := by
          omega
        _ = n * k + (m2 % n + n * (m2 / n)) := by
          rw [Int.emod_add_mul_ediv]
        _ = n * (k + m2 / n) + m2 % n := by
          ring
    apply modulo_eq_rest n m1 (k + m2 / n) (m2 % n) hn
    · constructor
      · exact Int.emod_nonneg m2 hn
      · exact Int.emod_lt m2 hn
    · exact hm1
  · intro hrem
    apply q_equality.mpr
    change n ∣ m1 - m2
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hrem

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro hsets
    have hx_mem : x ∈ {z : α | R x z} := by
      exact hR.refl x
    have hx_mem_y : x ∈ {z : α | R y z} := by
      rw [← hsets]
      exact hx_mem
    have hyx : R y x := by
      exact hx_mem_y
    exact hR.symm hyx
  · intro hRxy
    apply Set.Subset.antisymm_iff.mpr
    constructor
    · intro z hxz
      have hyx : R y x := hR.symm hRxy
      exact hR.trans hyx hxz
    · intro z hyz
      exact hR.trans hRxy hyz

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun x => q n (k * x)) ?_
  intro x y hxy
  apply q_equality.mpr
  change n ∣ k * x - k * y
  change n ∣ x - y at hxy
  obtain ⟨t, ht⟩ := hxy
  use k * t
  calc
    k * x - k * y = k * (x - y) := by ring
    _ = k * (n * t) := by rw [ht]
    _ = n * (k * t) := by ring

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  calc
    x = g (f x) := (h x).symm
    _ = g (f y) := congrArg g hxy
    _ = y := h y

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
  · -- Injective
    intro i j hij
    change q n (i.val : ℤ) = q n (j.val : ℤ) at hij
    have hrem :
        (i.val : ℤ) % n = (j.val : ℤ) % n := by
      exact (exercise0 hn).mp hij
    have hi_rem : (i.val : ℤ) % n = i.val := by
      apply modulo_eq_rest n (i.val : ℤ) 0 (i.val : ℤ) hn
      · constructor
        · omega
        · exact_mod_cast i.isLt
      · ring
    have hj_rem : (j.val : ℤ) % n = j.val := by
      apply modulo_eq_rest n (j.val : ℤ) 0 (j.val : ℤ) hn
      · constructor
        · omega
        · exact_mod_cast j.isLt
      · ring
    rw [hi_rem, hj_rem] at hrem
    apply Fin.ext
    exact_mod_cast hrem
  · -- Surjective
    intro z
    obtain ⟨m, rfl⟩ := Quotient.exists_rep z
    have hr_nonneg : 0 ≤ m % n := by
      exact Int.emod_nonneg m hn
    have hr_lt : m % n < n.natAbs := by
      exact Int.emod_lt m hn
    let i : Fin n.natAbs :=
      ⟨(m % n).toNat, by omega⟩
    use i
    change q n (i.val : ℤ) = q n m
    apply (exercise0 hn).mpr
    have hi_val : (i.val : ℤ) = m % n := by
      dsimp [i]
      exact Int.toNat_of_nonneg hr_nonneg
    rw [hi_val]
    apply modulo_eq_rest n (m % n) 0 (m % n) hn
    · exact ⟨hr_nonneg, hr_lt⟩
    · ring

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  exact (Nat.coprime_iff_gcd_eq_one.mpr h3).mul_dvd_of_dvd_of_dvd h1 h2
