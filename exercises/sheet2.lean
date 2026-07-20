import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- Complete induction

variable (P : ℕ → Prop)

def Q (P : ℕ → Prop) (n : ℕ) : Prop := ∀ m, m ≤ n → P m

lemma lemma0 : P 0 → Q P 0 := by
  intro hP0 m hm
  rw [Nat.le_zero.mp hm]
  exact hP0

lemma lemma1 (n : ℕ) : Q P n → P n := by
  intro hQ
  exact hQ n (Nat.le_refl n)

lemma lemma2 (n : ℕ) : (Q P n → P (n + 1)) → (Q P n → Q P (n + 1)) := by
  intro hnext hQ m hm
  by_cases hmn : m ≤ n
  · exact hQ m hmn
  · have hnm : n + 1 ≤ m := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hmn)
    have hm : m = n + 1 := Nat.le_antisymm hm hnm
    rw [hm]
    exact hnext hQ

lemma lemma3 : (∀ n, Q P n) → ∀ n, P n := by
  intro hQ n
  exact lemma1 P n (hQ n)

end

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have hk : k ≠ 0 := by
    intro hk
    rw [hk, Nat.mul_zero] at h
    exact hn h
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, Nat.zero_mul] at h
    exact hn h
  have hdgt : 1 < d := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hd0, hd⟩
  rw [h]
  calc
    k = 1 * k := by rw [Nat.one_mul]
    _ < d * k := Nat.mul_lt_mul_of_pos_right hdgt (Nat.pos_of_ne_zero hk)

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  intro hnext
  have hdvd1 : d ∣ 1 := (Nat.dvd_add_iff_right h).mpr hnext
  exact hd (Nat.dvd_one.mp hdvd1)

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  let N := ∏ i ∈ Finset.range n, (i + 1)
  have hN0 : N ≠ 0 := by
    dsimp [N]
    refine Finset.prod_induction (fun i ↦ i + 1) (fun x ↦ x ≠ 0) ?_ ?_ ?_
    · intro a b ha hb
      exact Nat.mul_ne_zero ha hb
    · exact Nat.one_ne_zero
    · intro i hi
      exact Nat.add_one_ne_zero i
  have hN1 : N + 1 ≠ 1 := by
    intro h
    have h' : N + 1 = 0 + 1 := by simpa using h
    have : N = 0 := Nat.add_right_cancel h'
    exact hN0 this
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hN1
  refine ⟨p, hp, ?_⟩
  by_contra hpn
  have hple : p ≤ n := Nat.le_of_not_gt hpn
  have hp0 : p ≠ 0 := Nat.ne_of_gt hp.pos
  have hindex : p - 1 < n :=
    lt_of_lt_of_le (Nat.pred_lt hp0) hple
  have hsubset : {p - 1} ⊆ Finset.range n := by
    intro i hi
    have hi' : i = p - 1 := Finset.mem_singleton.mp hi
    rw [hi']
    exact Finset.mem_range.mpr hindex
  have hpdivN : p ∣ N := by
    have hprod := Finset.prod_dvd_prod_of_subset
      {p - 1} (Finset.range n) (fun i ↦ i + 1) hsubset
    simpa [N, Nat.sub_add_cancel hp.one_le] using hprod
  exact (exercise1 hp.ne_one hpdivN) hpdiv
end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

variable {I : Finset α} {f : α → ℕ}

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
#check ∑ i ∈ I, f i

-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Nat.dvd_add (h a) ih
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?

One type for prime factorization is N→N₀, where each prime is assigned to its multiplicity.
∃ a unique function e whose domain has only primes and n = ∏₍p ∈ domain of e₎ pᵉ(p).
-/
