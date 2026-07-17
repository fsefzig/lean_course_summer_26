import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs
set_option linter.style.longLine false
/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity
theorem exercise0 {d k n : ℕ} (hd : d ≠ 0) (hk : k > 1) (h : n = d * k) : d < n := by
  rw[h]
  refine (Nat.lt_mul_iff_one_lt_right ?_).mpr hk
  exact Nat.zero_lt_of_ne_zero hd

lemma lemma1 {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : d ≤ n := by
  rcases hd with ⟨k, hk⟩
  rw[hk]
  have h : d≠0 ∧ k≠0 := by
    refine Nat.mul_ne_zero_iff.mp ?_
    /-Apparently this works, but I wanted to solve this part without exact? exact Ne.symm (ne_of_ne_of_eq (Ne.symm hn) hk)-/
    rw[←hk]
    exact hn
  refine Nat.le_mul_of_pos_right d ?_
  have hr := h.right
  exact Nat.zero_lt_of_ne_zero hr

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  by_contra
  rcases h with ⟨k, hk⟩
  rcases this with ⟨l, hl⟩
  rw[hk] at hl
  have h : d ≤ 1 := by
    apply lemma1
    · trivial
    apply Nat.eq_sub_of_add_eq' at hl
    rw[←Nat.mul_sub] at hl
    use(l-k)
  rcases d with c | hc
  · rw[Nat.zero_mul,Nat.zero_mul] at hl
    trivial
  rw[Nat.add_comm] at h
  apply Nat.le_sub_of_add_le' at h
  rw[Nat.sub_self] at h
  apply Nat.le_zero.mp at h
  rw[h] at hd
  trivial

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  by_cases h : n≤2
  · have h1 : Nat.Prime 3 := by
      exact Nat.prime_three
    use 3
    constructor
    · exact h1
    calc
    n ≤ 2 := h
    _ < 3 := by omega
  have h2 : ∀ p ∈ Finset.range (n + 1), p.Prime → p ∣ (∏ i ∈ (Finset.range (n+1)).filter Nat.Prime, i) := by
    intro h3 h4 h5
    have h6 : h3 ∈ (Finset.range (n+1)).filter Nat.Prime := by
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact h4
      exact h5
    exact Finset.dvd_prod_of_mem (fun i ↦ i) h6
  have h1 : ∀ p ∈ Finset.range (n + 1), p.Prime → ¬(p ∣ ((∏ i ∈ (Finset.range (n+1)).filter Nat.Prime, i)+1)) := by
    intro p hp1 hp2
    rw[Nat.prime_def] at hp2
    apply exercise1
    · rcases hp2 with ⟨left, right⟩
      exact Ne.symm (Nat.ne_of_lt left)
    apply h2
    · exact hp1
    exact Nat.prime_def.mpr hp2
  have hp : ∃p : ℕ, p.Prime ∧ p ∣ (∏ i ∈ (Finset.range (n+1)).filter Nat.Prime, i)+1 := by
    refine Nat.exists_prime_and_dvd ?_
    have h3 : n > 2:= by
      exact Nat.lt_of_not_le h
    have h4 : Nat.Prime 2 := by
      exact Nat.prime_two
    intro h5
    apply h2 at h4
    · apply lemma1 at h4
      · have h6 : 1 < (∏ i ∈ (Finset.range (n+1)).filter Nat.Prime, i) + 1 := calc
          1 < 2 := by omega
          _ ≤ ∏ i ∈ (Finset.range (n+1)).filter Nat.Prime, i := h4
          _ ≤ (∏ i ∈ (Finset.range (n+1)).filter Nat.Prime, i) + 1 := by omega
        apply ne_of_lt at h6
        exact h6.symm h5
      have h7 : 2 ∈ Finset.range (n+1) ∧ Nat.Prime 2 := by
        constructor
        · refine Finset.mem_range.mpr ?_
          calc
          2 < n := h3
          _ < n+1 := by omega
        exact Nat.prime_two
      apply Finset.mem_filter.mpr at h7
      have h8 : ∀a ∈ (Finset.range (n+1)).filter Nat.Prime, a ≠ 0 := by
        intro a h9
        apply Finset.mem_filter.mp at h9
        apply fun q↦q.right at h9
        exact Nat.Prime.ne_zero h9
      exact Finset.prod_ne_zero_iff.mpr h8
    refine Finset.mem_range.mpr ?_
    exact Nat.lt_add_right 1 h3
  rcases hp with ⟨q, hq⟩
  use q
  constructor
  ·  exact hq.left
  have hq2 := h1 q
  have h3 : q ∉ Finset.range (n+1) := by
    by_contra
    have hql := hq.left
    have hqr := hq.right
    exact hq2 this hql hqr
  contrapose h3
  apply Nat.lt_of_not_le at h3
  exact Finset.mem_range.mpr h3
/-Transparency: During this proof, I had ChatGPT help me learn the syntax required for the product.
I also used it to remind me how to split \and using rcases. I also used it for some other syntax and stuff.
The proof is based on Euclid's approach. The rest was all apply? exact?!
I tried to avoid using ChatGPT too much, and I think I did a pretty good job (I only used it when I was really confused for troubleshooting help).-/
end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
variable {I : Finset α} {f : α → ℕ}

#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise3_induction_proof (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a s z r =>
    rw[Finset.sum_insert]
    · exact (Nat.dvd_add_iff_right (h a)).mp r
    exact z

theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  have h1 : ∃g : α → ℕ,∀ x, d*(g x) = f x := by
    use fun x ↦ (f x)/d
    intro x
    exact Nat.mul_div_cancel' (h x)
  rcases h1 with ⟨g, hg⟩
  use ∑ i ∈ I, g i
  rw[Finset.mul_sum]
  exact Eq.symm (Finset.sum_congr rfl fun x a ↦ hg x)
end


/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
