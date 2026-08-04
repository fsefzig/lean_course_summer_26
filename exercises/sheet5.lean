import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le
#check inv_eq_one_div

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · use ⌈1 / ε⌉.toNat
    refine ⟨Nat.ceil_pos.mpr (show 0 < ⌈1 / ε⌉ by positivity), ?_⟩
    apply (one_div_le _ _).mpr
    · have h : (⌈1 / ε⌉.toNat : ℝ) = ⌈1 / ε⌉ := by
        exact_mod_cast Int.toNat_of_nonneg (by positivity)
      rw[h]
      exact Int.le_ceil (1 / ε)
    · apply Nat.cast_pos'.mpr
      exact Nat.ceil_pos.mpr (show 0 < ⌈1 / ε⌉ by positivity)
    exact hε
  use 1
  exact ⟨by positivity, by linarith⟩

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_to x a := by
  unfold tends_to
  intro ε hε
  obtain ⟨δ, hδ⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ hδ.1
  use N
  intro n hn
  have h := hN n hn
  exact lt_of_lt_of_le h hδ.2

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor <;>
  · unfold isCauchy isCauchyReal RatSeq.toRealSeq
    simp [Rat.dist_cast]

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_to x a) : isCauchyReal x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε / 2) (by positivity)
  use N
  intro m hm n hn
  calc
    dist (x m) (x n) ≤ dist (x m) a + dist a (x n) := dist_triangle (x m) a (x n)
    _ = dist (x m) a + dist (x n) a := by rw[dist_comm a (x n)]
    _ < ε / 2 + ε / 2 := by exact add_lt_add (hN m hm) (hN n hn)
    _ = ε := by exact add_halves ε

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem fiveadd : (5 : ℝ) = @Nat.cast ℝ Real.instNatCast 5 := by
  exact Eq.symm (Real.ext_cauchy rfl)

theorem exercise5 : ¬ ∃ a : ℝ, tends_to my_diverging_sequence a := by
  unfold tends_to my_diverging_sequence
  dsimp
  intro ⟨a, ha⟩
  obtain ⟨N, hN⟩ := ha 1 (by simp)
  obtain h₁ := hN (N+1) (by simp)
  obtain h₂ := hN (N+5) (by simp)
  rw [Nat.cast_add] at h₁ h₂
  rw [← fiveadd] at h₂
  rw [Nat.cast_one] at h₁
  have add := add_lt_add_of_lt_of_le h₁ (le_of_lt h₂)
  have tri := dist_triangle (N + 1 : ℝ) a (N + 5)
  rw [dist_comm a] at tri
  have x := lt_of_le_of_lt tri add
  rw [Real.dist_eq] at x
  norm_num at x

#check dist
#check Quotient.ind
#check Eq


inductive MQuot.{u} {α : Sort u} (r : α → α → Prop) : Sort (u + 1) where
| mk (a : α) : MQuot r
-- | sound {a b : α} (h : r a b) : MQuot.mk a = MQuot.mk b

-- MQuot.rec.{u v} {α : Sort u} {r : α → α → Prop} {motive : MQuot r → Sort v}
-- (mk : (a : α) → motive (MQuot.mk a))
-- (sound :
--  {a b : α} → (h : r a b) →
--  Eq.ndrec (mk a) (MQuot.sound h) = mk b
-- ) :
--  (x : MQuot r) → motive x

#check Eq.ndrec

def eqz : ℕ → Prop
| 0 => True
| Nat.succ _ => False

theorem not_succ (n : ℕ) : ¬(Nat.succ n = 0) := by
  exact Nat.add_one_ne_zero n


#print axioms Nat.add_one_ne_zero

instance natDecEq (a : ℕ) (b : ℕ) : Decidable (a = b) := match a, b with
| Nat.succ pa, Nat.succ pb =>
  match natDecEq pa pb with
  | Decidable.isTrue h => Decidable.isTrue (h ▸ rfl)
  | Decidable.isFalse h => Decidable.isFalse (fun heq => h <| Nat.succ_injective heq)
| Nat.zero, Nat.zero => Decidable.isTrue rfl
| Nat.zero, Nat.succ p => Decidable.isFalse <| (Nat.add_one_ne_zero p).symm
| Nat.succ p, Nat.zero => Decidable.isFalse <| Nat.add_one_ne_zero p

#print axioms natDecEq

#check Nat.noConfusion
#check Nat.noConfusionType

inductive MEq.{u} {α : Sort u} : α → α → Sort (u + 1) where
| rfl (a : α) : MEq a a
