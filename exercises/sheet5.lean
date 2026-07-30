import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.DivMod

import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Rat
import LectureNotes.lecture6.examples6
structure RatSeq where
  x : ℕ → ℚ

variable (a b : ℝ)
lemma flip_abl (h : a < b) : b > a := by
  exact h
lemma flip_able (h : a ≤ b) : b ≥ a := by
  exact h
/-
This instance tells Lean that a `RatSeq` may be used as a function `ℕ → ℚ`.
Thus, `f n` uses the stored function `f.x`.
-/
instance : CoeFun RatSeq (fun _ => ℕ → ℚ) where
  coe f := f.x

/-
Likewise, `RealSeq` is a type whose terms package functions `ℕ → ℝ`.
Although `RatSeq` and `RealSeq` have the same shape, they are distinct types:
one stores a rational-valued function and the other a real-valued function.
-/
structure RealSeq where
  x : ℕ → ℝ

instance : CoeFun RealSeq (fun _ => ℕ → ℝ) where
  coe f := f.x

/-
We can convert a `RatSeq` to a `RealSeq`. It builds a `RealSeq` from a
`RatSeq` by coercing each rational value `f.x n` to a real value.
-/
abbrev RatSeq.toRealSeq (f : RatSeq) : RealSeq where
  x n := (f.x n : ℝ)

/-
This instance tells Lean to insert `RatSeq.toRealSeq` when it has a `RatSeq`
but the expected type is `RealSeq`.
-/
instance : Coe RatSeq RealSeq where coe x := x.toRealSeq

-- The expected result type causes Lean to insert the registered coercion.
example (x : RatSeq) : RealSeq := x

/-
How to define a sequence of rational numbers.
-/
example : RatSeq where
  x n := 1 / n

example : RatSeq where
  x := fun n ↦ 1 / n

-- Direct wrapper
example : RatSeq := ⟨fun n ↦ 1 / n⟩


/-
We are ready to define Cauchy sequences and limits of sequences.
Note the type coercions in the definitions, including those for `ε`, `n`, `m`,
and `N`.
-/
def isCauchy (x : RatSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε

def tends_to (x : RatSeq) (a : ℚ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε

def isCauchyReal (x : RealSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε

def tends_toReal (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε


theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  push_cast
  have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn' : (1 : ℝ) / ε ≤ (n : ℝ) + 1 := by linarith
  exact (one_div_le hε hb).mp hn'

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε hε
  obtain ⟨δ, hδpos, hδle⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ hδpos
  exact ⟨N, fun n hn => lt_of_lt_of_le (hN n hn) hδle⟩

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro h ε hε
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
    obtain ⟨N, hN⟩ := h q hq0
    refine ⟨N, fun n hn m hm => ?_⟩
    have hmn := hN n hn m hm
    change dist (↑(x.x n) : ℝ) (↑(x.x m) : ℝ) < ε

    calc dist ((↑(x.x n) : ℝ)) (↑(x.x m : ℝ)) = dist (x n) (x m) := Rat.dist_cast (x n) (x m)
      _ < q := by exact_mod_cast hmn
      _ < ε := hqε
  · intro h ε hε
    have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨N, hN⟩ := h ε hε'
    refine ⟨N, fun m n hm hn => ?_⟩
    have hmn := hN m n hm hn
    rw [Rat.dist_cast] at hmn
    exact_mod_cast hmn

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx (ε / 2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  calc dist (x m) (x n) ≤ dist (x m) a + dist a (x n) := dist_triangle _ _ _
    _ = dist (x m) a + dist (x n) a := by rw [dist_comm a (x n)]
    _ < ε / 2 + ε / 2 := add_lt_add (hN m hm) (hN n hn)
    _ = ε := by ring

/-
Finally, define a sequence of real numbers that does not converge.
-/
def my_diverging_sequence : RealSeq where
  x n := (n : ℝ)

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  rintro ⟨a, ha⟩
  obtain ⟨N, hN⟩ := ha 1 (by norm_num)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (a + 1)
  set n := max N n0 with hn_def
  have hnN : n ≥ N := le_max_left _ _
  have hnn0 : n ≥ n0 := le_max_right _ _
  have h1 : dist ((n : ℝ)) a < 1 := hN n hnN
  have h2 : (n : ℝ) > a + 1 := lt_of_lt_of_le hn0 (by exact_mod_cast hnn0)
  have h3 : dist ((n : ℝ)) a ≥ 1 := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  have h4 : 1≤ dist (↑n) a := (by exact h3)

  have h5 : (dist (↑n) a < dist (↑n) a) := (by exact h1.trans_le h4)
  simp at h5
