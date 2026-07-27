import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Rat

/-
How to manage a zoo of types a.k.a. coercion.
-/

section

variable {n m : ℕ} {x : ℚ} {f : ℝ → ℝ}

#check 1/n

#check (1/n : ℚ)

#check x + 1/n

#check (x : ℝ) + (1/n : ℝ)

#check ((x + 1/n) : ℝ)

#check (((x : ℚ) + (1/n : ℚ)) : ℝ)

example : (((x : ℚ) + (1/n : ℚ)) : ℝ) = ((x + 1/n) : ℝ) := by
  simp


noncomputable example : ℝ := f (x + 1/n)

/-
What happens in the last example:
1) Since f expects a real number, lean knows to that the '+' is the one for real numbers,
so it needs to convert both x and 1/n to real numbers.
2) Lean knows how to convert rational numbers to real numbers, so it converts x to a real number.
3) Since lean expects a real number as 1/n, it converts n to a real number,
and then computes 1/n as a real number.
-/

/-
Lean is really good a figuring out which coercion to use.
-/
variable (k : Fin n) (l : Fin m)

#check (k : ℕ) + (l : ℕ)

#check (k + l : ℕ)

#check (k : ℕ) + l

#check (k + l: ℝ)


/-
Sequences of rational and real numbers.
A sequence of rational numbers is a function from natural numbers to rational numbers `x : ℕ → ℚ`.
-/

namespace MySequences

variable {a b : ℝ} {c d : ℚ}

#check |a|

#check |c|

#check dist a b

#check dist c d

example : dist a b = |a - b| := by
  rfl

class RatSeq where
  x : ℕ → ℚ

instance : CoeFun RatSeq (fun _ => ℕ → ℚ) where
  coe f := f.x

class RealSeq where
  x : ℕ → ℝ

instance : CoeFun RealSeq (fun _ => ℕ → ℝ) where
  coe f := f.x

abbrev RatSeq.toRealSeq (f : RatSeq) : RealSeq where
  x n := (f.x n : ℝ)

instance : Coe RatSeq RealSeq where coe x := x.toRealSeq

example (x : RatSeq) : RealSeq := x

-- Cauchy sequences. Note the type coercion in the defn (ε, and n, m, N)!
def isCauchy (x : RatSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε

def tends_to (x : RatSeq) (a : ℚ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε

def isCauchyReal (x : RealSeq) := ∀ ε > 0, ∃ N, ∀ m≥ N, ∀ n≥ N, dist (x m) (x n) < ε

def tends_toReal (x : RealSeq) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n≥ N, dist (x n) a < ε

-- We can evaluate tends_toReal on a sequence of rational numbers!
example (x : RatSeq) (a : ℝ) : tends_toReal x a := by sorry

lemma isCauchy_toReal (x : RatSeq) : isCauchy x → isCauchyReal x := by
  sorry

-- This is essentially the definition of the real numbers.
theorem real_numbers_complete {x : RatSeq} (hx : isCauchy x) : ∃ a : ℝ, tends_toReal x a := by
  sorry

/- Uniqueness of the limit of a sequence of real numbers follows from the following result.
Two numbers are equal if their distance is less than any positive number. -/

#check @eq_of_forall_dist_le _ _ a b

lemma tends_toReal_unique {x : RealSeq} {a b : ℝ} (hx : tends_toReal x a) (hy : tends_toReal x b) :
  a = b := by
  apply eq_of_forall_dist_le
  intro ε hε
  have ⟨N, hN⟩ := hx (ε/2) (half_pos hε)
  have ⟨M, hM⟩ := hy (ε/2) (half_pos hε)
  let K := max N M
  have hKa : dist (x K) a < ε/2 := by
    exact hN K (le_max_left N M)
  have hKb : dist (x K) b < ε/2 := by
    exact hM K (le_max_right N M)
  calc
    dist a b ≤ dist a (x K) + dist (x K) b := by
      exact dist_triangle a (x K) b
    _ ≤ ε/2 + ε/2 := by
        apply le_of_lt
        exact add_lt_add (Metric.mem_ball'.mp (hN K (le_max_left N M))) hKb
    _ = ε := by
      rw[add_halves]

end MySequences

end
