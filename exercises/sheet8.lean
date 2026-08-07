import LectureNotes.lecture9.examples9

open BoxIntegral

namespace MyRiemannIntegral

noncomputable section

/-!
In this exercise we transport a prepartition of `[0, 1]` to a prepartition of `[a, b]`
using the affine map

`x ↦ a + (b - a) * x`.

We work only with `Prepartition`s here: no tags are transported.
-/

abbrev exerciseUnitInterval : Box (Fin 1) :=
  intervalToBox 0 1 zero_lt_one

def affinePoint (a b : ℝ) (x : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun i => a + (b - a) * x i

def affineBox (a b : ℝ) (hab : a < b) (J : Box (Fin 1)) : Box (Fin 1) :=
  Box.mk (affinePoint a b J.lower) (affinePoint a b J.upper) (by
    intro i
    dsimp only [affinePoint]
    nlinarith [J.lower_lt_upper i])

/-
Exercise 1:
Define the affine image of a prepartition of `[0, 1]`.

The boxes of the new prepartition should be the images `affineBox a b hab J` of the
boxes `J` in `π`.  You may find `Finset.image` useful.  Besides defining this finite
set, you have to prove that every transformed box lies in `[a, b]` and that distinct
transformed boxes are disjoint.
-/
noncomputable def affinePrepartition {a b : ℝ} (hab : a < b)
    (π : Prepartition exerciseUnitInterval) :
    Prepartition (intervalToBox a b hab) := by
  sorry

/-
Exercise 2:
Show that the affine image of a partition is again a partition.  In other words, prove
that the transformed boxes cover all of `[a, b]` whenever the original boxes cover
all of `[0, 1]`.
-/
theorem affinePrepartition_isPartition {a b : ℝ} (hab : a < b)
    {π : Prepartition exerciseUnitInterval} (hπ : π.IsPartition) :
    (affinePrepartition hab π).IsPartition := by
  sorry

end

end MyRiemannIntegral
