import LectureNotes.lecture7.examples7
import LectureNotes.lecture6.examples6
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Rat

structure RatSeq where
  x : ℕ → ℚ
structure RealSeq where
  x : ℕ → ℝ

def isCauchySum (seq : RatSeq) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖∑ i ∈ Finset.Ico n (m + 1), seq.x i‖ < ε
def ConvergesToReal (seq : RealSeq) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (∑ i ∈ Finset.range n, seq.x i) a < ε
