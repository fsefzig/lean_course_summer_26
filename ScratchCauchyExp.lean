import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Topology.MetricSpace.CauSeqFilter

open CauSeq Finset IsAbsoluteValue

structure RealSeq where
  x : ℕ → ℝ

instance : CoeFun RealSeq (fun _ => ℕ → ℝ) where
  coe f := f.x

def MyTendsTo (x : RealSeq) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) a < ε

lemma cauSeq_tendsTo_lim (s : CauSeq ℝ abs) :
    MyTendsTo ⟨s⟩ (CauSeq.lim s) := by
  intro ε hε
  change CauSeq.LimZero (s - CauSeq.const abs (CauSeq.lim s)) at CauSeq.equiv_lim s
  obtain ⟨N, hN⟩ := CauSeq.equiv_lim s ε hε
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

lemma cauchySeq_has_custom_limit {x : RealSeq} (hx : CauchySeq x) :
    ∃ a : ℝ, MyTendsTo x a := by
  let s : CauSeq ℝ abs := ⟨x, isCauSeq_iff_cauchySeq.mpr hx⟩
  exact ⟨CauSeq.lim s, cauSeq_tendsTo_lim s⟩

theorem isCauSeq_real_exp (x : ℝ) :
    IsCauSeq abs fun n => ∑ m ∈ range n, x ^ m / m.factorial :=
  let ⟨n, hn⟩ := exists_nat_gt |x|
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg _) hn
  IsCauSeq.series_ratio_test n (|x| / n) (div_nonneg (abs_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_abs, abs_abs, Nat.factorial_succ, pow_succ', mul_comm m.succ, Nat.cast_mul,
        ← div_div, mul_div_assoc, mul_div_right_comm, abs_mul, abs_div, abs_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)

noncomputable def realExpSeq (x : ℝ) : CauSeq ℝ abs :=
  ⟨fun n => ∑ m ∈ range n, x ^ m / m.factorial, isCauSeq_real_exp x⟩

noncomputable def myExp (x : ℝ) : ℝ := CauSeq.lim (realExpSeq x)

theorem realExpSeq_tendsTo (x : ℝ) : MyTendsTo ⟨realExpSeq x⟩ (myExp x) :=
  cauSeq_tendsTo_lim (realExpSeq x)
