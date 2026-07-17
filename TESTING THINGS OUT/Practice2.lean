import Std
import Mathlib.Tactic.ByContra

section

variable {T : Type} {P Q : T → Prop} {R : Prop}

theorem qpractice1 (h : ∀ x, P x) (a b : T) : P a ∧ P b := by
  constructor
  · exact h a
  · exact h b


theorem qpractice2 (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) (a : T) : Q a := by
  apply h1 a
  exact h2 a

theorem qpractice3 (h : ∀ x, P x ∧ Q x) : ∀ x, P x := by
  intro x --x becomes a fixed, but unknown (unspecified; it can be anything) number
  --goal becomes just show P x
  have hx := h x
  exact hx.1

theorem qpractice4 (h : ∀ x, P x) : ∀ x, P x ∨ Q x := by
  intro x
  left
  exact h x

theorem qpractice5 : ∀ x : T, x = x := by
  intro x
  rfl

theorem qpractice6 (a : T) (h : P a) : ∃ x, P x := by
  sorry

theorem qpractice7 (h : ∃ x, P x ∧ Q x) : ∃ x, P x := by
  sorry

theorem qpractice8 (h1 : ∃ x, P x) (h2 : ∀ x, P x → Q x) : ∃ x, Q x := by
  sorry

theorem qpractice9 (h : ∃ x, P x) : ¬ (∀ x, ¬ P x) := by
  sorry

theorem qpractice10 (h : ¬ ∃ x, P x) : ∀ x, ¬ P x := by
  sorry

theorem qpractice11 (h : ∀ x, ¬ P x) : ¬ ∃ x, P x := by
  sorry

theorem qpractice12 (n : Nat) (h : ∃ k, n = k + k) : ∃ l, n + n = l + l + l + l := by
  sorry

theorem qpractice13 (h : ∀ x, P x → Q x) : (∃ x, P x) → (∃ x, Q x) := by
  sorry

end

