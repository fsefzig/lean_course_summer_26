import Std
import Mathlib.Tactic.Use

section

variable {P Q : Prop}

theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  apply Iff.intro
  · intro h
    by_cases hp : P
    · apply Or.inr
      intro hq
      apply h
      exact And.intro hp hq
    · apply Or.inl
      exact hp
  · intro h
    intro hpq
    cases h with
    | inl hnp =>
        exact hnp hpq.left
    | inr hnq =>
        exact hnq hpq.right

theorem exercise2 (h : P ∨ Q) (hp : ¬ P) : Q := by
  cases h with
  | inl hp' =>
      contradiction
  | inr hq =>
      exact hq

end

section -- Quantifiers

variable {T : Type} {P : T → Prop}

theorem exercise3 (h : ∀ x, P x) (x : T) : P x := by
  exact h x

theorem theorem_we_want_to_use (x : T) : P x := by
  sorry

theorem exercise4 : ∀ x, P x := by
  intro x
  exact theorem_we_want_to_use x

theorem exercise5 (h : ∀ x, P x) (y : T) : ∃ y, P y := by
  use y
  exact h y

theorem exercise6 (n : Nat) (h : ∃ k, n = 2 * k) : ∃ l, n*n = 4 * l := by
  rcases h with ⟨k, hk⟩
  use k * k
  rw [hk]
  rw [hk]
  -- now: (2 * k) * (2 * k) = 4 * (k * k)
  rw [Nat.mul_assoc]
  rw [Nat.mul_assoc]
  rw [Nat.mul_comm k 2]
  rw [← Nat.mul_assoc]
  rw [Nat.mul_comm k 2]
  rw [Nat.mul_assoc]
  rfl

end
