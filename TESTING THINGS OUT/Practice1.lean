/-
practice on the basics 7/15/25
thnx claude

exercise 15 is not really understood btw


key things to note:

cases AND
cases OR
by_cases
Classical.em (and what em means)
constructor
contradiction
hnp hp  (and not hp hnp, or whichever way it is)
exact \< h1, h2\>
absurd hp hnp (and the order it needs to be in)
right left
ordering
- like say hpq : P->Q
- hp:P
- then we write hpq hp
- or smth like that
intro
-/

import Std
import Mathlib.Tactic.ByContra

variable {P Q R : Prop}

theorem practice1 (hp : P) (h1 : P → Q) (h2 : Q → R) : R := by
  apply h2
  apply h1
  exact hp

theorem practice2 (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro h1 h2 =>
    exact ⟨h2, h1⟩


theorem practice3 (h : P ∧ Q) : P := by
  cases h with
  | intro h1 h2 =>
    exact h1

theorem practice4 (h : P ∨ Q) (h1 : P → R) (h2 : Q → R) : R := by
  cases h with
  | inl hp =>
      apply h1
      exact hp
  | inr hq =>
      apply h2
      exact hq

theorem practice5 (hnp : ¬ P) (hp : P) : Q := by
  exact absurd hp hnp

theorem practice6 (h : ¬ Q → ¬ P) (hp : P) : Q := by
  by_contra hq
  exact absurd hp (h hq)



theorem practice7 (h : ¬ P ∨ ¬ Q) : ¬ (P ∧ Q) := by
  intro hpq
  cases h with
  | inl hp =>
      exact hp hpq.1
  |inr hq =>
      exact hq hpq.2


variable {P Q R S : Prop}

theorem practice9 (h1 : P → Q) (h2 : Q → R) (h3 : R → S) (hp : P) : S :=
  /-
  apply h3
  apply h2
  apply h1
  exact hp
  -/
  h3 (h2 (h1 hp))
  --notice the () also we dropped "by"


theorem practice10 (h : P ∧ (Q ∧ R)) : (P ∧ Q) ∧ R := by
  constructor
  · cases h with
    | intro hp hqr
    cases hqr with
    | intro hq hr
    constructor
    · exact hp
    exact hq
  cases h with
  | intro hp hqr
  cases hqr with
  | intro hq hr
  exact hr


theorem practice11 (h : (P ∨ Q) ∨ R) : P ∨ (Q ∨ R) := by
  obtain (hp | hq) | hr := h
  · left
    exact hp
  · right
    left
    exact hq
  · right
    right
    exact hr

theorem practice12 (h1 : P ∨ Q) (h2 : ¬ P) : Q := by
  cases h1 with
  |inl hp =>
      contradiction
  |inr hq =>
      exact hq


theorem practice13 (h : P → (Q → R)) : (P ∧ Q) → R := by
  intro hpq
  cases hpq with
  | intro hp hq =>
      exact h hp hq

theorem practice13' (h : P → (Q → R)) : (P ∧ Q) → R := by
  intro hpq
  exact h hpq.1 hpq.2

--note: intro hp hq is the same as hpq.1 hpq.2

theorem practice14 (h : (P ∧ Q) → R) : P → (Q → R) := by
  intro hp hq
  exact h ⟨hp, hq⟩


--suppose goal is P->Q
--take intro hp
--then, Q becomes the goal, hp: P

--lowk dont know whats going on here but its chill
theorem practice15 (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  constructor
  · intro hp
    exact h (Or.inl hp)
  · intro hq
    exact h (Or.inr hq)

theorem practice16 (h : ¬ P ∧ ¬ Q) : ¬ (P ∨ Q) := by
  intro hpq
  cases hpq with
    | inl hp =>
      cases h with
      | intro hp' hq
      contradiction
    | inr hq =>
      cases h with
      | intro hp hq'
      contradiction

theorem practice17 : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · intro h hq
    by_cases hp : P
    · have hq' := h hp
      exact absurd hq' hq
    · exact hp
  intro h hp
  by_cases hq : Q
  · exact hq
  · have hp' := h hq
    exact absurd hp hp'

theorem practice18 (h : P ↔ Q) : ¬ P ↔ ¬ Q := by
  constructor
  · intro hnp hq
    have hp' := h.mpr hq
    exact hnp hp'
  intro hnq hp
  have hq' := h.mp hp
  exact hnq hq'

theorem practice19 (h : ¬ ¬ (P ∨ ¬ P)) : True := by
  have h' := h --just so it doesnt show an error
  trivial
  --lmao

theorem practice20 (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) : R := by
  by_cases hq : Q
  · exact h3 hq
  · cases h1 with
    |inl hp=>
      exact h2 hp
    |inr hq'=>
      contradiction





theorem exercise1 : (¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hq : Q
    · left
      intro hp
      have hpq : P ∧ Q := ⟨hp, hq⟩
      exact h hpq
    · right
      exact hq
  --now, show the <= that    (¬ P ∨ ¬ Q) => (¬(P ∧ Q))
  intro h
  cases h with
  | inl hnp=>
    intro hpq
    cases hpq with
    | intro hp hq
    exact hnp hp
  | inr hnq=>
    intro hpq
    cases hpq with
    | intro hp hq
    exact hnq hq
