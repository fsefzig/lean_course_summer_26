import Std
import Mathlib.Tactic.ByContra

-- Example 1. Implication is a function

/-
The Curry-Howard correspondence says that every proposition defines a type,
and a proof of that proposition corresponds to a term of that type.
In particular, an implication P → Q is a function from the type P to the type Q.
In other words, a proof of P → Q is a function that takes a proof of P and returns a proof of Q.
-/

variable {P Q : Prop}

theorem example1 (hp : P) (h : P → Q) : Q := by
  --goal is to construct an element of Q (as a function)
  --h is a function of P to Q, so it's enough to have
  --something of type p

  apply h

  --hp, the hypothesis, says there is an element of P
  --so, we take the function of this to Q
  --take the exact, we're done

  exact hp


--the following shows we can do this all in one step
--so we apply h to hp, it gives an element of Q

theorem example1' (hp : P) (h : P → Q) : Q := by
  exact h hp
  --in other words, h(hp), we dont need to write brackets tho


--and finally can ommit "exact" cuz like idk why not
theorem example1'' (hp : P) (h : P → Q) : Q :=
  h hp




-- Example 2. AND is a product

--note: hp, hq means we have a proof of P and a proof of Q
theorem example2 (hp : P) (hq : Q) : P ∧ Q := by
  constructor--this is the command to combin two things
    --tactic state changes from one goal of P ∧ Q, to two goals,
    --construct two terms of the product; proving P and proving Q
  · exact hp --small dot tells compiler "Hey i'm proving first goal"
  exact hq


theorem example2' (hp : P) (hq : Q) : P ∧ Q :=
  ⟨hp, hq⟩
  --this directly does it

--Alternatively, we can use the ⟨-,-⟩ notation to construct a term of the conjunction type directly.

-- Example 3. OR is a sum


theorem example3 (hp : P) : P ∨ Q := by
  left --take the left side, "P"
  exact hp

theorem example3' (hq : Q) : P ∨ Q := by
  right
  exact hq

/-
Whenever your goal is of the form P ∨ Q, we can use the 'left' or 'right' tactic to tell the proof
assistant which disjunct we want to prove.
The 'left' tactic creates a subgoal for the first disjunct,
and the 'right' tactic creates a subgoal for the second disjunct.
-/

theorem example3'' (h : P ∨ Q) : Q ∨ P := by
  cases h with --we dont know which of the two sides is true
  -- here being the h: P ∨ Q

  | inl hp => --case of the left true, we call it hp
      right  --and then we run right upon the Q ∨ P
      exact hp
  | inr hq => --case of the right true (Q), call it hq
      left  --run the left upon the Q ∨ P
      exact hq


--FIGURE THIS OUT!!
theorem example3''' (h : P ∨ Q) : Q ∨ P := by
  rcases h with h1 | h2

  | h1
    right
    exact hnp
  | h2
    left
    exact hnq



-- Example 4. NOT is a function to false
--WHATS GOING ON HERE??????
theorem example4 (h1 : P → Q) (h2 : ¬ Q) : ¬ P := by
--note ¬ P =  P => false

  intro hp --the is default defined hp : P

  have hq := h1 hp -- introduce something new
  -- we introd
  exact h2 hq --h2 to hq; the falsity of Q





/-
When proving an implication, here (P → False), we can use the 'intro' tactic to introduce
the assumption of the implication into the context.
Moreover, the 'have' tactic allows us to create a new hypothesis in the context.
-/


theorem example4' (h1 : P → Q) (h2 : ¬ Q) : ¬ P :=
  fun hp => h2 (h1 hp)
  --compose functions and define a new function
  --f(hp) = h2 (h1 (hp))
  --function of hp, output is applying h2 to (h1 applied to hp)




theorem example4'' (h1 : P → Q) (h2 : ¬ Q) : ¬ P :=
  h2.comp h1

-- The composition of two functions (or implications) is written as h2.comp h1.


theorem double_negation : ¬ ¬ P ↔ P := by
  --exact not_not
  exact?

--note: if we type in "exact?" it will find it for us
--pretty much just cheating lmao




-- Contrapostion

theorem contraposition (h : P → Q) : ¬ Q → ¬ P := by
  intro hq
  exact example4' h hq


theorem contraposition' (h : P → Q) : ¬ Q → ¬ P :=
  fun hq hp => hq (h hp)


-- Proof by contradiction

--two theorems in the library

theorem excluded_middle : P ∨ ¬ P := by
  exact Classical.em P

theorem by_contradiction1 (h : ¬ P → False) : P :=
  double_negation.mp h

/-
When we have a theorem of the form P ↔ Q, we can access the individual implications
using the .mp (P → Q), and .mpr (Q → P) methods.
-/

theorem by_contradiction2 (h : ¬ P → False) : P := by
  by_contra hnp
  --changes the goal to false, assumes whatever we want
  --to prove is not true
  --aka, we make "hnp" into the falsity of P
  --then just apply h to hnp
  exact h hnp

/-
The tactic called 'by_contra' that allows us to prove a proposition by contradiction.
It changes the goal from P to False, and adds ¬ P to the context.
-/
