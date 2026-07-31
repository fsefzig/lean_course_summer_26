-- A simple function that adds two natural numbers
def add (a : Nat) (b : Nat) : Nat :=
  a + b

#eval add 3 7  -- Output: 10

-- A function using conditional logic
def maxVal (a : Nat) (b : Nat) : Nat :=
  if a > b then a else b

#eval maxVal 12 4  -- Output: 12

example (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by
  injection h
-- if the succ(a) = succ(b), then a=b

example (n : Nat) : Nat.succ n ≠ Nat.zero := by
  intro h
  nomatch h
-- zero is nothe successor of any natural number

-- Def add
example (a b : Nat) : Nat :=
  match b with
  | Nat.zero => a
  | Nat.succ b' => Nat.succ (add a b')

  theorem zero_add (n : Nat) : 0 + n = n := by
    induction n with
    | zero =>
        rfl  -- Base case: 0 + 0 = 0
    | succ k hk =>
        -- hk is the induction hypothesis: 0 + k = k
        rw [Nat.add_succ, hk]

-- Lemma zero_add
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k hk =>
      -- 0 + succ k = succ (0 + k) by definition
      -- then substitute hk (0 + k = k) to get succ k
      rw [Nat.add_succ, hk]


-- lemma succ_add
example (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rfl
  | succ k hk =>
      -- Expand definitions using add_succ, apply hypothesis hk
      rw [Nat.add_succ, hk, Nat.add_succ]

theorem add_comm (a b : Nat) : a + b = b + a := by
  induction b with
  | zero =>
      rw [zero_add]
  | succ k hk =>
      rw [Nat.add_succ, Nat.succ_add, hk]

def mul (a b : Nat) : Nat :=
  match b with
  | Nat.zero => 0
  | Nat.succ b' => mul a b' + a
-- a x (b+1) = (axb) + a

def factorial (n : Nat) : Nat :=
  match n with
  | Nat.zero => 1
  | Nat.succ n' => (Nat.succ n') * factorial n'
-- (n + 1)! = (n + 1) x n!

#eval factorial 5 -- Evaluates to 120

-- Fibonacci Numbers
def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n
#eval fib 0 -- 0
#eval fib 1 -- 1
#eval fib 7 -- 13
#eval fib 15 -- 610
