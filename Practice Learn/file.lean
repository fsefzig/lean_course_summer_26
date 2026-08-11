#check 42     -- check type
#check "hello"
#check true

#eval 5+10 -- for expression
#eval "Hello, " ++ "Lean!" -- Output: "Hello, Lean!"

def add (a:Nat)(b:Nat):Nat :=
    a+b
#eval add 5 7 -- call function defined above

def maxVal (a:Nat)(b:Nat): Nat :=
    if a>b then a else b
#eval maxVal 12 4 -- Output 12

def minVal (a:Nat)(b:Nat): Nat :=
    if a<b then a else b
#eval minVal 12 4

-- Define a custom type representing days of the week
inductive Day where
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday

def isweekend (d:Day):Bool :=
    match d with
    | Day.saturday => true
    | Day.sunday => true
    | _          => false

#eval isweekend Day.saturday
#eval isweekend Day.friday

inductive Ninja where
    | Kai
    | Cole
    | Jay
    | Nya
    | Wu
    | Lloyd
    | Gale
    | Steve
    | Bentho

def isninja (d:Ninja):Bool :=
    match d with
    | Ninja.Bentho => false
    | Ninja.Gale => false
    | _          => true

#eval isninja Ninja.Bentho
#eval isninja Ninja.Lloyd

theorem add_zero_eq (n:Nat) : n+0 = n := by
    rfl -- 'rfl' reflexivity (equality by definition)

theorem add_num (n:Nat) : n+1+2 = n+3 := by
    rfl -- 'rfl' reflexivity (equality by definition)

--Define a structure for a 2D point
structure Point where
    x: Float
    y: Float
    deriving Repr -- Allows Lean to print the structure in #eval

-- Instantiate a point
def myPoint : Point := { x := 3.0, y:= 4.0}

#eval myPoint.x -- Output: 3.000000

def originDistance (p:Point): Float :=
    Float.sqrt (p.x * p.x + p.y * p.y)

#eval originDistance myPoint  -- Output: 5.000000


def myPoint3 : Point := { x := 3.0, y:= 4.0, z:= 6.0}

#eval myPoint3.x -- Output: 3.000000

def originDistance3 (p:Point): Float :=
    Float.sqrt (p.x * p.x + p.y * p.y + p.z * p.z)

#eval originDistance myPoint3  -- Output: 5.000000

-- Factorial function using pattern matching
def factorial (n : Nat) : Nat :=
  match n with
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5  -- Output: 120

-- Computing the sum of a list
def sumList (xs : List Nat) : Nat :=
  match xs with
  | []      => 0
  | x :: rest => x + sumList rest

#eval sumList [1, 2, 3, 4]  -- Output: 10


theorem add_example (a b c : Nat) : (a+b)+c = a+ (c+b) := by
-- 1. Regroup LHS from (a + b) + c to a + (b + c)
    rw [Nat.add_assoc]
-- 2. Swap b + c to c + b
    rw [Nat.add_comm b c]

theorem imp_example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  -- Goal: Q
  apply hPQ
  -- Goal is now: P
  exact hP

theorem imp_example2 (P Q : Prop) (hP : Q) (hPQ : Q → P) : P := by
  -- Goal: Q
  apply hPQ
  -- Goal is now: P
  exact hP

theorem or_swap (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  -- Case split on whether P is true or Q is true
  rcases h with hP | hQ
  · -- Case 1: P is true
    right
    exact hP
  · -- Case 2: Q is true
    left
    exact hQ
