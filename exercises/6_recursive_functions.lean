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
