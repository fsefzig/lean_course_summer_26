-- Define a structure for a 2D Point
structure Point where
  x : Float
  y : Float
  deriving Repr  -- Allows Lean to print the structure in #eval

-- Instantiate a Point
def myPoint : Point := { x := 3.0, y := 4.0 }

-- Access fields using dot notation
#eval myPoint.x  -- Output: 3.000000

-- Functions operating on structures
def originDistance (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval originDistance myPoint  -- Output: 5.000000
