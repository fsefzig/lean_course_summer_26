-- Single-line comments start with two dashes
/- Multi-line comments
   are enclosed like this -/

-- Checking types
#check 42        -- Output: 42 : Nat
#check "hello"   -- Output: "hello" : String
#check true      -- Output: true : Bool
#check false     -- Output: false: Bool

-- Evaluating expressions
#eval 5 + 10                -- Output: 15
#eval "Hello, " ++ "Lean!"  -- Output: "Hello, Lean!"
