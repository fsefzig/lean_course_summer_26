-- Define a custom type representing days of the week
inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

-- Function using pattern matching
def isWeekend (d : Day) : Bool :=
  match d with
  | Day.saturday => true
  | Day.sunday   => true
  | _            => false  -- wildcard matching all other days

#eval isWeekend Day.saturday  -- Output: true
#eval isWeekend Day.monday    -- Output: false
