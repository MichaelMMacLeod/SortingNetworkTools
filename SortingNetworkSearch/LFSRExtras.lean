def checkPeriod (f : Nat → Nat) : Nat := Id.run do
  let start := 1
  let mut i := f start
  let mut result : Nat := 1
  while i ≠ start do
    i := f i
    result := result + 1
    if result % 10000000 = 0 then
      result := dbgTraceVal result
  pure result
