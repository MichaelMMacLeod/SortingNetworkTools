def Array.isValidLayer (la : Array Nat) : Bool := Id.run do
  for i in [0:la.size] do
    if let some lai := la[i]? then
      if let some lalai := la[lai]? then
        if i = lalai then
          continue
    return false
  true

def Nat.factorial (n : Nat) : Nat :=
  go n 1
where
  go (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc else go (n - 1) (n * acc)

-- Sequence A000085 in OEIS
def countValidLayers (size : Nat) : Nat :=
  (size / 2 + 1).fold
    (init := 0)
    fun k _ acc =>
      acc + size.factorial / ((size - 2 * k).factorial * 2 ^ k * k.factorial)
