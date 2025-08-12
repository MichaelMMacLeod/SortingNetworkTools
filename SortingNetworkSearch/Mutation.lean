import Std.Data.HashMap

inductive Mutation where
  | swapLayers
  | removeSmallestLayer
  | removeRandomLayer
  | rotateRandomLayer
  | addRandomSwap
  | removeRandomSwap
  deriving BEq, Hashable, Repr

instance : Inhabited Mutation where
  default := .addRandomSwap

def Mutation.chances : Std.HashMap Mutation Nat := .ofList [
  (swapLayers, 100),
  (removeSmallestLayer, 0),
  (removeRandomLayer, 10),
  (rotateRandomLayer, 0),
  (addRandomSwap, 1300),
  (removeRandomSwap, 620),
]

def Mutation.chancesSum : Nat := Mutation.chances.valuesArray.sum

def Mutation.chancesNormalized : Std.HashMap Mutation Float :=
  Mutation.chances.filterMap
    fun _ v =>
      if v = 0 then
        none
      else
        some <| v.toFloat / Mutation.chancesSum.toFloat

def Mutation.bounds : Array (Float × Mutation) :=
  let result := Prod.fst <| Mutation.chancesNormalized.fold
    (init := ([], (0 : Float), 0))
    fun (acc, lowerBound, numSeen) k v =>
      let upperBound : Float :=
        if numSeen + 1 = Mutation.chancesNormalized.size then
          1
        else
          lowerBound + v
      let acc := acc.cons (upperBound, k)
      (acc, upperBound, numSeen + 1)
  result.mergeSort (le := fun (a, _) (b, _) => a ≤ b) |>.toArray

def Mutation.pickAtRandom [RandomGen Gen] (g : Gen) : Mutation × Gen :=
  let (k, g) := randNat g 0 USize.size
  let k := k.toFloat / USize.size.toFloat
  let m := Id.run do
    for (upperBound, m) in Mutation.bounds do
      if k ≤ upperBound then
        return m
    panic! "no mutation found"
  (m, g)
