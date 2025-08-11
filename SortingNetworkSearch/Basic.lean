import Std.Data.HashSet
import Batteries.Data.Rat
import Mathlib.Data.List.Defs
import SortingNetworkSearch.LFSR

def Nat.toBitArray (n : Nat) : Array Bool := Id.run do
  let mut result := default
  for i in [0 : Nat.log2 n + 1] do
    result := result.push <| (n >>> i) &&& 1 = 1
  result

def Nat.toBitString (n : Nat) : String := n.toBitArray.reverse.map (·.toNat) |>.foldl (· ++ ·.repr) ""

def UInt64.toBitString (u : UInt64) : String := u.toNat.toBitString

structure Network (size : Nat) where
  toArray : Array (Array Nat)
  deriving Repr, DecidableEq, Hashable

def Network.instInhabited : Network size :=
  {
    toArray := #[]
  }

instance : Inhabited (Network size) where
  default := Network.instInhabited

abbrev Swaps := Array (Nat × Nat)

def Layer.toSwaps (layer : Array Nat) : Array (Nat × Nat) :=
  Prod.fst <| layer.foldl
    (init := (
      Array.emptyWithCapacity (layer.size / 2),
      Array.replicate layer.size true,
      0
    ))
    fun (acc, notSeen, a) b =>
      if a = b then
        (acc, notSeen, a + 1)
      else
        if notSeen[a]! then
          let acc := acc.push (a, b)
          let notSeen := notSeen.set! b false
          (acc, notSeen, a + 1)
        else
          (acc, notSeen, a + 1)

def Swaps.toLayer (size : Nat) (swaps : Array (Nat × Nat)) : Array Nat :=
  swaps.foldl
    (init := Array.range size)
    fun acc (a, b) =>
      let acc := acc.set! a b
      let acc := acc.set! b a
      acc

def Network.toSwaps (n : Network size) : Swaps :=
  n.toArray.flatMap fun l =>
    let swaps : Std.HashSet (Nat × Nat) := Prod.fst <| l.foldl
      (init := (default, 0))
      fun (acc, a) b =>
        let min := a.min b
        let max := a.max b
        let acc := acc.insert (min, max)
        (acc, a + 1)
    swaps.filter (fun (a, b) => a ≠ b) |>.toArray

def Network.fromLayerSwaps (layers : Array Swaps) : Network size :=
  Network.mk <|
    layers.map fun swaps =>
      swaps.foldl (init := .range size)
        fun acc (a, b) =>
          let acc := acc.set! a b
          let acc := acc.set! b a
          acc


-- def Swaps.run [Inhabited α] (swaps : Swaps) (arr : Array α)
--     (le : α → α → Bool := by exact fun a b => a ≤ b) : Array α :=
--   swaps.foldl
--     (init := arr)
--     fun arr (a, b) =>
--       if !(le arr[a]! arr[b]!) then arr.swapIfInBounds a b else arr

def binaryCompareAndSwap (a b : UInt8) (val : UInt64) : UInt64 :=
  let aBitPos := a.toUInt64 --size - a - 1 |>.toUInt64
  let bBitPos := b.toUInt64 --size - b - 1 |>.toUInt64
  let aBit := val >>> aBitPos &&& 1
  let bBit := val >>> bBitPos &&& 1
  let aBit' := bBit &&& aBit
  let bBit' := bBit ||| aBit
  let aBit's := aBit' <<< aBitPos
  let bBit's := bBit' <<< bBitPos
  let na := ~~~(1 <<< aBitPos)
  let nb := ~~~(1 <<< bBitPos)
  let val := val &&& na &&& nb
  val ||| aBit's ||| bBit's

def Network.run (n : Network size) (input : UInt64) : UInt64 :=
  n.toArray.foldl
    (init := input)
    fun acc layer =>
      Prod.fst <|
        layer.foldl
          (init := (acc, 0))
          fun (acc, a) b =>
            (binaryCompareAndSwap a.toUInt8 b.toUInt8 acc, a + 1)

def UInt64.bitsSorted (n : UInt64) : Bool :=
  let n := n ^^^ (n >>> 1)
  n &&& (n - 1) = 0

@[specialize]
def Network.run'
    [Inhabited α]
    (n : Network size)
    (arr : Array α)
    (le : α → α → Bool := by exact fun a b => a ≤ b)
    : Array α :=
  n.toArray.foldl runLayer arr
where
  @[specialize, inline]
  runLayer (arr : Array α) (layer : Array Nat) : Array α :=
    let (arr, _) := layer.foldl
      (init := (arr, 0))
      fun (arr, i) ce =>
        let arr := if i ≠ ce ∧ !(le arr[ce]! arr[i]!) then arr.swapIfInBounds i ce else arr
        (arr, i + 1)
    arr

@[specialize]
def Array.sorted [Inhabited α] (arr : Array α)
    (le : α → α → Bool := by exact fun a b => a ≤ b) : Bool :=
  if arr.size <= 1 then
    true
  else Id.run do
    for i in [1 : arr.size] do
      if !(le arr[i - 1]! arr[i]!) then
        return false
    true

def Array.pad (arr : Array α) (a : α) (newSize : Nat) :=
  arr.append (.replicate (newSize - arr.size) a)

def Array.shuffle [Inhabited α] [RandomGen Gen] (arr : Array α) (gen : Gen): Array α :=
  Prod.fst <| arr.size.fold
    (init := (arr, gen))
    fun i _ (arr, gen) =>
      if i = 0 then
        (arr, gen)
      else
        let (j, gen) := randNat gen 0 (i - 1)
        let a := arr[i]!
        let b := arr[j]!
        let arr := arr.set! i b
        let arr := arr.set! j a
        (arr, gen)

def mkInput (size : Nat) : Array (Array Bool) :=
  (Array.shuffle · mkStdGen) <| .ofFn (n := 2 ^ size) fun i =>
    i.toNat.toBitArray.pad false size

def Network.correctlySortsInput (n : Network size) (input : UInt64) : Bool :=
  n.run input |>.bitsSorted

def Network.output (n : Network size) : Std.HashSet UInt64 := Id.run do
  let mut result := default
  let numInputs := 2 ^ size
  for i in [0:numInputs] do
    let output := n.run i.toUInt64
    result := result.insert output
  result

-- def Network.correctnessScore (n : Network size) : Rat := Id.run do
--   let mut successes := 0
--   let numTests := 2 ^ size
--   for i in [0 : numTests] do
--     if n.correctlySortsInput i.toUInt64 then
--       successes := successes + 1
--   (successes : Rat) / (numTests : Rat)

def Network.correctnessScore' (n : Network size) : Nat × Nat := Id.run do
  let mut successes := 0
  let mut failures := 0
  let mut start : Nat := 1
  let mut i := start
  while true do
    if n.correctlySortsInput i.toUInt64 then
      successes := successes + 1
    else
      failures := failures + 1
    i := LFSR.randNat size i
    if i = 1 then
      break
  pure (successes, failures)
  -- ((dbgTraceVal successes) : Rat) / ((2 ^ size - 1 : Nat) : Rat)

-- def Network.isCorrect (n : Network size) : Bool := Id.run do
--   let numTests := 2 ^ size
--   for i in [0 : numTests] do
--     if !n.correctlySortsInput i.toUInt64 then
--       return false
--   true

def Network.isCorrect' (n : Network size) : Bool := Id.run do
  let mut start : Nat := 1
  let mut i := start
  while true do
    if !n.correctlySortsInput i.toUInt64 then
      return false
    i := LFSR.randNat size i
    if i = 1 then
      break
  true

def Network.swapsScore (n : Network size) : Rat :=
  if size ≤ 1 then
    if n.toSwaps.size = 0 then 0 else 1
  else
    n.toSwaps.size

def Network.layersScore (n : Network size) : Rat :=
  if size ≤ 1 then
    if n.toArray.size = 0 then 0 else 1
  else
    n.toArray.size

def Network.addLayer (n : Network size) : Network size :=
  Network.mk <| n.toArray.push <| .range size

def Array.swapRemove! [Inhabited α] (arr : Array α) (i : Nat) (a : α) : Array α × α :=
  let result := arr[i]!
  let arr := arr.set! i a
  (arr, result)

def Network.addSwap (n : Network size) (layer : Nat) (swap : Nat × Nat) : Network size × Nat :=
  let (n, layer) :=
    if layer ≥ n.toArray.size then
      let n := n.addLayer
      (n, n.toArray.size - 1)
    else
      (n, layer)
  let a := n.toArray[layer]![swap.fst]!
  let b := n.toArray[layer]![swap.snd]!
  if (a = swap.fst ∧ b = swap.snd) ∨ (a = swap.snd ∧ b = swap.fst) then
    let (n, l) := n.toArray.swapRemove! layer #[]
    let l := l.swapIfInBounds swap.fst swap.snd
    (Network.mk <| n.set! layer l, layer)
  else
    let newlayer := Array.range size
    let newLayer := newlayer.swapIfInBounds swap.fst swap.snd
    (Network.mk <| n.toArray.insertIdx! (layer + 1) newLayer, layer + 1)

def Network.removeSwap (n : Network size) (layer : Nat) (a : Nat) : Network size :=
  let b := n.toArray[layer]![a]!
  if a ≠ b then
    let (n, l) := n.toArray.swapRemove! layer #[]
    let l := l.swapIfInBounds a b
    Network.mk <| n.set! layer l
  else
    n

def isUselessLayer (layer : Array Nat) : Bool := Id.run do
  for i in [0 : layer.size], v in layer do
    if i ≠ v then
      return false
  true

def Network.removeLayerIfUseless (n : Network size) (layer : Nat) : Network size :=
  let l := n.toArray[layer]!
  if isUselessLayer l then
    let n := n.toArray.eraseIdx! layer
    Network.mk n
  else
    n

def Network.removeDuplicateAdjacentLayers (n : Network size) : Network size := Id.run do
  let mut n := n.toArray
  let mut i := n.size - 1
  while i > 0 do
    let xs := n[i - 1]!
    let ys := n[i]!
    if xs = ys then
      n := n.pop
    i := i - 1
  Network.mk n

def Network.countExchangeEndpoints (n : Network size) : Array Nat :=
  n.toArray.foldl
    (init := Array.replicate size 0)
    fun acc layer =>
      Prod.fst <|
        layer.foldl
          (init := (acc, 0))
          fun (acc, a) b =>
            if a ≠ b then
              let acc := acc.set! a (acc[a]! + 1)
              (acc, a + 1)
            else
              (acc, a + 1)

def Network.addRandomSwap [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if size = 0 then
    (n, g)
  else
    let (layer, g) := randNat g 0 n.toArray.size
    let (fst, g) := randNat g 0 (size - 1)
    let (snd, g) := randNat g 0 (size - 1)
    let (fst, snd) :=
      if fst = snd then
        if fst = 0 then
          (0, 1)
        else
          (fst - 1, fst)
      else
        (fst, snd)
    let (n, layer) := n.addSwap layer (fst, snd)
    let n := n.removeLayerIfUseless layer
    let n := n.removeDuplicateAdjacentLayers
    (n, g)

def Network.swapRandomLayers [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.toArray.size < 2 then
    (n, g)
  else
    let (layerA, g) := randNat g 0 n.toArray.size
    let (layerB, g) := randNat g 0 n.toArray.size
    let n := Network.mk <| n.toArray.swapIfInBounds layerA layerB
    (n, g)

def Network.removeSmallestLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.toArray.size < 1 then
    (n, g)
  else
    let (_, smallestLayer) := n.toArray.zipIdx.toList.mergeSort (fun (a, _) (b, _) => a.size ≤ b.size) |>.head!
    let n := Network.mk <| n.toArray.eraseIdx! smallestLayer
    (n, g)

def Network.removeRandomLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.toArray.size < 1 then
    (n, g)
  else
    let (layer, g) := randNat g 0 (n.toArray.size - 1)
    let n := Network.mk <| n.toArray.eraseIdx! layer
    (n, g)

def Layer.rotate (arr : Array Nat) (amount : Nat) : Array Nat :=
  if arr.size = 0 then
    arr
  else
    let adjust : Nat → Nat :=
      fun n => (n + amount) % arr.size
    arr
      |> Layer.toSwaps
      |>.map (fun (a, b) => (adjust a, adjust b))
      |> Swaps.toLayer arr.size

def Network.rotateRandomLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.toArray.size < 1 then
    (n, g)
  else
    let (layerIdx, g) := randNat g 0 (n.toArray.size - 1)
    let (n, layer) := n.toArray.swapRemove! layerIdx #[]
    let (amount, g) := randNat g 1 (layer.size - 1)
    let layer := Layer.rotate layer amount
    let n := Network.mk <| n.set! layerIdx layer
    (n, g)

inductive Mutation where
  | swapCE
  | swapLayers
  | removeSmallestLayer
  | removeRandomLayer
  | rotateRandomLayer
  deriving BEq, Hashable, Repr

instance : Inhabited Mutation where
  default := .swapCE

def Mutation.chances : Std.HashMap Mutation Nat := .ofList [
  (swapCE, 1250),
  (swapLayers, 250),
  (removeSmallestLayer, 0),
  (removeRandomLayer, 1),
  (rotateRandomLayer, 100),
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

#eval Mutation.bounds

def Mutation.pickAtRandom [RandomGen Gen] (g : Gen) : Mutation × Gen :=
  let (k, g) := randNat g 0 USize.size
  let k := k.toFloat / USize.size.toFloat
  let m := Id.run do
    for (upperBound, m) in Mutation.bounds do
      if k ≤ upperBound then
        return m
    panic! "no mutation found"
  (m, g)

def Network.mutate [RandomGen Gen] (n : Network size) (g : Gen) (numMutations : Nat) : Network size × Gen :=
  if numMutations = 0 then
    (n, g)
  else
    let (m, g) := Mutation.pickAtRandom g
    let (n, g) :=
      match m with
      | .swapCE => n.addRandomSwap g
      | .swapLayers => n.swapRandomLayers g
      | .removeSmallestLayer => n.removeSmallestLayer g
      | .removeRandomLayer => n.removeRandomLayer g
      | .rotateRandomLayer => n.rotateRandomLayer g
    n.mutate g (numMutations - 1)

def Network.satisfiesReachabilityCondition (nw : Network size) : Bool := Id.run do
  let output : Array (Std.HashSet Nat) :=
    nw.toArray.foldl
      (init := Array.ofFn (n := size) fun i => (default : Std.HashSet Nat).insert i)
      fun acc la => Id.run do
        let mut acc := acc
        for a in [0:size] do
          let b := la[a]!
          let mut s := default
          (acc, s) := acc.swapRemove! a default
          s := s.union acc[b]!
          acc := acc.set! a s
        acc
  for o in output do
    if o.size ≠ size then
      return false
  true

def Network.improve
    [RandomGen Gen]
    (n : Network size)
    (g : Gen)
    (fuel : Nat)
    (lastFailures : Option Nat)
    (numMutations : Nat := (size * (size - 1) / 2))
    : Network size × Gen × Option Nat :=
  if fuel = 0 ∨ size = 0 then
    (n, g, lastFailures)
  else
    let nIsCorrect := lastFailures.getD 1 = 0
    let (numMutations, g) := randNat g 1 numMutations
    let (n', g) := n.mutate g numMutations
    let n'IsSmaller :=
      (n'.swapsScore ≤ n.swapsScore ∧ n'.layersScore ≤ n.layersScore)
      ∧ (n'.swapsScore ≠ n.swapsScore ∨ n'.layersScore ≠ n.layersScore)
    let (n, g, lastFailures) :=
      if n'IsSmaller then
        let (_successes, failures) := n'.correctnessScore'
        let n'IsCorrect := failures = 0
        if n'IsCorrect then
          (n', g, failures)
        else
          (n, g, lastFailures)
      else
        if nIsCorrect then
          (n, g, lastFailures)
        else
          let (_successes, failures) := n'.correctnessScore'
          (n', g, failures)
    n.improve g (fuel - 1) lastFailures numMutations

-- Output representation consumable by Brian Pursley's "sorting-network" visualization code:
-- https://github.com/brianpursley/sorting-network
def Network.toPursleyString (n : Network size) : String :=
  (fun s => s.take (s.length - 1) /- removes the trailing comma -/) <|
    n.toSwaps.foldl
      (init := "")
      fun str (a, b) =>
        str ++ s!"{a}:{b},"

def Network.bubble : Network size :=
  .mk <| ascending ++ (ascending.pop |>.reverse)
where
  numAscending := (2 * (size - 2) + 1) / 2 + 1
  ascending := .ofFn (n := numAscending) fun i => Id.run do
    let mut arr := Array.range size
    let i := i.toNat
    let numSwaps := i / 2 + 1
    for j in [0 : numSwaps] do
      let a := j * 2 + if i % 2 = 0 then 0 else 1
      arr := arr.swapIfInBounds a (a + 1)
    arr

def Network.fromLayerSwapsList (layers : List (List (Nat × Nat))) : Network size :=
  let layers := layers.map (·.toArray) |>.toArray
  .fromLayerSwaps layers

def nw6_12x5 : Network 6 := .fromLayerSwapsList [[(0,5),(1,3),(2,4)],[(1,2),(3,4)],[(0,3),(2,5)],[(0,1),(2,3),(4,5)],[(1,2),(3,4)]]
def nw7_16x6 : Network 7 := .fromLayerSwapsList [[(0,6),(2,3),(4,5)],[(0,2),(1,4),(3,6)],[(0,1),(2,5),(3,4)],[(1,2),(4,6)],[(2,3),(4,5)],[(1,2),(3,4),(5,6)]]
def nw8_19x6 : Network 8 := .fromLayerSwapsList [[(0,2),(1,3),(4,6),(5,7)],[(0,4),(1,5),(2,6),(3,7)],[(0,1),(2,3),(4,5),(6,7)],[(2,4),(3,5)],[(1,4),(3,6)],[(1,2),(3,4),(5,6)]]
def nw9_25x7 : Network 9 := .fromLayerSwapsList [[(0,3),(1,7),(2,5),(4,8)],[(0,7),(2,4),(3,8),(5,6)],[(0,2),(1,3),(4,5),(7,8)],[(1,4),(3,6),(5,7)],[(0,1),(2,4),(3,5),(6,8)],[(2,3),(4,5),(6,7)],[(1,2),(3,4),(5,6)]]
def nw10_29x8 : Network 10 := .fromLayerSwapsList [[(0,8),(1,9),(2,7),(3,5),(4,6)],[(0,2),(1,4),(5,8),(7,9)],[(0,3),(2,4),(5,7),(6,9)],[(0,1),(3,6),(8,9)],[(1,5),(2,3),(4,8),(6,7)],[(1,2),(3,5),(4,6),(7,8)],[(2,3),(4,5),(6,7)],[(3,4),(5,6)]]
def nw10_31x7 : Network 10 := .fromLayerSwapsList [[(0,1),(2,5),(3,6),(4,7),(8,9)],[(0,6),(1,8),(2,4),(3,9),(5,7)],[(0,2),(1,3),(4,5),(6,8),(7,9)],[(0,1),(2,7),(3,5),(4,6),(8,9)],[(1,2),(3,4),(5,6),(7,8)],[(1,3),(2,4),(5,7),(6,8)],[(2,3),(4,5),(6,7)]]
def nw11_35x8 : Network 11 := .fromLayerSwapsList [[(0,9),(1,6),(2,4),(3,7),(5,8)],[(0,1),(3,5),(4,10),(6,9),(7,8)],[(1,3),(2,5),(4,7),(8,10)],[(0,4),(1,2),(3,7),(5,9),(6,8)],[(0,1),(2,6),(4,5),(7,8),(9,10)],[(2,4),(3,6),(5,7),(8,9)],[(1,2),(3,4),(5,6),(7,8)],[(2,3),(4,5),(6,7)]]
def nw12_39x9 : Network 12 := .fromLayerSwapsList [[(0,8),(1,7),(2,6),(3,11),(4,10),(5,9)],[(0,1),(2,5),(3,4),(6,9),(7,8),(10,11)],[(0,2),(1,6),(5,10),(9,11)],[(0,3),(1,2),(4,6),(5,7),(8,11),(9,10)],[(1,4),(3,5),(6,8),(7,10)],[(1,3),(2,5),(6,9),(8,10)],[(2,3),(4,5),(6,7),(8,9)],[(4,6),(5,7)],[(3,4),(5,6),(7,8)]]
def nw12_40x8 : Network 12 := .fromLayerSwapsList [[(0,8),(1,7),(2,6),(3,11),(4,10),(5,9)],[(0,2),(1,4),(3,5),(6,8),(7,10),(9,11)],[(0,1),(2,9),(4,7),(5,6),(10,11)],[(1,3),(2,7),(4,9),(8,10)],[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11)],[(1,2),(3,5),(6,8),(9,10)],[(2,4),(3,6),(5,8),(7,9)],[(1,2),(3,4),(5,6),(7,8),(9,10)]]
def nw13_45x10 : Network 13 := .fromLayerSwapsList [[(0,12),(1,10),(2,9),(3,7),(5,11),(6,8)],[(1,6),(2,3),(4,11),(7,9),(8,10)],[(0,4),(1,2),(3,6),(7,8),(9,10),(11,12)],[(4,6),(5,9),(8,11),(10,12)],[(0,5),(3,8),(4,7),(6,11),(9,10)],[(0,1),(2,5),(6,9),(7,8),(10,11)],[(1,3),(2,4),(5,6),(9,10)],[(1,2),(3,4),(5,7),(6,8)],[(2,3),(4,5),(6,7),(8,9)],[(3,4),(5,6)]]
def nw13_46x9 : Network 13 := .fromLayerSwapsList [[(0,11),(1,7),(2,4),(3,5),(8,9),(10,12)],[(0,2),(3,6),(4,12),(5,7),(8,10)],[(0,8),(1,3),(2,5),(4,9),(6,11),(7,12)],[(0,1),(2,10),(3,8),(4,6),(9,11)],[(1,3),(2,4),(5,10),(6,8),(7,9),(11,12)],[(1,2),(3,4),(5,8),(6,9),(7,10)],[(2,3),(4,7),(5,6),(8,11),(9,10)],[(4,5),(6,7),(8,9),(10,11)],[(3,4),(5,6),(7,8),(9,10)]]
def nw14_51x10 : Network 14 := .fromLayerSwapsList [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)],[(0,2),(1,3),(4,8),(5,9),(10,12),(11,13)],[(0,4),(1,2),(3,7),(5,8),(6,10),(9,13),(11,12)],[(0,6),(1,5),(3,9),(4,10),(7,13),(8,12)],[(2,10),(3,11),(4,6),(7,9)],[(1,3),(2,8),(5,11),(6,7),(10,12)],[(1,4),(2,6),(3,5),(7,11),(8,10),(9,12)],[(2,4),(3,6),(5,8),(7,10),(9,11)],[(3,4),(5,6),(7,8),(9,10)],[(6,7)]]
def nw14_52x9 : Network 14 := .fromLayerSwapsList [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)],[(0,2),(1,3),(4,8),(5,9),(10,12),(11,13)],[(0,10),(1,6),(2,11),(3,13),(5,8),(7,12)],[(1,4),(2,8),(3,6),(5,11),(7,10),(9,12)],[(0,1),(3,9),(4,10),(5,7),(6,8),(12,13)],[(1,5),(2,4),(3,7),(6,10),(8,12),(9,11)],[(1,2),(3,5),(4,6),(7,9),(8,10),(11,12)],[(2,3),(4,5),(6,7),(8,9),(10,11)],[(3,4),(5,6),(7,8),(9,10)]]
def nw15_56x10 : Network 15 := .fromLayerSwapsList [[(1,2),(3,10),(4,14),(5,8),(6,13),(7,12),(9,11)],[(0,14),(1,5),(2,8),(3,7),(6,9),(10,12),(11,13)],[(0,7),(1,6),(2,9),(4,10),(5,11),(8,13),(12,14)],[(0,6),(2,4),(3,5),(7,11),(8,10),(9,12),(13,14)],[(0,3),(1,2),(4,7),(5,9),(6,8),(10,11),(12,13)],[(0,1),(2,3),(4,6),(7,9),(10,12),(11,13)],[(1,2),(3,5),(8,10),(11,12)],[(3,4),(5,6),(7,8),(9,10)],[(2,3),(4,5),(6,7),(8,9),(10,11)],[(5,6),(7,8)]]

def goodNetworks : Array (Σ size : Nat, Network size) :=
  #[
    ⟨6, nw6_12x5⟩,
    ⟨7, nw7_16x6⟩,
    ⟨8, nw8_19x6⟩,
    ⟨9, nw9_25x7⟩,
    ⟨10, nw10_29x8⟩,
    ⟨10, nw10_31x7⟩,
    ⟨11, nw11_35x8⟩,
    ⟨12, nw12_39x9⟩,
    ⟨12, nw12_40x8⟩,
    ⟨13, nw13_45x10⟩,
    ⟨13, nw13_46x9⟩,
    ⟨14, nw14_51x10⟩,
    ⟨14, nw14_52x9⟩,
    ⟨15, nw15_56x10⟩,
  ]

def Network.bfsStep (n : Network size) : Array (Network size) := Id.run do
  if size <= 1 then
    return #[]
  -- Number of iterations of the inner loop is 1,3,6,10,15,21, which looks like
  -- the triangle numbers (sequence A000217 in OEIS). This is how we get the capacity
  -- formula.
  let mut result := Array.emptyWithCapacity (size * (size + 1) / 2)
  let lastLayer :=
    if n.toArray.size = 0 then
      Array.range size
    else
      n.toArray[n.toArray.size - 1]!
  for swapDist in [1:size] do
    for a in [0:size - swapDist] do
      let b := a + swapDist
      let newLayers :=
        if lastLayer[a]! = a ∧ lastLayer[b]! = b then
          let initialLayers := n.toArray.take (n.toArray.size - 1)
          let newLastLayer := lastLayer.swapIfInBounds a b
          initialLayers.push newLastLayer
        else
          let newLastLayer := Array.range size
          let newLastLayer := newLastLayer.swapIfInBounds a b
          n.toArray.push newLastLayer
      result := result.push <| Network.mk newLayers
  result

def isDuplicateComparison (layers : Array (Array Nat)) (layer : Nat) (ce : Nat × Nat) : Bool := Id.run do
  let (a, b) := ce
  let ta := layers[layer]![a]!
  let tb := layers[layer]![b]!
  if ta = a ∧ tb = b then
    return false
  let mut i := layer - 1
  while true do
    let ta' := layers[i]![a]!
    let tb' := layers[i]![b]!
    if ta' = ta ∧ tb' = tb then
      return true
    if i = 0 then
      break
    i := i - 1
  false

partial def Network.normalize (n : Network size) : Network size := Id.run do
  if size <= 1 then
    return n
  let mut layers := n.toArray
  let mut i := layers.size - 1
  while i > 0 ∧ i < layers.size do
    for a in [0:size] do
      let b := layers[i]![a]!
      if isDuplicateComparison layers i (a, b) then
        let mut layerI := #[]
        (layers, layerI) := layers.swapRemove! i #[]
        layerI := layerI.set! a a
        layerI := layerI.set! b b
        layers := layers.set! i layerI
    let mut numPopped := 0
    if layers[i]! = layers[i - 1]! then
      layers := layers.pop
      numPopped := numPopped + 1
    if layers[i]! = .range size then
      layers := layers.pop
      numPopped := numPopped + 1
    i := #[i - 1, i, i - 1][numPopped]!
  let n' := Network.mk layers
  if n' ≠ n then
    n'.normalize
  else
    n'

def Network.bestNext
    (n : Network size)
    (nOutput : Std.HashSet UInt64)
    : Network size × (Std.HashSet UInt64)
    := Id.run do
  let mut best := n
  let mut bestOutput := nOutput
  let candidates : Std.HashSet (Network size) :=
    best.bfsStep.foldl
      (init := default)
      fun acc n => acc.insert n.normalize
  for c in candidates do
    let cOutputs := c.output
    if cOutputs.size ≤ bestOutput.size then
      best := c
      bestOutput := cOutputs
  (best, bestOutput)

def Network.exploreBfs
    (n : Network size)
    (nOutput : Std.HashSet UInt64)
    (fuel : Nat)
    : Network size × (Std.HashSet UInt64)
    := Id.run do
  let mut best := n
  let mut bestOutput := nOutput
  for _ in [0:fuel] do
    if bestOutput.size = size + 1 then
      return (best, bestOutput)
    (best, bestOutput) := best.bestNext bestOutput
  (best, bestOutput)

def Array.isValidLayer (la : Array Nat) : Bool := Id.run do
  for i in [0:la.size] do
    if let some lai := la[i]? then
      if let some lalai := la[lai]? then
        if i = lalai then
          continue
    return false
  true

def Array.permutations (arr : Array Nat) : Array (Array Nat) :=
  arr.toList.permutations.toArray.map (·.toArray)

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

def countValidLayersViaPermutationFiltering (size : Nat) : Nat :=
  (Array.range size).permutations.filter (·.isValidLayer) |>.size

#eval (Array.range 5)
  |>.permutations
  |>.filter (·.isValidLayer)

#eval (Array.range 5)
  |>.permutations
  |>.filter (·.isValidLayer)
  |>.map (fun (l : Array Nat) => (l, Layer.rotate l 1, (Layer.rotate l 1).isValidLayer))
  |>.filter (·.snd.snd)
