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

@[grind →]
theorem ByteArray.usize_index_lt_size
    (arr : ByteArray)
    (idx : USize)
    (h : idx < arr.usize)
    (h2 : arr.size < USize.size)
    : idx.toNat < arr.size := by
  exact (USize.lt_ofNat_iff h2).mp h

@[grind =]
theorem ByteArray.size_uset {xs : ByteArray} {v : UInt8} {i : USize} (h : i.toNat < xs.size) :
    (uset xs i v h).size = xs.size := by
  apply Array.size_uset

instance : Repr ByteArray where
  reprPrec b n := reprPrec b.toList.toArray n

structure Network (size : UInt8) where
  toArray : Array ByteArray
  deriving Repr, DecidableEq, Hashable

def Network.instInhabited : Network size :=
  {
    toArray := #[]
  }
instance : Inhabited (Network size) where
  default := Network.instInhabited

def Layer.toSwaps (layer : ByteArray) : Array (UInt8 × UInt8) :=
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
        if notSeen[a.toNat]! then
          let acc := acc.push (a, b)
          let notSeen := notSeen.set! b.toNat false
          (acc, notSeen, a + 1)
        else
          (acc, notSeen, a + 1)

def ByteArray.range (n : UInt8) : ByteArray := Id.run do
  let mut result := ByteArray.emptyWithCapacity n.toNat
  let mut i := 0
  while i < n do
    result := result.push i
    i := i + 1
  result

def Swaps.toLayer (size : UInt8) (swaps : Array (UInt8 × UInt8)) : ByteArray :=
  swaps.foldl
    (init := .range size)
    fun acc (a, b) =>
      let acc := acc.set! a.toNat b
      let acc := acc.set! b.toNat a
      acc

def Network.toSwaps (n : Network size) : Array (UInt8 × UInt8) :=
  n.toArray.flatMap (Layer.toSwaps ·)

def Network.fromLayerSwaps (layers : Array (Array (UInt8 × UInt8))) : Network size :=
  Network.mk <|
    layers.map fun swaps =>
      swaps.foldl (init := .range size)
        fun acc (a, b) =>
          let acc := acc.set! a.toNat b
          let acc := acc.set! b.toNat a
          acc

@[inline]
def binaryCompareAndSwap (a b : UInt8) (val : UInt64) : UInt64 :=
  let aBitPos := a.toUInt64
  let bBitPos := b.toUInt64
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

@[grind]
structure CompiledNetwork where
  as : ByteArray
  bs : ByteArray
  size_eq : as.size = bs.size
  size_lt_USize_size : as.size < USize.size

attribute [grind →] ByteArray.size

def Network.compile (n : Network size) : CompiledNetwork :=
  let swaps := n.toSwaps |>.unzip
  if h : swaps.fst.size = swaps.snd.size ∧ swaps.fst.size < USize.size then by
    refine CompiledNetwork.mk (.mk swaps.fst) (.mk swaps.snd) (by grind) (by grind)
  else by
    refine CompiledNetwork.mk .empty .empty (by grind) ?_
    unfold ByteArray.size
    exact USize.size_pos

@[inline]
def CompiledNetwork.run (n : CompiledNetwork) (input : UInt64) : UInt64 := Id.run do
  let mut input := input
  let mut i : USize := 0
  while h : i < n.as.usize do
    let a := n.as.uget i (by grind)
    let b := n.bs.uget i (by grind)
    input := binaryCompareAndSwap b a input
    i := i + 1
  input
  -- n.as.size.fold
  --   (init := input)
  --   fun layer b acc =>
  --     Prod.fst <|
  --       layer.foldl
  --         (init := (acc, 0))
  --         fun (acc, a) b =>
  --           (binaryCompareAndSwap a b acc, a + 1)

@[inline]
def UInt64.bitsSorted (n : UInt64) : Bool :=
  let n := n ^^^ (n >>> 1)
  n &&& (n - 1) = 0

@[inline]
def CompiledNetwork.correctlySortsInput (n : CompiledNetwork) (input : UInt64) : Bool :=
  n.run input |>.bitsSorted

def Network.output (n : Network size) : Std.HashSet UInt64 := Id.run do
  let mut result := default
  let numInputs := 2 ^ size.toNat
  let n := n.compile
  for i in [0:numInputs] do
    let output := n.run i.toUInt64
    result := result.insert output
  result

def Network.correctnessScore (n : Network size) : Nat × Nat := Id.run do
  let mut successes := 0
  let mut failures := 0
  let mut start : UInt64 := 1
  let mut i := start
  let n := n.compile
  while true do
    if n.correctlySortsInput i then
      successes := successes + 1
    else
      failures := failures + 1
    i := LFSR.rand64 size.toUInt64 i
    if i = 1 then
      break
  (successes, failures)

def Network.swapsScore (n : Network size) : Nat :=
  if size ≤ 1 then
    if n.toSwaps.size = 0 then 0 else 1
  else
    n.toSwaps.size

def Network.layersScore (n : Network size) : Nat :=
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

def ByteArray.swapIfInBounds (ba : ByteArray) (a : UInt8) (b : UInt8) (h : ba.size < USize.size) : ByteArray :=
  if h : a.toUSize < ba.usize ∧ b.toUSize < ba.usize then
    let tmp := ba.uget a.toUSize (by grind)
    let ba := ba.uset a.toUSize (ba.uget b.toUSize (by grind)) (by grind)
    let ba := ba.uset b.toUSize tmp (by grind)
    ba
  else ba

def Network.addSwap
    (n : Network size)
    (layerIdx : Nat)
    (swap : UInt8 × UInt8)
    (symmetric : Bool)
    : Network size :=
  let n := if layerIdx = n.toArray.size then n.addLayer else n
  let a := n.toArray[layerIdx]![swap.fst.toNat]!
  let b := n.toArray[layerIdx]![swap.snd.toNat]!
  if a = swap.fst ∧ b = swap.snd then
    let (n, layer) := n.toArray.swapRemove! layerIdx .empty
    let layer :=
      if h : layer.size < USize.size then
        layer.swapIfInBounds swap.fst swap.snd h
      else
        layer
    let n := Network.mk <| n.set! layerIdx layer
    if symmetric then
      n.addSwap layerIdx (size - 1 - swap.fst, size - 1 - swap.snd) false
    else n
  else n
termination_by symmetric.toNat

def Network.removeSwap
    (n : Network size)
    (layerIdx : Nat)
    (swapIdx : Nat)
    (symmetric : Bool)
    : Network size :=
  let swaps := Layer.toSwaps n.toArray[layerIdx]!
  if 0 < swaps.size then
    let (a, b) := swaps[swapIdx % swaps.size]!
    let (n, layer) := n.toArray.swapRemove! layerIdx .empty
    let layer :=
      if h : layer.size < USize.size then
        layer.swapIfInBounds a b h
      else
        layer
    let n := Network.mk <| n.set! layerIdx layer
    if symmetric then
      let (n, layer) := n.toArray.swapRemove! layerIdx .empty
      let layer :=
        if h : layer.size < USize.size then
          layer.swapIfInBounds (size - 1 - a) (size - 1 - b) h
        else
          layer
      let n := Network.mk <| n.set! layerIdx layer
      n
    else n
  else n

def isUselessLayer (layer : ByteArray) : Bool := Id.run do
  for i in [0 : layer.size], v in layer.toList do
    if i ≠ v.toNat then
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

partial def Network.removeRedundancy (n : Network size) : Network size :=
  let n' : Network size := Id.run do
    if n.toArray.size < 1 then
      return n
    let mut n := Network.mk n.toArray
    let mut i := n.toArray.size - 1
    while true do
      n := n.removeLayerIfUseless i
      if i = 0 then
        break
      i := (i - 1).min (n.toArray.size - 1)
    n
  let n' := n'.removeDuplicateAdjacentLayers
  if n' ≠ n then
    n'.removeRedundancy
  else
    n'

def Network.countExchangeEndpoints (n : Network size) : Array Nat :=
  n.toArray.foldl
    (init := Array.replicate size.toNat 0)
    fun acc layer =>
      Prod.fst <|
        layer.foldl
          (init := (acc, 0))
          fun (acc, a) b =>
            if a ≠ b.toNat then
              let acc := acc.set! a (acc[a]! + 1)
              (acc, a + 1)
            else
              (acc, a + 1)

def Network.addRandomSwap [RandomGen Gen] (n : Network size) (g : Gen) (symmetric : Bool) : Network size × Gen :=
  if size = 0 then
    (n, g)
  else
    let (layer, g) := randNat g 0 n.toArray.size
    let (fst, g) := randNat g 0 (size - 1).toNat
    let (snd, g) := randNat g 0 (size - 1).toNat
    let (fst, snd) :=
      if fst = snd then
        if fst = 0 then
          (0, 1)
        else
          (fst - 1, fst)
      else
        (fst, snd)
    let n := n.addSwap layer (fst.toUInt8, snd.toUInt8) symmetric
    let n := n.removeRedundancy
    (n, g)

def Network.removeRandomSwap [RandomGen Gen] (n : Network size) (g : Gen) (symmetric : Bool) : Network size × Gen :=
  if size = 0 ∨ n.toArray.size = 0 then
    (n, g)
  else
    let (layer, g) := randNat g 0 (n.toArray.size - 1)
    let (fst, g) := randNat g 0 (size / 2).toNat
    let n := n.removeSwap layer fst symmetric
    let n := n.removeRedundancy
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

def Layer.rotate (arr : ByteArray) (amount : Nat) : ByteArray :=
  if arr.size = 0 then
    arr
  else
    let adjust : UInt8 → UInt8 :=
      fun n => (n.toNat + amount) % arr.size |>.toUInt8
    arr
      |> Layer.toSwaps
      |>.map (fun (a, b) => (adjust a, adjust b))
      |> Swaps.toLayer arr.size.toUInt8

def Network.rotateRandomLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.toArray.size < 1 then
    (n, g)
  else
    let (layerIdx, g) := randNat g 0 (n.toArray.size - 1)
    let (n, layer) := n.toArray.swapRemove! layerIdx .empty
    let (amount, g) := randNat g 1 (layer.size - 1)
    let layer := Layer.rotate layer amount
    let n := Network.mk <| n.set! layerIdx layer
    (n, g)

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

def Network.mutate [RandomGen Gen] (n : Network size) (g : Gen) (numMutations : Nat) (symmetric : Bool) : Network size × Gen :=
  if numMutations = 0 then
    (n, g)
  else
    let (m, g) := Mutation.pickAtRandom g
    let (n, g) :=
      match m with
      | .swapLayers => n.swapRandomLayers g
      | .removeSmallestLayer => n.removeSmallestLayer g
      | .removeRandomLayer => n.removeRandomLayer g
      | .rotateRandomLayer => n.rotateRandomLayer g
      | .addRandomSwap => n.addRandomSwap g symmetric
      | .removeRandomSwap => n.removeRandomSwap g symmetric
    n.mutate g (numMutations - 1) symmetric

-- def Network.satisfiesReachabilityCondition (nw : Network size) : Bool := Id.run do
--   let output : Array (Std.HashSet Nat) :=
--     nw.toArray.foldl
--       (init := Array.ofFn (n := size.toNat) fun i => (default : Std.HashSet Nat).insert i)
--       fun acc la => Id.run do
--         let mut acc := acc
--         for a in [0:size.toNat] do
--           let b := la[a]!
--           let mut s := default
--           (acc, s) := acc.swapRemove! a default
--           s := s.union acc[b.toNat]!
--           acc := acc.set! a s
--         acc
--   for o in output do
--     if o.size ≠ size.toNat then
--       return false
--   true

def Network.improve
    [RandomGen Gen]
    (n : Network size)
    (g : Gen)
    (fuel : Nat)
    (lastFailures : Option Nat)
    (symmetric : Bool)
    (numMutations : Nat := (size.toNat * (size.toNat - 1) / 2))
    : Network size × Gen × Option Nat :=
  if fuel = 0 ∨ size = 0 then
    (n, g, lastFailures)
  else
    let nIsCorrect : Bool := lastFailures.getD 1 = 0
    let (numMutations, g) := randNat g 1 numMutations
    let (n', g) := n.mutate g numMutations symmetric
    let n'IsSmaller :=
      (n'.swapsScore ≤ n.swapsScore ∧ n'.layersScore ≤ n.layersScore)
      ∧ (n'.swapsScore ≠ n.swapsScore ∨ n'.layersScore ≠ n.layersScore)
    let (n, g, lastFailures) :=
      if n'IsSmaller then
        let (_successes, failures) := n'.correctnessScore
        let n'IsCorrect := failures = 0
        if n'IsCorrect then
          (n', g, failures)
        else
          (n, g, lastFailures)
      else
        if nIsCorrect then
          (n, g, lastFailures)
        else
          let (_successes, failures) := n'.correctnessScore
          (n', g, failures)
    n.improve g (fuel - 1) lastFailures symmetric numMutations

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
  ascending := .ofFn (n := numAscending.toNat) fun i => Id.run do
    let mut arr := ByteArray.range size
    let i := i.toNat
    let numSwaps := i / 2 + 1
    for j in [0 : numSwaps] do
      let a := j * 2 + if i % 2 = 0 then 0 else 1
      arr :=
        if h : arr.size < USize.size then
          arr.swapIfInBounds a.toUInt8 (a.toUInt8 + 1) h
        else arr
    arr

def Network.fromLayerSwapsList (layers : List (List (UInt8 × UInt8))) : Network size :=
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

#eval nw6_12x5.compile
#eval binaryCompareAndSwap 0 1 0b01 |>.toBitString
#eval nw6_12x5.correctnessScore

def goodNetworks : Array (Σ size : UInt8, Network size) :=
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

-- def Network.bfsStep (n : Network size) : Array (Network size) := Id.run do
--   if size <= 1 then
--     return #[]
--   -- Number of iterations of the inner loop is 1,3,6,10,15,21, which looks like
--   -- the triangle numbers (sequence A000217 in OEIS). This is how we get the capacity
--   -- formula.
--   let mut result := Array.emptyWithCapacity (size * (size + 1) / 2).toNat
--   let lastLayer :=
--     if n.toArray.size = 0 then
--       Array.range size
--     else
--       n.toArray[n.toArray.size - 1]!
--   for swapDist in [1:size] do
--     for a in [0:size - swapDist] do
--       let b := a + swapDist
--       let newLayers :=
--         if lastLayer[a]! = a ∧ lastLayer[b]! = b then
--           let initialLayers := n.toArray.take (n.toArray.size - 1)
--           let newLastLayer := lastLayer.swapIfInBounds a b
--           initialLayers.push newLastLayer
--         else
--           let newLastLayer := Array.range size
--           let newLastLayer := newLastLayer.swapIfInBounds a b
--           n.toArray.push newLastLayer
--       result := result.push <| Network.mk newLayers
--   result

-- def isDuplicateComparison (layers : Array (Array Nat)) (layer : Nat) (ce : Nat × Nat) : Bool := Id.run do
--   let (a, b) := ce
--   let ta := layers[layer]![a]!
--   let tb := layers[layer]![b]!
--   if ta = a ∧ tb = b then
--     return false
--   let mut i := layer - 1
--   while true do
--     let ta' := layers[i]![a]!
--     let tb' := layers[i]![b]!
--     if ta' = ta ∧ tb' = tb then
--       return true
--     if i = 0 then
--       break
--     i := i - 1
--   false

-- partial def Network.normalize (n : Network size) : Network size := Id.run do
--   if size <= 1 then
--     return n
--   let mut layers := n.toArray
--   let mut i := layers.size - 1
--   while i > 0 ∧ i < layers.size do
--     for a in [0:size] do
--       let b := layers[i]![a]!
--       if isDuplicateComparison layers i (a, b) then
--         let mut layerI := #[]
--         (layers, layerI) := layers.swapRemove! i #[]
--         layerI := layerI.set! a a
--         layerI := layerI.set! b b
--         layers := layers.set! i layerI
--     let mut numPopped := 0
--     if layers[i]! = layers[i - 1]! then
--       layers := layers.pop
--       numPopped := numPopped + 1
--     if layers[i]! = .range size then
--       layers := layers.pop
--       numPopped := numPopped + 1
--     i := #[i - 1, i, i - 1][numPopped]!
--   let n' := Network.mk layers
--   if n' ≠ n then
--     n'.normalize
--   else
--     n'

-- def Network.bestNext
--     (n : Network size)
--     (nOutput : Std.HashSet UInt64)
--     : Network size × (Std.HashSet UInt64)
--     := Id.run do
--   let mut best := n
--   let mut bestOutput := nOutput
--   let candidates : Std.HashSet (Network size) :=
--     best.bfsStep.foldl
--       (init := default)
--       fun acc n => acc.insert n.normalize
--   for c in candidates do
--     let cOutputs := c.output
--     if cOutputs.size ≤ bestOutput.size then
--       best := c
--       bestOutput := cOutputs
--   (best, bestOutput)

-- def Network.exploreBfs
--     (n : Network size)
--     (nOutput : Std.HashSet UInt64)
--     (fuel : Nat)
--     : Network size × (Std.HashSet UInt64)
--     := Id.run do
--   let mut best := n
--   let mut bestOutput := nOutput
--   for _ in [0:fuel] do
--     if bestOutput.size = size + 1 then
--       return (best, bestOutput)
--     (best, bestOutput) := best.bestNext bestOutput
--   (best, bestOutput)

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

-- #eval (Array.range 5)
--   |>.permutations
--   |>.filter (·.isValidLayer)

-- #eval (Array.range 5)
--   |>.permutations
--   |>.filter (·.isValidLayer)
--   |>.map (fun (l : Array Nat) => (l, Layer.rotate l 1, (Layer.rotate l 1).isValidLayer))
--   |>.filter (·.snd.snd)
