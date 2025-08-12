import Std.Data.HashSet
import SortingNetworkSearch.LFSR
import SortingNetworkSearchFFI

abbrev Layer := Array USize
abbrev Swap := USize × USize

structure Network (size : USize) where
  toArray : Array Layer
  deriving Repr, DecidableEq, Hashable

def Network.instInhabited : Network size :=
  {
    toArray := #[]
  }
instance : Inhabited (Network size) where
  default := Network.instInhabited

def Layer.toSwaps (layer : Array USize) : Array Swap :=
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

def Swaps.toLayer (size : USize) (swaps : Array Swap) : Layer :=
  swaps.foldl
    (init := Array.range size.toNat |>.map (·.toUSize))
    fun acc (a, b) =>
      let acc := acc.set! a.toNat b
      let acc := acc.set! b.toNat a
      acc

def Network.toSwaps (n : Network size) : Array Swap :=
  n.toArray.flatMap (Layer.toSwaps ·)

def Network.fromLayerSwaps (layers : Array (Array Swap)) : Network size :=
  Network.mk <|
    layers.map fun swaps =>
      swaps.foldl (init := Array.range size.toNat |>.map (·.toUSize))
        fun acc (a, b) =>
          let acc := acc.set! a.toNat b
          let acc := acc.set! b.toNat a
          acc

@[grind →]
theorem array_index_lt_size_ofNat_of_lt_usize
    (vals : Array UInt64)
    (a : USize)
    (h : a < vals.usize)
    : a < USize.ofNat vals.size := by
  exact h

attribute [grind =] USize.lt_ofNat_iff

@[grind]
structure binaryParallelCompareAndSwap.h (vals : Array UInt64) (a b : USize) where
  size_vals_lt : vals.size < USize.size := by grind
  a_lt_vals_usize : a < vals.usize
  b_lt_vals_usize : b < vals.usize

def binaryParallelCompareAndSwap
    (a b : USize)
    (vals : Subtype (binaryParallelCompareAndSwap.h · a b) )
    : Array UInt64 :=
  have : a.toNat < vals.val.size := by grind
  have : b.toNat < vals.val.size := by grind
  let tmp := vals.val[a]
  let vals := vals.val.uset a (tmp &&& vals.val[b]) (by grind)
  let vals := vals.uset b (tmp ||| vals[b]'(by grind)) (by grind)
  vals

theorem binaryParallelCompareAndSwap_size_eq
    (a b : USize)
    (vals : Subtype (binaryParallelCompareAndSwap.h · a b))
    : (binaryParallelCompareAndSwap a b vals).size = vals.val.size := by
  simp [binaryParallelCompareAndSwap]

@[grind]
structure CompiledNetwork (size : USize) where
  as : Array USize
  bs : Array USize
  size_eq : as.size = bs.size := by grind
  size_lt_USize_size : as.size < USize.size := by grind
  as_sizes : ∀ a ∈ as, a < size := by grind
  bs_sizes : ∀ b ∈ bs, b < size := by grind

instance { size : USize } : Inhabited (CompiledNetwork size) where
  default := by
    refine CompiledNetwork.mk #[] #[] (size_lt_USize_size := ?_)
    rw [Array.size_empty]
    exact USize.size_pos

attribute [grind] Array.all_eq_true_iff_forall_mem

def Network.compile (n : Network size) : CompiledNetwork size :=
  let swaps := n.toSwaps |>.unzip
  if h : swaps.fst.size = swaps.snd.size ∧ swaps.fst.size < USize.size then
    let as := swaps.fst
    let bs := swaps.snd
    if h : as.all (· < size) ∧ bs.all (· < size) then
      CompiledNetwork.mk as bs
    else panic! "invariant violated: not all swaps are < size"
  else panic! "invariant violated: swaps has wrong size"

@[grind]
structure CompiledNetwork.runParallel.h (n : CompiledNetwork size) (vals : Array UInt64) where
  size_vals_lt_size_USize : vals.size < USize.size := by grind
  lt_usize_as : ∀ a ∈ n.as, a < vals.usize := by grind
  lt_usize_bs : ∀ b ∈ n.bs, b < vals.usize := by grind

attribute [grind] USize.lt_ofNat_iff

@[grind →]
theorem toNat_lt_size_of_lt_usize_of_lt_size_USize
    {i : USize}
    {xs : Array USize}
    (h₁ : xs.size < USize.size)
    (h₂ : i < xs.usize)
    : i.toNat < xs.size := by
  refine (USize.lt_ofNat_iff ?_).mp h₂
  exact h₁

@[grind]
theorem Array.mem_of_uget {as : Array α} {i : USize} {h} (h : as.uget i h = a) : a ∈ as :=
  Array.mem_of_getElem h

attribute [grind] Array.usize

partial def CompiledNetwork.runParallel
    (n : CompiledNetwork size)
    (vals : Subtype (runParallel.h n ·))
    : Array UInt64 :=
  let rec loop
      (i : USize)
      (vals : Subtype (runParallel.h n ·))
      : Array UInt64 :=
    if h : i < n.as.usize then
      let a := n.as.uget i (by grind)
      let b := n.bs.uget i (by grind)
      have vals_property := vals.property
      let vals := ⟨vals, by grind⟩
      let vals' := binaryParallelCompareAndSwap a b vals
      have size_eq := binaryParallelCompareAndSwap_size_eq a b vals
      have runParallel_h : runParallel.h n vals' := by
        apply runParallel.h.mk
        all_goals simp only [size_eq, vals']
        . exact vals_property.size_vals_lt_size_USize
        all_goals simp only [Array.usize, size_eq, Nat.toUSize_eq]
        . exact vals_property.lt_usize_as
        . exact vals_property.lt_usize_bs
      loop (i + 1) ⟨vals', by grind⟩
    else vals
  loop 0 vals

/--
Packs the bits of each element of `src` into `dest` like so:
```
src  [0b0000,
      0b0001,
      0b0010,
      0b0011,
      0b0100,
      0b0101,
      0b0110,
      0b0111, ------------------------\
      0b1000,                          \
      0b1001,                           \
      0b1010,                            \
      0b1011,                            |
      0b1100,                            |
      0b1101,                            |
      0b1110,                            |
      0b1111]                            v

dest [0b0000000000000000000000000000000000000000000000001010101010101010,
      0b0000000000000000000000000000000000000000000000001100110011001100,
      0b0000000000000000000000000000000000000000000000001111000011110000,
      0b0000000000000000000000000000000000000000000000001111111100000000]
```
-/
partial def pack
    -- (size : USize)
    (src dest : Array UInt64)
    -- (size_src : src.usize = 64)
    -- (size_dest : dest.usize = size)
    : Array UInt64 /- result.size = size -/ :=
  let rec loop1
      (dest : Array UInt64)
      (bitIdx : USize)
      : Array UInt64 :=
    if bitIdx < 64 then
      let rec loop2
          (dest : Array UInt64)
          (testCaseIdx : USize)
          : Array UInt64 :=
        if testCaseIdx < src.usize ∧ testCaseIdx < dest.usize then
          let bitIdx64 := bitIdx.toUInt64
          let bit := 1 &&& src[bitIdx]! >>> testCaseIdx.toUInt64
          let dest := dest.set! testCaseIdx.toNat <|
            (dest[testCaseIdx]! &&& ~~~(1 <<< bitIdx64))
            ||| (bit <<< bitIdx64)
          loop2 dest (testCaseIdx + 1)
        else dest
      let dest := loop2 dest 0
      loop1 dest (bitIdx + 1)
    else dest
  loop1 dest 0

partial def mkParallelInputChunk
    (size : USize)
    (src dest : Array UInt64)
    -- (size_src : src.usize = 64)
    -- (size_dest : dest.usize = size)
    (seed : UInt64)
    : Array UInt64 × UInt64 /- result.fst.usize = size, result.snd is the new seed -/ :=
  let rec loop
      (testCase : USize)
      (src : Array UInt64)
      (seed : UInt64)
      : Array UInt64 × UInt64 :=
    if testCase < 64 then
      let src := src.set! testCase.toNat seed
      let seed := LFSR.rand64 size.toUInt64 seed
      if seed = 1 then
        (src, seed)
      else loop (testCase + 1) src seed
    else (src, seed)
  let (src, seed) := loop 0 src seed
  let dest := pack src dest
  (dest, seed)

/-- Returns the number of `1`s in the binary representation of `u`. -/
def UInt64.countSetBits (u : UInt64) : UInt64 := Id.run do
  let mut u := u
  for h : i in [0:6] do
    u := ((u &&& masksA[i]) >>> 2^i) + (u &&& masksB[i])
  u
where
  masksA : Vector UInt64 6 := #[
    0b1010101010101010101010101010101010101010101010101010101010101010,
    0b1100110011001100110011001100110011001100110011001100110011001100,
    0b1111000011110000111100001111000011110000111100001111000011110000,
    0b1111111100000000111111110000000011111111000000001111111100000000,
    0b1111111111111111000000000000000011111111111111110000000000000000,
    0b1111111111111111111111111111111100000000000000000000000000000000,
  ].toVector
  masksB : Vector UInt64 6 := #[
    0b0101010101010101010101010101010101010101010101010101010101010101,
    0b0011001100110011001100110011001100110011001100110011001100110011,
    0b0000111100001111000011110000111100001111000011110000111100001111,
    0b0000000011111111000000001111111100000000111111110000000011111111,
    0b0000000000000000111111111111111100000000000000001111111111111111,
    0b0000000000000000000000000000000011111111111111111111111111111111,
  ].toVector

partial def ParallelChunk.countNotSorted (chunk : Array UInt64) : UInt64 :=
  let rec loop (i : USize) (acc : UInt64) : UInt64 :=
    if i + 1 < chunk.usize then
      let acc := acc ||| chunk[i]! &&& ~~~chunk[i + 1]!
      loop (i + 1) acc
    else acc
  loop 0 0 |>.countSetBits

@[grind]
theorem size_eq_of_size_lt_size_USize_of_usize_eq
    (dest : Array α)
    (h : dest.usize = size)
    (h2 : dest.size < USize.size)
    : dest.size = size.toNat := by
  rw [← h]
  exact Eq.symm (USize.toNat_ofNat_of_lt' h2)

def CompiledNetwork.countTestFailures (c : CompiledNetwork size) : UInt64 := Id.run do
  let mut seed := 1
  let mut src := Array.replicate 64 0
  let mut dest := Array.replicate size.toNat 0
  let mut failures := 0
  let mut isFirstIteration := true
  while seed ≠ 1 ∨ isFirstIteration do
    isFirstIteration := false
    (dest, seed) := mkParallelInputChunk size src dest seed
    if h : dest.usize = size ∧ dest.size < USize.size then
      dest := c.runParallel ⟨dest, by grind⟩
      failures := failures + ParallelChunk.countNotSorted dest
    else panic! "invariant violated: dest has wrong size"
  failures

def Network.addLayer (n : Network size) : Network size :=
  Network.mk <| n.toArray.push <| Array.range size.toNat |>.map (·.toUSize)

def Array.swapRemove! [Inhabited α] (arr : Array α) (i : Nat) (a : α) : Array α × α :=
  let result := arr[i]!
  let arr := arr.set! i a
  (arr, result)

def Network.addSwap
    (n : Network size)
    (layerIdx : Nat)
    (swap : USize × USize)
    (symmetric : Bool)
    : Network size :=
  let n := if layerIdx = n.toArray.size then n.addLayer else n
  let a := n.toArray[layerIdx]![swap.fst.toNat]!
  let b := n.toArray[layerIdx]![swap.snd.toNat]!
  if a = swap.fst ∧ b = swap.snd then
    let (n, layer) := n.toArray.swapRemove! layerIdx .empty
    let layer := layer.swapIfInBounds swap.fst.toNat swap.snd.toNat
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
    let layer := layer.swapIfInBounds a.toNat b.toNat
    let n := Network.mk <| n.set! layerIdx layer
    if symmetric then
      let (n, layer) := n.toArray.swapRemove! layerIdx .empty
      let layer := layer.swapIfInBounds (size - 1 - a).toNat (size - 1 - b).toNat
      let n := Network.mk <| n.set! layerIdx layer
      n
    else n
  else n

def isUselessLayer (layer : Layer) : Bool := Id.run do
  for i in [0 : layer.size], v in layer.toList do
    if i ≠ v.toNat then
      return false
  true

def Network.removeLayerIfUseless (n : Network size) (layerIdx : Nat) : Network size :=
  let l := n.toArray[layerIdx]!
  if isUselessLayer l then
    let n := n.toArray.eraseIdx! layerIdx
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
    let n := n.addSwap layer (fst.toUSize, snd.toUSize) symmetric
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

def Layer.rotate (arr : Layer) (amount : Nat) : Layer :=
  if arr.size = 0 then
    arr
  else
    let adjust : USize → USize :=
      fun n => (n.toNat + amount) % arr.size |>.toUSize
    arr
      |> Layer.toSwaps
      |>.map (fun (a, b) => (adjust a, adjust b))
      |> Swaps.toLayer arr.usize

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

def Network.improve
    [RandomGen Gen]
    (n : Network size)
    (g : Gen)
    (fuel : Nat)
    (lastFailures : Option UInt64)
    (symmetric : Bool)
    (numMutations : Nat := (size.toNat * (size.toNat - 1) / 2))
    : Network size × Gen × Option UInt64 :=
  if fuel = 0 ∨ size = 0 then
    (n, g, lastFailures)
  else
    let nIsCorrect : Bool := lastFailures.getD 1 = 0
    let (numMutations, g) := randNat g 1 numMutations
    let (n', g) := n.mutate g numMutations symmetric
    let n'IsSmaller :=
      (n'.toSwaps.size ≤ n.toSwaps.size ∧ n'.toArray.size ≤ n.toArray.size)
      ∧ (n'.toSwaps.size ≠ n.toSwaps.size ∨ n'.toArray.size ≠ n.toArray.size)
    let (n, g, lastFailures) :=
      if n'IsSmaller then
        let failures := n'.compile.countTestFailures
        let n'IsCorrect := failures = 0
        if n'IsCorrect then
          (n', g, some failures)
        else
          (n, g, lastFailures)
      else
        if nIsCorrect then
          (n, g, lastFailures)
        else
          let failures := n'.compile.countTestFailures
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
    let mut arr := Array.range size.toNat |>.map (·.toUSize)
    let i := i.toNat
    let numSwaps := i / 2 + 1
    for j in [0 : numSwaps] do
      let a := j * 2 + if i % 2 = 0 then 0 else 1
      arr :=
        if arr.size < USize.size then
          arr.swapIfInBounds a (a + 1)
        else arr
    arr

def Network.fromLayerSwapsList (layers : List (List Swap)) : Network size :=
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

def goodNetworks : Array (Σ size : USize, Network size) :=
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
