import Std.Data.HashSet
import SortingNetworkSearch.LFSR
import SortingNetworkSearch.CompiledNetwork
import SortingNetworkSearch.TestPack
import SortingNetworkSearch.ExtraTheorems
import SortingNetworkSearch.Layer
import SortingNetworkSearch.ArrayExtras
import SortingNetworkSearch.Mutation

structure Network (size : USize) where
  layers : Array Layer
  deriving Repr, DecidableEq, Hashable

def Network.instInhabited : Network size := .mk #[]

instance : Inhabited (Network size) where
  default := Network.instInhabited

def Network.toSwaps (n : Network size) : Array Swap :=
  n.layers.flatMap (Layer.toSwapLayer ·)

def Network.fromSwapLayers (layers : Array (Array Swap)) : Network size :=
  Network.mk <|
    layers.map fun swaps =>
      swaps.foldl (init := Array.range size.toNat |>.map (·.toUSize))
        fun acc (a, b) =>
          let acc := acc.set! a.toNat b
          let acc := acc.set! b.toNat a
          acc

def Network.compile (n : Network size) : CompiledNetwork size :=
  let swaps := n.toSwaps |>.unzip
  if h : swaps.fst.size = swaps.snd.size ∧ swaps.fst.size < USize.size then
    let as := swaps.fst
    let bs := swaps.snd
    if h : as.all (· < size) ∧ bs.all (· < size) then
      CompiledNetwork.mk as bs
    else panic! "invariant violated: not all swaps are < size"
  else panic! "invariant violated: swaps has wrong size"

def CompiledNetwork.countTestFailures (c : CompiledNetwork size) : UInt64 := Id.run do
  let mut seed := 1
  let mut src := Array.replicate 64 0
  let mut dest := Array.replicate size.toNat 0
  let mut failures := 0
  let mut isFirstIteration := true
  if h : src.size < USize.size ∧ src.usize = 64 then
    while seed ≠ 1 ∨ isFirstIteration do
      isFirstIteration := false
      if h : dest.usize = size then
        (dest, seed) := TestPack.mkRandom size dest ⟨src, by grind⟩ seed
        if h : dest.usize = size ∧ dest.size < USize.size then
          dest := c.runTestPack ⟨dest, by grind⟩
          failures := failures + TestPack.countFailures dest
        else panic! "invariant violated: dest has wrong size"
      else panic! "invariants violated for mkPackedTests: dest size"
    failures
  else panic! "invariants violated for mkPackedTests: src size"

def Network.addLayer (n : Network size) : Network size :=
  Network.mk <| n.layers.push <| Array.range size.toNat |>.map (·.toUSize)

def Network.addSwap
    (n : Network size)
    (layerIdx : Nat)
    (swap : USize × USize)
    (symmetric : Bool)
    : Network size :=
  let n := if layerIdx = n.layers.size then n.addLayer else n
  let a := n.layers[layerIdx]![swap.fst.toNat]!
  let b := n.layers[layerIdx]![swap.snd.toNat]!
  if a = swap.fst ∧ b = swap.snd then
    let (n, layer) := n.layers.swapRemove! layerIdx .empty
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
  let swaps := Layer.toSwapLayer n.layers[layerIdx]!
  if 0 < swaps.size then
    let (a, b) := swaps[swapIdx % swaps.size]!
    let (n, layer) := n.layers.swapRemove! layerIdx .empty
    let layer := layer.swapIfInBounds a.toNat b.toNat
    let n := Network.mk <| n.set! layerIdx layer
    if symmetric then
      let (n, layer) := n.layers.swapRemove! layerIdx .empty
      let layer := layer.swapIfInBounds (size - 1 - a).toNat (size - 1 - b).toNat
      let n := Network.mk <| n.set! layerIdx layer
      n
    else n
  else n

def Network.removeLayerIfUseless (n : Network size) (layerIdx : Nat) : Network size :=
  let l := n.layers[layerIdx]!
  if l.isUseless then
    let n := n.layers.eraseIdx! layerIdx
    Network.mk n
  else
    n

def Network.removeDuplicateAdjacentLayers (n : Network size) : Network size := Id.run do
  let mut n := n.layers
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
    if n.layers.size < 1 then
      return n
    let mut n := Network.mk n.layers
    let mut i := n.layers.size - 1
    while true do
      n := n.removeLayerIfUseless i
      if i = 0 then
        break
      i := (i - 1).min (n.layers.size - 1)
    n
  let n' := n'.removeDuplicateAdjacentLayers
  if n' ≠ n then
    n'.removeRedundancy
  else
    n'

def Network.countExchangeEndpoints (n : Network size) : Array Nat :=
  n.layers.foldl
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
    let (layer, g) := randNat g 0 n.layers.size
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
  if size = 0 ∨ n.layers.size = 0 then
    (n, g)
  else
    let (layer, g) := randNat g 0 (n.layers.size - 1)
    let (fst, g) := randNat g 0 (size / 2).toNat
    let n := n.removeSwap layer fst symmetric
    let n := n.removeRedundancy
    (n, g)

def Network.swapRandomLayers [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.layers.size < 2 then
    (n, g)
  else
    let (layerA, g) := randNat g 0 n.layers.size
    let (layerB, g) := randNat g 0 n.layers.size
    let n := Network.mk <| n.layers.swapIfInBounds layerA layerB
    (n, g)

def Network.removeSmallestLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.layers.size < 1 then
    (n, g)
  else
    let (_, smallestLayer) := n.layers.zipIdx.toList.mergeSort (fun (a, _) (b, _) => a.size ≤ b.size) |>.head!
    let n := Network.mk <| n.layers.eraseIdx! smallestLayer
    (n, g)

def Network.removeRandomLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.layers.size < 1 then
    (n, g)
  else
    let (layer, g) := randNat g 0 (n.layers.size - 1)
    let n := Network.mk <| n.layers.eraseIdx! layer
    (n, g)

def Network.rotateRandomLayer [RandomGen Gen] (n : Network size) (g : Gen) : Network size × Gen :=
  if n.layers.size < 1 then
    (n, g)
  else
    let (layerIdx, g) := randNat g 0 (n.layers.size - 1)
    let (n, layer) := n.layers.swapRemove! layerIdx .empty
    let (amount, g) := randNat g 1 (layer.size - 1)
    let layer := Layer.rotate layer amount
    let n := Network.mk <| n.set! layerIdx layer
    (n, g)

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
      (n'.toSwaps.size ≤ n.toSwaps.size ∧ n'.layers.size ≤ n.layers.size)
      ∧ (n'.toSwaps.size ≠ n.toSwaps.size ∨ n'.layers.size ≠ n.layers.size)
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

/--
Convert `n` to a `String` consumable by Brian Pursley's "sorting-network" visualization code:
https://github.com/brianpursley/sorting-network
-/
def Network.toPursleyString (n : Network size) : String :=
  let result := n.toSwaps.foldl (init := "")
    fun str (a, b) => str ++ s!"{a}:{b},"
  let result := result.dropRight 1 -- remove the trailing comma
  result
