import Std.Data.HashSet
import Batteries.Data.Rat

structure Network (size : Nat) where
  toArray : Array (Array Nat)
  deriving Repr

def Network.instInhabited : Network size :=
  {
    toArray := #[]
  }

instance : Inhabited (Network size) where
  default := Network.instInhabited

abbrev Swaps := Array (Nat × Nat)

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

-- def Swaps.run [Inhabited α] (swaps : Swaps) (arr : Array α)
--     (le : α → α → Bool := by exact fun a b => a ≤ b) : Array α :=
--   swaps.foldl
--     (init := arr)
--     fun arr (a, b) =>
--       if !(le arr[a]! arr[b]!) then arr.swapIfInBounds a b else arr

@[specialize]
def Network.run
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

def Nat.toBitArray (n : Nat) : Array Bool := Id.run do
  let mut result := default
  for i in [0 : Nat.log2 n + 1] do
    result := result.push <| (n >>> i) &&& 1 = 1
  result

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

@[specialize]
def Array.pad (arr : Array α) (a : α) (newSize : Nat) :=
  arr.append (.replicate (newSize - arr.size) a)

@[specialize]
def Network.correctlySortsArray [Inhabited α] (n : Network size) (arr : Array α)
    (le : α → α → Bool := by exact fun a b => a ≤ b) : Bool :=
  n.run arr le |>.sorted le

def Network.correctnessScore (n : Network size) : Rat := Id.run do
  let mut successes := 0
  let numTests := 2 ^ size
  for i in [0 : numTests] do
    let arr := i.toBitArray.pad false size
    if n.correctlySortsArray arr fun a b => a = b ∨ ((¬a) ∧ b) then
      successes := successes + 1
  (successes : Rat) / (numTests : Rat)

def Network.isCorrect (n : Network size) : Bool := Id.run do
  let numTests := 2 ^ size
  for i in [0 : numTests] do
    let arr := i.toBitArray.pad false size
    if !n.correctlySortsArray arr fun a b => a = b ∨ ((¬a) ∧ b) then
      return false
  return true

def Network.swapsScore (n : Network size) : Rat :=
  if size ≤ 1 then
    if n.toSwaps.size = 0 then 0 else 1
  else
    -- 1 - n.toSwaps.size / (size * (size - 1) / 2)
    n.toSwaps.size

def Network.layersScore (n : Network size) : Rat :=
  if size ≤ 1 then
    if n.toArray.size = 0 then 0 else 1
  else
    n.toArray.size
    -- 1 - n.toArray.size / (2 * size - 3)

def Network.myScore1 (n : Network size) : Rat :=
  n.swapsScore
  -- let cs := n.correctnessScore
  -- if cs < 1 then
  --   cs
  -- else
    -- 1/2 * n.swapsScore + 1/2 * n.layersScore

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

def Network.addRandomSwaps [RandomGen Gen] (n : Network size) (g : Gen) (numSwaps : Nat) : Network size × Gen :=
  if numSwaps = 0 then
    (n, g)
  else
    let (n, g) := n.addRandomSwap g
    n.addRandomSwaps g (numSwaps - 1)

def Network.improve [RandomGen Gen] (n : Network size) (g : Gen) (fuel : Nat) (maxSwaps : Nat := (size * (size - 1) / 2)) (trustCorrect : Bool := false) : Network size × Gen :=
  if fuel = 0 ∨ size = 0 then
    (n, g)
  else
    let (numSwaps, g) := randNat g 1 maxSwaps
    let (n', g) := n.addRandomSwaps g numSwaps
    let ns := if trustCorrect then 1 else n.correctnessScore
    let (n, g, trustCorrect) := if (n'.swapsScore ≤ n.swapsScore ∧ n'.layersScore ≤ n.layersScore)
                      ∧ (n'.swapsScore ≠ n.swapsScore ∨ n'.layersScore ≠ n.layersScore) then
        if ns = 1 then
          let n'correct := n'.isCorrect
          if n'correct then
            (n', g, true)
          else
            (n, g, trustCorrect)
        else
          let nps := n'.correctnessScore
          if nps = 1 then
            (n', g, true)
          else
            (n, g, trustCorrect)
      else
        if ns = 1 then
          (n, g, true)
        else
          let nps := n'.correctnessScore
          if ns < nps then
            (n', g, nps = 1)
          else
            (n, g, trustCorrect)
    n.improve g (fuel - 1)

-- Output representation consumable by Brian Pursley's "sorting-network" visualization code:
-- https://github.com/brianpursley/sorting-network
def Network.toPursleyString (n : Network size) : String :=
  (fun s => s.take (s.length - 1)) <| n.toSwaps.foldl
    (init := "")
    fun str (a, b) =>
      str ++ s!"{a}:{b},"

-- def myGen := mkStdGen 0
-- #eval (default : Network 10).improve (Gen := StdGen) myGen 10
  -- |>.fst
  -- |>.correctnessScore
-- #eval (default : Network 5).addRandomSwaps (Gen := StdGen) myGen 10
--   |>.fst
--   |>.correctnessScore

-- def bubble2 : Network 2 := Network.mk
--   #[
--     #[1, 0],
--   ]
-- #eval (default : Network 4).addSwap 10 (0, 1)
def bubble3 : Network 3 := Network.mk
  #[
    #[1, 0, 2],
    #[0, 2, 1],
    #[1, 0, 2],
  ]
-- def bubble4 : Network 4 := Network.mk
--   #[
--     #[1, 0, 2, 3],
--     #[0, 2, 1, 3],
--     #[1, 0, 3, 2]
--   ]

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

-- #eval (.bubble : Network 2).correctnessScore
-- #eval (.bubble : Network 3).swapsScore
-- #eval (.bubble : Network 4).swapsScore
-- #eval (.bubble : Network 5).swapsScore
-- #eval (.bubble : Network 6).swapsScore
-- #eval (.bubble : Network 7).swapsScore
-- #eval (.bubble : Network 8).swapsScore
-- #eval (.bubble : Network 9).swapsScore
-- #eval (.bubble : Network 10).swapsScore
-- #eval (.bubble : Network 0).correctnessScore

  -- Network.fromLayers <| Array.ofFn (n := size) fun i =>


-- set_option profiler true
-- #eval (default : Network 5).addLayer.correctnessScore
-- def nw4a : Network 4 := Network.mk
--   #[
--     #[2, 3, 0, 1],
--     #[1, 0, 3, 2],
--     #[0, 2, 1, 3],
--   ]
-- -- #eval nw4a.correctnessScore
-- #eval nw4a.swapsScore
-- #eval nw4a.correctnessScore
-- #eval (default : Network 3).correctnessScore
-- -- def sw := nw4a.toSwaps
-- -- #eval nw4a.toSwaps.run #[4, 3, 2, 1]
-- -- #eval sw.run #[4, 3, 2, 1]
-- #eval nw4a.run #[4, 3, 2, 1]
-- #eval nw4a.correctlySortsArray #[4, 3, 2, 1]
