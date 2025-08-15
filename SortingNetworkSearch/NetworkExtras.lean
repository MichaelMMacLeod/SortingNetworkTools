import SortingNetworkSearch.Network
import SortingNetworkSearch.SVGWidget

def Network.fromSwapLayersList (layers : List (List Swap)) : Network size :=
  let layers := layers.map (·.toArray) |>.toArray
  .fromSwapLayers layers

def Layers.fromSwaps (size : Nat) (swaps : Array Swap) : Array Layer := Id.run do
  let mut result := #[]
  let mut layer := Array.range size |>.map (·.toUSize)
  let mut occupied := Array.replicate size false
  let mut i := 0
  while h : i < swaps.size do
    let (a, b) := swaps[i]
    if occupied[a]! ∨ occupied[b]! then
      result := result.push layer
      layer := Array.range size |>.map (·.toUSize)
      occupied := Array.replicate size false
    else
      layer := layer.set! a.toNat b
      layer := layer.set! b.toNat a
      occupied := occupied.set! a.toNat true
      occupied := occupied.set! b.toNat true
      i := i + 1
      if i = swaps.size then
        result := result.push layer
  result

/--
Returns a `Network` implementing Batcher odd-even mergesort.
Reference: https://en.wikipedia.org/wiki/Batcher_odd%E2%80%93even_mergesort
-/
def Network.Algorithm.batcherOddEven : Network size := Id.run do
  let mut swaps : Array Swap := #[]
  let n := size.toNat
  let mut p := 1
  while p < n do
    let mut k := p
    while k ≥ 1 do
      let mut j := k%p
      while j ≤ n-1-k do
        let mut i := 0
        while i ≤ min (k-1) (n-j-k-1) do
          if (i+j) / (p*2) = (i+j+k) / (p*2) then
            let a := j+i
            let b := j+i+k
            swaps := swaps.push (a.toUSize, b.toUSize)
          i := i+1
        j := j+2*k
      k := k/2
    p := p+p
  .consolidateLayers <| .mk <| Layers.fromSwaps size.toNat swaps

/--
Returns a `Network` implementing Bubble sort.
Reference: https://en.wikipedia.org/wiki/Bubble_sort.
-/
def Network.Algorithm.bubble : Network size :=
  if size ≤ 1 then default else Network.mk <| ascending ++ (ascending.pop |>.reverse)
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

-- Definitions of some of the best known sorting networks
-- See https://bertdobbelaere.github.io/sorting_networks.html

def nw6_12x5 : Network 6 := .fromSwapLayersList [[(0,5),(1,3),(2,4)],[(1,2),(3,4)],[(0,3),(2,5)],[(0,1),(2,3),(4,5)],[(1,2),(3,4)]]
def nw7_16x6 : Network 7 := .fromSwapLayersList [[(0,6),(2,3),(4,5)],[(0,2),(1,4),(3,6)],[(0,1),(2,5),(3,4)],[(1,2),(4,6)],[(2,3),(4,5)],[(1,2),(3,4),(5,6)]]
def nw8_19x6 : Network 8 := .fromSwapLayersList [[(0,2),(1,3),(4,6),(5,7)],[(0,4),(1,5),(2,6),(3,7)],[(0,1),(2,3),(4,5),(6,7)],[(2,4),(3,5)],[(1,4),(3,6)],[(1,2),(3,4),(5,6)]]
def nw9_25x7 : Network 9 := .fromSwapLayersList [[(0,3),(1,7),(2,5),(4,8)],[(0,7),(2,4),(3,8),(5,6)],[(0,2),(1,3),(4,5),(7,8)],[(1,4),(3,6),(5,7)],[(0,1),(2,4),(3,5),(6,8)],[(2,3),(4,5),(6,7)],[(1,2),(3,4),(5,6)]]
def nw10_29x8 : Network 10 := .fromSwapLayersList [[(0,8),(1,9),(2,7),(3,5),(4,6)],[(0,2),(1,4),(5,8),(7,9)],[(0,3),(2,4),(5,7),(6,9)],[(0,1),(3,6),(8,9)],[(1,5),(2,3),(4,8),(6,7)],[(1,2),(3,5),(4,6),(7,8)],[(2,3),(4,5),(6,7)],[(3,4),(5,6)]]
def nw10_31x7 : Network 10 := .fromSwapLayersList [[(0,1),(2,5),(3,6),(4,7),(8,9)],[(0,6),(1,8),(2,4),(3,9),(5,7)],[(0,2),(1,3),(4,5),(6,8),(7,9)],[(0,1),(2,7),(3,5),(4,6),(8,9)],[(1,2),(3,4),(5,6),(7,8)],[(1,3),(2,4),(5,7),(6,8)],[(2,3),(4,5),(6,7)]]
def nw11_35x8 : Network 11 := .fromSwapLayersList [[(0,9),(1,6),(2,4),(3,7),(5,8)],[(0,1),(3,5),(4,10),(6,9),(7,8)],[(1,3),(2,5),(4,7),(8,10)],[(0,4),(1,2),(3,7),(5,9),(6,8)],[(0,1),(2,6),(4,5),(7,8),(9,10)],[(2,4),(3,6),(5,7),(8,9)],[(1,2),(3,4),(5,6),(7,8)],[(2,3),(4,5),(6,7)]]
def nw12_39x9 : Network 12 := .fromSwapLayersList [[(0,8),(1,7),(2,6),(3,11),(4,10),(5,9)],[(0,1),(2,5),(3,4),(6,9),(7,8),(10,11)],[(0,2),(1,6),(5,10),(9,11)],[(0,3),(1,2),(4,6),(5,7),(8,11),(9,10)],[(1,4),(3,5),(6,8),(7,10)],[(1,3),(2,5),(6,9),(8,10)],[(2,3),(4,5),(6,7),(8,9)],[(4,6),(5,7)],[(3,4),(5,6),(7,8)]]
def nw12_40x8 : Network 12 := .fromSwapLayersList [[(0,8),(1,7),(2,6),(3,11),(4,10),(5,9)],[(0,2),(1,4),(3,5),(6,8),(7,10),(9,11)],[(0,1),(2,9),(4,7),(5,6),(10,11)],[(1,3),(2,7),(4,9),(8,10)],[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11)],[(1,2),(3,5),(6,8),(9,10)],[(2,4),(3,6),(5,8),(7,9)],[(1,2),(3,4),(5,6),(7,8),(9,10)]]
def nw13_45x10 : Network 13 := .fromSwapLayersList [[(0,12),(1,10),(2,9),(3,7),(5,11),(6,8)],[(1,6),(2,3),(4,11),(7,9),(8,10)],[(0,4),(1,2),(3,6),(7,8),(9,10),(11,12)],[(4,6),(5,9),(8,11),(10,12)],[(0,5),(3,8),(4,7),(6,11),(9,10)],[(0,1),(2,5),(6,9),(7,8),(10,11)],[(1,3),(2,4),(5,6),(9,10)],[(1,2),(3,4),(5,7),(6,8)],[(2,3),(4,5),(6,7),(8,9)],[(3,4),(5,6)]]
def nw13_46x9 : Network 13 := .fromSwapLayersList [[(0,11),(1,7),(2,4),(3,5),(8,9),(10,12)],[(0,2),(3,6),(4,12),(5,7),(8,10)],[(0,8),(1,3),(2,5),(4,9),(6,11),(7,12)],[(0,1),(2,10),(3,8),(4,6),(9,11)],[(1,3),(2,4),(5,10),(6,8),(7,9),(11,12)],[(1,2),(3,4),(5,8),(6,9),(7,10)],[(2,3),(4,7),(5,6),(8,11),(9,10)],[(4,5),(6,7),(8,9),(10,11)],[(3,4),(5,6),(7,8),(9,10)]]
def nw14_51x10 : Network 14 := .fromSwapLayersList [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)],[(0,2),(1,3),(4,8),(5,9),(10,12),(11,13)],[(0,4),(1,2),(3,7),(5,8),(6,10),(9,13),(11,12)],[(0,6),(1,5),(3,9),(4,10),(7,13),(8,12)],[(2,10),(3,11),(4,6),(7,9)],[(1,3),(2,8),(5,11),(6,7),(10,12)],[(1,4),(2,6),(3,5),(7,11),(8,10),(9,12)],[(2,4),(3,6),(5,8),(7,10),(9,11)],[(3,4),(5,6),(7,8),(9,10)],[(6,7)]]
def nw14_52x9 : Network 14 := .fromSwapLayersList [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)],[(0,2),(1,3),(4,8),(5,9),(10,12),(11,13)],[(0,10),(1,6),(2,11),(3,13),(5,8),(7,12)],[(1,4),(2,8),(3,6),(5,11),(7,10),(9,12)],[(0,1),(3,9),(4,10),(5,7),(6,8),(12,13)],[(1,5),(2,4),(3,7),(6,10),(8,12),(9,11)],[(1,2),(3,5),(4,6),(7,9),(8,10),(11,12)],[(2,3),(4,5),(6,7),(8,9),(10,11)],[(3,4),(5,6),(7,8),(9,10)]]
def nw15_56x10 : Network 15 := .fromSwapLayersList [[(1,2),(3,10),(4,14),(5,8),(6,13),(7,12),(9,11)],[(0,14),(1,5),(2,8),(3,7),(6,9),(10,12),(11,13)],[(0,7),(1,6),(2,9),(4,10),(5,11),(8,13),(12,14)],[(0,6),(2,4),(3,5),(7,11),(8,10),(9,12),(13,14)],[(0,3),(1,2),(4,7),(5,9),(6,8),(10,11),(12,13)],[(0,1),(2,3),(4,6),(7,9),(10,12),(11,13)],[(1,2),(3,5),(8,10),(11,12)],[(3,4),(5,6),(7,8),(9,10)],[(2,3),(4,5),(6,7),(8,9),(10,11)],[(5,6),(7,8)]]

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

def OccupiedChannels.mk (size : USize) : Array Bool := Array.replicate size.toNat false

def OccupiedChannels.clear (occupiedChannels : Array Bool) : Array Bool := Id.run do
  let mut occupiedChannels := occupiedChannels
  for i in [0:occupiedChannels.size] do
    occupiedChannels := occupiedChannels.set! i false
  occupiedChannels

def OccupiedChannels.addSwap (occupiedChannels : Array Bool) (swap : USize × USize) : Array Bool := Id.run do
  let (a, b) := swap
  let mut occupiedChannels := occupiedChannels
  for i in [a.toNat:b.toNat+1] do
    occupiedChannels := occupiedChannels.set! i true
  occupiedChannels

def OccupiedChannels.swapGoesOnNextLine (occupiedChannels : Array Bool) (swap : USize × USize) : Bool := Id.run do
  let (a, b) := swap
  for i in [a.toNat:b.toNat+1] do
    if occupiedChannels[i]! then
      return true
  false

def Swap.size (s : Swap) : Nat :=
  let (a, b) := s
  let (a, b) := (min a b, max a b)
  b.toNat - a.toNat

def Swap.lt (s1 : Swap) (s2 : Swap) : Bool :=
  let s1Size := s1.size
  let s2Size := s2.size
  s1Size > s2Size ∨ (s1Size = s2Size ∧ s1.fst > s2.fst)

def Network.toNicelyOrderedSwapLayers (n : Network size) : Array SwapLayer := Id.run do
  let mut result : Array SwapLayer := #[]
  for layer in n.layers do
    let mut resultLayer : Array Swap := #[]
    let mut swaps := Layer.toSwapLayer layer |>.qsort (lt := Swap.lt)
    while h : 0 < swaps.size do
      let smallest := swaps[swaps.size - 1]
      swaps := swaps.pop
      resultLayer := resultLayer.push smallest
      let mut occupiedChannels := OccupiedChannels.mk size
      occupiedChannels := OccupiedChannels.addSwap occupiedChannels smallest
      let mut i := swaps.size - 1
      while h : 0 < i ∧ i < swaps.size do
        let swap := swaps[i]
        if swap.size = smallest.size ∧ !OccupiedChannels.swapGoesOnNextLine occupiedChannels swap then
          resultLayer := resultLayer.push swap
          swaps := swaps.eraseIdx i
        occupiedChannels := OccupiedChannels.addSwap occupiedChannels swap
        i := i - 1
    result := result.push resultLayer
  result

def Network.toSVG (n : Network size) : SVG.Node :=
  let result := {
    name := "svg"
    attributes := .ofList [
      ("xmlns", "http://www.w3.org/2000/svg"),
      ("width", s!"{width}"),
      ("height", s!"{height}"),
      ("viewBox", s!"0 0 {vbWidth} {vbHeight}"),
    ]
    children := [
      {
        name := "rect"
        attributes := .ofList [
          ("width", s!"{width}"),
          ("height", s!"{height}"),
          ("fill", s!"{bgColor}"),
        ]
        children := []
      }
    ] ++ swapNodes
      ++ channels
  }
  result
where
  swaps : Array SwapLayer := n.toNicelyOrderedSwapLayers
  hscale : Float := 9
  vscale : Float := 20
  hoffset := hscale
  voffset := vscale
  width := 2 * hoffset + hscale * numVerticalLines.toFloat
  height := voffset + vscale * size.toFloat
  vbWidth := width
  vbHeight := height
  bgColor := "white"
  swapLineColor := "black"
  swapLineStrokeWidth := 0.5
  swapCircleColor := swapLineColor
  swapCircleRadius := 3
  channelColor := swapLineColor
  channelStrokeWidth := 0.5
  channels : List SVG.Node := List.ofFn (n := size.toNat) fun i =>
    let i : Nat := i.toNat
    let y := voffset + vscale * i.toFloat
    {
      name := "line"
      attributes := .ofList [
        ("x1", s!"{0}"),
        ("x2", s!"{width}"),
        ("y1", s!"{y}"),
        ("y2", s!"{y}"),
        ("stroke", s!"{swapLineColor}"),
        ("stroke-width", s!"{channelStrokeWidth}"),
      ]
      children := []
    }
  numVerticalLines := swapNodesAndVerticalLineCount.snd - 2
  swapNodes := swapNodesAndVerticalLineCount.fst
  swapNodesAndVerticalLineCount : List SVG.Node × Nat :=
    let (xs, _, vlineCount) := swaps.foldl SwapLayer.toSVG ([], 1, 1)
    (xs, vlineCount)
  swapGoesOnNextLine (occupiedChannels : Array Bool) (swap : USize × USize) : Bool := Id.run do
    let (a, b) := swap
    for i in [a.toNat:b.toNat+1] do
      if occupiedChannels[i]! then
        return true
    false
  SwapLayer.toSVG (acc : List SVG.Node × Nat × Nat) (sl : SwapLayer) : List SVG.Node × Nat × Nat :=
    let (acc, sIdx, vlineCount) := acc
    let (sIdx, _, xs, vlineCount) := sl.foldl Swap.toSVG (sIdx, OccupiedChannels.mk size, [], vlineCount)
    (acc ++ xs, sIdx + 3, vlineCount + 3)
  Swap.toSVG (acc : Nat × Array Bool × List SVG.Node × Nat) (s : Swap) : Nat × Array Bool × List SVG.Node × Nat :=
    let (sIdx, occupiedChannels, acc, vlineCount) := acc
    let (a, b) := (min s.fst s.snd, max s.fst s.snd)
    let (sIdx, occupiedChannels, vlineCount) :=
      if !swapGoesOnNextLine occupiedChannels (a, b) then
        let occupiedChannels := Id.run do
          let mut occupiedChannels := occupiedChannels
          for i in [a.toNat:b.toNat+1] do
            occupiedChannels := occupiedChannels.set! i true
          occupiedChannels
        (sIdx, occupiedChannels, vlineCount)
      else
        let occupiedChannels := Id.run do
          let mut occupiedChannels := occupiedChannels
          for i in [0:occupiedChannels.size] do
            occupiedChannels := occupiedChannels.set! i false
          occupiedChannels

        let occupiedChannels := Id.run do
          let mut occupiedChannels := occupiedChannels
          for i in [a.toNat:b.toNat+1] do
            occupiedChannels := occupiedChannels.set! i true
          occupiedChannels
        (sIdx + 1, occupiedChannels, vlineCount + 1)
    let a := a.toFloat
    let b := b.toFloat
    let x := hoffset + hscale * sIdx.toFloat
    let y1 := voffset + vscale * a
    let y2 := voffset + vscale * b
    let line := {
      name := "line"
      attributes := .ofList [
        ("x1", s!"{x}"),
        ("x2", s!"{x}"),
        ("y1", s!"{y1}"),
        ("y2", s!"{y2}"),
        ("stroke", s!"{swapLineColor}"),
        ("stroke-width", s!"{swapLineStrokeWidth}"),
      ]
      children := []
    }
    let c1 := {
      name := "circle"
      attributes := .ofList [
        ("cx", s!"{x}"),
        ("cy", s!"{y1}"),
        ("r", s!"{swapCircleRadius}"),
        ("fill", s!"{swapCircleColor}"),
      ]
      children := []
    }
    let c2 := {
      name := "circle"
      attributes := .ofList [
        ("cx", s!"{x}"),
        ("cy", s!"{y2}"),
        ("r", s!"{swapCircleRadius}"),
        ("fill", s!"{swapCircleColor}"),
      ]
      children := []
    }
    (sIdx, occupiedChannels, [line, c1, c2] ++ acc, vlineCount)
