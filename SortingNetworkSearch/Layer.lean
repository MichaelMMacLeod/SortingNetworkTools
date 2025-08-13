abbrev Layer := Array USize
abbrev Swap := USize × USize
abbrev SwapLayer := Array Swap

def Layer.toSwapLayer (layer : Array USize) : Array Swap :=
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

def SwapLayer.toLayer (size : USize) (swaps : Array Swap) : Layer :=
  swaps.foldl
    (init := Array.range size.toNat |>.map (·.toUSize))
    fun acc (a, b) =>
      let acc := acc.set! a.toNat b
      let acc := acc.set! b.toNat a
      acc

/-- Returns `true` if `layer` contains no compare-and-swap operations, `false` otherwise. -/
def Layer.isUseless (layer : Layer) : Bool := Id.run do
  for i in [0 : layer.size], v in layer do
    if i ≠ v.toNat then
      return false
  true

def Layer.rotate (arr : Layer) (amount : Nat) : Layer :=
  if arr.size = 0 then
    arr
  else
    let adjust : USize → USize :=
      fun n => (n.toNat + amount) % arr.size |>.toUSize
    arr
      |> Layer.toSwapLayer
      |>.map (fun (a, b) => (adjust a, adjust b))
      |> SwapLayer.toLayer arr.usize
