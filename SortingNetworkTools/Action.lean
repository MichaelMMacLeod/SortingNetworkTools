import SortingNetworkTools.NetworkExtras

inductive SerializationIn where
| list
deriving Inhabited

inductive SerializationOut where
| list
| svg
deriving Inhabited, Repr

inductive Algorithm where
| empty
| bubble
| batcher
deriving Inhabited, Repr

inductive NetworkSource where
| algorithm : Algorithm → (size : USize) → NetworkSource
| fromFile : System.FilePath → NetworkSource
deriving Inhabited, Repr

def NetworkSource.load : NetworkSource → IO (Σ size, Network size)
| .algorithm a size =>
  let n :=
    match a with
    | .empty => default
    | .bubble => Network.Algorithm.bubble
    | .batcher => Network.Algorithm.batcherOddEven
  pure ⟨size, n⟩
| .fromFile filePath => do
  match Network.fromPursleyString (← IO.FS.readFile filePath) with
  | .inl s => throw (IO.Error.userError s!"loading network failed: parse error at '{s}'")
  | .inr sizeNetworkPair => pure sizeNetworkPair

inductive Action where
| convert : NetworkSource → SerializationOut → Action
| evolve : (seed : Option Nat) → (timeoutSeconds : Option Nat) → NetworkSource → Action
| verify : NetworkSource → Action
deriving Inhabited, Repr

def Network.evolve (seedOption timeoutSecondsOption : Option Nat) (network : Network size) : IO Unit := do
  let startMs ← IO.monoMsNow
  let mut currentMs := startMs
  let stopTimeMs : Option Nat := timeoutSecondsOption.map fun s => s * 1000 + currentMs
  let seed := seedOption.getD (← IO.rand 0 USize.size)
  if let none := seedOption then
    println! "Evolving with randomly selected seed {seed}"
  else
    println! "Evolving with seed {seed}"
  let mut stdGen := mkStdGen seed
  let mut lastFailures : UInt64 := network.compile.countTestFailures
  let mut network := network
  let numLayers := network.layers.size
  let numSwaps := network.toSwaps.size
  let pursleyString := network.toPursleyString
  println! ""
  if 0 < network.layers.size then
    let warning :=
      if lastFailures = 0 then
        "a correct"
      else
        "an incorrect"
    println! "Evolving from {warning} network of {numLayers} layers containing a total of {numSwaps} compare-and-exchange operations"
    println! pursleyString
  else
    println! "Evolving from an empty network"
  println! ""
  while currentMs < stopTimeMs.getD (currentMs + 1) do
    let mut newNetwork := network
    let mut lastFailures' := none
    (newNetwork, stdGen, lastFailures') := network.improve stdGen 1 (some lastFailures) true
    lastFailures := lastFailures'.get!
    if newNetwork ≠ network then
      network := newNetwork
      let numLayers := network.layers.size
      let numSwaps := network.toSwaps.size
      let pursleyString := network.toPursleyString
      let warning :=
        if lastFailures = 0 then
          "(Reducing the size of a correct network) "
        else
          "(Attempting to grow a correct network) "
      println! "{warning}Evolved to {numLayers} layers containing a total of {numSwaps} compare-and-exchange operations"
      println! pursleyString
      println! ""
    currentMs ← IO.monoMsNow
  let elapsedSeconds := (currentMs - startMs) / 1000
  println! "Evolution from seed {seed} finished after {elapsedSeconds} seconds"

def Network.verify (network : Network size) : IO Unit := do
  let failures := network.compile.countTestFailures
  if failures = 0
  then println! "This network correctly sorts all possible inputs"
  else println! "This network fails to sort some inputs"

def Action.main : Action → IO Unit
| convert networkSource serializationOut => do
  let ⟨_size, network⟩ ← networkSource.load
  match serializationOut with
  | .list => IO.println network.toPursleyString
  | .svg => IO.println network.toSVG.toString
| .evolve seedOption timeoutSecondsOption networkSource => do
  let ⟨_size, network⟩ ← networkSource.load
  network.evolve seedOption timeoutSecondsOption
| .verify networkSource => do
  let ⟨_size, network⟩ ← networkSource.load
  network.verify
