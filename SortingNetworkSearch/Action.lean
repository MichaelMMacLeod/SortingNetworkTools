import SortingNetworkSearch.NetworkExtras
import Init.System.IO

inductive SerializationIn where
  -- | listOfLayers
  -- | listOfSwapLayers
  -- | listOfSwaps
  | swapsString

inductive SerializationOut where
  -- | listOfLayers
  -- | listOfSwapLayers
  -- | listOfSwaps
  | swapsString
  | svg

inductive ExistingNetwork where
  | bubble : USize → ExistingNetwork
  | batcherOddEven : USize → ExistingNetwork
  | fromFile : SerializationIn → System.FilePath → ExistingNetwork

def ExistingNetwork.load : ExistingNetwork → IO (Σ size, Network size)
  | .bubble size => pure ⟨size, .Algorithm.bubble⟩
  | .batcherOddEven size => pure ⟨size, .Algorithm.batcherOddEven⟩
  | .fromFile .swapsString filePath => do
    match Network.fromPursleyString (← IO.FS.readFile filePath) with
    | .inl s => throw (IO.Error.userError s!"loading network failed: parse error at '{s}'")
    | .inr sizeNetworkPair => pure sizeNetworkPair

structure EvolveConfig where
  timeoutSeconds : Option Nat

inductive Action where
  | convert : ExistingNetwork → SerializationOut → Action
  | evolve : (seed : Option Nat) → (timeoutSeconds : Option Nat) → ExistingNetwork ⊕ USize → Action

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
          "(Reducing a the size of a correct network) "
        else
          "(Attempting to grow a correct network) "
      println! "{warning}Evolved to {numLayers} layers containing a total of {numSwaps} compare-and-exchange operations"
      println! pursleyString
      println! ""
    currentMs ← IO.monoMsNow
  let elapsedSeconds := (currentMs - startMs) / 1000
  println! "Evolution from seed {seed} finished after {elapsedSeconds} seconds"

def Action.main : Action → IO Unit
  | convert existingNetwork serializationOut => do
    let ⟨_size, network⟩ ← existingNetwork.load
    match serializationOut with
    | .swapsString => IO.println network.toPursleyString
    | .svg => IO.println network.toSVG.toString
  | .evolve seedOption timeoutSecondsOption existingNetworkOrSize => do
    let ⟨_size, network⟩ ← do
      match existingNetworkOrSize with
      | .inl existingNetwork => existingNetwork.load
      | .inr size => pure ⟨size, default⟩
    network.evolve seedOption timeoutSecondsOption
