import SortingNetworkSearch
import SortingNetworkSearch.LFSR

def main (args : List String) : IO Unit := do
  -- let n : Network 3 := Network.mk #[.mk #[0, 2, 1], .mk #[0, 2, 1]]
  -- let n := show Network 3 from default
  -- let (n, g, lastFailures) := n.improve (mkStdGen) 50 (.some 1) true
  -- println! "{n.toArray} {lastFailures}"
  let size := args[0]!.toNat!.toUInt8
  let symmetric := args[1]! = "true"
  let mut lastFailures : Option Nat := .some 1
  let mut n : Network size := default
  let mut g := mkStdGen (← IO.rand 0 USize.size)
  let mut i := 1
  let mut isCorrect := false
  let mut historicIsCorrect := false
  let mut historicBestCEs := 0
  let mut historicBestLayers := 0
  let mut bestCEs : Nat := 0
  let mut bestLayers := 0
  let mut lastImprovementTime ← IO.monoMsNow
  let mut lastImprovementDuration := 0
  let mut numRestarts := 0
  while true do
    (n, g, lastFailures) := n.improve g 50 lastFailures symmetric ((size * (size - 1) / 2)).toNat
    i := i + 1
    if !isCorrect ∧ lastFailures = some 0 then
      isCorrect := true
      bestCEs := n.swapsScore
      bestLayers := n.layersScore
      lastImprovementTime ← IO.monoMsNow
      let historicBestCEs' := bestCEs
      let historicBestLayers' := bestLayers
      if !historicIsCorrect ∨ (bestCEs ≤ historicBestCEs ∧ bestLayers ≤ historicBestLayers)
            ∧ (bestCEs ≠ historicBestCEs ∧ bestLayers ≠ historicBestLayers) then
        historicIsCorrect := true
        historicBestCEs := historicBestCEs'
        historicBestLayers := historicBestLayers'
        println! s!"{n.toPursleyString}"
        println! s!"Found a size {size} network with {bestCEs} CEs and {bestLayers} layers after iteration {i} with {numRestarts} restarts"
    else if isCorrect then
      let swaps := n.swapsScore
      let layers := n.layersScore
      if swaps < bestCEs ∨ layers < bestLayers then
        bestCEs := swaps
        bestLayers := layers
        lastImprovementDuration := (← IO.monoMsNow) - lastImprovementTime
        lastImprovementTime ← IO.monoMsNow
        let historicBestCEs' := bestCEs.min historicBestCEs
        let historicBestLayers' := bestLayers.min historicBestLayers
        if (bestCEs ≤ historicBestCEs ∧ bestLayers ≤ historicBestLayers)
            ∧ (bestCEs ≠ historicBestCEs ∧ bestLayers ≠ historicBestLayers) then
          historicBestCEs := historicBestCEs'
          historicBestLayers := historicBestLayers'
          println! s!"{n.toPursleyString}"
          println! s!"Found a size {size} network with {swaps} CEs and {layers} layers after iteration {i} with {numRestarts} restarts"
      else
        let duration := (← IO.monoMsNow) - lastImprovementTime
        if lastImprovementDuration ≠ 0 ∧ duration > lastImprovementDuration * (5 + numRestarts.log2) then
          n := default
          isCorrect := false
          lastFailures := none
          numRestarts := numRestarts + 1
          i := 0
          lastImprovementDuration := 0
          -- println! "Restarting (total {numRestarts})"
