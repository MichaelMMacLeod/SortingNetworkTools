import SortingNetworkSearch
import SortingNetworkSearch.LFSR

def main (args : List String) : IO Unit := do
  let size := args[0]!.toNat!
  let mut lastFailures : Option Nat := .some 1
  let mut n : Network size := default
  let mut g := mkStdGen 0
  let mut i := 1
  let mut isCorrect := false
  let mut bestCEs := 0
  let mut bestLayers := 0
  while true do
    (n, g, lastFailures) := n.improve g 50 lastFailures
    i := i + 1
    if !isCorrect ∧ n.isCorrect' then
      isCorrect := true
      bestCEs := n.swapsScore
      bestLayers := n.layersScore
      println! s!"{n.toPursleyString}"
      println! s!"Found a size {size} network with {bestCEs} CEs and {bestLayers} layers after iteration {i}"
    else if isCorrect then
      let swaps := n.swapsScore
      let layers := n.layersScore
      if swaps < bestCEs ∨ layers < bestLayers then
        bestCEs := swaps
        bestLayers := layers
        println! s!"{n.toPursleyString}"
        println! s!"Found a size {size} network with {swaps} CEs and {layers} layers after iteration {i}"
