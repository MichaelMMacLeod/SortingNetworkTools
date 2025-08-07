import SortingNetworkSearch

def main (args : List String) : IO Unit := do
  let size := args[0]!.toNat!
  let mut n : Network size := default
  let mut g := mkStdGen 0
  let mut i := 1
  let mut isCorrect := false
  let mut bestCEs := 0
  let mut bestLayers := 0
  while true do
    (n, g) := n.improve g 50
    i := i + 1
    if !isCorrect ∧ n.correctnessScore = 1 then
      isCorrect := true
      bestCEs := n.swapsScore
      bestLayers := n.layersScore
      println! s!"{n.toPursleyString}"
    else if isCorrect then
      let swaps := n.swapsScore
      let layers := n.layersScore
      if swaps < bestCEs ∨ layers < bestLayers then
        bestCEs := swaps
        bestLayers := layers
        println! s!"{n.toPursleyString}"


    -- println! s!"Found a size {size} network with {swaps} CEs and {layers} layers after iteration {i}"
