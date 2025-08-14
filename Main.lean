import SortingNetworkSearch.LFSR
import SortingNetworkSearch.Network
import SortingNetworkSearch.SVG
-- import SortingNetworkSearch.NetworkWidget

-- @[noinline]
-- def computeWithCata (lst : List Nat) : Nat := cata (β := Nat) lst List.project
--     (fun lst =>
--       match lst with
--       | .nil => 0
--       | .cons a b => a + b)
--     (fun state xs f =>
--     match xs with
--     | .nil => (state, .nil)
--     | .cons a b =>
--       let (state, c) := f state b
--       (state, .cons a c))


def main (args : List String) : IO Unit := do
  let size := args[0]!.toNat!
  -- let str := (List.range size).map (·.repr) |>.foldl (· ++ ·) ""
  -- println! str |>.get! 0

  let c1 := SVG.Node.matryoshka (size / 2)
  let c2 := SVG.Node.matryoshka (size / 5)
  let c3 := SVG.Node.matryoshka (size / 8)
  let n := { SVG.Node.matryoshka 0 with children := [c1, c2, c3] }
  println! n.toString
  -- let x2 : Trampoline (Nat × String → Trampoline String) := SVG.Node.cataTR SVG.toStringFunc'' n
  -- println! x2.run (0, "")

  -- let x2 : Trampoline String := SVG.Node.cataTR SVG.toStringFunc (SVG.mkDeepNode size) 0

  -- let beforeA ← IO.monoMsNow
  -- let lst := List.range args[0]!.toNat!
  -- let afterA ← IO.monoMsNow
  -- println! "took {afterA - beforeA} to make the list"
  -- let afterA ← IO.monoMsNow
  -- println! "took {afterA - beforeA} to make the list"
  -- let beforeA ← IO.monoMsNow
  -- let v := lst.foldr (· + ·) 0
  -- println! "{v} in {afterA - beforeA}"
  -- let afterA ← IO.monoMsNow
  -- println! "{v} in {afterA - beforeA}"
  -- let beforeA ← IO.monoMsNow
  -- let v := computeWithCata lst
  -- let afterA ← IO.monoMsNow
  -- println! "{v} in {afterA - beforeA}"
  -- let afterA ← IO.monoMsNow
  -- println! "{v} in {afterA - beforeA}"



  -- let size := args[0]!.toNat!.toUSize
  -- let symmetric := args[1]! = "true"
  -- let mut lastFailures : Option UInt64 := .some 1
  -- let mut n : Network size := default
  -- let mut g := mkStdGen (← IO.rand 0 USize.size)
  -- let mut i := 1
  -- let mut isCorrect := false
  -- let mut historicIsCorrect := false
  -- let mut historicBestCEs := 0
  -- let mut historicBestLayers := 0
  -- let mut bestCEs : Nat := 0
  -- let mut bestLayers := 0
  -- let mut lastImprovementTime ← IO.monoMsNow
  -- let mut lastImprovementDuration := 0
  -- let mut numRestarts := 0
  -- while true do
  --   (n, g, lastFailures) := n.improve g 50 lastFailures symmetric ((size * (size - 1) / 2)).toNat
  --   i := i + 1
  --   if !isCorrect ∧ lastFailures = some 0 then
  --     isCorrect := true
  --     bestCEs := n.toSwaps.size
  --     bestLayers := n.layers.size
  --     lastImprovementTime ← IO.monoMsNow
  --     let historicBestCEs' := bestCEs
  --     let historicBestLayers' := bestLayers
  --     if !historicIsCorrect ∨ (bestCEs ≤ historicBestCEs ∧ bestLayers ≤ historicBestLayers)
  --           ∧ (bestCEs ≠ historicBestCEs ∧ bestLayers ≠ historicBestLayers) then
  --       historicIsCorrect := true
  --       historicBestCEs := historicBestCEs'
  --       historicBestLayers := historicBestLayers'
  --       println! s!"{n.toPursleyString}"
  --       println! s!"Found a size {size} network with {bestCEs} CEs and {bestLayers} layers after iteration {i} with {numRestarts} restarts"
  --   else if isCorrect then
  --     let swaps := n.toSwaps.size
  --     let layers := n.layers.size
  --     if swaps < bestCEs ∨ layers < bestLayers then
  --       bestCEs := swaps
  --       bestLayers := layers
  --       lastImprovementDuration := (← IO.monoMsNow) - lastImprovementTime
  --       lastImprovementTime ← IO.monoMsNow
  --       let historicBestCEs' := bestCEs.min historicBestCEs
  --       let historicBestLayers' := bestLayers.min historicBestLayers
  --       if (bestCEs ≤ historicBestCEs ∧ bestLayers ≤ historicBestLayers)
  --           ∧ (bestCEs ≠ historicBestCEs ∧ bestLayers ≠ historicBestLayers) then
  --         historicBestCEs := historicBestCEs'
  --         historicBestLayers := historicBestLayers'
  --         println! s!"{n.toPursleyString}"
  --         println! s!"Found a size {size} network with {swaps} CEs and {layers} layers after iteration {i} with {numRestarts} restarts"
  --     else
  --       let duration := (← IO.monoMsNow) - lastImprovementTime
  --       if lastImprovementDuration ≠ 0 ∧ duration > lastImprovementDuration * (5 + numRestarts.log2) then
  --         n := default
  --         isCorrect := false
  --         lastFailures := none
  --         numRestarts := numRestarts + 1
  --         i := 0
  --         lastImprovementDuration := 0
