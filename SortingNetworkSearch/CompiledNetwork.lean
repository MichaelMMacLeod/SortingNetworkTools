import SortingNetworkSearch.ExtraTheorems
import SortingNetworkSearch.Layer
import SortingNetworkSearch.TestPack

@[grind]
structure CompiledNetwork (size : USize) where
  swaps : Array Swap
  size_lt_USize_size : swaps.size < USize.size := by grind
  swaps_sizes : ∀ s ∈ swaps, s.fst < size ∧ s.snd < size := by grind

instance { size : USize } : Inhabited (CompiledNetwork size) where
  default := by
    refine CompiledNetwork.mk #[] (size_lt_USize_size := ?_)
    rw [Array.size_empty]
    exact USize.size_pos

@[grind]
structure binaryParallelCompareAndSwap.h (vals : Array UInt64) (a b : USize) where
  size_vals_lt : vals.size < USize.size := by grind
  a_lt_vals_usize : a < vals.usize := by grind
  b_lt_vals_usize : b < vals.usize := by grind

def binaryParallelCompareAndSwap
    (a b : USize)
    (vals : Subtype (binaryParallelCompareAndSwap.h · a b) )
    : Array UInt64 :=
  have : a.toNat < vals.val.size := by grind
  have : b.toNat < vals.val.size := by grind
  let tmp := vals.val[a]
  let vals := vals.val.uset a (tmp &&& vals.val[b]) (by grind)
  let vals := vals.uset b (tmp ||| vals[b]'(by grind)) (by grind)
  vals

@[grind =]
theorem binaryParallelCompareAndSwap_size_eq
    (a b : USize)
    (vals : Subtype (binaryParallelCompareAndSwap.h · a b))
    : (binaryParallelCompareAndSwap a b vals).size = vals.val.size := by
  simp [binaryParallelCompareAndSwap]

@[grind]
structure CompiledNetwork.runTestPack.h (n : CompiledNetwork size) (testPack : Array UInt64) where
  size_vals_lt_size_USize : testPack.size < USize.size := by grind
  swaps_lt_testPack_usize : ∀ swap ∈ n.swaps, swap.fst < testPack.usize ∧ swap.snd < testPack.usize := by grind

partial def CompiledNetwork.runTestPack
    (n : CompiledNetwork size)
    (testPack : Subtype (runTestPack.h n ·))
    : Array UInt64 :=
  let rec loop
      (i : USize)
      (testPack : Subtype (runTestPack.h n ·))
      : Array UInt64 :=
    if h : i < n.swaps.usize then
      let swap := n.swaps.uget i (by grind)
      let a := swap.fst
      let b := swap.snd
      have testPack_property := testPack.property
      let testPack := ⟨testPack, by grind⟩
      let testPack' := binaryParallelCompareAndSwap a b testPack
      have size_eq := binaryParallelCompareAndSwap_size_eq a b testPack
      have runParallel_h : runTestPack.h n testPack' := by
        apply runTestPack.h.mk
        . rw [binaryParallelCompareAndSwap_size_eq]
          exact testPack_property.size_vals_lt_size_USize
        . simp_wf
          rw [binaryParallelCompareAndSwap_size_eq]
          intro a b
          exact testPack_property.swaps_lt_testPack_usize (a, b)
      loop (i + 1) ⟨testPack', by grind⟩
    else testPack
  loop 0 testPack

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
