import SortingNetworkSearch.ExtraTheorems

@[grind]
structure CompiledNetwork (size : USize) where
  as : Array USize
  bs : Array USize
  size_eq : as.size = bs.size := by grind
  size_lt_USize_size : as.size < USize.size := by grind
  as_sizes : ∀ a ∈ as, a < size := by grind
  bs_sizes : ∀ b ∈ bs, b < size := by grind

instance { size : USize } : Inhabited (CompiledNetwork size) where
  default := by
    refine CompiledNetwork.mk #[] #[] (size_lt_USize_size := ?_)
    rw [Array.size_empty]
    exact USize.size_pos

@[grind]
structure binaryParallelCompareAndSwap.h (vals : Array UInt64) (a b : USize) where
  size_vals_lt : vals.size < USize.size := by grind
  a_lt_vals_usize : a < vals.usize
  b_lt_vals_usize : b < vals.usize

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

theorem binaryParallelCompareAndSwap_size_eq
    (a b : USize)
    (vals : Subtype (binaryParallelCompareAndSwap.h · a b))
    : (binaryParallelCompareAndSwap a b vals).size = vals.val.size := by
  simp [binaryParallelCompareAndSwap]

@[grind]
structure CompiledNetwork.runTestPack.h (n : CompiledNetwork size) (testPack : Array UInt64) where
  size_vals_lt_size_USize : testPack.size < USize.size := by grind
  lt_usize_as : ∀ a ∈ n.as, a < testPack.usize := by grind
  lt_usize_bs : ∀ b ∈ n.bs, b < testPack.usize := by grind

partial def CompiledNetwork.runTestPack
    (n : CompiledNetwork size)
    (testPack : Subtype (runTestPack.h n ·))
    : Array UInt64 :=
  let rec loop
      (i : USize)
      (testPack : Subtype (runTestPack.h n ·))
      : Array UInt64 :=
    if h : i < n.as.usize then
      let a := n.as.uget i (by grind)
      let b := n.bs.uget i (by grind)
      have testPack_property := testPack.property
      let testPack := ⟨testPack, by grind⟩
      let testPack' := binaryParallelCompareAndSwap a b testPack
      have size_eq := binaryParallelCompareAndSwap_size_eq a b testPack
      have runParallel_h : runTestPack.h n testPack' := by
        apply runTestPack.h.mk
        all_goals simp only [size_eq, testPack']
        . exact testPack_property.size_vals_lt_size_USize
        all_goals simp only [Array.usize, size_eq, Nat.toUSize_eq]
        . exact testPack_property.lt_usize_as
        . exact testPack_property.lt_usize_bs
      loop (i + 1) ⟨testPack', by grind⟩
    else testPack
  loop 0 testPack
