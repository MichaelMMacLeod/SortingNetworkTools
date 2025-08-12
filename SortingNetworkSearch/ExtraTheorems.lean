attribute [grind] USize.lt_ofNat_iff Array.usize Array.all_eq_true_iff_forall_mem

@[grind →]
theorem array_index_lt_size_ofNat_of_lt_usize
    (vals : Array UInt64)
    (a : USize)
    (h : a < vals.usize)
    : a < USize.ofNat vals.size := by
  exact h

@[grind →]
theorem toNat_lt_size_of_lt_usize_of_lt_size_USize
    {i : USize}
    {xs : Array USize}
    (h₁ : xs.size < USize.size)
    (h₂ : i < xs.usize)
    : i.toNat < xs.size := by
  refine (USize.lt_ofNat_iff ?_).mp h₂
  exact h₁

@[grind]
theorem Array.mem_of_uget {as : Array α} {i : USize} {h} (h : as.uget i h = a) : a ∈ as :=
  Array.mem_of_getElem h
