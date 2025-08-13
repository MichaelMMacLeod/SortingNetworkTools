-- Useful for more easily ensuring the refcount of an array stays at 1
-- when attempting to mutate one of its elements.
@[specialize, inline]
def Array.swapRemove! [Inhabited α] (arr : Array α) (i : Nat) (a : α) : Array α × α :=
  let result := arr[i]!
  let arr := arr.set! i a
  (arr, result)

@[specialize]
def Array.swapRemove [Inhabited α] (arr : Array α) (i : Nat) (a : α) (h : i < arr.size) : Array α × α :=
  let result := arr[i]
  let arr := arr.set i a
  (arr, result)

@[specialize]
def Array.uSwapRemove [Inhabited α] (arr : Array α) (i : USize) (a : α) (h : i.toNat < arr.size) : Array α × α :=
  let result := arr.uget i h
  let arr := arr.uset i a h
  (arr, result)
