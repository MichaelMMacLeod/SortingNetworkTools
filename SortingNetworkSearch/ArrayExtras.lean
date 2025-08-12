-- Useful for more easily ensuring the refcount of an array stays at 1
-- when attempting to mutate one of its elements.
def Array.swapRemove! [Inhabited α] (arr : Array α) (i : Nat) (a : α) : Array α × α :=
  let result := arr[i]!
  let arr := arr.set! i a
  (arr, result)
