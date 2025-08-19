import SortingNetworkTools.Trampoline

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

def Array.sequenceTrampoline (xs : Array (Trampoline α)) : Trampoline (Array α) := Id.run do
  let mut result := .ret (.emptyWithCapacity xs.size)
  for x in xs do
    result := .flatMap result fun result =>
      match x with
      | .ret a => .ret (result.push a)
      | .suspend f =>
        .flatMap (f ()) fun a =>
          .ret (result.push a)
      | .flatMap x f =>
        .flatMap x fun t =>
          .flatMap (f t) fun a =>
            .ret (result.push a)
  result
