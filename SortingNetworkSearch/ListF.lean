import SortingNetworkSearch.Recursive
import SortingNetworkSearch.Trampoline

inductive ListF (α : Type u) (β : Type v)
  | nil : ListF α β
  | cons : α → β → ListF α β

def List.project : List α → ListF α (List α)
  | .nil => .nil
  | .cons a b => .cons a b

def ListF.map (f : β → χ) (l : ListF α β) : ListF α χ :=
  match l with
  | .nil => .nil
  | .cons a b => .cons a (f b)

instance instBaseList : Base (List α) where
  base := ListF α

instance instFunctorListF: Functor (ListF α) where
  map := ListF.map

instance instFunctorBaseList : Functor (Base.base (List α)) where
  map := ListF.map

instance instRecursiveList : Recursive (List α) where
  project := List.project

/--
A tail-recursive right-to-left fold on Lists. Won't cause stack overflows. This is more
or less just a slower version of `List.foldr` from the standard library. It's defined
as an example of how to implement a tail-recursive `cata`.

Example:
```
def sumFunc : ListF Nat Nat → Nat
  | .nil => 0
  | .cons a b => a + b
#eval [1, 2, 3].cataTR sumFunc = [1, 2, 3].foldr (· + ·) 0
```
-/
partial def List.cataTR {α β : Type} [Nonempty β] (f : ListF α β → β) (n : List α) : β :=
  cataTRAux f n |>.run
where
  cataTRAux [Nonempty β] (f : ListF α β → β) (n : List α) : Trampoline β :=
    .flatMap
      (.suspend fun _ =>
        match n.project with
          | .nil => .ret .nil
          | .cons a b =>
            .flatMap (cataTRAux f b) (fun b => .ret (.cons a b)))
      (fun x => .ret (f x))

def List.sequenceTrampoline (xs : List (Trampoline α)) : Trampoline (List α) := Id.run do
  let mut result := .ret []
  for x in xs do
    result := .flatMap result fun result =>
      match x with
      | .ret a => .ret (result.cons a)
      | .suspend f =>
        .flatMap (f ()) fun a =>
          .ret (result.cons a)
      | .flatMap x f =>
          .flatMap x fun t =>
            .flatMap (f t) fun a =>
              .ret (result.cons a)
  result
