import SortingNetworkSearch.Recursive
import SortingNetworkSearch.ListF

/--
A generic bottom-up fold. See `X.cataTR` (for a given `X` that defines it) for
the tail recursive version (e.g., `List.cataTR`). *This one will cause stack
overflows if `n` is large enough*.

This implementation is taken from Edward A. Kmett's Haskell package
'recursion-schemes' (see https://hackage.haskell.org/package/recursion-schemes.)

NOTE: I haven't yet figured out how to make the `cataTR` variants generic. I
ran into universe-bumping problems with implemeting `Traversable` for `Trampoline`
that I need to resolve. This is why there is no non-type-specific `cataTR`.

Example:
```
import SortingNetworkSearch.ListF
def sumFunc : ListF Nat Nat → Nat
  | .nil => 0
  | .cons a b => a + b
#eval cata sumFunc [1, 2, 3] = [1, 2, 3].foldr (· + ·) 0
```
-/
partial def cata [Inhabited α] [Base t] [Functor (Base.base t)] [Recursive t]
    (f : Base.base t α → α) (n : t) : α :=
  f <| (cata f) <$> (Recursive.project n)

-- abbrev Cata t [Base t] (α : Type u) := Base.base t α → α
