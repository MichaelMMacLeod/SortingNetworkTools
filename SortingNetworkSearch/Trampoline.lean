/--
A Trampoline is a type which stores would-be stack frames on the heap, enabling us
to write non-tail-recursive functions that use constant stack space, thereby
eliminating the chance of stack overflows when dealing with large inputs.

This implementation is taken from Ziyang Liu's blog post "How Trampoline Works in
Scala" (see https://free.cofree.io/2017/08/24/trampoline/.)
-/
@[specialize]
inductive Trampoline : Type u → Type (u+1) where
  | ret : α → Trampoline α
  | suspend : (Unit → Trampoline α) → Trampoline α
  | flatMap : Trampoline α → (α → Trampoline β) → Trampoline β
  deriving Nonempty

@[specialize]
def Trampoline.map (f : α → β) (t : Trampoline α) : Trampoline β :=
  match t with
  | .ret a => .ret <| f a
  | .suspend g => .suspend <| fun _ => map f (g ())
  | .flatMap t g => .flatMap t <| fun a => map f (g a)

instance : Functor Trampoline where
  map := .map

@[specialize]
partial def Trampoline.run [Nonempty α] : Trampoline α → α
  | .ret a => a
  | .suspend f => (f ()).run
  | .flatMap x f =>
    match x with
    | .ret a => (f a).run
    | .suspend r => (Trampoline.flatMap (r ()) f).run
    | .flatMap y g => (y.flatMap (fun q => .flatMap (g q) f)).run
