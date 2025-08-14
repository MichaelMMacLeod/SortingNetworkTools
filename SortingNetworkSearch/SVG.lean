import Std.Data.HashMap
import SortingNetworkSearch.Recursive
import SortingNetworkSearch.Cata

namespace SVG

abbrev Tags := Std.HashMap String String

def Tags.toString (tags : Std.HashMap String String) : String := Id.run do
  let mut result := ""
  for (tag, value) in tags do
    result := result ++ s!"{tag}=\"{value}\" "
  result := result.dropRight 1
  result

structure Node where
  name : String
  tags : Tags
  children : Array Node
  deriving Inhabited, Repr

structure NodeF (α : Type u) where
  name : String
  tags : Tags
  children : Array α
  deriving Inhabited, Repr

def Node.project (n : Node) : NodeF Node :=
  { n with }

def NodeF.map (f : α → β) (n : NodeF α) : NodeF β :=
  { n with children := f <$> n.children}

instance instBaseNode : Base Node where
  base := NodeF

instance instFunctorNodeF : Functor NodeF where
  map := NodeF.map

instance instFunctorBaseNode : Functor (Base.base Node) where
  map := NodeF.map

instance instNodeRecursive : Recursive Node where
  project := Node.project

def Array.sequenceTrampoline (xs : Array (Trampoline α)) : Trampoline (Array α) := Id.run do
  let mut result := .ret <| .emptyWithCapacity xs.size
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

partial def Node.cataTR {α : Type u} [Nonempty α] (f : NodeF α → α) (n : Node) : α :=
  cataTRAux f n |>.run
where
  cataTRAux [Nonempty α] (f : NodeF α → α) (n : Node) : Trampoline α :=
    .flatMap
      (.suspend fun _ =>
        let n := n.project
        let x1 : Array Node := n.children
        let g1 : Node → Trampoline α := cataTRAux f
        let x2 : Array (Trampoline α) := x1.map g1
        let x3 : Trampoline (Array α) := Array.sequenceTrampoline x2
        let x4 : Trampoline (NodeF α) := .flatMap x3 fun children =>
          .ret { n with children := children }
        x4
      )
      (fun (x : NodeF α) => .ret (f x))

def mkDeepNode (depth : Nat) : Node := Id.run do
  let mut result := { name := (0).repr, tags := ∅, children := #[] }
  let mut depth := depth
  while 0 < depth do
    result := { name := depth.repr, tags := ∅, children := #[result] }
    depth := depth - 1
  result

def toStringFunc : NodeF (Nat → Trampoline String) → (Nat → Trampoline String) :=
  fun { name, tags, children } indentLevel =>
    let children := children.map (· (indentLevel + 2))
    let children := Array.sequenceTrampoline children
    .flatMap children fun children =>
      let childStrs := children.foldl (· ++ · ++ "\n") ""
      let space := if tags.size > 0 then " " else ""
      let indent1 := "".pushn ' ' indentLevel
      let indent2 := if children.size = 0 then "" else indent1
      let nl := if children.size = 0 then "" else "\n"
      .ret s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>"

def toStringFunc' : NodeF (Trampoline (Nat → String)) → (Trampoline (Nat → String)) :=
  fun { name, tags, children } =>
    let children := Array.sequenceTrampoline children
    .flatMap children fun children =>
      .ret fun indentLevel =>
        -- let children := #[children[0]?.getD (fun _ => "") <| indentLevel + 2]
        let children := children.map (· (indentLevel + 2))
        let childStrs := children.foldl (· ++ · ++ "\n") ""
        let space := if tags.size > 0 then " " else ""
        let indent1 := "".pushn ' ' indentLevel
        let indent2 := if children.size = 0 then "" else indent1
        let nl := if children.size = 0 then "" else "\n"
        s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>"

-- #eval println! cata toStringFunc (mkDeepNode 5) 0 |>.run |>.get! 0
-- #eval println! (mkDeepNode 100).cataTR toStringFunc 0 |>.get! 0

end SVG
