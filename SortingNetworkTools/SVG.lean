import Std.Data.HashMap
import SortingNetworkTools.Recursive
import SortingNetworkTools.Cata

namespace SVG

abbrev Attributes := Std.HashMap String String

def Attributes.toString (tags : Std.HashMap String String) : String := Id.run do
  let mut result := ""
  for (tag, value) in tags do
    result := result ++ s!"{tag}=\"{value}\" "
  result := result.dropRight 1
  result

structure Node where
  name : String
  attributes : Attributes
  children : List Node
  deriving Inhabited, Repr

structure NodeF (α : Type u) where
  name : String
  attributes : Attributes
  children : List α
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

/--
A tail-recursive bottom-up fold on Nodes. Won't cause stack overflows. See
`Node.toString` for an example of its use, and `List.cataTR` for a `List`-specific
version.
-/
partial def Node.cataTR {α : Type u} [Nonempty α] (f : NodeF α → α) (n : Node) : α :=
  cataTRAux f n |>.run
where
  cataTRAux [Nonempty α] (f : NodeF α → α) (n : Node) : Trampoline α :=
    .flatMap
      (.suspend fun _ =>
        let result : List (Trampoline α) := n.project.children.map (cataTRAux f)
        let result : Trampoline (List α) := result.sequenceTrampoline
        .flatMap result fun children =>
          .ret { n with children := children })
      fun (x : NodeF α) => .ret (f x)

/--
Creates a node with `depth` number of children, all nested inside each other
(for 'matryoshka', see https://en.wikipedia.org/wiki/Matryoshka_doll.)
-/
def Node.matryoshka (depth : Nat) : Node := Id.run do
  let mut result := { name := (0).repr, attributes := ∅, children := [] }
  let mut depth := depth
  while 0 < depth do
    result := { name := depth.repr, attributes := ∅, children := [result] }
    depth := depth - 1
  result

abbrev toStringAuxResult := Trampoline (Nat × String → Trampoline String)

/--
Converts a `Node` into a `String`.

Note: this function is stack-safe; it won't cause stack overflows, even for
deeply-nested nodes.
-/
def Node.toString (n : Node) : String :=
  let initialIndentLevel := 0
  let result := ""
  n.cataTR toStringAux |>.run (initialIndentLevel, result) |>.run
where
  /--
  This function does the actual folding. It consumes/produces the accumulating
  `String` result linearly, which means the result is produced through in-place
  mutation.
  -/
  toStringAux : NodeF toStringAuxResult → toStringAuxResult :=
    fun { name, attributes, children } =>
      let children := List.sequenceTrampoline children
      .flatMap children fun children =>
        .ret fun (indentLevel, result) =>
          let space := if attributes.size > 0 then " " else ""
          let indent1 := "".pushn ' ' indentLevel
          let indent2 := if children.isEmpty then "" else indent1
          let nl := if children.isEmpty then "" else "\n"
          let result := result ++ s!"{indent1}<{name}{space}{Attributes.toString attributes}>{nl}"
          let indentLevel := indentLevel + 2
          let result := children.foldl (init := Trampoline.ret result)
            fun result c =>
              .flatMap result fun result =>
                .flatMap (c (indentLevel, result)) fun result =>
                  .ret (result ++ nl)
          .flatMap result fun result =>
            .ret (result ++ s!"{indent2}</{name}>")

end SVG
