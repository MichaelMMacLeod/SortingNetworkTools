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

structure NodeF α where
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



def mkDeepNode (depth : Nat) : Node := Id.run do
  let mut result := { name := (0).repr, tags := ∅, children := #[] }
  let mut depth := depth
  while 0 < depth do
    result := { name := depth.repr, tags := ∅, children := #[result] }
    depth := depth - 1
  result

def toStringFunc : NodeF (Nat → String) → (Nat → String) :=
  fun { name, tags, children } indentLevel => Id.run do
    let mut childStrs := ""
    for c in children do
      childStrs := childStrs ++ (c <| indentLevel + 2) ++ "\n"
    let space := if tags.size > 0 then " " else ""
    let indent1 := "".pushn ' ' indentLevel
    let indent2 := if children.size = 0 then "" else indent1
    let nl := if children.size = 0 then "" else "\n"
    s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>"

#eval println! cata toStringFunc (mkDeepNode 5) 0

end SVG
