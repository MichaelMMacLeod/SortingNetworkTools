import SortingNetworkSearch.Recursive
import SortingNetworkSearch.Trampoline
import SortingNetworkSearch.ArrayExtras

inductive SubstringTree where
| node : Array SubstringTree → SubstringTree
| leaf : Substring → SubstringTree
deriving Repr, Inhabited

inductive SubstringTreeF α where
| node : Array α → SubstringTreeF α
| leaf : Substring → SubstringTreeF α
deriving Repr, Inhabited

def SubstringTree.project : SubstringTree → SubstringTreeF SubstringTree
| node xs => .node xs
| leaf x => .leaf x

def SubstringTreeF.map (f : α → β) : SubstringTreeF α → SubstringTreeF β
| node xs => .node (f <$> xs)
| leaf x => leaf x

instance instBaseSubstringTree : Base SubstringTree where
  base := SubstringTreeF

instance instFunctorSubstringTreeF : Functor SubstringTreeF where
  map := SubstringTreeF.map

instance instFunctorBaseSubstringTree : Functor (Base.base SubstringTree) where
  map := SubstringTreeF.map

instance instSubstringTreeRecursive : Recursive SubstringTree where
  project := SubstringTree.project

partial def SubstringTree.cataTR {α : Type u} [Nonempty α] (f : SubstringTreeF α → α) (st : SubstringTree) : α :=
  cataTRAux f st |>.run
where
  cataTRAux [Nonempty α] (f : SubstringTreeF α → α) (st : SubstringTree) : Trampoline α :=
    .flatMap
      (.suspend fun _ =>
        match st with
        | .leaf x => .ret (.leaf x)
        | .node xs =>
          let result : Array (Trampoline α) := xs.map (cataTRAux f)
          let result : Trampoline (Array α) := result.sequenceTrampoline
          .flatMap result fun (xs : Array α) =>
            .ret (.node xs))
      fun (st : SubstringTreeF α) => .ret (f st)

def String.appendSubstring (s : String) (sub : Substring) : String := Id.run do
  let mut s := s
  let mut sub := sub
  while !sub.isEmpty do
    s := s.push (sub.front)
    sub := sub.drop 1
  s

instance : HAppend String Substring String where
  hAppend := String.appendSubstring

abbrev toStringAuxResult := Trampoline (String → Trampoline String)

def SubstringTree.toString (st : SubstringTree) : String :=
  let result := ""
  st.cataTR toStringAux |>.run result |>.run
where
  toStringAux : SubstringTreeF toStringAuxResult → toStringAuxResult
  | .leaf x => .ret (fun s => .ret (s ++ x))
  | .node xs =>
    .flatMap xs.sequenceTrampoline fun xs =>
      .ret fun s =>
        let s := s.push '['
        Prod.fst <| xs.foldl (init := (.ret s, 0)) fun (s, i) x =>
          let s := Trampoline.flatMap s fun s =>
            Trampoline.flatMap (x s) fun x =>
              if i = xs.size - 1
                then .ret <| x ++ "]"
                else .ret <| x ++ ", "
          (s, i + 1)
