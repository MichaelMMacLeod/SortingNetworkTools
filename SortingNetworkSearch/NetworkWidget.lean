import Lean
import SortingNetworkSearch.Network
import SortingNetworkSearch.Layer
import Std.Data.HashMap

open Lean Widget

inductive ListF (α : Type u) (β : Type v)
  | nil : ListF α β
  | cons : α → β → ListF α β

@[specialize, inline]
def List.project : List α → ListF α (List α)
  | .nil => .nil
  | .cons a b => .cons a b

def ListF.embed : ListF α (List α) → List α
  | .nil => .nil
  | .cons a b => .cons a b

def ListF.fmap (f : β → χ) (l : ListF α β) : ListF α χ :=
  match l with
  | .nil => .nil
  | .cons a b => .cons a (f b)

class Base (α : Type u) where
  base : Type u → Type u

class Recursive t [Base t] [f : Functor (Base.base t)] where
  project : t → Base.base t t

partial def cata [Inhabited α] [Base t] [Functor (Base.base t)] [Recursive t]
    (f : Base.base t α → α) (n : t) : α :=
  f (Functor.map (cata f) (Recursive.project n))

inductive TailRec : Type u → Type (u+1) where
  | ret : α → TailRec α
  | suspend : (Unit → TailRec α) → TailRec α
  | flatMap : TailRec α → (α → TailRec β) → TailRec β
  deriving Nonempty

def TailRec.map (f : α → β) (t : TailRec α) : TailRec β :=
  match t with
  | .ret a => .ret <| f a
  | .suspend g => .suspend <| fun _ => map f (g ())
  | .flatMap t g => .flatMap t <| fun a => map f (g a)

instance : Functor TailRec where
  map := .map

partial def TailRec.run [Nonempty α] : TailRec α → α
  | .ret a => a
  | .suspend f => (f ()).run
  | .flatMap x f =>
    match x with
    | .ret a => (f a).run
    | .suspend r => (TailRec.flatMap (r ()) f).run
    | .flatMap y g => (y.flatMap (fun q => .flatMap (g q) f)).run

instance instBaseList : Base (List α) where
  base := ListF α

instance instFunctorListF: Functor (ListF α) where
  map := ListF.fmap

instance instFunctorBaseList : Functor (Base.base (List α)) where
  map := ListF.fmap

instance instRecursiveList : Recursive (List α) where
  project := List.project

partial def List.cataTR [Inhabited β]
    (f : ListF α β → β) (n : List α) : β :=
  let x1 : ListF α (List α) := n.project
  let g1 : List α → β := cataTR f
  let x2 : ListF α β := g1 <$> x1
  let x3 : β := f x2
  x3

partial def List.cataTR' {α β : Type} [Nonempty β]
    (f : ListF α β → β) (n : List α) : β := cataTR'Aux f n |>.run
where
  cataTR'Aux [Nonempty β] (f : ListF α β → β) (n : List α) : TailRec β :=
    let x1 : ListF α (List α) := n.project
    .flatMap
      (.suspend fun _ =>
        let g1 : List α → TailRec β := cataTR'Aux f
        let x1 : ListF α (List α) := x1
        let x9 : TailRec (ListF α β) :=
          match x1 with
          | .nil => .ret .nil
          | .cons a b => .flatMap (g1 b) (fun b => .ret (.cons a b))
        x9)
      (fun (x2 : ListF α β) => .ret (f x2))

        -- let x2 : ListF α (TailRec β) := g1 <$> x1


#eval (List.range 1).cataTR' (match · with | .nil => 0 | .cons a b => a + b)

  -- let rec loop (x : (ListF α (ListF α β ⊕ β) ⊕ β)) : β :=
  --   match x with
  --   | Sum.inr a => a
  --   | Sum.inl b => sorry
  --     -- match Functor.map (fun y => Sum.inl (Functor.map (fun z => Sum.inr z) y)) b with
  --     -- | mapped => loop (Functor.map (fun y =>
  --     --     match y with
  --     --     | Sum.inl x => loop (Sum.inl x)
  --     --     | Sum.inr x => Sum.inr (f x)) mapped)
  -- let x1 : Base.base t (Rec t α α) := sorry
  -- loop (Sum.inl x1)


-- instance [Base t] : Functor (Sum (Base.base t α)) where
--   map := fun a b => Sum.map id a b

-- abbrev Rec a b c [Base a] := Base.base a b ⊕ c

-- partial def cataTR [Inhabited α] [Base t] [Functor (Base.base t)] [Recursive t]
--     (f : Base.base t α → α) (n : t) : α :=
--   let rec loop (x : (Rec t (Rec t α α) α)) : α :=
--     match x with
--     | Sum.inr a => a
--     | Sum.inl b => sorry
--       -- match Functor.map (fun y => Sum.inl (Functor.map (fun z => Sum.inr z) y)) b with
--       -- | mapped => loop (Functor.map (fun y =>
--       --     match y with
--       --     | Sum.inl x => loop (Sum.inl x)
--       --     | Sum.inr x => Sum.inr (f x)) mapped)
--   let x1 : Base.base t (Rec t α α) := sorry
--   loop (Sum.inl x1)
--   -- loop (Sum.inl (Functor.map (fun x => Sum.inl x) (Recursive.project n)))

instance instBaseList : Base (List α) where
  base := ListF α

instance instFunctorBaseList : Functor (Base.base (List α)) where
  map := ListF.fmap

instance instRecursiveList : Recursive (List α) where
  project := List.project

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

def Node.project (n : Node) : NodeF Node := { n with }

def NodeF.map (f : α → β) (n : NodeF α) : NodeF β :=
  { n with children := f <$> n.children }

def mkDeepNode (depth : Nat) : Node := Id.run do
  let mut result := { name := (0).repr, tags := ∅, children := #[] }
  let mut depth := depth
  while 0 < depth do
    result := { name := depth.repr, tags := ∅, children := #[result] }
    depth := depth - 1
  result

instance instBaseNode : Base Node where
  base := NodeF

instance instFunctorBaseNode : Functor (Base.base Node) where
  map := NodeF.map

instance instRecursiveNode : Recursive Node where
  project := Node.project

def sumFunc : ListF Nat Nat → Nat
  | .nil => 0
  | .cons a b => a + b

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

#eval cata sumFunc (List.range 1000)
#eval println! cata toStringFunc (mkDeepNode 10) 0

-- def List.cata (l : List α) (f : ListF α β → β) : β :=
--   let rec loop1
--       (stack : Array (ListF α (β ⊕ Unit)))
--       (l : List α)
--       : β :=
--     match List.project l with
--     | .nil =>
--       let rec loop2
--           (stack : Array (ListF α (β ⊕ Unit)))
--           (b : β)
--           : β :=
--         if 0 < stack.size then
--           let x :=
--     | .cons a b =>
--       let stack := stack.push <| .cons a <| Sum.inr ()
--       loop1 stack b
--   sorry

inductive CataNode α β where
  | expand : Nat → α → CataNode α β
  | collapse : Nat → β → CataNode α β

abbrev IDK1 := (s t u : Type) → (f : Type → Type) → s → f t → (s → t → s × u) → s × f u
abbrev IDK2 := {s : Type → Type} → (t u : Type) → [Monad s] → (f : Type → Type) → s (f t) → (s t → s u) → s (f u)

-- #check Array
-- def Array.clear (as : Array α) : Array α :=
--   if 0 < as.size then as.pop.clear else as

@[specialize]
partial def cata
    [Inhabited β]
    {Frame : Type → Type}
    {α}
    (a : α)
    (project : α → Frame α)
    (f : Frame β → β)
    (fmapWithState : {State : Type} → {t u : Type} → State → Frame t → (State → t → State × u) → State × Frame u)
    : β :=
  let rec @[specialize] loop
      (vals : Array (Option β))
      (stack : Array (CataNode α (Frame Nat)))
      : β :=
    if h : 0 < stack.size then
      let item := stack[stack.size - 1]
      let stack := stack.pop
      match item with
      | .expand valIdx seed =>
        let node := project seed
        let seeds := #[]
        let ((vals, seeds), node) := fmapWithState (vals, seeds) node fun (vals, seeds) seed =>
          let vals := vals.push none
          let idx := vals.size - 1
          let seeds := seeds.push <| .expand idx seed
          ((vals, seeds), idx)
        let stack := stack.push <| .collapse valIdx node
        let stack := stack.append seeds
        loop vals stack
      | .collapse valIdx node =>
        let (vals, node) := fmapWithState vals node fun vals k =>
          let (vals, node) := vals.swapRemove! k none
          (vals, node.get!)
        let vals := vals.set! valIdx (f node)
        loop vals stack
    else
      (vals[0]!).get!
  loop #[none] #[.expand 0 a]



-- inductive TailRec where
--   | ret : Nat → TailRec
--   | suspend : (Unit → TailRec) → TailRec
--   | flatMap : TailRec → (Nat → TailRec) → TailRec

-- def fac' (n : Nat) : Nat :=
--   if n = 0 then
--     1
--   else
--     n * fac' (n - 1)

-- def fac (n : Nat) : TailRec :=
--   if n = 0 then
--     .ret 1
--   else
--     .flatMap
--       (.suspend fun _ => fac (n - 1))
--       fun x => .ret (n * x)

-- partial def TailRec.run : TailRec → Nat
--   | .ret a => a
--   | .suspend f => (f ()).run
--   | .flatMap x f =>
--     match x with
--     | .ret a => (f a).run
--     | .suspend r => (TailRec.flatMap (r ()) f).run
--     | .flatMap y g => (y.flatMap (fun q => .flatMap (g q) f)).run


abbrev Tags := Std.HashMap String String

structure Node where
  name : String
  tags : Tags
  children : Array Node
  deriving Inhabited, Repr

def mkDeepNode (depth : Nat) : Node := Id.run do
  let mut result := { name := (0).repr, tags := ∅, children := #[] }
  let mut depth := depth
  while 0 < depth do
    result := { name := depth.repr, tags := ∅, children := #[result] }
    depth := depth - 1
  result

structure NodeF α where
  name : String
  tags : Tags
  children : Array α
  deriving Inhabited, Repr

def NodeF.fmap  (f : α → β) (n : NodeF α) : NodeF β :=
  { n with children := f <$> n.children }

def Node.project (n : Node) : NodeF Node := { n with }
def NodeF.embed (n : NodeF Node) : Node := { n with }

inductive TailRec : Type u → Type (u+1) where
  | ret : α → TailRec α
  | suspend : (Unit → TailRec α) → TailRec α
  | flatMap : TailRec α → (α → TailRec β) → TailRec β

partial def TailRec.run [Nonempty α] : TailRec α → α
  | .ret a => a
  | .suspend f => (f ()).run
  | .flatMap x f =>
    match x with
    | .ret a => (f a).run
    | .suspend r => (TailRec.flatMap (r ()) f).run
    | .flatMap y g => (y.flatMap (fun q => .flatMap (g q) f)).run


partial def Node.cata (f : NodeF α → α) (n : Node) : TailRec α :=
  -- f (NodeF.fmap (Node.cata f) n.project)
  .flatMap
    (.suspend fun _ => NodeF.fmap (Node.cata f) n.project)
    fun x => .ret (f x)

partial def Node.cata (f : NodeF α → α) (n : Node) : TailRec α :=
  .flatMap
    (.suspend fun _ =>
      .flatMap
        (.suspend fun _ => .ret n.project)
        fun x1 =>
          .flatMap
            (.suspend fun _ => .ret (Node.cata f))
            fun x2 => NodeF.fmap x2 x1
    )
    fun x => .ret (f x)

partial def Node.cata (f : NodeF α → α) (n : Node) : TailRec α :=
  -- f (NodeF.fmap (Node.cata f) n.project)
  .flatMap
    (.suspend fun _ =>
      .flatMap
        (.suspend fun _ => .ret n.project)
        fun x => NodeF.fmap (Node.cata f) x
    )
    fun x => .ret (f x)

partial def Node.cata (f : NodeF α → α) (n : Node) : TailRec α :=
  -- f (NodeF.fmap (Node.cata f) n.project)
  .flatMap
    (.suspend fun _ => NodeF.fmap (Node.cata f) n.project)
    fun x => .ret (f x)

  -- let f : NodeF (TailRec α) → TailRec α :=
  --   fun n =>
  --     let cs : Array (TailRec α) :=  <$> n.children
  --     sorry
  -- sorry
  -- let x1 := Node.cata f
  -- let x2 := n.project
  -- .flatMap
  --   (fun _ => NodeF.fmap x1 x2)
  -- let x3 := x2.fmap x1
  -- let x4 := f x3
  -- x4

-- class inductive Trampoline (α : Type) where
--   | done : α → Trampoline α
--   | delay : (Unit → Trampoline α) → Trampoline α
--   | flatMap :


-- structure FlatMap (α β : Type) where
--   t : TailRec α
--   f : α → (TailRec α ⊕ FlatMap β α)

-- inductive TailRec where
--   | ret : String → TailRec
--   | suspend : (Unit → TailRec) → TailRec
--   | flatMap : TailRec → (String → TailRec) → TailRec
--   deriving Inhabited

-- partial def TailRec.run : TailRec → String
--   | .ret a => a
--   | .suspend f => (f ()).run
--   | .flatMap x f =>
--     match x with
--     | .ret a => (f a).run
--     | .suspend r => (TailRec.flatMap (r ()) f).run
--     | .flatMap y g => (y.flatMap (fun q => .flatMap (g q) f)).run

partial def Node.cata'' (f : NodeF String → String) (n : Node) : TailRec :=
  let x1 := Node.cata'' f
  let x2 := n.project
  let x3 :=
    TailRec.flatMap
      (TailRec.suspend fun _ => TailRec.ret <| f <| x2.fmap x1)
      fun x3 => f x3
  x3


partial def Node.cata' (f : NodeF String → String) (n : Node) : String :=
  let x1 := Node.cata' f
  let x2 := n.project
  let x3 := x2.fmap x1
  let x4 := f x3
  x4

partial def Node.cata [Inhabited α] (f : NodeF α → α) (n : Node) : α :=
  f (NodeF.fmap (Node.cata f) n.project)

partial def Node.cataold [Inhabited α] (f : NodeF α → α) (n : Node) : α :=
  f (NodeF.fmap (Node.cataold f) n.project)

def Tags.toString (tags : Std.HashMap String String) : String := Id.run do
  let mut result := ""
  for (tag, value) in tags do
    result := result ++ s!"{tag}=\"{value}\" "
  result := result.dropRight 1
  result

def Node.toString (n : Node) : String :=
  let f : Nat → String := n.cata
    (fun { name, tags, children } indentLevel => Id.run do
    let mut childStrs := ""
    for c in children do
      childStrs := childStrs ++ (c <| indentLevel + 2) ++ "\n"
    let space := if tags.size > 0 then " " else ""
    let indent1 := "".pushn ' ' indentLevel
    let indent2 := if children.size = 0 then "" else indent1
    let nl := if children.size = 0 then "" else "\n"
    s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>")
  f 0

-- def dn1 := mkDeepNode 10000 |>.toString |>.get! 0

-- #eval dn1

#eval println! Node.toString {
  name := "svg",
  tags := .ofList [("width", "536"), ("height", "840"), ("viewBox", "0 0 1610 840")],
  children := #[
    {
      name := "rect",
      tags := .ofList [("width", "1610"), ("height", "840"), ("fill", "#fff")],
      children := #[]
    },
    {
      name := "rect",
      tags := .ofList [("width", "1610"), ("height", "840"), ("fill", "#ccc")],
      children := #[]
    }
  ]
}


-- def Node.toString (n : Node) : String :=
--   let f : Nat → String := cata n
--     (fun n => show NodeF Node from { n with children := n.children })
--     (fun { name, tags, children } indentLevel => Id.run do
--     let mut childStrs := ""
--     for c in children do
--       childStrs := childStrs ++ (c <| indentLevel + 2) ++ "\n"
--     let space := if tags.size > 0 then " " else ""
--     let indent1 := "".pushn ' ' indentLevel
--     let indent2 := if children.size = 0 then "" else indent1
--     let nl := if children.size = 0 then "" else "\n"
--     s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>")
--     (fun state n f =>
--       let (state, children) := f state n.children
--       (state, {n with children}))
--   f 0

-- #eval (fac 10000).run

-- def TailRec.flatMap (sub : TailRec α) (k : α → TailRec β) : TailRec β :=


-- structure FlatMap (α β : Type) where
--   sub : TailRec α
--   k : α → TailRec β

-- #check (· <$> ·)

-- inductive

-- inductive TailRec where
--   | map : {β : Type} → (α → β) → TailRec
--   | flatMap : {β : Type} → (α → TailRec) → TailRec

-- class FlatMap (α β : Type) where


-- inductive TailRec (α β : Type) where
--   | ret : α → TailRec α β
--   | suspend : (Unit → TailRec α β) → TailRec α β
--   | flatMap : TailRec α β → (β → TailRec α β) → TailRec α β


-- inductive TailRec (α : Type) where
--   | tPure : α → TailRec α
--   | tSuspend : (Unit → TailRec α) → TailRec α
--   | tBind : {β : Type} → TailRec α → (α → TailRec β) → TailRec β

#check pure
-- inductive Apply (α β : Type) where
--   | loop : (α → Apply α β) → α → Apply α β
--   | value : β → Apply α β

-- def trampoline (x : Apply α β) : β :=
--   match x with
--   | .loop f a => trampoline (f a)
--   | .value b => b

-- def fibtramp (n : Nat) (c : Nat → β) : Apply α β :=
--   if n ≤ 1 then
--     Apply.value (c n)
--   else
--     Apply.loop (fibtramp (n - 1)) fun x =>
--       Apply.loop (fibtramp (n - 2)) fun y =>
--         Apply.value (c (x + y))

-- structure Apply (α β : Type) where
--   f : α → Apply α β ⊕ β
--   a : α

-- def fibcps (n : Nat) (c : Nat → α) : α :=
--   if n ≤ 1 then
--     c n
--   else
--     fibcps (n - 1) fun x =>
--       fibcps (n - 2) fun y =>
--         c (x + 1)

-- def trampoline (x : Apply α β) : β :=
--   match x.f x.a with
--   | .inr b => b
--   | .inl x => trampoline x

-- def fibt (n : Nat) (c : Nat → α) : α :=


-- partial def cata'
--     ()

/-
cata f [1,2,3]
f (fmap (cata f) 1 :: [2,3])
f (1 :: (cata f [2,3]))
f (1 :: (fmap (cata f) 2 :: [3]))
f (1 :: (2 :: (cata f [3])))
f (1 ::)

cata f [1,2,3]
{ f := f
  a := fun () =>
    {
    }
}
f (fmap (cata f) 1 :: [2,3])
f (1 :: (cata f [2,3]))
f (1 :: (fmap (cata f) 2 :: [3]))
f (1 :: (2 :: (cata f [3])))
f (1 ::)
-/



-- def myListFmap (state : State) (lst : ListF α β) (f : State → β → State × χ) : State × ListF α χ :=
--   match lst with
--   | .nil => (state, .nil)
--   | .cons a b =>
--     let (state, c) := f state b
--     (state, .cons a c)
-- -- set_option trace.profiler.output "/tmp/0Aperf.json"
-- set_option trace.profiler.threshold 0
-- set_option trace.profiler.output.pp true
-- set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler true in
-- #eval! v
-- #eval lst.foldr (· + ·) 0

-- def expandAndCollapse
--     [Inhabited α]
--     {Frame : Type → Type}
--     {Seed}
--     (seed : Seed)
--     (project : Seed → Frame Seed)
--     (embed : Frame α → α)
--     (fmap : {State : Type} → {t u : Type} → State × Frame t → (State → t → State × u) → State × Frame u)
--     : α :=
--   let rec loop
--       (vals : Array (Option α))
--       (stack : Array (ExpandAndCollapseState Seed (Frame Nat)))
--       : α :=
--     if h : 0 < stack.size then
--       let item := stack[stack.size - 1]
--       let stack := stack.pop
--       match item with
--       | .expand valIdx seed =>
--         let node := project seed
--         let seeds := #[]
--         let ((vals, seeds), node) := fmap ((vals, seeds), node) fun (vals, seeds) seed =>
--           let vals := vals.push none
--           let idx := vals.size - 1
--           let seeds := seeds.push <| .expand idx seed
--           ((vals, seeds), idx)
--         let stack := stack.push <| .collapse valIdx node
--         let stack := stack.append seeds
--         loop vals stack
--       | .collapse valIdx node =>
--         let (vals, node) := fmap (vals, node) fun vals k =>
--           let (vals, node) := vals.swapRemove! k none
--           (vals, node.get!)
--         let vals := vals.set! valIdx (embed node)
--         loop vals stack
--     else
--       vals[0]!.get!
--   loop #[none] #[.expand 0 seed]

-- #eval! expandAndCollapse (α := Nat) [1,2,3] List.project
--   (fun lst =>
--     match lst with
--     | .nil => 0
--     | .cons a b => a + b)
--   (fun (state, xs) f =>
--   match xs with
--   | .nil => (state, .nil)
--   | .cons a b =>
--     let (state, c) := f state b
--     (state, .cons a c))

/-
-- cata f = c where c = f . fmap c . project
-- cata f x = f (fmap (cata f) (project x))

cata f [1,2,3]
f (fmap (cata f) 1 :: [2,3])
f (1 :: (cata f [2,3]))
f (1 :: (fmap (cata f) 2 :: [3]))
f (1 :: (2 :: (cata f [3])))
f (1 ::)

stack = [[1,2,3]]

stack = [1, [2, 3]]
-/















namespace SVG

abbrev Tags := Std.HashMap String String

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

def Tags.toString (tags : Std.HashMap String String) : String := Id.run do
  let mut result := ""
  for (tag, value) in tags do
    result := result ++ s!"{tag}=\"{value}\" "
  result := result.dropRight 1
  result

def Node.toString (n : Node) : String :=
  let f : Nat → String := cata n
    (fun n => show NodeF Node from { n with children := n.children })
    (fun { name, tags, children } indentLevel => Id.run do
    let mut childStrs := ""
    for c in children do
      childStrs := childStrs ++ (c <| indentLevel + 2) ++ "\n"
    let space := if tags.size > 0 then " " else ""
    let indent1 := "".pushn ' ' indentLevel
    let indent2 := if children.size = 0 then "" else indent1
    let nl := if children.size = 0 then "" else "\n"
    s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>")
    (fun state n f =>
      let (state, children) := f state n.children
      (state, {n with children}))
  f 0
open SVG
#eval println! Node.toString {
  name := "svg",
  tags := .ofList [("width", "536"), ("height", "840"), ("viewBox", "0 0 1610 840")],
  children := #[
    {
      name := "rect",
      tags := .ofList [("width", "1610"), ("height", "840"), ("fill", "#fff")],
      children := #[]
    },
    {
      name := "rect",
      tags := .ofList [("width", "1610"), ("height", "840"), ("fill", "#ccc")],
      children := #[]
    }
  ]
}

end SVG

-- mutual
-- def Node.size : Node → Nat
--   | { children, .. } => 1 + Node.sizeAux children
-- def Node.sizeAux : List Node → Nat
--   | [] => 0
--   | c :: cs => c.size + (Node.sizeAux cs)
-- end


-- structure Tree (α : Type) where
--   label : α
--   children : List (Tree α)
--   deriving ToExpr

-- structure TreeF (α : Type) (β : Type) where
--   label : α
--   children : List β
--   deriving ToExpr

-- def Tree.project (t : Tree α) : TreeF α (Tree α) := { t with }
-- def TreeF.embed (t : TreeF α (Tree α)) : Tree α := { t with }

-- def t1 : Tree Nat := Tree.mk 0 [Tree.mk 1 [], Tree.mk 2 [], Tree.mk 3 []]
-- #eval t1.project.embed

-- def Tree.cata (t : Tree α) (f : TreeF α β → β) : β :=
--   sorry

-- @[grind]
-- structure NodeF α where
--   name : String
--   tags : Tags
--   children : Array α
--   deriving Inhabited, Repr

-- @[grind]
-- def NodeF.size {α} (_n : NodeF α) := 0

-- abbrev Stack α := Array ((Nat × Node) ⊕ (Nat × NodeF α))
-- abbrev Acc α := Array (Array α)

-- def Node.cata (n : Node) (f : NodeF α → α) : α :=
--   let rec loop
--       (acc : Acc α)
--       (stack : { s : Stack α // 0 < s.size ∧ s.size = acc.size } )
--       (fuel : Nat)
--       (orig_node : Node := n)
--       : α :=
--     let n := stack.val[stack.val.size - 1]
--     let stack := stack.val.pop
--     match n with
--     | Sum.inl (i, n) =>
--       let stack' := stack.push <| Sum.inr (i, { n with children := #[] })
--       let nIndex := stack'.size - 1
--       let rec loop2
--           (acc : Acc α)
--           (stack : { s : Stack α // 0 < s.size ∧ s.size = acc.size } )
--           (children : Array Node)
--           : { s : Stack α × Acc α // 0 < s.fst.size ∧ s.fst.size = s.snd.size } :=
--         if h : 0 < children.size then
--           let acc := acc.push #[]
--           let stack := stack.val.push <| Sum.inl (nIndex, children[children.size - 1])
--           let children := children.pop
--           loop2 acc ⟨stack, by grind⟩ children
--         else ⟨(stack, acc), by grind⟩
--       let ⟨(stack'', acc'), p⟩ := loop2 acc ⟨stack', by grind⟩ n.children
--       loop acc' ⟨stack'', by grind⟩ (fuel + 1) orig_node
--     | Sum.inr (i, n) =>
--       let as := acc[acc.size - 1]
--       let acc := acc.pop
--       let a := f { n with children := as }
--       if h : i < acc.size then /- equivalently, 0 < acc.size -/
--         let acc := acc.set i (acc[i].push a)
--         loop acc ⟨stack, by grind⟩ (fuel + 1) orig_node
--       else a
--   termination_by orig_node.size - fuel
--   decreasing_by
--     simp_wf
--     grind
--   loop #[.emptyWithCapacity n.children.size] ⟨#[Sum.inl (0, n)], by grind⟩ 0

-- def Node.cata' [Inhabited α] (n : Node) (f : NodeF α → α) : α := Id.run do
--   let mut stack : Array ((Nat × Node) ⊕ (Nat × NodeF α)) := #[Sum.inl (0, n)]
--   let mut acc : Array (Array α) := #[.emptyWithCapacity n.children.size]
--   let mut isFirstIteration := true
--   while h : stack.size > 1 ∨ (stack.size = 1 ∧ isFirstIteration) do
--     isFirstIteration := false
--     let n := stack[stack.size - 1]
--     stack := stack.pop
--     match n with
--     | Sum.inl (i, n) =>
--       stack := stack.push (Sum.inr (i, { n with children := #[] }))
--       let mut children := n.children
--       acc := acc.push (.emptyWithCapacity children.size)
--       let nIndex := stack.size - 1
--       while h : children.size > 0 do
--         acc := acc.push #[]
--         stack := stack.push (Sum.inl (nIndex, children[children.size - 1]))
--         children := children.pop
--     | Sum.inr (i, n) =>
--       let as := acc[acc.size - 1]!
--       acc := acc.pop
--       let a := f { n with children := as }
--       acc := acc.set! i (acc[i]!.push a)
--   match stack[0]? with
--   | none | some (Sum.inl _) => panic! ""
--   | some (Sum.inr (i, n)) => f { n with children := acc[0]?.get! }


--   -- let (stack, acc) :=
--   -- match stack[0]? with
--   -- | none | some (Sum.inl _) => panic! ""
--   -- | some (Sum.inr (i, n)) => f { n with children := acc[0]?.get! }


-- -- structure ViewBox where
-- --   minX : Float
-- --   minY : Float
-- --   width : Float
-- --   height : Float

-- -- inductive Node where
-- --   | SVG (width : Float) (height : Float) (viewBox : ViewBox)
-- --   | Rect (width : Float) (height : Float) (fill : String)

-- -- structure Document where
-- --   node : Node
-- --   children : Array Node

-- -- def Node.toString : Node → String
-- --   | SVG width height viewBox =>
-- --     let viewBox :=
-- --       let { minX, minY, width, height } := viewBox
-- --       s!"viewBox={minX} {minY} {width} {height}"
-- --     s!"svg width={width} height={height} {viewBox}"
-- --   | Rect width height fill => s!"rect width={width} height={height} fill={fill}"



-- instance instToStringNode : ToString Node where
--   toString n := n.toString

-- #eval Node.SVG 536 280 (ViewBox.mk 0 0 1610 840)

-- end SVG

-- def Layers.toSVG (size : Nat) (layers : Array SwapLayer) : String :=



-- -- def Layer.countVerticalLines (l : Layer) : Nat := sorry

-- -- def Network.countVerticalLines (n : Network size) := sorry

-- -- def Network.toSVGString (n : Network size) : String := sorry


-- -- @[widget_module]
-- -- def helloWidget : Widget.Module where
-- --   javascript := "
-- --     import * as React from 'react';
-- --     export default function(props) {
-- --       const name = props.name || 'world'
-- --       return React.createElement('p', {}, 'Hello ' + name + '!')
-- --     }"

-- -- structure HelloWidgetProps where
-- --   name? : Option String := none
-- --   deriving Server.RpcEncodable

-- -- #widget helloWidget

-- -- #widget helloWidget with { name? := "<your name here>" : HelloWidgetProps }

-- -- structure GetTypeParams where
-- --   /-- Name of a constant to get the type of. -/
-- --   name : Name
-- --   /-- Position of our widget instance in the Lean file. -/
-- --   pos : Lsp.Position
-- --   deriving FromJson, ToJson

-- -- open Server RequestM in

-- -- @[server_rpc_method]
-- -- def getType (params : GetTypeParams) : RequestM (RequestTask CodeWithInfos) :=
-- --   withWaitFindSnapAtPos params.pos fun snap => do
-- --     runTermElabM snap do
-- --       let name ← resolveGlobalConstNoOverloadCore params.name
-- --       let c ← try getConstInfo name
-- --         catch _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
-- --       Widget.ppExprTagged c.type

-- -- @[widget_module]
-- -- def checkWidget : Widget.Module where
-- --   javascript := "
-- -- import * as React from 'react';
-- -- const e = React.createElement;
-- -- import { useRpcSession, InteractiveCode, useAsync, mapRpcError } from '@leanprover/infoview';

-- -- export default function(props) {
-- --   const rs = useRpcSession()
-- --   const [name, setName] = React.useState('getType')

-- --   const st = useAsync(() =>
-- --     rs.call('getType', { name, pos: props.pos }), [name, rs, props.pos])

-- --   const type = st.state === 'resolved' ? st.value && e(InteractiveCode, {fmt: st.value})
-- --     : st.state === 'rejected' ? e('p', null, mapRpcError(st.error).message)
-- --     : e('p', null, 'Loading..')
-- --   const onChange = (event) => { setName(event.target.value) }
-- --   return e('div', null,
-- --     e('input', { value: name, onChange }), ' : ', type)
-- -- }
-- -- "

-- -- #widget checkWidget
