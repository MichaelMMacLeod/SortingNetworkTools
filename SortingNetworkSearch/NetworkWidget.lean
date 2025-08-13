import Lean
import SortingNetworkSearch.Network
import SortingNetworkSearch.Layer
import Std.Data.HashMap

open Lean Widget


inductive ListF (α : Type) (β : Type)
  | nil : ListF α β
  | cons : α → β → ListF α β

@[specialize, inline]
def List.project : List α → ListF α (List α)
  | .nil => .nil
  | .cons a b => .cons a b

def ListF.embed : ListF α (List α) → List α
  | .nil => .nil
  | .cons a b => .cons a b

def ListF.fmap (l : ListF α β) (f : β → χ) : ListF α χ :=
  match l with
  | .nil => .nil
  | .cons a b => .cons a (f b)

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

inductive cataState Seed α where
  | expand : Nat → Seed → cataState Seed α
  | collapse : Nat → α → cataState Seed α

#check Array.mapM

#check StateT.bind

    -- (mapM : {β χ : Type} → {m : Type → Type} → [Monad m] → Frame β → (β → m χ) → m (Frame χ))

def myListFmap (state : State) (lst : ListF α β) (f : State → β → State × χ) : State × ListF α χ :=
  match lst with
  | .nil => (state, .nil)
  | .cons a b =>
    let (state, c) := f state b
    (state, .cons a c)

abbrev IDK1 := (s t u : Type) → (f : Type → Type) → s → f t → (s → t → s × u) → s × f u
abbrev IDK2 := {s : Type → Type} → (t u : Type) → [Monad s] → (f : Type → Type) → s (f t) → (s t → s u) → s (f u)

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
      (stack : Array (cataState α (Frame Nat)))
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

def lst := List.range 100000
set_option trace.profiler.output "./ffperf"
set_option trace.profiler true
#eval lst.foldr (· + ·) 0
def v := cata (β := Nat) lst List.project
  (fun lst =>
    match lst with
    | .nil => 0
    | .cons a b => a + b)
  (fun state xs f =>
  match xs with
  | .nil => (state, .nil)
  | .cons a b =>
    let (state, c) := f state b
    (state, .cons a c))
#eval! v

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

@[grind]
structure Node where
  name : String
  tags : Tags
  children : List Node
  deriving Inhabited, Repr

mutual
def Node.size : Node → Nat
  | { children, .. } => 1 + Node.sizeAux children
def Node.sizeAux : List Node → Nat
  | [] => 0
  | c :: cs => c.size + (Node.sizeAux cs)
end

def Tags.toString (tags : Std.HashMap String String) : String := Id.run do
  let mut result := ""
  for (tag, value) in tags do
    result := result ++ s!"{tag}=\"{value}\" "
  result := result.dropRight 1
  result

structure Tree (α : Type) where
  label : α
  children : List (Tree α)
  deriving ToExpr

structure TreeF (α : Type) (β : Type) where
  label : α
  children : List β
  deriving ToExpr

def Tree.project (t : Tree α) : TreeF α (Tree α) := { t with }
def TreeF.embed (t : TreeF α (Tree α)) : Tree α := { t with }

def t1 : Tree Nat := Tree.mk 0 [Tree.mk 1 [], Tree.mk 2 [], Tree.mk 3 []]
#eval t1.project.embed

def Tree.cata (t : Tree α) (f : TreeF α β → β) : β :=
  sorry

@[grind]
structure NodeF α where
  name : String
  tags : Tags
  children : Array α
  deriving Inhabited, Repr

@[grind]
def NodeF.size {α} (_n : NodeF α) := 0

abbrev Stack α := Array ((Nat × Node) ⊕ (Nat × NodeF α))
abbrev Acc α := Array (Array α)

def Node.cata (n : Node) (f : NodeF α → α) : α :=
  let rec loop
      (acc : Acc α)
      (stack : { s : Stack α // 0 < s.size ∧ s.size = acc.size } )
      (fuel : Nat)
      (orig_node : Node := n)
      : α :=
    let n := stack.val[stack.val.size - 1]
    let stack := stack.val.pop
    match n with
    | Sum.inl (i, n) =>
      let stack' := stack.push <| Sum.inr (i, { n with children := #[] })
      let nIndex := stack'.size - 1
      let rec loop2
          (acc : Acc α)
          (stack : { s : Stack α // 0 < s.size ∧ s.size = acc.size } )
          (children : Array Node)
          : { s : Stack α × Acc α // 0 < s.fst.size ∧ s.fst.size = s.snd.size } :=
        if h : 0 < children.size then
          let acc := acc.push #[]
          let stack := stack.val.push <| Sum.inl (nIndex, children[children.size - 1])
          let children := children.pop
          loop2 acc ⟨stack, by grind⟩ children
        else ⟨(stack, acc), by grind⟩
      let ⟨(stack'', acc'), p⟩ := loop2 acc ⟨stack', by grind⟩ n.children
      loop acc' ⟨stack'', by grind⟩ (fuel + 1) orig_node
    | Sum.inr (i, n) =>
      let as := acc[acc.size - 1]
      let acc := acc.pop
      let a := f { n with children := as }
      if h : i < acc.size then /- equivalently, 0 < acc.size -/
        let acc := acc.set i (acc[i].push a)
        loop acc ⟨stack, by grind⟩ (fuel + 1) orig_node
      else a
  termination_by orig_node.size - fuel
  decreasing_by
    simp_wf
    grind
  loop #[.emptyWithCapacity n.children.size] ⟨#[Sum.inl (0, n)], by grind⟩ 0

def Node.cata' [Inhabited α] (n : Node) (f : NodeF α → α) : α := Id.run do
  let mut stack : Array ((Nat × Node) ⊕ (Nat × NodeF α)) := #[Sum.inl (0, n)]
  let mut acc : Array (Array α) := #[.emptyWithCapacity n.children.size]
  let mut isFirstIteration := true
  while h : stack.size > 1 ∨ (stack.size = 1 ∧ isFirstIteration) do
    isFirstIteration := false
    let n := stack[stack.size - 1]
    stack := stack.pop
    match n with
    | Sum.inl (i, n) =>
      stack := stack.push (Sum.inr (i, { n with children := #[] }))
      let mut children := n.children
      acc := acc.push (.emptyWithCapacity children.size)
      let nIndex := stack.size - 1
      while h : children.size > 0 do
        acc := acc.push #[]
        stack := stack.push (Sum.inl (nIndex, children[children.size - 1]))
        children := children.pop
    | Sum.inr (i, n) =>
      let as := acc[acc.size - 1]!
      acc := acc.pop
      let a := f { n with children := as }
      acc := acc.set! i (acc[i]!.push a)
  match stack[0]? with
  | none | some (Sum.inl _) => panic! ""
  | some (Sum.inr (i, n)) => f { n with children := acc[0]?.get! }


  -- let (stack, acc) :=
  -- match stack[0]? with
  -- | none | some (Sum.inl _) => panic! ""
  -- | some (Sum.inr (i, n)) => f { n with children := acc[0]?.get! }

def Node.toString (n : Node) : String :=
  let f : Nat → String := n.cata fun { name, tags, children } indentLevel => Id.run do
    let mut childStrs := ""
    for c in children do
      childStrs := childStrs ++ (c <| indentLevel + 2) ++ "\n"
    let space := if tags.size > 0 then " " else ""
    let indent1 := "".pushn ' ' indentLevel
    let indent2 := if children.size = 0 then "" else indent1
    let nl := if children.size = 0 then "" else "\n"
    s!"{indent1}<{name}{space}{Tags.toString tags}>{nl}{childStrs}{indent2}</{name}>"
  f 0

#eval println! Node.depth {
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

-- structure ViewBox where
--   minX : Float
--   minY : Float
--   width : Float
--   height : Float

-- inductive Node where
--   | SVG (width : Float) (height : Float) (viewBox : ViewBox)
--   | Rect (width : Float) (height : Float) (fill : String)

-- structure Document where
--   node : Node
--   children : Array Node

-- def Node.toString : Node → String
--   | SVG width height viewBox =>
--     let viewBox :=
--       let { minX, minY, width, height } := viewBox
--       s!"viewBox={minX} {minY} {width} {height}"
--     s!"svg width={width} height={height} {viewBox}"
--   | Rect width height fill => s!"rect width={width} height={height} fill={fill}"



instance instToStringNode : ToString Node where
  toString n := n.toString

#eval Node.SVG 536 280 (ViewBox.mk 0 0 1610 840)

end SVG

def Layers.toSVG (size : Nat) (layers : Array SwapLayer) : String :=



-- def Layer.countVerticalLines (l : Layer) : Nat := sorry

-- def Network.countVerticalLines (n : Network size) := sorry

-- def Network.toSVGString (n : Network size) : String := sorry


-- @[widget_module]
-- def helloWidget : Widget.Module where
--   javascript := "
--     import * as React from 'react';
--     export default function(props) {
--       const name = props.name || 'world'
--       return React.createElement('p', {}, 'Hello ' + name + '!')
--     }"

-- structure HelloWidgetProps where
--   name? : Option String := none
--   deriving Server.RpcEncodable

-- #widget helloWidget

-- #widget helloWidget with { name? := "<your name here>" : HelloWidgetProps }

-- structure GetTypeParams where
--   /-- Name of a constant to get the type of. -/
--   name : Name
--   /-- Position of our widget instance in the Lean file. -/
--   pos : Lsp.Position
--   deriving FromJson, ToJson

-- open Server RequestM in

-- @[server_rpc_method]
-- def getType (params : GetTypeParams) : RequestM (RequestTask CodeWithInfos) :=
--   withWaitFindSnapAtPos params.pos fun snap => do
--     runTermElabM snap do
--       let name ← resolveGlobalConstNoOverloadCore params.name
--       let c ← try getConstInfo name
--         catch _ => throwThe RequestError ⟨.invalidParams, s!"no constant named '{name}'"⟩
--       Widget.ppExprTagged c.type

-- @[widget_module]
-- def checkWidget : Widget.Module where
--   javascript := "
-- import * as React from 'react';
-- const e = React.createElement;
-- import { useRpcSession, InteractiveCode, useAsync, mapRpcError } from '@leanprover/infoview';

-- export default function(props) {
--   const rs = useRpcSession()
--   const [name, setName] = React.useState('getType')

--   const st = useAsync(() =>
--     rs.call('getType', { name, pos: props.pos }), [name, rs, props.pos])

--   const type = st.state === 'resolved' ? st.value && e(InteractiveCode, {fmt: st.value})
--     : st.state === 'rejected' ? e('p', null, mapRpcError(st.error).message)
--     : e('p', null, 'Loading..')
--   const onChange = (event) => { setName(event.target.value) }
--   return e('div', null,
--     e('input', { value: name, onChange }), ' : ', type)
-- }
-- "

-- #widget checkWidget
