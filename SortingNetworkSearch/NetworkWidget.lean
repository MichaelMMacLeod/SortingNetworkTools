import Lean
import SortingNetworkSearch.Network
import SortingNetworkSearch.Layer
import Std.Data.HashMap

open Lean Widget

namespace SVG

abbrev Tags := Std.HashMap String String

@[grind]
structure Node where
  name : String
  tags : Tags
  children : Array Node
  deriving Inhabited, Repr

mutual
@[grind]
def Node.size : Node → Nat
  | { children, .. } => 1 + Node.sizeAux children
@[grind]
def Node.sizeAux (xs : Array Node) : Nat :=
  xs.map (·.size) |>.sum
end

mutual
@[grind]
theorem Node.size_lt (n : Node) {i : Nat} {h} {c : Node}
    : c = n.children[i] → c.size < n.size := by
  sorry
-- theorem Node.sizeAux_lt (xs : Array Node) :
--    c = xs[i] → c.size < xs.map (·.size) |>.sum := by
end

-- theorem Node.size_children_lt (n : Node) {i : Nat} {h} {c : Node}
--     : c = n.children[i] → c.size < n.size := by
--   intro c_eq
--   induction h : n.size with
--   | zero => grind
--   | succ n' ih =>
--     unfold size
--     split
--     rename_i children tags name
--     unfold sizeAux
--     grind
--     -- simp [*]

--     -- grind

def Tags.toString (tags : Std.HashMap String String) : String := Id.run do
  let mut result := ""
  for (tag, value) in tags do
    result := result ++ s!"{tag}=\"{value}\" "
  result := result.dropRight 1
  result

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
