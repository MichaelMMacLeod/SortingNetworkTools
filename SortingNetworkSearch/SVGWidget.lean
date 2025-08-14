import Lean

open Lean Widget

@[widget_module]
def svgWidget : Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const svg = props.svgString;
      const img = React.createElement('img', { src : `data:image/svg+xml;utf8,${encodeURIComponent(svg)}` });
      return img
    }"

structure SVGWidgetProps where
  svgString : String
  deriving Server.RpcEncodable

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
