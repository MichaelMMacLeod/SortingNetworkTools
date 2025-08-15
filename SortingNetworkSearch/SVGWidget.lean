import Lean
import Lean.Widget.UserWidget

/-
Defines a widget for displaying SVG images in the Lean InfoView panel.

To display sorting networks in the InfoView panel, see NetworkCommand.lean,
which is a convenient way to use this widget.
-/

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
