import SortingNetworkSearch.SVGWidget
import SortingNetworkSearch.NetworkExtras
import SortingNetworkSearch.Network

open Lean Widget Lean.Elab.Command Lean.Elab

syntax (name := networkCmd) "#network " term : command

/--
Displays the a network in the Lean InfoView panel.

Example:
```
import SortingNetworkSearch.NetworkExtras
#network (Network.Algorithm.batcherOddEven : Network 16)
```
-/
@[command_elab networkCmd]
def elabNetworkCmd : CommandElab
  | stx@`(#network $n) => liftTermElabM do
    let s : TSyntax `Lean.Widget.widgetInstanceSpec ← `(widgetInstanceSpec| svgWidget with { svgString := ($n).toSVG.toString : SVGWidgetProps })
    let wi : Expr ← elabWidgetInstanceSpec s
    let wi : WidgetInstance ← evalWidgetInstance wi
    savePanelWidgetInfo wi.javascriptHash wi.props stx
  | _ => throwUnsupportedSyntax
