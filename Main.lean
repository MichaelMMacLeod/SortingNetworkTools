import SortingNetworkTools.Cli
import SortingNetworkTools.Action

def main (args : List String) : IO Unit := do
  let args := args.foldl (s!"{·} {·}") ""
  match Dep.action.run args.toSubstring with
  | .error e => println! e.fmt "snt"
  | .ok (a, _) => a.main
