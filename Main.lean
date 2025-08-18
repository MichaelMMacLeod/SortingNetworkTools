import SortingNetworkSearch.CLI
import SortingNetworkSearch.Action

def main (args : List String) : IO Unit := do
  let args := args.foldl (s!"{·} {·}") ""
  let s := sns.parser.run args
  if let some error := s.errorMessage then
    println! error
  else
    let action := Action.fromParsedCLI s.stack.back!
    if let some action := action
    then action.main
    else unreachable!
