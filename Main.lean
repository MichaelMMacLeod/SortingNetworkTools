import SortingNetworkSearch.CLI

def main (args : List String) : IO Unit := do
  let args := args.foldl (s!"{·} {·}") ""
  let s := sns.parser.run args
  if let some error := s.errorMessage then
    println! error
  else
    println! s.stack.back!.toString
