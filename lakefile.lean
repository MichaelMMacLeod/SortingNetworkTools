import Lake

open System Lake DSL

package SortingNetworkTools where
  version := v!"0.1.0"

require "leanprover" / "Cli" @ "git#cacb481a1eaa4d7d4530a27b606c60923da21caf"

lean_lib SortingNetworkTools where

@[default_target]
lean_exe snt where
  root := `Main
  buildType := .release
