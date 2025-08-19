import Lake

open System Lake DSL

package SortingNetworkTools where
  version := v!"0.1.0"

lean_lib SortingNetworkTools

@[default_target]
lean_exe snt where
  root := `Main
  buildType := .release
