import Lake

open System Lake DSL

package SortingNetworkSearch where
  version := v!"0.1.0"

lean_lib SortingNetworkSearch where

@[default_target]
lean_exe sortingnetworksearch where
  root := `Main
  buildType := .release
