import Lake

open System Lake DSL

#check LeanOption

package SortingNetworkSearch
where
  version := v!"0.1.0"
  buildType := .release

require "leanprover-community" / mathlib

def cExtrasPathC : FilePath := "SortingNetworkSearchFFI" / "c" / "extras.c"
def cExtrasPathO : FilePath := "SortingNetworkSearchFFI" / "c" / "extras.o"

-- input_file extras.c where
--   path := cExtrasPathC
--   text := true

-- target extras.o pkg : FilePath := do
--   let srcJob ← extras.c.fetch
--   let oFile := pkg.buildDir / cExtrasPathO
--   buildO oFile srcJob #[] #["-fPIC"] "cc"

-- target libextras pkg : FilePath := do
--   let ffiO ← extras.o.fetch
--   let name := nameToStaticLib "extras"
--   buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- lean_lib SortingNetworkSearchFFI where
--   precompileModules := true
--   srcDir := "SortingNetworkSearchFFI"
--   moreLinkObjs := #[libextras]

lean_lib SortingNetworkSearch where
  -- needs := #[SortingNetworkSearchFFI]

@[default_target]
lean_exe sortingnetworksearch where
  root := `Main
