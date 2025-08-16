import SortingNetworkSearch.Action
import SortingNetworkSearch.ExtraTheorems
import Lean.Parser
import Lean.Elab.GuardMsgs
import Lean.Data.Trie

inductive SubstringTree where
  | node : Array SubstringTree → SubstringTree
  | leaf : Substring → SubstringTree
  deriving Repr, Inhabited

structure Parser.Error where
  unexpected : Substring
  expected : Array String
  deriving Repr, Inhabited

def Parser.Error.append (e1 : Error) (e2 : Error) : Error :=
  -- we ignore e2's 'unexpected' string, since it should be the same as e1's
  { e1 with expected := e1.expected ++ e2.expected }

open Parser in
instance : Append Error where
  append := .append

structure Parser.State where
  input : String
  stack : Array SubstringTree := #[]
  pos : String.Pos := 0
  error : Option Error := none
  deriving Repr, Inhabited

structure Parser.State.SavePoint where
  stackSize : Nat
  pos : String.Pos
  error : Option Error

def errorAt (unexpected : Substring) (expected : Array String) : Parser.Error :=
  { unexpected
    expected
  }

def Parser.State.errorAtCurrentPos (s : State) (expected : String) : Error :=
  errorAt (Substring.mk s.input s.pos (s.input.next s.pos)) #[expected]

def Parser.State.errorsFrom (s : State) (sp : SavePoint) (expected : Array String) : Error :=
  errorAt (Substring.mk s.input sp.pos s.pos) expected

def Parser.State.errorFrom (s : State) (sp : SavePoint) (expected : String) : Error :=
  s.errorsFrom sp #[expected]

def Parser.State.save (s : State) : SavePoint := { s with stackSize := s.stack.size }

def Parser.State.back (s : Parser.State) : SubstringTree :=
  if h : 0 < s.stack.size then
    s.stack.back
  else
    panic! "State.back: stack is empty"

def Parser.State.pop (s : State) : State :=
  if s.stack.size > 0 then
    { s with stack := s.stack.pop }
  else
    panic! "State.pop: stack is empty"

def Parser.State.shrink (s : State) (size : Nat) : State :=
  { s with stack := s.stack.shrink size }

def Parser.State.leaf (s : Parser.State) : Substring :=
  match s.back with
  | .leaf str => str
  | .node _ => panic! "State.leaf: expected leaf, got branch"

def Parser.State.branch (s : Parser.State) : Array SubstringTree :=
  match s.back with
  | .node xs => xs
  | .leaf _ => panic! "State.branch: expected branch, got leaf"

def Parser.State.fail (s : Parser.State) (error : Error) : Parser.State :=
  { s with error := some error }

def Parser.State.restore (s : Parser.State) (sp : SavePoint) : Parser.State :=
  { sp with input := s.input, stack := s.stack.shrink sp.stackSize }

def Parser.State.next (s : Parser.State) : Parser.State :=
  { s with pos := s.input.next s.pos }

def Parser.State.atEnd (s : Parser.State) : Bool := s.input.atEnd s.pos

def Parser.State.get (s : Parser.State) : Char := s.input.get s.pos

def Parser.State.pushLeaf (s : Parser.State) (init : String.Pos) : Parser.State :=
  { s with stack := s.stack.push <| .leaf (Substring.mk s.input init s.pos )}

def Parser.State.mkNode (s : Parser.State) (size : Nat) : Parser.State :=
  let xs := s.stack.extract (s.stack.size - size)
  let s := s.shrink (s.stack.size - size)
  { s with stack := s.stack.push <| .node xs }

abbrev Parser := Parser.State → Parser.State

def Parser.run (p : Parser) (input : String) : Parser.State := p { input }

def Parser.State.hasError (s : State) : Bool := s.error.isSome

def Parser.andThen (p q : Parser) : Parser := fun s =>
  let s := p s
  if s.hasError then s else q s

instance : AndThen Parser where
  andThen p q := p.andThen (q ())

instance : AndThen (Parser.State → Parser.State) where
  andThen p q := Parser.andThen p (q ())

open Parser in
instance : AndThen (State → State) where
  andThen p q := Parser.andThen p (q ())

def Parser.optional (p : Parser) : Parser := fun s =>
  let s' := p s
  if s'.hasError then s else s'

def Parser.orElse (p q : Parser) : Parser := fun s =>
  let sp := s.save
  let s := p s
  if let some error1 := s.error then
    let s := q (s.restore sp)
    if let some error2 := State.error s then
      s.fail (error1 ++ error2)
    else s
  else s

instance : OrElse Parser where
  orElse p q := p.orElse (q ())

def Parser.eof : Parser := fun s =>
  let isEof := s.input.get? s.pos |>.isNone
  if isEof then s else s.fail (s.errorAtCurrentPos "end of input")

partial def Parser.takeUntil (isStopChar : Char → Bool) : Parser := fun s =>
  if s.atEnd ∨ isStopChar s.get then
    s
  else takeUntil isStopChar s.next

partial def Parser.takeWhileInside (substring : Substring) (s : State) : State :=
  aux substring.startPos s
where
  sp := s.save
  mkError (s : State) := s.fail <| s.errorFrom sp s!"'{substring}'"
  aux pos s :=
    if pos ≥ substring.stopPos then s
    else if s.atEnd then mkError s
    else if s.get = substring.get pos then
      aux (substring.next pos) s.next
    else mkError s

def Parser.token (isStopChar : Char → Bool) (s : State) : State := aux s
where
  initPos := s.pos
  aux := takeUntil isStopChar >> fun s =>
    if s.pos > initPos then
      s.pushLeaf initPos
    else
      s.fail (s.errorAtCurrentPos "token")

def Parser.ws : Parser := takeUntil (!·.isWhitespace)

def Parser.mandatoryWs : Parser := fun s =>
  let sp := s.save
  s |> ws >> fun (s : State) =>
  if s.pos = sp.pos then
    s.fail <| s.errorFrom sp "whitespace"
  else s

def Parser.ignore (p : Parser) : Parser := fun s =>
  let initSize := s.stack.size
  s |> p >> fun s => State.shrink s initSize

def Parser.string (str : String) : Parser := fun s =>
  let sp := s.save
  let s := takeWhileInside str.toSubstring s
  if s.hasError then
    s.fail <| s.errorFrom sp str
  else s

def Parser.word : Parser := token (·.isWhitespace)

def Parser.symbol (sym : String) : Parser :=
  ignore ws >> fun s =>
    let sp := s.save
    s |> word >> fun s =>
      let l := State.leaf s
      if l == sym.toSubstring then
        s
      else s.fail <| s.errorFrom sp s!"'{sym}'"

def Parser.sequence (ps : Array Parser) : Parser := aux 0
where
  aux n (s : State) :=
    if h : n < ps.size then
      s |> ps[n] >> aux (n+1)
    else s

def Parser.option (name : String) (args : Array Parser) (isLongDash : Bool := true) :=
  let dash := if isLongDash then "--" else "-"
  ws >> fun s =>
    let sp := s.save
    s |> ignore (string dash)
      >> (fun s =>
        let s := s |> symbol name >> mandatoryWs
        if s.hasError then
          s.fail <| s.errorFrom sp s!"'{dash}{name}'"
        else
          let s := sequence args s
          if let some error := s.error then
            s.fail <| (s.errorFrom sp s!"'{dash}{name}'") ++ error
          else s)
      >> (State.mkNode · (args.size + 1))

-- def Parser.option (name : String) (args : Array Parser) (isLongDash : Bool := true) :=
--   let dash := if isLongDash then "--" else "-"
--   ws >> fun s =>
--     let sp := s.save
--     s |> ignore (symbol dash)
--       >> (fun s =>
--         let s := s |> symbol name >> mandatoryWs
--         if s.hasError then
--           s.fail <| s.errorFrom sp s!"'{dash}{name}'"
--         else s)
--       >> (State.mkNode · (args.size + 1))

def Parser.nat : Parser :=
  ignore ws >> fun s =>
    let sp := s.save
    let s := token (Char.isWhitespace) s
    let mkError : State → State := fun s => s.fail (s.errorFrom sp "a natural number")
    if s.hasError then
      mkError s
    else
      let str := State.leaf s
      if str.isNat then s else mkError s

def Parser.State.errorMessage (s : State) : Option String :=
  s.error.map fun error =>
    let expected := error.expected.foldl (init := (0, "")) fun (i, acc) e =>
      let acc := if i = 0 then
          s!"{e}"
        else if i = error.expected.size - 1 then
          if error.expected.size = 2 then
            s!"{acc} or {e}"
          else
            s!"{acc}, or {e}"
        else
          s!"{acc}, {e}"
      (i + 1, acc)
    let (_, expected) := expected
    -- if s.atEnd then
    --   s!"unexpected end of command line arguments; expected {expected}"
    -- else
    let unexpected := Substring.mk s.input error.unexpected.startPos error.unexpected.stopPos
    s!"expected {expected} at '{unexpected}'"

def Parser.algorithmNames :=
  symbol "batcher" <|>
  symbol "bubble" <|>
  symbol "empty"

def Parser.algorithmArgs : Parser := sequence #[algorithmNames, nat]
def Parser.loadArgs : Parser := ignore ws >> word

open Lean.Data

def Parser.cases (p : Parser) (cs : Array (String × Parser)) : Parser := fun s =>
  let t := cs.foldl (init := Trie.empty) fun acc (str, p) => acc.insert str p
  let sp := s.save
  s |> p >> fun (s : State) =>
    let l := s.leaf.toString
    if let some p := t.find? l then
      p s
    else s.fail <| s.errorsFrom sp <| cs.map fun (a : String × Parser) => s!"'{a.fst}'"

def Parser.optionsArray := #[
  ("--algorithm", Parser.algorithmArgs),
  ("--load", Parser.loadArgs),
]

def Parser.options := ignore ws >> cases word optionsArray

def runAO : String → Option String := fun s => Parser.options.run s |>.errorMessage

/--info: some "expected '--algorithm' or '--load' at '--algorithmbatcher'"-/
#guard_msgs in #eval runAO "--algorithmbatcher 16"
/--info: some "expected '--algorithm' or '--load' at '--algo'"-/
#guard_msgs in #eval runAO "--algo batcher 16"
/--info: none-/
#guard_msgs in #eval runAO "--algorithm batcher 16"
/--info: none-/
#guard_msgs in #eval runAO "--algorithm bubble 16"
/--info: none-/
#guard_msgs in #eval runAO "--algorithm empty 16"
/--info: some "expected 'batcher', 'bubble', or 'empty' at 'unknown'"-/
#guard_msgs in #eval runAO "--algorithm unknown 16"
/--info: some "expected a natural number at 'foo'"-/
#guard_msgs in #eval runAO "--algorithm batcher foo"

-- def USize.MAX := (2^System.Platform.numBits - 1).toUSize

-- theorem USize.MAX_largest : ¬∃n : USize, n > USize.MAX := by sorry

-- def USize.saturatingAddOne (u : USize) := max (u + 1) USize.MAX

-- @[grind]
-- theorem USize.le_saturatingAddOne (u : USize) : u ≤ u.saturatingAddOne := by
--   simp [saturatingAddOne]
--   unfold max
--   simp [instMaxUSize]
--   simp [maxOfLe]
--   split
--   . if h : u ≤ MAX then
--       exact h
--     else
--       refine (USize.MAX_largest ?h).elim
--       apply Exists.intro
--       exact USize.not_le.mp h
--   . sorry
--     grind

-- theorem USize.idk2 (u : USize) (h : u < USize.size)

-- def Parser.sequenceArrayUSize (ps : Array Parser) : Parser :=
--   if h : ps.size < USize.size then
--     aux 0 h
--   else unreachable!
-- where
--   aux n (h : ps.size < USize.size) s :=
--     if h : n < ps.usize then
--       aux n.saturatingAddOne (by grind) ((ps[n]'(by grind)) s)
--     else s
--   termination_by ps.usize - n
--   decreasing_by
--     simp_wf
--     refine USize.lt_iff_toNat_lt.mp ?_
--     have h : n < n.saturatingAddOne := by sorry
--     simp

-- #eval Parser.while <| { input := "qwe abc" }
-- #eval Parser.symbol "qwe" <| { input := "qwe abc" }
-- #eval Parser.whitespace <| { input := "   qwe abc" }

-- def Substring.eqSymbol (s : Substring) (s : String) : Bool

-- def Parser.symConvert : Parser := fun s =>


-- import Lean.Data.Trie

-- #check Lean.Data.Trie


-- structure Cmd.Option where
--   name : String -- e.g., for `--myOption`, name is `myOption`
--   argParser :



-- def usage : String :=
-- r#"sns - Sorting Network Search
-- An evolutionary approach to constructing sorting networks

-- Usage: sns <command> [<option>...]

-- Commands:

--   evolve    Create new sorting networks through evolution.
--   validate  Verify a network's correctness
--   convert   Convert a network to a format

-- Options:

--   --algorithm <algorithm> <channels>

--     Create a comparison network with the specified number of
--     channels via a known method.

--       <algorithm>

--         empty (default)  Network with no comparisons
--         batcher          Batcher odd-even mergesort
--         bubble           Bubble sort

--       <channels>  Non-negative integer (2, 8, 10, etc.).
--                   Specifies the fixed size of lists that the
--                   given network processes.

--   --load <file>

--     Reads a comparison network from a file.

--       <file>  A path to a file containing a network in the 'list'
--               format (e.g., '/tmp/MyNetwork.txt'), or '-' to load
--               from standard input.

-- Examples:

--   sns convert --algorithm batcher 8 --format svg

--     Create an SVG (Scalable Vector Graphics) representation of
--     Batcher Even-Odd mergesort on lists of length 8.

-- Commands:
--   evolve [--seed <seed>] [--timeout <seconds>]
-- "#
-- import SortingNetworkSearch.Action
-- import Cli



-- def Parser.map (f : α → β) : Parser α → Parser β
--   | x => .nil .mk

-- instance instFunctorParser : Functor Parser where
--   map := .map

-- abbrev Args := List String

-- class Parser.Monad {m} [Alternative m] where
--   enterContext : String →

-- def Parser.run (p : Parser) (args : Args) : m ()

-- open Cli

-- def installCmd := `[Cli|
--   installCmd NOOP;
--   "installCmd provides an example for a subcommand without flags or arguments that does nothing. " ++
--   "Versions can be omitted."
-- ]

-- def runExampleCmd (p : Parsed) : IO UInt32 := do
--   let input   : String       := p.positionalArg! "input" |>.as! String
--   let outputs : Array String := p.variableArgsAs! String
--   IO.println <| "Input: " ++ input
--   IO.println <| "Outputs: " ++ toString outputs

--   if p.hasFlag "verbose" then
--     IO.println "Flag `--verbose` was set."
--   if p.hasFlag "invert" then
--     IO.println "Flag `--invert` was set."
--   if p.hasFlag "optimize" then
--     IO.println "Flag `--optimize` was set."

--   let priority : Nat := p.flag! "priority" |>.as! Nat
--   IO.println <| "Flag `--priority` always has at least a default value: " ++ toString priority

--   if p.hasFlag "module" then
--     let moduleName : ModuleName := p.flag! "module" |>.as! ModuleName
--     IO.println <| s!"Flag `--module` was set to `{moduleName}`."

--   if let some setPathsFlag := p.flag? "set-paths" then
--     IO.println <| toString <| setPathsFlag.as! (Array String)
--   return 0

/-
sns convert <existing-network> <format>
sns convert --load /tmp/nw1.txt --format svg
sns convert --load /tmp/nw1.txt --format list
sns convert --algorithm bubble 8 --format matrix

sns validate --load /tmp/nw1.txt
sns validate --algorithm bubble 8

sns evolve <seed> <timeout> (<existing-network>|<size>)
sns evolve --seed 123 --timeout 5 --load /tmp/nw1.txt
sns evolve --seed 123 --timeout 5 --algorithm batcher 32
sns evolve --seed 123 --timeout 5 --algorithm empty 10
-/

-- #check Type*
-- -- def exampleCmd : Cli.Cmd := `[Cli|
-- --   sns VIA runExampleCmd; ["0.1.0"]
-- --   "an evolutionary approach to constructing sorting networks"

-- --   FLAGS:
-- --     a, algorithm : String × Nat;      "Create a sorting network via an algorithm"
-- --     l, load;                    "Load a sorting network from a file"
-- --     i, invert;                  "Declares a flag `--invert` with an associated short alias `-i`."
-- --     o, optimize;                "Declares a flag `--optimize` with an associated short alias `-o`."
-- --     p, priority : Nat;          "Declares a flag `--priority` with an associated short alias `-p` " ++
-- --                                 "that takes an argument of type `Nat`."
-- --     module : ModuleName;        "Declares a flag `--module` that takes an argument of type `ModuleName` " ++
-- --                                 "which be can used to reference Lean modules like `Init.Data.Array` " ++
-- --                                 "or Lean files using a relative path like `Init/Data/Array.lean`."
-- --     "set-paths" : Array String; "Declares a flag `--set-paths` " ++
-- --                                 "that takes an argument of type `Array String`. " ++
-- --                                 "Quotation marks allow the use of hyphens."

-- --   ARGS:
-- --     input : String;      "Declares a positional argument <input> " ++
-- --                          "that takes an argument of type `String`."

-- --   SUBCOMMANDS:
-- --     installCmd;
-- --     testCmd

-- --   -- The EXTENSIONS section denotes features that
-- --   -- were added as an external extension to the library.
-- --   -- `./Cli/Extensions.lean` provides some commonly useful examples.
-- --   EXTENSIONS:
-- --     author "mhuisi";
-- --     defaultValues! #[("priority", "0")]
-- -- ]
