import SortingNetworkSearch.ExtraTheorems
import Lean.Parser
import Lean.Elab.GuardMsgs
import Lean.Data.Trie
import Init.Data.Format.Basic
import SortingNetworkSearch.SubstringTree

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

def Parser.State.errorsAtCurrentPos (s : State) (expected : Array String) : Error :=
  errorAt (Substring.mk s.input s.pos (s.input.next s.pos)) expected

def Parser.State.errorAtCurrentPos (s : State) (expected : String) : Error :=
  s.errorsAtCurrentPos #[expected]

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
      let s := s |> ps[n]
      let p : Parser := id >> aux (n+1)
      p s
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
    if s.input.trim.isEmpty then
      s!"expected {expected}"
    else
      let unexpected := Substring.mk s.input error.unexpected.startPos error.unexpected.stopPos
      s!"expected {expected} at '{unexpected}'"

open Lean.Data

def Parser.cases (cs : Array (String × Bool × Parser)) (onMatchFail : Unit → State): Parser := fun s =>
  let t := cs.foldl (init := Trie.empty) fun acc (str, p) => acc.insert str p.snd
  let l := s.leaf.toString
  if let some p := t.find? l
    then p s
    else onMatchFail ()

def Parser.switch (cases : Array (Parser × Parser)) : Parser := fun s => Id.run do
  let mut unexpectedOption : Option Substring := none
  let mut expected : Array String := #[]
  for h : i in 0...cases.size do
    let s := cases[i].fst s
    if let some error := s.error then
      if let none := unexpectedOption then
        unexpectedOption := error.unexpected -- just take the first failing position
      expected := expected ++ error.expected
    else
      return cases[i].snd s
  let unexpected : Substring := unexpectedOption.getD <| Substring.mk s.input s.pos (s.input.next s.pos)
  s.fail <| { unexpected, expected }

def Parser.options (optionsArray : Array (String × Bool × Parser)) : Parser := ignore ws >> fun s =>
  let sp := s.save
  let s := word s
  let mkError : Unit → State := fun _ =>
    let s := s.fail <| s.errorsFrom sp <| optionsArray.filterMap fun (a : String × Bool × Parser) =>
      let (n, shouldDisplay, _) := a
      if shouldDisplay
        then s!"'{n}'"
        else none
    s
  if s.hasError then
    mkError ()
  else
    s |> cases optionsArray mkError

def Parser.wordSatisfying (validate : String → Bool) (description : String) : Parser := fun s =>
  let sp := s.save
  let mkError : State → State := fun s => s.fail <| s.errorFrom sp description
  let s := s |> ignore ws |> word
  if s.hasError then
    mkError s
  else
    let l := s.leaf
    if validate l.toString
      then s
      else mkError s

def Parser.algorithmNames :=
  symbol "batcher" <|>
  symbol "bubble" <|>
  symbol "empty"

def Parser.algorithmArgs : Parser := sequence #[algorithmNames, nat]
def Parser.loadArgs : Parser := ignore ws >> word

def alOptions := #[
  ("--algorithm", true, Parser.algorithmArgs),
  ("-a", false, Parser.algorithmArgs),
  ("--load", true, Parser.loadArgs),
  ("-l", false, Parser.loadArgs),
]

def Parser.formatNames : Parser :=
  symbol "list" <|>
  symbol "svg"

def Parser.convertCmd : Parser := options #[
  ("--format", true, formatNames),
  ("-f", false, formatNames),
]

def Parser.cmds := #[
  ("convert", true, Parser.convertCmd),
  -- ("evolve", Parser.evolveCmd),
  -- ("verify", Parser.verifyCmd),
]
def Parser.sns : Parser := options alOptions >> options cmds

def runAO : String → Option String := fun s => Parser.options alOptions |>.run  s |>.errorMessage

/--info: none-/
#guard_msgs in #eval Parser.wordSatisfying (·.isNat) "a natural number" |>.run "123" |>.errorMessage
/--info: some "expected a natural number at '12-3'"-/
#guard_msgs in #eval Parser.wordSatisfying (·.isNat) "a natural number" |>.run "12-3" |>.errorMessage
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
/--info: some "expected '--algorithm' or '--load'"-/
#guard_msgs in #eval runAO ""
/--info: some "expected '--algorithm' or '--load'"-/
#guard_msgs in #eval runAO "   \n \t\t    "
/--info: none-/
#guard_msgs in #eval runAO "--load /tmp/nw1.txt"
/--info: none-/
#guard_msgs in #eval runAO "--load /tmp/nw1.txt"

def runSns : String → Option String := fun s => Parser.sns.run s |>.errorMessage

/--info: none-/
#guard_msgs in #eval runSns "--algorithm batcher 8 convert --format list"
/--info: none-/
#guard_msgs in #eval runSns "-a batcher 8 convert -f list"
/--info: some "expected 'batcher', 'bubble', or 'empty' at '8'"-/
#guard_msgs in #eval runSns "-a 8 convert -f list"
/--info: some "expected a natural number at 'convert'"-/
#guard_msgs in #eval runSns "-a batcher convert -f list"
/--info: some "expected 'convert' at 'c'"-/
#guard_msgs in #eval runSns "-a batcher 8 c -f list"

inductive Cli.Name where
| long : String → Cli.Name
| short : String → Cli.Name
| shortAndLong : String → String → Cli.Name

def Cli.Name.parser (n : Cli.Name) : Parser :=
  Parser.ignore .ws >> fun s =>
    match n with
    | .long l => s |> Parser.symbol s!"--{l}"
    | .short sh => s |> Parser.symbol s!"-{sh}"
    | .shortAndLong sh l =>
      let sp := s.save
      let s := s |> Parser.symbol s!"-{sh}"
      if s.hasError
        then s.restore sp |> Parser.symbol s!"--{l}"
        else s

structure Cli.Example where
  eg : String
  description : Option String

inductive Cli.Arg.Value.Vague.Description where
| any : Description
| satisfies : (validate : String → Bool) → (label : String) → Description

structure Cli.Arg.Value.Vague where
  examples : Array String
  description : Vague.Description

structure Cli.Arg.Value.Exact where
  value : String
  description : String

inductive Cli.Arg.Value where
| vague : Value.Vague → Value
| exact : Value.Exact → Value

structure Cli.Arg where
  name : String
  description : Option String
  values : Array Cli.Arg.Value

structure Cli.Option where
  name : Cli.Name
  description : String
  args : Array Cli.Arg
  examples : Array Cli.Example

structure Cli.Command where
  name : String
  description : String
  options : Array Cli.Option
  examples : Array Cli.Example

structure Cli.Program where
  executableName : String
  name : _root_.Option String
  description : String
  usage : String
  globalOptions : Array Cli.Option
  commands : Array Cli.Command
  examples : Array Cli.Example

def Cli.Arg.Value.Vague.hasTextContent (v : Cli.Arg.Value.Vague) : Bool :=
  v.examples.size > 0 || (match v.description with | .any => false | .satisfies _ _ => true)

def Cli.Arg.valuesWithTextContent (a : Cli.Arg) : Array Cli.Arg.Value :=
  a.values.filter fun v =>
    match v with
    | .vague v => v.hasTextContent
    | .exact _ => true

def Cli.Arg.Value.parser : Cli.Arg.Value → Parser
| vague { description := .any, .. } => fun s => s
| vague { description := .satisfies p description, ..} => Parser.wordSatisfying p description
| exact v => Parser.symbol v.value

def Cli.Arg.parser (a : Cli.Arg) : Parser :=
  let valueParsers : Array Parser := a.values.map (·.parser)
  match h : valueParsers.size with
  | 0 => fun s => s
  | 1 => valueParsers[0]
  | _ => fun s =>
    let sp := s.save
    let mkError : Parser := fun s => s.fail <| s.errorsFrom sp #[]
    s |> show Parser from
      valueParsers.foldl (init := mkError) fun acc vp => vp <|> acc

def Cli.Option.parsers (o : Cli.Option) : Parser × Parser :=
  let argParser := Parser.sequence <| o.args.map (·.parser)
  let argParser := argParser >> fun s => s.mkNode (o.args.size + 1)
  (o.name.parser, argParser)

def Cli.Command.parsers (c : Cli.Command) : Parser × Parser :=
  let cOptions := c.options.foldl (·.push ·.parsers) #[]
  (Parser.symbol c.name, Parser.switch cOptions)

def Cli.Program.parser (pg : Cli.Program) : Parser :=
  let globalOptions := pg.globalOptions.foldl (·.push ·.parsers) #[]
  let commandOptions := pg.commands.foldl (·.push ·.parsers) #[]
  Parser.switch globalOptions >> fun s =>
    let s := s.mkNode s.stack.size
    s |> show Parser from
      Parser.switch commandOptions >> fun s =>
        let s := s.mkNode (s.stack.size - 2)
        s.mkNode 3

def sns : Cli.Program := {
  executableName := "sns"
  name := some "Sorting Network Search"
  description := "An evolutionary approach to constructing sorting networks"
  usage := "sns <global-option>... <command> <command-option>..."
  globalOptions := #[
    { name := .shortAndLong "a" "algorithm"
      description := "Create a network of the specified size via a known method"
      args := #[
        { name := "algorithm"
          description := none
          values := #[
            .exact {
              value := "batcher"
              description := "batcher odd-even mergesort" },
            .exact {
              value := "bubble"
              description := "bubble sort" },
            .exact {
              value := "empty"
              description := "network with no comparisons"
            }
          ]
        },
        { name := "channels"
          description := "number of inputs to the network"
          values := #[
            .vague {
              examples := #["2", "10", "16", "32"]
              description := .satisfies (·.isNat) "natural number"
            }
          ]
        }
      ]
      examples := #[
        { eg := "--algorithm batcher 16"
          description := "Batcher odd-even mergesort with 16 channels"
        },
        { eg := "--algorithm empty 8"
          description := "Empty network with 16 channels"
        }
      ]
    },
    { name := .shortAndLong "l" "load"
      description := "Read a network from a file"
      args := #[
        { name := "file"
          description := "path storing a network in the list format"
          values := #[
            .vague {
              examples := #[]
              description := .any
            }
          ]
        }
      ]
      examples := #[]
    }
  ]
  commands := #[
    { name := "convert"
      description := "Translate between network formats"
      options := #[
        { name := .shortAndLong "f" "format"
          description := "Select a network encoding to produce"
          args := #[
            { name := "format"
              description := none
              values := #[
                .exact {
                  value := "list"
                  description := "a comma-separated list of compare-and-exchange operations"
                },
                .exact {
                  value := "svg"
                  description := "Scalable Vector Graphics"
                }
              ]
            }
          ]
          examples := #[]
        }
      ]
      examples := #[
        { eg := "sns --algorithm bubble 3 convert --format list"
          description := "Output a bubble sort comparison network with 3 channels in list format"
        },
        { eg := "sns --algorithm batcher 16 convert --format svg"
          description := "Create an SVG of Batcher odd-even mergesort with 16 channels"
        }
      ]
    },
    { name := "evolve"
      description := "Search for more efficient networks through repeated mutation"
      options := #[]
      examples := #[]
    },
    { name := "verify"
      description := "Exhaustively test a network for correctness"
      options := #[]
      examples := #[]
    },
  ]
  examples := #[
    { eg := "sns --algorithm batcher 16 convert --format svg > BatcherOddEven.html"
      description := "Create a SVG of size-16 Batcher odd-even mergesort viewable in a web browser"
    },
    { eg := "sns --algorithm empty 10 evolve --timeout 30"
      description := "Starting from an empty network, search for efficient sorting networks with 10 channels in at most 30 seconds"
    },
    { eg := "sns --load /tmp/network.txt verify"
      description := "Verify the correctness of the network at /tmp/network.txt"
    },
  ]
}

open Std.Format
export Std (Format)

def Cli.Name.fmt : Cli.Name → Format
| long l => s!"--{l}"
| short s => s!"-{s}"
| shortAndLong s l => s!"-{s}, --{l}"

def Cli.Arg.namefmt (a : Cli.Arg) : Format :=
  "<" ++ a.name ++ ">"

def Cli.Arg.Value.Exact.fmt (v : Cli.Arg.Value.Exact) : Format :=
  v.value ++ nest 16 (align true ++ v.description)

def Cli.Arg.Value.Vague.fmt (v : Cli.Arg.Value.Vague) : Format :=
  let result := if v.examples.size > 0
    then joinSep v.examples.toList "," ++ "…"
    else ""
  match v.description with
  | .any => result
  | .satisfies _ label => result ++ nest 16 (align true ++ label)

def Cli.Arg.fmt (a : Cli.Arg) : Format :=
  let result := align true ++ a.namefmt
  let result := result ++ if let some description := a.description
    then nest 16 (align true ++ description)
    else ""
  let values := a.valuesWithTextContent
  let result := result ++ if values.size > 0
    then prefixJoin (line ++ " | ") (values.toList.map (fun v =>
      match v with
      | .vague v => v.fmt
      | .exact v => v.fmt
      ))
    else ""
  result

def Cli.Option.fmt (o : Cli.Option) : Format :=
  let result : Format := align true ++ o.name.fmt
  let result := result ++ " " ++ joinSep (o.args.toList.map (·.namefmt)) " "
  let result := result ++ line
  let result := result ++ nest 4 (align true ++ o.description)
  let result :=
    if o.args.size > 0 then
      let result := result ++ line ++ line
      result ++ nest 4 (joinSep (o.args.toList.map (·.fmt)) line)
    else result
  result

def Cli.Command.shortFmt (c : Cli.Command) (executableName : String) : Format :=
  let result := executableName ++ " " ++ c.name
  let result := result ++ nest 16 (align true ++ c.description)
  result

def Cli.Example.fmt (e : Cli.Example) : Format :=
  let result := e.eg
  let result :=
    if let some description := e.description
      then result ++ line ++ nest 4 (align true ++ description)
      else result
  result

def Cli.Program.globalHelpFmt (p : Program) : Format :=
  let result := p.executableName
  let result :=
    if let some name := p.name
    then result ++ s!" - {name}"
    else result
  let result := result ++ line ++ p.description ++ line ++ line
  let result := result ++ "Commands" ++ line ++ line
  let result := result ++ nest 4 (align true ++ joinSep (p.commands.toList.map (·.shortFmt p.executableName)) line)
  let result := result ++ line ++ line
  let result := result ++ "Global Options" ++ line
  let result := result ++ nest 4 (align true ++ joinSep (p.globalOptions.toList.map (·.fmt)) line)
  let result :=
    if p.examples.size > 0 then
      let result := result ++ line ++ line ++ "Examples" ++ line ++ line
      let result := result ++ nest 4 (align true ++ joinSep (p.examples.toList.map (·.fmt)) (line ++ line))
      result
    else result
  result

/--info: some "expected 'svg' or 'list' at 'idk'"-/
#guard_msgs in #eval sns.parser.run "-a batcher 16 convert --format idk" |>.errorMessage
/--info: none-/
#guard_msgs in #eval sns.parser.run "-a batcher 16 convert --format list" |>.errorMessage
/--info: none-/
#guard_msgs in #eval sns.parser.run "--algorithm batcher 16 convert --format list" |>.errorMessage
/--info: some "expected 'convert', 'evolve', or 'verify' at '--load'"-/
#guard_msgs in #eval sns.parser.run "--algorithm batcher 16 --load nw.txt" |>.errorMessage
/--info: some "expected 'convert', 'evolve', or 'verify' at '--load'"-/
#guard_msgs in #eval sns.parser.run "-a batcher 16 --load nw.txt" |>.errorMessage
/--info: some "expected 'convert', 'evolve', or 'verify' at '-l'"-/
#guard_msgs in #eval sns.parser.run "-a batcher 16 -l nw.txt" |>.errorMessage
/--info: some "expected 'convert', 'evolve', or 'verify' at '-l'"-/
#guard_msgs in #eval sns.parser.run "--algorithm batcher 16 -l nw.txt" |>.errorMessage
/--info: some "expected '--algorithm' or '--load' at 'convert'"-/
#guard_msgs in #eval sns.parser.run "convert --format svg" |>.errorMessage

-- def Cli.Program.Parser.Output.toAction (s : SubstringTree) :
