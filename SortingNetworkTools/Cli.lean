import SortingNetworkTools.Action

/-
Implements a rudimentary command line parser in the style of Paolo Capriotti & Huw Campbell's
optparse-applicative Haskell package (see https://hackage.haskell.org/package/optparse-applicative.)
-/

structure Expected where
  name : String
  description : Option String
deriving Repr, Inhabited

structure Error where
  unexpected : Substring
  expected : Array Expected
deriving Repr, Inhabited

def Error.append (e₁ e₂ : Error) : Error :=
  let s₁ := e₁.unexpected.startPos
  let s₂ := e₂.unexpected.startPos
  if s₁ < s₂
  then e₂
  else if s₂ < s₁
  then e₁
  else { e₁ with expected := e₁.expected ++ e₂.expected }

instance : Append Error where
  append := Error.append

abbrev Parser α := Substring → Except Error (α × Substring)

def Parser.bind (p : Parser α) (f : α → Parser β) : Parser β := fun s => do
  let (a, s) ← p s
  f a s

def Parser.pure (a : α) : Parser α := fun s => .ok (a, s)

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

def Parser.startPos : Parser String.Pos := fun s => .ok (s.startPos, s)
def Parser.input : Parser String := fun s => .ok (s.str, s)

def Parser.andThen (pa : Parser α) (pb : Unit → Parser β) : Parser β := do
  let _ ← pa
  let b ← pb ()
  pure b

instance : AndThen (Parser α) where
  andThen := Parser.andThen

instance : HAndThen (Parser α) (Parser β) (Parser β) where
  hAndThen := Parser.andThen

structure Opt α where
  parse : Parser α

def Opt.map (f : α → β) (o : Opt α) : Opt β :=
  { parse s := do
      let (a, s) ← o.parse s
      pure (f a, s)
  }

instance : Functor Opt where
  map := Opt.map

/--
A 'dependency'. For example, in `snt convert --algorithm <algo> <size>`, we say
that the `convert` command has a dependency on the `--algorithm <algo> <size>` option.
The `α` in `Dep α` is the type that `Dep α` will attempt to produce when it is run
(see `Dep.run`.)
-/
inductive Dep : Type u → Type (u+1) where
| nil : Option α → Dep α
| opt : Opt α → Dep α
| alt : Dep α → (Unit → Dep α) → Dep α
| mult : Dep (x → α) → (Unit → Dep x) → Dep α
| bind : Dep x → (x → Dep α) → Dep α

def Dep.map (f : α → β) : Dep α → Dep β
| nil a => .nil (f <$> a)
| opt o => .opt (f <$> o)
| alt d₁ d₂ => .alt (d₁.map f) (fun _ => (d₂ ()).map f)
| mult g dx => .mult (g.map (fun xa => f ∘ xa)) dx
| bind d xda => .bind d (fun x => (xda x).map f)

instance : Functor Dep where
  map := Dep.map

def Dep.pure (a : α) : Dep α := .nil (.some a)
def Dep.seq (d : Dep (α → β)) (da : Unit → Dep α) : Dep β := .mult d da

instance : Applicative Dep where
  pure := Dep.pure
  seq := Dep.seq

instance : Alternative Dep where
  failure := .nil none
  orElse := Dep.alt

def Dep.run (d : Dep α) (s : Substring) : Except Error (α × Substring) :=
  match d with
  | .nil (.some a) => .ok (a, s)
  | .nil .none => .error (panic! "what goes here?")
  | .opt o => o.parse s
  | .alt d₁ d₂ =>
    match d₁.run s with
    | .ok (a, s) => .ok (a, s)
    | .error e₁ =>
      match (d₂ ()).run s with
      | .ok (a, s) => .ok (a, s)
      | .error e₂ => .error (e₁ ++ e₂)
  | .mult dxa dx => do
    let (a, s) ← dxa.run s
    let (x, s) ← dx () |>.run s
    .ok (a x, s)
  | .bind dx dxa => do
    let (x, s) ← dx.run s
    dxa x |>.run s

partial def takeUntil (isStopChar : Char → Bool) : Parser Substring := fun s =>
  let (a, s) := takeUntilAux isStopChar s.startPos s
  .ok (a, s)
where
  takeUntilAux (isStopChar : Char → Bool) (startPos : String.Pos) (s : Substring) : Substring × Substring :=
    if s.isEmpty then
      (Substring.mk s.str startPos s.startPos, s)
    else
      let c := s.str.get! s.startPos
      if isStopChar c then
        (Substring.mk s.str startPos s.startPos, s)
      else
        takeUntilAux isStopChar startPos (s.drop 1)

def token : Parser Substring := takeUntil (·.isWhitespace)

def ws : Parser Substring := takeUntil (!·.isWhitespace)

def ignore (p : Parser α) : Parser Unit := fun s => do
  let (_, s) ← p s
  .ok ((), s)

def word (expected : Unit → Array Expected) : Parser (Substring) := do
  let _ ← ws
  let t ← token
  if t.startPos ≠ t.stopPos
  then pure t
  else
    fun _ => .error {
      unexpected := Substring.mk t.str t.startPos t.startPos
      expected := expected ()
    }

def symbol (str name description : String) : Parser Substring := fun s => do
  let mkExpected := fun _ => #[{ name, description := some description }]
  let (a, s) ← word mkExpected s
  let startPos := a.startPos
  let stopPos := a.stopPos
  if str.toSubstring == a
  then .ok (a, s)
  else
    .error {
      unexpected := Substring.mk s.str startPos stopPos
      expected := mkExpected ()
    }

def Parser.map (p : Parser α) (f : α → β) : Parser β := do
  let a ← p
  pure (f a)

def Parser.nat (name description : String) : Parser Nat := do
  let mkExpected := fun _ => #[{ name, description := s!"{description} (a natural number)" }]
  let w ← word mkExpected
  let sp := w.startPos
  let ep := w.stopPos
  if let some n := w.toNat?
  then pure n
  else
    let s ← input
    let unexpected := Substring.mk s sp ep
    fun _ =>
      .error {
        unexpected
        expected := mkExpected ()
      }

def Parser.boundedNat (name description : String) (loInclusive hiInclusive : Nat) : Parser Nat := do
  let mkExpected := fun _ => #[{
      name
      description := s!"{description} (a natural number in the range {loInclusive}..={hiInclusive})"
    }]
  let w ← word mkExpected
  let sp := w.startPos
  let ep := w.stopPos
  let mkError : String → Substring → Except Error (Nat × Substring) := fun s =>
    let unexpected := Substring.mk s sp ep
    fun _ =>
      .error {
        unexpected
        expected := mkExpected ()
      }
  if let some n := w.toNat? then
    if n ≥ loInclusive ∧ n ≤ hiInclusive
    then pure n
    else mkError (← input)
  else mkError (← input)

def arg (a : α) (name description : String) : Dep α := .opt { parse := symbol name s!"'{name}'" description |>.map fun _ => a }

def cmd1 (f : α → x) (name description : String) (d : Dep α) : Dep x :=
  .bind (.opt { parse := symbol name name description })
    fun _ => f <$> d

def cmd2 (f : α → β → x) (name description : String) (d₁ : Dep α) (d₂ : Dep β) : Dep x :=
  .bind (.opt { parse := symbol name name description })
    fun _ => f <$> d₁ <*> d₂

def cmd3 (f : α → β → γ → x) (name description : String) (d₁ : Dep α) (d₂ : Dep β) (d₃ : Dep γ) : Dep x :=
  .bind (.opt { parse := symbol name name description })
    fun _ => f <$> d₁ <*> d₂ <*> d₃

def option1 (f : α → x) (name description : String) (d : Dep α) : Dep x :=
  .bind (.opt { parse := symbol s!"--{name}" s!"--{name}" description })
    fun _ => f <$> d

def option2 (f : α → β → x) (name description : String) (d₁ : Dep α) (d₂ : Dep β) : Dep x :=
  .bind (.opt { parse := symbol s!"--{name}" s!"--{name}" description })
    fun _ => f <$> d₁ <*> d₂

def bubble : Dep Algorithm := arg .bubble "bubble" "bubble sort"
def batcher : Dep Algorithm := arg .batcher "batcher" "batcher odd-even mergesort"
def empty : Dep Algorithm := arg .empty "empty" "network with no comparisons (recommended option for 'snt evolve')"

def Parser.usize : Parser USize := Nat.toUSize <$> Parser.boundedNat "network size" "number of inputs to the network" 2 32

def size : Dep USize := .opt { parse := Parser.usize }

def algo : Dep Algorithm := empty <|> bubble <|> batcher

def algorithmOption : Dep NetworkSource := option2 .algorithm "algorithm" "creates a comparison network via a known method" algo size

def filePath : Dep System.FilePath := .opt { parse := (Coe.coe ∘ Substring.toString) <$> word fun _ => #[{ name := "file", description := "path to a network stored in the 'list' format" }] }

def loadOption : Dep NetworkSource := option1 .fromFile "load" "loads a comparison network stored in the 'list' format from a file" filePath

def networkSource : Dep NetworkSource := algorithmOption <|> loadOption

def list : Dep SerializationOut := .opt { parse := symbol "list" "'list'" "converts a network to a comma-separated list of compare-and-exchanges, e.g., '0:1,1:2,0:2'" |>.map fun _ => .list }
def svg : Dep SerializationOut := .opt { parse := symbol "svg" "'svg'" "converts a network to scalable vector graphics (SVG), viewable in a web browser" |>.map fun _ => .svg }

def seed : Dep Nat := option1 id "seed" "" (.opt { parse := Parser.nat "seed" "initial value for the psuedorandom number generator controling mutations" })
def timeout : Dep Nat := option1 id "timeout" "" (.opt { parse := Parser.nat "timeout" "time in seconds before terminating evolution" })

def convert : Dep Action := cmd2 .convert "convert" "translate an existing network to different formats" networkSource (list <|> svg)
def evolve : Dep Action := cmd3 .evolve "evolve" "search for better networks through repeated mutation" (optional seed) (optional timeout) networkSource
def verify : Dep Action := cmd1 .verify "verify" "exaustively test a network for correctness" networkSource

def Dep.action : Dep Action := convert <|> evolve <|> verify

open Std.Format in
def Error.fmt (programName : String) (e : Error) : Std.Format :=
  let result := programName ++ e.unexpected.str
  let result := result ++ "\n"
  let result := result.pushn ' ' (programName.length + e.unexpected.startPos.byteIdx)
  let result := result ++ "^ expected "
  let expected1 : Std.Format := joinSep (e.expected.toList.take (e.expected.size - 2) |>.map (·.name)) ", "
  let expected2 : Std.Format := joinSep (e.expected.toList.drop (e.expected.size - 2) |>.map (·.name)) " or "
  let expected1 := if expected1.isEmpty then expected1 else expected1 ++ ", "
  let result := result ++ expected1 ++ expected2
  let descriptions : List Std.Format := e.expected.toList.filterMap fun exp =>
    if let some d := exp.description
    then s!"{exp.name}: {d}"
    else none
  let descriptions : Std.Format := joinSep descriptions "\n"
  let result := result ++ if descriptions.isEmpty then "" else "\n"
  let result := result ++ descriptions
  result
