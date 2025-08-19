import SortingNetworkSearch.Action

structure Error where
  unexpected : Substring
  expected : Array String
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

-- def Parser.Result.idk (r : Except Error (α × Substring)) : Except String α :=


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

def word : Parser Substring := ws >> token

def symbol (str : String) : Parser Substring := fun s => do
  let startPos := s.startPos
  let (a, s) ← word s
  let endPos := s.startPos
  if str.toSubstring == a
  then .ok (a, s)
  else .error { unexpected := Substring.mk s.str startPos endPos, expected := #[str] }

def Parser.map (p : Parser α) (f : α → β) : Parser β := do
  let a ← p
  pure (f a)

def bubble : Dep Algorithm := .opt { parse := symbol "bubble" |>.map fun _ => .bubble }
def batcher : Dep Algorithm := .opt { parse := symbol "batcher" |>.map fun _ => .batcher }
def empty : Dep Algorithm := .opt { parse := symbol "empty" |>.map fun _ => .empty }

def Parser.nat : Parser Nat := do
  let sp ← startPos
  let w ← word
  let ep ← startPos
  if let some n := w.toNat?
  then pure n
  else do
    let s ← input
    let unexpected := Substring.mk s sp ep
    fun _ => .error { unexpected, expected := #["a natural number"] }

-- def Parser.switch (cases : Array (Parser Unit × Parser α)) : Parser α :=
--   let rec loop (i : Nat) (errors : Array Error) : Parser α := fun s =>
--     if h : i < cases.size then
--       let (p₁, p₂) := cases[i]
--       match p₁ s with
--       | .error e => loop (i + 1) (errors.push e) s
--       | .ok (_, s) => p₂ s
--     else .error (errors.foldl (init := Error.unknown) (· ++ ·))
--   loop 0 (.emptyWithCapacity cases.size)

def cmd1 (f : α → x) (name : String) (d : Dep α) : Dep x :=
  .bind (.opt { parse := symbol name })
    fun _ => f <$> d

def cmd2 (f : α → β → x) (name : String) (d₁ : Dep α) (d₂ : Dep β) : Dep x :=
  .bind (.opt { parse := symbol name })
    fun _ => f <$> d₁ <*> d₂

def cmd3 (f : α → β → γ → x) (name : String) (d₁ : Dep α) (d₂ : Dep β) (d₃ : Dep γ): Dep x :=
  .bind (.opt { parse := symbol name })
    fun _ => f <$> d₁ <*> d₂ <*> d₃

def option1 (f : α → x) (name : String) (d : Dep α) : Dep x :=
  .bind (.opt { parse := symbol s!"--{name}" })
    fun _ => f <$> d

def option2 (f : α → β → x) (name : String) (d₁ : Dep α) (d₂ : Dep β) : Dep x :=
  .bind (.opt { parse := symbol s!"--{name}" })
    fun _ => f <$> d₁ <*> d₂

def Parser.usize : Parser USize := Nat.toUSize <$> Parser.nat

def size : Dep USize := .opt { parse := Parser.usize }

def algorithmFlag : Dep Substring := .opt { parse := symbol "--algorithm" }

def algo : Dep Algorithm := bubble <|> batcher <|> empty

def algorithmOption : Dep NetworkSource := option2 .algorithm "algorithm" algo size

def filePath : Dep System.FilePath := .opt { parse := (Coe.coe ∘ Substring.toString) <$> word }

def fromFile : Dep NetworkSource := NetworkSource.fromFile <$> filePath

def loadOption : Dep NetworkSource := option1 .fromFile "load" filePath

def networkSource : Dep NetworkSource := algorithmOption <|> loadOption

def list : Dep SerializationOut := .opt { parse := symbol "list" |>.map fun _ => .list }
def svg : Dep SerializationOut := .opt { parse := symbol "svg" |>.map fun _ => .svg }

def seed : Dep Nat := option1 id "seed" (.opt { parse := Parser.nat })
def timeout : Dep Nat := option1 id "timeout" (.opt { parse := Parser.nat })

def convert : Dep Action := cmd2 .convert "convert" networkSource (list <|> svg)
def evolve : Dep Action := cmd3 .evolve "evolve" (optional seed) (optional timeout) networkSource

def action : Dep Action := convert <|> evolve

-- def serializationOut : Dep SerializationOut := option1

#eval networkSource.run "--algorithm batcher 3".toSubstring
#eval networkSource.run "--load /tmp/nw.txt".toSubstring
#eval convert.run "convert --algorithm batcher 3 svg".toSubstring
#eval convert.run "convert --load /tmp/nw.txt svg".toSubstring
#eval evolve.run "evolve --seed 123 --timeout 10 --load /tmp/nw.txt".toSubstring
#eval action.run "convert --algorithm batcher 3 svg".toSubstring |>.toOption |>.get! |> fun (x, _) => x.main
#eval action.run "evolve --seed 123 --timeout 5 --algorithm empty 8".toSubstring

-- def bubble : Dep Algorithm := .satisfies (if ·.toString == "bubble" then Algorithm.bubble else none)
-- def batcher : Dep Algorithm := .satisfies (if ·.toString == "batcher" then Algorithm.batcher else none)
-- def empty : Dep Algorithm := .satisfies (if ·.toString == "empty" then Algorithm.empty else none)
-- def size : Dep USize := .satisfies (if let some n := ·.toNat? then n.toUSize else none)

-- structure DepM r where
--   runDepM : (r → Dep x) → Dep x

-- def DepM.pure (x : r) : DepM r := { runDepM := fun k => k x }
-- def DepM.bind (f : DepM α) (g : (α → DepM β)) : DepM β :=
--   { runDepM := fun k => f.runDepM (fun x => (g x).runDepM k) }

-- instance : Monad DepM where
--   pure := DepM.pure
--   bind := DepM.bind

-- def DepM.seq (dab : DepM (α → β)) (da : (Unit → DepM α)) : DepM β :=
--   dab.bind fun x1 =>
--     (da ()).bind fun x2 =>
--       pure (x1 x2)

-- instance : Applicative DepM where
--   pure := DepM.pure
--   seq := DepM.seq

-- def DepM.map (f : α → β) (d : DepM α) : DepM β :=


-- instance : Functor DepM where
--   map := DepM.map



-- class FromSubstring (α : Type) where
--   fromSubstring : Substring → Option α

-- instance : FromSubstring Nat where
--   fromSubstring := Substring.toNat?

-- -- A variable, such 'foo' in '--myOption foo'
-- structure Var (α : Type) [FromSubstring α] where


-- structure Flag where

-- structure Cmd where

-- -- inductive Dep (α : Type) [FromSubstring α] where
-- -- | symbol : String → Dep α
-- -- | nat : Dep Nat
-- -- | var : Var α → Dep α
-- -- | flag : Flag → Dep α
-- -- | cmd : Cmd → Dep α
-- -- | optional : Dep α → Dep α
-- -- | all : Array Dep → Dep α
-- -- | xor : Array Dep → Dep α

-- -- #check {x α : Type} → (x → α)

-- -- inductive Dep α where
-- -- | alt : Dep α → Dep α → Dep α
-- -- | mult {x} : Dep (x → α) → Dep x

-- inductive Dep.{u,v} : Type u → Type v where
-- -- | unsat : Dep α
-- | satisfies : (Substring → Option α) → Dep α
-- -- | optional : Dep α → Dep α
-- | app : (α → β) → Dep α → Dep β
-- | xor : Dep α → Dep α → Dep α

-- -- def Dep.idk1 (d : Dep (α → β)) (a : α) : Dep β :=
-- --   match d with
-- --   | .app f x => sorry
-- --   | _ => sorry

-- def bubble : Dep Algorithm := .satisfies (if ·.toString == "bubble" then Algorithm.bubble else none)
-- def batcher : Dep Algorithm := .satisfies (if ·.toString == "batcher" then Algorithm.batcher else none)
-- def empty : Dep Algorithm := .satisfies (if ·.toString == "empty" then Algorithm.empty else none)
-- def size : Dep USize := .satisfies (if let some n := ·.toNat? then n.toUSize else none)

-- def algorithm' : Dep (USize → NetworkSource) :=
--   .app NetworkSource.algorithm
--     (.xor bubble
--       (.xor batcher empty))

-- def algorithm : Dep NetworkSource :=
--   .app
--     algorithm'
--     size

-- def v : Dep Action :=
--   .xor
--     (app
--       Action.convert
--       ())
--     <| .xor
--       ?evolve
--       ?verify


-- -- | xor : Array (Dep α) → Dep α
-- -- | all : Array (Dep α) → Dep α

-- /-
-- - auto generate help text, inserting useful --help and -h flags everywhere necessary
-- - report informative parse errors
-- - output value of type α, user specified
-- -/

-- /-
--   cmd evolve
--   - all
--     - optional
--       - flag --timeout
--     - optional
--       - flag --seed
-- program : Action
--   cmd convert :
--   - xor
--     - flag --algorithm : ExistingNetwork
--       - optional : Algorithm
--         - var : Algorithm
--           - xor : Algorithm
--             - str batcher : Algorithm
--             - str bubble : Algorithm
--             - str empty : Algorithm
--       - var : Nat
--         - nat : Nat
--   - option --load
-- -/
