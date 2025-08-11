import Std.Data.HashSet
import Lean

-- From https://www.partow.net/programming/polynomials/primitive_polynomials_GF2.txt
-- These are the coefficients of the polynomials, excluding the constant one on the right end.
def coefficients : Array (Array Nat) := #[
  #[2, 1],
  #[3, 1],
  #[4, 1],
  #[5, 2],
  #[6, 1],
  #[7, 1],
  #[8, 4, 3, 2],
  #[9, 4],
  #[10, 3],
  #[11, 2],
  #[12, 6, 4, 1],
  #[13, 4, 3, 1],
  #[14, 8, 6, 1],
  #[15, 1],
  #[16, 9, 8, 7, 6, 4, 3, 2],
  #[17, 3],
  #[18, 5, 4, 3, 2, 1],
  #[19, 5, 2, 1],
  #[20, 3],
  #[21, 2],
  #[22, 1],
  #[23, 5],
  #[24, 7, 2, 1],
  #[25, 3],
  #[26, 6, 2, 1],
  #[27, 5, 2, 1],
  #[28, 3],
  #[29, 2],
  #[30, 23, 2, 1],
  #[31, 3],
  #[32, 22, 2, 1],
]

def mkLFSR (coefficients : Array Nat) : Nat → Nat :=
  let numBitsSub1 := coefficients[0]! - 1
  let trailingCoefficients := coefficients.drop 1
  fun state =>
    let bit : Nat :=
      1 &&&
      trailingCoefficients.foldl
       (init := state)
       fun acc coefficient =>
         acc ^^^ (state >>> coefficient)
    state >>> 1 ||| bit <<< numBitsSub1

def LFSRArray : Array (Nat → Nat) := coefficients.map (mkLFSR ·)

/--
Generates a random `Nat` using at most `size` bits and an initial `seed`. If the
output is fed back in as the seed, eventually every single `Nat` in the range
`2^size` will be produced (except for `0`).
- `seed` is a non-zero `Nat` less than `2^size`
-/
def LFSR.randNat (size : Nat) (seed : Nat) : Nat :=
  if h : size < 2 ∨ LFSRArray.size ≤ size - 2 then
    panic! s!"LFSR only implemented for 2..={LFSRArray.size + 1} sizes"
  else
    LFSRArray[size - 2] seed

def checkPeriod (f : Nat → Nat) : Nat := Id.run do
  let start := 1
  let mut i := f start
  let mut result : Nat := 1
  while i ≠ start do
    i := f i
    result := result + 1
    if result % 10000000 = 0 then
      result := dbgTraceVal result
  pure result
