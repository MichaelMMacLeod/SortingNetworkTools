import Std.Data.HashSet
import Lean

/-
The zero-one principle states that a sorting network with n channels
is correct if it correctly sorts all 2^n arrays of zeros and ones.

For efficiency, instead of sorting arrays of zeros and ones, we sort
the zeros and ones inside the binary representation of unsigned
integers. This reduces the problem to checking our network correctly
sorts the zeros and ones in all 2^n unsigned integers. (we also pack
these test cases together so we can do 64 of them in parallel using
bitwise operations, see TestPack.lean for how.)

It is advantageous to test these integers in a random order so as to
more quickly rule out incorrect networks which may succeed on several
adjacent integers. One way to do this would be to put all 2^n integers
in an array and then shuffle it. Unfortunately, the memory requirement
for storing 2^n integers quickly makes this strategy infeasible.

Instead, we use a maximal linear feedback shift register (maximal
LFSR): a pseudorandom number generator which only repeats after it has
generated every single integer in the range 2^n (except for zero). We
don't care about zero because its bits (all zero) are already in
sorted order, so even incorrect networks will 'sort it correctly'.

For more on LFSRs, see https://en.wikipedia.org/wiki/Linear-feedback_shift_register
-/

-- From https://www.partow.net/programming/polynomials/primitive_polynomials_GF2.txt
-- (excluding the extra `1` at the end of each of them)
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

def mkLFSR (coefficients : Array UInt64) : UInt64 → UInt64 :=
  let numBitsSub1 := coefficients[0]! - 1
  let trailingCoefficients := coefficients.drop 1
  fun state =>
    let bit : UInt64 :=
      (1 : UInt64) &&&
      trailingCoefficients.foldl
       (init := state)
       fun acc coefficient =>
         acc ^^^ (state >>> coefficient)
    state >>> 1 ||| bit <<< numBitsSub1

def LFSRArray : Array (UInt64 → UInt64) := coefficients.map (·.map (·.toUInt64)) |>.map (mkLFSR ·)

def LFSR.rand (size : USize) (seed : UInt64) : UInt64 :=
  LFSRArray[size - 2]! seed
