import SortingNetworkSearch.ExtraTheorems
import SortingNetworkSearch.LFSR
import SortingNetworkSearch.UInt64Extras

@[grind]
structure pack.h (size : USize) (src dest : Array UInt64) where
  size_src_lt_size_USize : src.size < USize.size := by grind
  -- size_dest_lt_size_USize : dest.size < USize.size := by grind
  usize_src_eq_64 : src.usize = 64 := by grind
  usize_dest_eq_size : dest.usize = size := by grind

/--
Packs the bits of each element of `src` into `dest` like so:
```
src  [0b0000,
      0b0001,
      0b0010,
      0b0011,
      0b0100,
      0b0101,
      0b0110,
      0b0111, ------------------------\
      0b1000,                          \
      0b1001,                           \
      0b1010,                            \
      0b1011,                            |
      0b1100,                            |
      0b1101,                            |
      0b1110,                            |
      0b1111, ...]                       v

dest [0b0000000000000000000000000000000000000000000000001010101010101010,
      0b0000000000000000000000000000000000000000000000001100110011001100,
      0b0000000000000000000000000000000000000000000000001111000011110000,
      0b0000000000000000000000000000000000000000000000001111111100000000]
```
-/
@[inline]
partial def pack
    (src : Array UInt64)
    (dest : Subtype (pack.h size src ·))
    : Subtype (pack.h size src ·) :=
  let rec loop1
      (dest : Subtype (pack.h size src ·))
      (bitIdx : USize)
      : Subtype (pack.h size src ·) :=
    if h : bitIdx < 64 then
      let rec loop2
          (dest : Subtype (pack.h size src ·))
          (testCaseIdx : USize)
          : Subtype (pack.h size src ·) :=
        if h : testCaseIdx < src.usize ∧ testCaseIdx < dest.val.usize then
          let bitIdx64 := bitIdx.toUInt64
          let bit := 1 &&& src.uget bitIdx (by grind) >>> testCaseIdx.toUInt64
          let dest := dest.val.uset
            testCaseIdx
            ((dest.val.uget testCaseIdx (by grind) &&& ~~~(1 <<< bitIdx64))
              ||| (bit <<< bitIdx64))
            (by grind)
          loop2 ⟨dest, by grind⟩ (testCaseIdx + 1)
        else dest
      let dest := loop2 dest ⟨0, by grind⟩
      loop1 dest (bitIdx + 1)
    else dest
  loop1 dest 0

@[grind]
structure TestPack.mkRandom.h (size : USize) (src dest : Array UInt64) where
  size_src_lt_size_USize : src.size < USize.size := by grind
  usize_src_eq_64 : src.usize = 64 := by grind
  usize_dest_eq_size : dest.usize = size := by grind

/--
Returns `64` random tests (numbers whose binary representation uses no more than `size` bits)
packed into a `Array UInt64` whose size is `size`.
-/
partial def TestPack.mkRandom
    (size : USize)
    (dest : Array UInt64)
    (src : Subtype (TestPack.mkRandom.h size · dest))
    (seed : UInt64)
    : Array UInt64 × UInt64 /- result.fst.usize = size, result.snd is the new seed -/ :=
  let rec loop
      (testCase : USize)
      (src : Subtype (TestPack.mkRandom.h size · dest))
      (seed : UInt64)
      : Array UInt64 × UInt64 :=
    if h : testCase < 64 then
      let src := src.val.uset testCase seed (by grind)
      let seed := LFSR.rand64 size seed
      if seed = 1 then
        (src, seed)
      else loop (testCase + 1) ⟨src, by grind⟩ seed
    else (src, seed)
  let (src, seed) := loop 0 src seed
  if h : src.size < USize.size ∧ src.usize = 64 ∧ dest.usize = size then
    let dest := pack src ⟨dest, show pack.h size src dest by grind⟩
    (dest, seed)
  else panic! "invariant violated: pack.h"

/-- Returns the number of tests in `testPack` that are not in sorted order. -/
partial def TestPack.countFailures (testPack : Array UInt64) : UInt64 :=
  let rec loop (i : USize) (acc : UInt64) : UInt64 :=
    if i + 1 < testPack.usize then
      let acc := acc ||| testPack[i]! &&& ~~~testPack[i + 1]!
      loop (i + 1) acc
    else acc
  loop 0 0 |>.countSetBits
