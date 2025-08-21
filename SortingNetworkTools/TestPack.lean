import SortingNetworkTools.ExtraTheorems
import SortingNetworkTools.LFSR
import SortingNetworkTools.UInt64Extras
import SortingNetworkTools.BinaryVisualization

def TestPack.starter : Array UInt64 := #[
  0b1010101010101010101010101010101010101010101010101010101010101010,
  0b1100110011001100110011001100110011001100110011001100110011001100,
  0b1111000011110000111100001111000011110000111100001111000011110000,
  0b1111111100000000111111110000000011111111000000001111111100000000,
  0b1111111111111111000000000000000011111111111111110000000000000000,
  0b1111111111111111111111111111111100000000000000000000000000000000,
]

def TestPack.additions : Array UInt64 := #[
  0b0000000000000000000000000000000000000000000000000000000000000000,
  0b1111111111111111111111111111111111111111111111111111111111111111,
]

def USize.ithBit (u : USize) (i : USize) : USize :=
  (u &&& (1 <<< i)) >>> i

def TestPack.nth (size : USize) (n : USize) (dest : Array UInt64) : Array UInt64 := Id.run do
  let mut dest := dest
  for h : i in [0:6] do
    dest := dest.set! i TestPack.starter[i]
  for h : i in [6:size.toNat] do
    let v := n.ithBit (i - 6).toUSize
    dest := dest.set! i TestPack.additions[v]!
  dest

def TestPack.mkRandom
    (size : USize)
    (dest : Array UInt64)
    (seed : UInt64)
    : Array UInt64 × UInt64 :=
  if size ≤ TestPack.starter.usize then
    (TestPack.starter.take size.toNat, 1)
  else
    let n := LFSR.rand (size - TestPack.starter.usize) seed
    let dest := TestPack.nth size n.toUSize dest
    let seed := n
    (dest, seed)

@[grind]
structure TestPack.compareAndSwap.h (vals : Array UInt64) (a b : USize) where
  size_vals_lt : vals.size < USize.size := by grind
  a_lt_vals_usize : a < vals.usize := by grind
  b_lt_vals_usize : b < vals.usize := by grind

/--
Performs `64` compare-and-swap operations between channels `a` and `b` in parallel.
```
           ╭──────────── 64 tests (only using 16) ────────────────────────╮
input:  [0b0000000000000000000000000000000000000000000000001010101010101010, channel 0
         0b0000000000000000000000000000000000000000000000001100110011001100, channel 1
         0b0000000000000000000000000000000000000000000000001111000011110000, channel 2
         0b0000000000000000000000000000000000000000000000001111111100000000] channel 3

... compare-and-swap channels 0 and 1 of all 64 tests ...

output: [0b0000000000000000000000000000000000000000000000001000100010001000, channel 0
         0b0000000000000000000000000000000000000000000000001110111011101110, channel 1
         0b0000000000000000000000000000000000000000000000001111000011110000, channel 2
         0b0000000000000000000000000000000000000000000000001111111100000000] channel 3
```
-/
def TestPack.compareAndSwap
    (a b : USize)
    (testPack : Subtype (compareAndSwap.h · a b) )
    : Array UInt64 :=
  have : a.toNat < testPack.val.size := by grind
  have : b.toNat < testPack.val.size := by grind
  let tmp := testPack.val[a]
  let testPack := testPack.val.uset a (tmp &&& testPack.val[b]) (by grind)
  let testPack := testPack.uset b (tmp ||| testPack[b]'(by grind)) (by grind)
  testPack

@[grind =]
theorem TestPack.compareAndSwap_size_eq
    (a b : USize)
    (vals : Subtype (compareAndSwap.h · a b))
    : (TestPack.compareAndSwap a b vals).size = vals.val.size := by
  simp [TestPack.compareAndSwap]

/-- Returns the number of tests in `testPack` that are not in sorted order. -/
partial def TestPack.countFailures (testPack : Array UInt64) : UInt64 :=
  let rec loop (i : USize) (acc : UInt64) : UInt64 :=
    if i + 1 < testPack.usize then
      let acc := acc ||| testPack[i]! &&& ~~~testPack[i + 1]!
      loop (i + 1) acc
    else acc
  loop 0 0 |>.countSetBits
