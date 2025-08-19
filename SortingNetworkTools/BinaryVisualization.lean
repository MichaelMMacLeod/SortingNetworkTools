/--
Converts `n` to an array of bits, with most significant bits coming first.

Example:
* 0b100011.toBitArray = #[true, true, false, false, false, true]
-/
def Nat.toBitArray (n : Nat) : Array Bool := Id.run do
  let mut result := default
  for i in [0 : Nat.log2 n + 1] do
    result := result.push <| (n >>> i) &&& 1 = 1
  result

def Nat.bitString (n : Nat) : String := n.toBitArray.reverse.map (·.toNat) |>.foldl (· ++ ·.repr) ""

def UInt64.bitString (v : UInt64) : String := v.toNat.bitString
def USize.bitString (v : USize) : String := v.toNat.bitString
