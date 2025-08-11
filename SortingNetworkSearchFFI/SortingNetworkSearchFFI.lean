@[extern "uShr64x8"]
opaque uShr64x8 : UInt64 → UInt8 → UInt64

@[extern "uShl64x8"]
opaque uShl64x8 : UInt64 → UInt8 → UInt64

instance : HShiftRight UInt64 UInt8 UInt64 where
  hShiftRight := uShr64x8

instance : HShiftLeft UInt64 UInt8 UInt64 where
  hShiftLeft := uShl64x8
