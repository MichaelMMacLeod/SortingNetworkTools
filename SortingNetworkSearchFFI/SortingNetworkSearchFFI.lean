@[extern c inline "#1 >> #2"]
protected def UInt64.uShiftRight8 (lhs : UInt64) (rhs : UInt8) (h : rhs < 64 := by grind) : UInt64 :=
  lhs >>> rhs.toUInt64

@[extern c inline "#1 << #2"]
protected def UInt64.uShiftLeft8 (lhs : UInt64) (rhs : UInt8) (h : rhs < 64 := by grind) : UInt64 :=
  lhs <<< rhs.toUInt64
