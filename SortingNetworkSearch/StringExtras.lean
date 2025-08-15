def String.parseLeadingNat (s : String) : Option (Nat × String) := Id.run do
  let mut resultStr := ""
  let mut s := s.trimLeft
  while 0 < s.length ∧ (s.get 0).isDigit do
    resultStr := resultStr.push (s.get 0)
    s := s.drop 1
  resultStr.toNat?.map (·, s)

def String.parseLeadingChar (c : Char) (s : String) : Option String :=
  let s := s.trimLeft
  if s.get 0 = c then
    some (s.drop 1)
  else
    none
