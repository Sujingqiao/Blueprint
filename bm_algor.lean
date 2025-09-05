import Init.Data.String.Basic
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace BoyerMoore

-- 坏字符表
def badCharacterTable (pattern : String) : HashMap Char Nat :=
  let m := pattern.length
  let mut table := HashMap.empty
  for i in [:m] do
    table := table.insert (pattern.get? i).get! (max 1 (m - i - 1))
  table

-- 好后缀表
def goodSuffixTable (pattern : String) : Array Nat :=
  let m := pattern.length
  let mut f : Array Nat := mkArray (m + 1) 0
  let mut s : Array Nat := mkArray (m + 1) 0
  
  -- Step 1: Compute f and s
  let mut i := m
  let mut j := m + 1
  f := f.set! i j
  while i > 0 do
    while j ≤ m ∧ (pattern.get? (i - 1)).get! ≠ (pattern.get? (j - 1)).get! do
      if (s.get! j) = 0 then
        s := s.set! j (j - i)
      j := f.get! j
    i := i - 1
    j := j - 1
    f := f.set! i j

  -- Step 2: Process the suffixes
  j := f.get! 0
  for i in [:m+1] do
    if (s.get! i) = 0 then
      s := s.set! i j
    if i = j then
      j := f.get! j

  s

-- Boyer-Moore 算法
def boyerMoore (text pattern : String) : List Nat :=
  let n := text.length
  let m := pattern.length
  if m > n then
    []
  else
    let badChar := badCharacterTable pattern
    let goodSuffix := goodSuffixTable pattern
    
    let rec findMatches (matches : List Nat) (i : Nat) : List Nat :=
      if i > n - m then
        matches
      else
        let mut j := m - 1
        while j ≥ 0 ∧ (pattern.get? j).get! = (text.get? (i + j)).get! do
          j := j - 1
        
        if j < 0 then
          findMatches (i :: matches) (i + if i + m < n then goodSuffix.get! 0 else 1)
        else
          let badShift := badChar.findD (text.get? (i + j)).get! m
          let goodShift := goodSuffix.get! (j + 1)
          findMatches matches (i + max badShift goodShift)
    
    findMatches [] 0

end BoyerMoore

-- 示例
#eval BoyerMoore.boyerMoore "HERE IS A SIMPLE EXAMPLE" "EXAMPLE"
