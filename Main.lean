import LeanQuorum.Checker
import LeanQuorum.Threshold

open LeanQuorum

def main : IO UInt32 := do
  IO.println "LEAN QUORUM | certified voting safety"
  IO.println "------------------------------------"
  for (n, f) in [(4, 1), (7, 2), (10, 3), (6, 2)] do
    let q := minimumSafeThreshold n f
    IO.println s!"n={n}, f={f}: minimum safe quorum={q}, available={decide (q + f ≤ n)}"
  IO.println ""
  IO.println s!"4 validators, 1 fault, threshold 3: {checkSafety (Finset.range 4) 3 {0}}"
  IO.println s!"3 validators, 1 fault, threshold 2: {checkSafety (Finset.range 3) 2 {0}}"
  IO.println ""
  IO.println "Exhaustive quorum-pair regression sweep (n = 0..7)..."
  let mut configurations := 0
  for n in List.range 8 do
    for f in List.range (n + 1) do
      for q in List.range (n + 2) do
        let actual := checkSafety (Finset.range n) q (Finset.range f)
        let predicted := decide (n + f < q + q)
        if actual != predicted then
          IO.eprintln s!"FAIL: n={n}, f={f}, q={q}, checked={actual}, formula={predicted}"
          return 1
        configurations := configurations + 1
  IO.println s!"PASS: {configurations} configurations; every quorum pair checked."
  IO.println "This finite sweep supplements the universal Lean theorems."
  return 0
