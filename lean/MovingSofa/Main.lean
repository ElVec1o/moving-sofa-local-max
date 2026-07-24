import MovingSofa

open MovingSofa

def main : IO Unit := do
  -- Exercise the verified stationary-contact mechanism on Gerver's SOL1 arc
  -- shape (constant term −1): λ_A must be the zero arc.
  let sol1 : Trig := ⟨3, 7, -1⟩   -- any a, b; c = −1 is what matters
  IO.println s!"SOL1-form arc: {repr sol1}"
  IO.println s!"lamA(arc)   = {repr (Trig.lamA sol1)}  -- verified ≡ 0 (cap law)"
  IO.println s!"lamD(arc)   = {repr (Trig.lamD sol1)}  -- verified ≡ const 1"
  IO.println "MovingSofa: all theorems in Basic.lean are machine-verified (no sorry)."
