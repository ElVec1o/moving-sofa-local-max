import MovingSofa

open MovingSofa

def main : IO Unit := do
  let v : Vec2 := ⟨1.0, 0.0⟩
  let r := rot 0.0 v
  IO.println s!"rot(0)·(1,0) = ({r.x}, {r.y})  -- should be (1, 0)"
  let p := perp ⟨1.0, 0.0⟩
  IO.println s!"perp(1,0) = ({p.x}, {p.y})  -- should be (0, 1)"
  IO.println "MovingSofa Lean skeleton compiled successfully."
