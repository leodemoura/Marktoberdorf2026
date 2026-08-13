import Imp.Basic

/-! # A fuel-based interpreter

`BigStep` is a relation; it specifies behavior but does not compute.
This small interpreter lets you *run* Imp programs (`#eval`, `#guard`)
before you verify them. `fuel` bounds the number of loop iterations, so
the function is total; `none` means "out of fuel". Loop invariant
annotations are ignored, like in `BigStep`.
-/

def Stmt.run (s : Stmt) (σ : State) (fuel : Nat) : Option State :=
  match s, fuel with
  | .skip, _ => some σ
  | .assign x e, _ => some (σ.set x (e.eval σ))
  | .seq s₁ s₂, fuel => (s₁.run σ fuel).bind (s₂.run · fuel)
  | .ite c s₁ s₂, fuel =>
    if c.eval σ then s₁.run σ fuel else s₂.run σ fuel
  | .whileDo _ _ _, 0 => none
  | .whileDo c inv body, fuel + 1 =>
    if c.eval σ then (body.run σ fuel).bind ((Stmt.whileDo c inv body).run · fuel)
    else some σ
termination_by (fuel, s)

/-- Run a program from the all-zero initial state and read one variable. -/
def Stmt.runGet (s : Stmt) (x : String) (fuel : Nat := 1000) : Option Int :=
  (s.run State.init fuel).map (·.get x)
