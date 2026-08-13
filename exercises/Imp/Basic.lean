/-
Imp: a small imperative language.

This is given code for the Lecture 4 exercises. Read it top to bottom;
it is short. The language has integer-valued variables, arithmetic
expressions, boolean expressions, and the usual statements: `skip`,
assignment, sequencing, `if`, and `while`.

Loops carry an *invariant annotation*. The annotation plays no role in
the semantics — `BigStep` and the interpreter ignore it — it is
information for verification tools, exactly as in real VC generators.
-/

/-- A program state maps variable names to integer values. -/
def State : Type := String → Int

/-- The state where every variable is `0`. -/
def State.init : State := fun _ => 0

/-- Read a variable. -/
def State.get (σ : State) (x : String) : Int := σ x

/-- Update a variable. -/
def State.set (σ : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else σ y

@[simp, grind =] theorem State.get_set_same (σ : State) (x : String) (v : Int) :
    (σ.set x v).get x = v := by
  simp [State.get, State.set]

@[simp, grind =] theorem State.get_set_ne (σ : State) (x y : String) (v : Int) (h : y ≠ x) :
    (σ.set x v).get y = σ.get y := by
  simp [State.get, State.set, h]

/-- Assertions are predicates on states. Used for pre/postconditions and
loop invariants. -/
def Assertion : Type := State → Prop

/-- Arithmetic expressions. -/
inductive Expr where
  | const (n : Int)
  | var   (x : String)
  | add   (a b : Expr)
  | sub   (a b : Expr)
  | mul   (a b : Expr)
  deriving Repr

/-- Evaluating an expression in a state. -/
def Expr.eval (σ : State) : Expr → Int
  | const n => n
  | var x   => σ.get x
  | add a b => a.eval σ + b.eval σ
  | sub a b => a.eval σ - b.eval σ
  | mul a b => a.eval σ * b.eval σ

/-- Boolean expressions. -/
inductive BExpr where
  | tt
  | lt  (a b : Expr)
  | le  (a b : Expr)
  | eq  (a b : Expr)
  | not (c : BExpr)
  | and (c d : BExpr)
  deriving Repr

/-- Evaluating a boolean expression in a state. -/
def BExpr.eval (σ : State) : BExpr → Bool
  | tt      => true
  | lt a b  => a.eval σ < b.eval σ
  | le a b  => a.eval σ ≤ b.eval σ
  | eq a b  => a.eval σ == b.eval σ
  | not c   => !c.eval σ
  | and c d => c.eval σ && d.eval σ

/-- Statements. The `inv` on `whileDo` is the loop invariant annotation;
the semantics ignores it. -/
inductive Stmt where
  | skip
  | assign  (x : String) (e : Expr)
  | seq     (s₁ s₂ : Stmt)
  | ite     (c : BExpr) (s₁ s₂ : Stmt)
  | whileDo (c : BExpr) (inv : Assertion) (body : Stmt)

/--
Big-step operational semantics: `BigStep σ s σ'` means that executing the
statement `s` in the initial state `σ` terminates in the final state `σ'`.
Note that the loop invariant annotation is ignored.
-/
inductive BigStep : State → Stmt → State → Prop where
  | skip :
      BigStep σ .skip σ
  | assign :
      BigStep σ (.assign x e) (σ.set x (e.eval σ))
  | seq (h₁ : BigStep σ s₁ σ') (h₂ : BigStep σ' s₂ σ'') :
      BigStep σ (.seq s₁ s₂) σ''
  | ifTrue (hc : c.eval σ = true) (h : BigStep σ s₁ σ') :
      BigStep σ (.ite c s₁ s₂) σ'
  | ifFalse (hc : c.eval σ = false) (h : BigStep σ s₂ σ') :
      BigStep σ (.ite c s₁ s₂) σ'
  | whileTrue (hc : c.eval σ = true) (hbody : BigStep σ body σ')
      (hrest : BigStep σ' (.whileDo c inv body) σ'') :
      BigStep σ (.whileDo c inv body) σ''
  | whileFalse (hc : c.eval σ = false) :
      BigStep σ (.whileDo c inv body) σ

/--
The Hoare triple, partial correctness: if `P` holds initially and `s`
terminates, then `Q` holds in the final state.
-/
def Triple (P : Assertion) (s : Stmt) (Q : Assertion) : Prop :=
  ∀ σ σ', P σ → BigStep σ s σ' → Q σ'

/-- The *safe region* of `s`: the states from which every terminating
run of `s` establishes `Q`. Restricting a triple to a single state
unfolds to `∀ σ', BigStep σ s σ' → Q σ'` — Dijkstra's weakest liberal
precondition. -/
def Stmt.wlp (s : Stmt) (Q : Assertion) : Assertion :=
  fun σ => Triple (· = σ) s Q
