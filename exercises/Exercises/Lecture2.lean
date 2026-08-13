/-
Lecture 2 — Inductive types, type classes, first program proofs.

Replace each `sorry`. Exercises get harder as you go; *(harder)* ones are
optional. Useful tactics: `induction`, `simp`, `lia`, `fun_induction`,
`grind`.
-/

/-! ## 1. Your own lists

We define lists from scratch to practice inductive types. (Lean's builtin
`List` is defined exactly like this.) -/

inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)

namespace MyList

/-- The length of a list. -/
def length : MyList α → Nat
  | nil => 0
  | cons _ xs => xs.length + 1

/-- Append two lists. -/
def append : MyList α → MyList α → MyList α := sorry

-- #guard ((cons 1 (cons 2 nil)).append (cons 3 nil)).length = 3

/-- Apply `f` to every element. -/
def map (f : α → β) : MyList α → MyList β := sorry

/-- Reverse a list. Use `append`. -/
def reverse : MyList α → MyList α := sorry

/-- The length of an append is the sum of the lengths.
Hint: induction on `xs`, then `simp [append, length]` and `lia` — or try
`grind [append, length]`. -/
theorem length_append (xs ys : MyList α) :
    (xs.append ys).length = xs.length + ys.length := by
  sorry

/-- Mapping twice is mapping the composition. -/
theorem map_map (f : α → β) (g : β → γ) (xs : MyList α) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  sorry

/-- *(harder)* Reversing distributes over append, contravariantly.
You will need `append_assoc` and `append_nil` — state and prove them
first. -/
theorem reverse_append (xs ys : MyList α) :
    (xs.append ys).reverse = ys.reverse.append xs.reverse := by
  sorry

/-- *(harder)* Reversing twice is the identity. Use `reverse_append`. -/
theorem reverse_reverse (xs : MyList α) : xs.reverse.reverse = xs := by
  sorry

end MyList

/-! ## 2. Structures and type classes -/

structure Vec2 where
  x : Int
  y : Int
  deriving Repr

/-- Componentwise addition. After this instance, `v + w` works. -/
instance : Add Vec2 where
  add v w := sorry

-- #guard (Vec2.mk 1 2 + Vec2.mk 3 4).x = 4

/-- Make `#eval` print `Vec2` values as `(x, y)`. -/
instance : ToString Vec2 where
  toString v := sorry

-- #eval toString (Vec2.mk 1 2)  -- expected: "(1, 2)"

/-- Addition of vectors is commutative. Hint: first state a helper
theorem `Vec2.add_eq : v + w = ⟨v.x + w.x, v.y + w.y⟩` — it is `rfl`,
and it saves every proof from looking inside the `Add` instance. Then
`simp only [Vec2.add_eq]` exposes the components, and `grind`
finishes. -/
theorem Vec2.add_comm (v w : Vec2) : v + w = w + v := by
  sorry

/-! ## 3. The state monad

`StateM S α` is mutable state as a *pure function*: a program is a
function from the initial state to the result paired with the final
state (`S → α × S`). `get` reads the state, `set` writes it,
`modify f` applies `f` to it, and `(x.run s₀).run` runs the program —
plain function application. (The second `.run` peels off the trivial
`Id` monad: the library's `StateM S` is `StateT S Id`, the same
function type with a generalization hook.) Lecture 4 verifies programs written in exactly
this style. -/

/-- `tick` returns the current counter value and increments the
counter. Use `get` and `set` (or `modify`); `return` gives back the old
value. Uncomment the `#guard`s when your definition is complete — the
second one shows two `tick`s in sequence, with the state threaded
between them. -/
def tick : StateM Nat Nat := do
  sorry

-- #guard (tick.run 5).run = (5, 6)
-- #guard ((tick >>= fun _ => tick).run 0).run = (1, 2)

/-- `swapPair` swaps the two components of the state. One `modify` with
a pure function is enough — no field-by-field plumbing. -/
def swapPair : StateM (Nat × Nat) Unit := do
  sorry

-- #guard (swapPair.run (1, 2)).run = ((), (2, 1))

/-! ## 4. An expression language

A tiny language of arithmetic expressions with variables — the seed of
what we do in Lecture 4. Variables live in a `State`, the total-map API
from the slides. Its two laws are your first exercises here; they
reappear as `grind` annotations in Lecture 3, and Lecture 4's verifier
runs on them. -/

def State := String → Int

def State.init : State := fun _ => 0

def State.get (σ : State) (x : String) : Int := σ x

def State.set (σ : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else σ y

/-- Reading a variable you just wrote gives the written value.
Hint: `simp [State.get, State.set]` unfolds both; what remains is an
`if` on `x = x`, which `simp` closes. The `@[simp]` attribute registers
the lemma so later proofs rewrite with it automatically — this is the
"design your simp lemmas" habit from the slides. -/
@[simp] theorem State.get_set_same (σ : State) (x : String) (v : Int) :
    (σ.set x v).get x = v := by
  sorry

/-- Reading a *different* variable is unaffected by a write.
Hint: same unfolding; this time the hypothesis `h` decides the `if`
(pass it to `simp`). -/
@[simp] theorem State.get_set_ne (σ : State) (x y : String) (v : Int)
    (h : y ≠ x) : (σ.set x v).get y = σ.get y := by
  sorry

inductive Expr where
  | const (n : Int)
  | var   (x : String)
  | add   (a b : Expr)
  | mul   (a b : Expr)
  deriving Repr, BEq

namespace Expr

/-- Evaluate an expression, reading variables from the state. -/
def eval (σ : State) : Expr → Int
  | const n => n
  | var x   => σ.get x
  | add a b => a.eval σ + b.eval σ
  | mul a b => a.eval σ * b.eval σ

/--
A simple optimizer: recursively rewrite `0 + e` to `e`, `e + 0` to `e`,
`1 * e` to `e`, `e * 1` to `e`, and `0 * e` and `e * 0` to `0`.

Hint: recurse first, then fix up the result with a `match`. It pays off to
define a helper "smart constructor" `mkAdd : Expr → Expr → Expr` (and
`mkMul`) that performs the fix-up.
-/
def optimize : Expr → Expr := sorry

-- #guard (add (const 0) (var "x")).optimize == var "x"
-- #guard (mul (const 1) (add (var "x") (const 0))).optimize == var "x"

/-- The optimizer does not change the meaning of an expression.

Hint: if you followed the hint above, prove a lemma about each smart
constructor first (e.g. `(mkAdd a b).eval σ = a.eval σ + b.eval σ`).
Then this proof is an induction where every case is `simp` — or
`fun_induction optimize <;> grind [eval]`. -/
theorem optimize_correct (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  sorry

/-- *(harder)* The optimizer is idempotent: optimizing twice is the same as
optimizing once. -/
theorem optimize_idempotent (e : Expr) : e.optimize.optimize = e.optimize := by
  sorry

end Expr

/-! ## 5. Verifying an optimized implementation *(harder)*

`sumTo n = 0 + 1 + ⋯ + n`, written naively, and then with an accumulator
(tail-recursively, the way a compiler would like it). Prove they agree.

This is the pattern behind verifying any optimized reimplementation:
find the *generalized* invariant that makes the induction go through.
-/

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

def sumToTR (n : Nat) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc => go n (acc + (n + 1))

/-- Hint: do NOT attack this directly. First state and prove the invariant
of `go` by induction on `n`, generalizing `acc`:
`sumToTR.go n acc = sumTo n + acc`. -/
theorem sumToTR_eq (n : Nat) : sumToTR n = sumTo n := by
  sorry
