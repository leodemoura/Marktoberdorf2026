/-
Solutions for Lecture 2, with notes.
-/

/-! ## 1. Your own lists -/

inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)

namespace MyList

def length : MyList α → Nat
  | nil => 0
  | cons _ xs => xs.length + 1

def append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | cons x xs, ys => cons x (xs.append ys)

#guard ((cons 1 (cons 2 nil)).append (cons 3 nil)).length = 3

def map (f : α → β) : MyList α → MyList β
  | nil => nil
  | cons x xs => cons (f x) (xs.map f)

def reverse : MyList α → MyList α
  | nil => nil
  | cons x xs => xs.reverse.append (cons x nil)

/-- Note: the induction is on `xs` because `append` recurses on its
*first* argument — always induct on the argument the function recurses
on. After `simp` uses the induction hypothesis, what is left is
arithmetic (`+ 1` reassociation), which `lia` closes. -/
theorem length_append (xs ys : MyList α) :
    (xs.append ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [append, length]
  | cons x xs ih => simp [append, length, ih]; lia

theorem map_map (f : α → β) (g : β → γ) (xs : MyList α) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

theorem append_nil (xs : MyList α) : xs.append nil = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

theorem append_assoc (xs ys zs : MyList α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

theorem reverse_append (xs ys : MyList α) :
    (xs.append ys).reverse = ys.reverse.append xs.reverse := by
  induction xs with
  | nil => simp [append, reverse, append_nil]
  | cons x xs ih => simp [append, reverse, ih, append_assoc]

/-- Note the structure of this development: `reverse_reverse` needs
`reverse_append`, which needs `append_assoc` and `append_nil`. Finding
that lemma chain — not the individual proofs — is the actual work.
Each helper is a good `simp` lemma; that is not an accident, it is what
makes the final proofs one-liners. -/
theorem reverse_reverse (xs : MyList α) : xs.reverse.reverse = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reverse, reverse_append, ih, append]

end MyList

/-! ## 2. Structures and type classes -/

structure Vec2 where
  x : Int
  y : Int
  deriving Repr

instance : Add Vec2 where
  add v w := ⟨v.x + w.x, v.y + w.y⟩

#guard (Vec2.mk 1 2 + Vec2.mk 3 4).x = 4

instance : ToString Vec2 where
  toString v := s!"({v.x}, {v.y})"

#guard toString (Vec2.mk 1 2) = "(1, 2)"

theorem Vec2.add_eq (v w : Vec2) : v + w = ⟨v.x + w.x, v.y + w.y⟩ :=
  rfl

/-- Note: `Vec2.add_eq` is the same design as `mkAdd_eval` in the next
section — one `rfl` lemma characterizing a definition, so no proof ever
has to look inside the `Add` instance (`+` is notation backed by
instance search, and automation does not unfold instances on its own).
After rewriting with it, injectivity of `Vec2.mk` and commutativity of
`Int` addition are routine for `grind` — no destructuring needed. -/
theorem Vec2.add_comm (v w : Vec2) : v + w = w + v := by
  simp only [Vec2.add_eq]
  grind

/-! ## 3. The state monad -/

/-- Note: `return s` ends the `do` block with the *old* value, read
before the increment — order matters in a monad, and that is the point:
`do` makes the state-threading invisible but not ambiguous. Unfolded,
`tick` is the pure function `fun s => (s, s + 1)`. -/
def tick : StateM Nat Nat := do
  let s ← get
  set (s + 1)
  return s

#guard (tick.run 5).run = (5, 6)
#guard ((tick >>= fun _ => tick).run 0).run = (1, 2)

/-- Note: the state is a pair, and `modify` takes any pure function of
the state — pattern-matching lambdas included. Compare the `bind` of
`StateM` on the slides: all the plumbing is already written. -/
def swapPair : StateM (Nat × Nat) Unit := do
  modify fun (a, b) => (b, a)

#guard (swapPair.run (1, 2)).run = ((), (2, 1))

/-! ## 4. An expression language -/

def State := String → Int

def State.init : State := fun _ => 0

def State.get (σ : State) (x : String) : Int := σ x

def State.set (σ : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else σ y

/-- Note: unfolding `State.get` and `State.set` leaves
`(if x = x then v else σ x) = v`, and `simp` closes the `if` by
reflexivity. Registered `@[simp]` here — and `[grind =]` in
Lecture 3 — so state bookkeeping is automatic from now on. -/
@[simp] theorem State.get_set_same (σ : State) (x : String) (v : Int) :
    (σ.set x v).get x = v := by
  simp [State.get, State.set]

/-- Note: this time the hypothesis `h : y ≠ x` decides the `if`;
passing it to `simp` finishes. Together the two laws say a state
behaves exactly like a map — which is everything Lecture 4's `grind`
proofs will need to know about it. -/
@[simp] theorem State.get_set_ne (σ : State) (x y : String) (v : Int)
    (h : y ≠ x) : (σ.set x v).get y = σ.get y := by
  simp [State.get, State.set, h]

inductive Expr where
  | const (n : Int)
  | var   (x : String)
  | add   (a b : Expr)
  | mul   (a b : Expr)
  deriving Repr, BEq

namespace Expr

def eval (σ : State) : Expr → Int
  | const n => n
  | var x   => σ.get x
  | add a b => a.eval σ + b.eval σ
  | mul a b => a.eval σ * b.eval σ

/-- Smart constructor for `add`: applies the identity rules. -/
def mkAdd : Expr → Expr → Expr
  | const 0, b => b
  | a, const 0 => a
  | a, b => add a b

/-- Smart constructor for `mul`: applies the identity and zero rules. -/
def mkMul : Expr → Expr → Expr
  | const 1, b => b
  | a, const 1 => a
  | const 0, _ => const 0
  | _, const 0 => const 0
  | a, b => mul a b

def optimize : Expr → Expr
  | const n => const n
  | var x   => var x
  | add a b => mkAdd a.optimize b.optimize
  | mul a b => mkMul a.optimize b.optimize

#guard (add (const 0) (var "x")).optimize == var "x"
#guard (mul (const 1) (add (var "x") (const 0))).optimize == var "x"

theorem mkAdd_eval (a b : Expr) (σ : State) :
    (mkAdd a b).eval σ = a.eval σ + b.eval σ := by
  unfold mkAdd
  split <;> simp [eval] <;> lia

theorem mkMul_eval (a b : Expr) (σ : State) :
    (mkMul a b).eval σ = a.eval σ * b.eval σ := by
  unfold mkMul
  split <;> simp [eval]

/-- Note: this is where the smart-constructor design pays off. Because
`mkAdd_eval`/`mkMul_eval` characterize the smart constructors once and
for all, the main proof never has to case-split on whether a rewrite
fired — each induction case is a single `simp`. Proving this without the
helper lemmas means a nested case analysis in every branch. Structuring
definitions so that each function gets its own small lemma is the single
most useful proof-engineering habit. -/
theorem optimize_correct (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb => simp [optimize, mkAdd_eval, eval, iha, ihb]
  | mul a b iha ihb => simp [optimize, mkMul_eval, eval, iha, ihb]

/-- Note: `fun_induction` gives an induction principle following the
definition of `optimize`. The `.eq_def` lemmas give `grind` the full
match-equations for the smart constructors, so it can perform the case
analysis on the match arms itself; with just `[mkAdd, mkMul]` it only
sees the fallback equations and fails. -/
theorem optimize_idempotent (e : Expr) : e.optimize.optimize = e.optimize := by
  fun_induction optimize <;> grind [optimize, mkAdd.eq_def, mkMul.eq_def]

end Expr

/-! ## 5. Verifying an optimized implementation -/

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

def sumToTR (n : Nat) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc => go n (acc + (n + 1))

/-- The generalized invariant: the accumulator is just added at the end.

Note: proving `sumToTR.go n 0 = sumTo n` directly fails — the induction
hypothesis is then only about `acc = 0`, but the recursive call changes
the accumulator. `generalizing acc` quantifies the induction hypothesis
over *all* accumulators, which is what the recursion actually needs.
"Strengthen the statement until the induction goes through" is the
fundamental trick of verifying accumulator/tail-recursive code, and it
reappears in Lecture 4 for loop invariants. -/
theorem sumToTR_go (n acc : Nat) : sumToTR.go n acc = sumTo n + acc := by
  induction n generalizing acc with
  | zero => simp [sumToTR.go, sumTo]
  | succ n ih => simp [sumToTR.go, sumTo, ih]; lia

theorem sumToTR_eq (n : Nat) : sumToTR n = sumTo n := by
  simp [sumToTR, sumToTR_go]
