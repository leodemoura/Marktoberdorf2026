import Std.Tactic.BVDecide
/-
Solutions for Lecture 3, with notes.
-/

/-! ## 1. `simp` and rewriting -/

def double (n : Nat) : Nat := 2 * n

@[simp] theorem double_zero : double 0 = 0 := rfl

@[simp] theorem double_eq (n : Nat) : double n = 2 * n := rfl

/-- Note: `double_eq` rewrites `double` away on both sides; `+arith`
normalizes `2 * (a + b)` against `2 * a + 2 * b`. Without it, you would
pass `Nat.mul_add` to `simp` explicitly. -/
theorem double_add (a b : Nat) : double (a + b) = double a + double b := by
  simp +arith

/-! ## 2. `grind`

Notes on what `grind` is doing in each example:
1. Congruence closure: from `a = b` it merges the equivalence classes of
   `f a` and `f b` — no rewriting, just union-find on the E-graph.
2. Linear integer arithmetic (the `cutsat` solver): solves the two
   equations. Try this one by hand with `lia` after `rw` to see what
   you were spared.
3. Cooperation: the arithmetic solver derives `x + y = 4`, the equality
   flows into the E-graph, and congruence merges `f (x + y)` with `f 4`.
   Neither engine can do this alone; the E-graph is where they meet. -/

example (f : Nat → Nat) (a b c : Nat) (h₁ : a = b) (h₂ : f b = c) :
    f a = c := by
  grind

example (x y : Int) (h₁ : 2 * x + 3 * y = 7) (h₂ : 3 * x - y = 5) :
    x = 2 := by
  grind

example (f : Int → Int) (x y : Int)
    (h₁ : f (x + y) = 0) (h₂ : y = x + 2) (h₃ : x = 1) :
    f 4 = 0 := by
  grind

/-! ## 3. E-matching annotations -/

def enc (n : Nat) : Nat := n + 1
def dec (n : Nat) : Nat := n - 1

@[grind =] theorem dec_enc (n : Nat) : dec (enc n) = n := by
  unfold enc dec
  lia

/-- Note: the term `dec (enc c)` appears nowhere in this goal. E-matching
works *modulo the E-graph*: since `a = enc c` is known, the existing term
`dec a` matches the pattern `dec (enc ?n)`, the annotated equation is
instantiated to `dec (enc c) = c`, and the chain
`b = dec a = dec (enc c) = c` closes the goal. Pattern choice is the
entire craft of `[grind]` annotations — the equation is useless to
`grind` until its left-hand side can be found in the goal's terms. -/
example (a b c : Nat) (h₁ : dec a = b) (h₂ : a = enc c) : b = c := by
  grind

/-! ## 4. The proof ladder, revisited -/

-- The `State` from Lecture 2 — just what the evaluator needs.
def State := String → Int

def State.get (σ : State) (x : String) : Int := σ x

inductive Expr where
  | const (n : Int)
  | var   (x : String)
  | add   (a b : Expr)

namespace Expr

def eval (σ : State) : Expr → Int
  | const n => n
  | var x   => σ.get x
  | add a b => a.eval σ + b.eval σ

def optimize : Expr → Expr
  | const n => const n
  | var x   => var x
  | add a b =>
    match a.optimize, b.optimize with
    | const 0, b' => b'
    | a', const 0 => a'
    | a', b'      => add a' b'

/-- 1. Structural induction: we induct on the *data*, so in the `add`
case the match inside `optimize` is still unreduced and we must `split`
it ourselves, then clean up each branch. Honest, but the proof mirrors
the definition's structure only after manual work. -/
theorem optimize_correct₁ (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
    simp only [optimize]
    split <;> simp_all [eval] <;> lia

/-- 2. `fun_induction` inducts on the *definition*: one case per match
arm, with the match already split and the right induction hypotheses in
scope. The manual `split` from version 1 is gone. -/
theorem optimize_correct₂ (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  fun_induction optimize <;> simp_all [eval] <;> lia

/-- 3. Same induction, `grind` closes every case uniformly — it unfolds
`eval`, uses the induction hypotheses, and does the arithmetic. This
ladder (manual → fun_induction+simp → fun_induction+grind) is how proofs
about functions shrink as automation grows; the *statement* never
changed. -/
theorem optimize_correct₃ (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  fun_induction optimize <;> grind [eval]

end Expr

/-! ## 5. `bv_decide`

Note: `bv_decide` bit-blasts the goal to SAT, runs a SAT solver, and
*replays the solver's UNSAT certificate (LRAT) through a verified
checker* — so the kernel still checks everything and the solver is not
trusted. Try proving the lowest-set-bit identity by induction on 32 bits
to appreciate the trade. When a goal is false, `bv_decide` reports a
counterexample — try it on `x &&& (x - 1) = x - 1`. -/

example (x y : BitVec 32) : x ^^^ y ^^^ x = y := by
  bv_decide

example (x : BitVec 32) : -x = ~~~x + 1 := by
  bv_decide

example (x : BitVec 32) : x &&& (x - 1) = x - (x &&& -x) := by
  bv_decide

/-- The corrected xor-swap. The bug was `x ^^^ x` (always zero); the
real trick cancels one operand at a time: `a = x ^^^ y`, then
`a ^^^ y = x` and `a ^^^ x = y`. -/
def xorSwap (p : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  let a := p.1 ^^^ p.2
  let b := a ^^^ p.2   -- = p.1
  let a := a ^^^ b     -- = p.2
  (a, b)

theorem xorSwap_correct (x y : BitVec 32) : xorSwap (x, y) = (y, x) := by
  simp only [xorSwap, Prod.mk.injEq]
  constructor <;> bv_decide

example (x : BitVec 32) :
    (x ^^^ (x.sshiftRight 31)) - x.sshiftRight 31 =
      (if x.slt 0 then -x else x) := by
  split <;> bv_decide
