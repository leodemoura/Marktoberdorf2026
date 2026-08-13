import Std.Tactic.BVDecide
/-
Lecture 3 — Proof automation: `simp`, `grind`, `bv_decide`.

The goal of this file is different from the previous ones: the proofs
should be *short*. If you are writing more than a couple of lines, step
back and let the automation work for you.
-/

/-! ## 1. `simp` and rewriting -/

def double (n : Nat) : Nat := 2 * n

@[simp] theorem double_zero : double 0 = 0 := rfl

/-- State the unfolding lemma `double n = 2 * n`, mark it `@[simp]`, and
the proof is `simp +arith` — the `+arith` option lets `simp` finish the
linear arithmetic, as on the slides. -/
theorem double_add (a b : Nat) : double (a + b) = double a + double b := by
  sorry

/-! ## 2. `grind`

`grind` combines congruence closure, E-matching, and theory solvers
(linear integer arithmetic, commutative rings, ...). First prove each
goal *by hand* (`rw`, `lia`, ...), then replace your proof with `grind`
and compare. -/

/-- Congruence closure: equal arguments, equal results. -/
example (f : Nat → Nat) (a b c : Nat) (h₁ : a = b) (h₂ : f b = c) :
    f a = c := by
  sorry

/-- Linear integer arithmetic. -/
example (x y : Int) (h₁ : 2 * x + 3 * y = 7) (h₂ : 3 * x - y = 5) :
    x = 2 := by
  sorry

/-- Theories cooperating: arithmetic facts flow through congruence. -/
example (f : Int → Int) (x y : Int)
    (h₁ : f (x + y) = 0) (h₂ : y = x + 2) (h₃ : x = 1) :
    f 4 = 0 := by
  sorry

/-! ## 3. E-matching annotations

`grind` instantiates annotated theorems by pattern matching modulo known
equalities. `@[grind =]` uses the left-hand side as the pattern. -/

def enc (n : Nat) : Nat := n + 1
def dec (n : Nat) : Nat := n - 1

/-- Prove this (e.g. with `simp [enc, dec]` or `lia` after unfolding),
and annotate it with `@[grind =]` so `grind` can use it below. -/
theorem dec_enc (n : Nat) : dec (enc n) = n := by
  sorry

/-- With `dec_enc` annotated, `grind` closes this. Note that the term
`dec (enc c)` appears nowhere in the goal: E-matching works *modulo the
known equalities*. From `a = enc c`, the term `dec a` matches the pattern
`dec (enc ?n)`, so `grind` learns `dec (enc c) = c` and chains
`b = dec a = dec (enc c) = c`. Once the previous exercise works, replace
the `sorry` with `grind`. -/
example (a b c : Nat) (h₁ : dec a = b) (h₂ : a = enc c) : b = c := by
  sorry

/-! ## 4. The proof ladder, revisited

The optimizer from Lecture 2, and one theorem proved four ways. Fill in
all four; notice what each layer of automation buys you. -/

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

/-- Rewrite `0 + e` and `e + 0` to `e`, bottom-up. -/
def optimize : Expr → Expr
  | const n => const n
  | var x   => var x
  | add a b =>
    match a.optimize, b.optimize with
    | const 0, b' => b'
    | a', const 0 => a'
    | a', b'      => add a' b'

/-- 1. By structural induction: `induction e` with `simp [optimize, eval]`
and manual case analysis (`split`) in the `add` case. -/
theorem optimize_correct₁ (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  sorry

/-- 2. With `fun_induction optimize`: the induction principle that follows
the *shape of the definition*, so the match is already split. Finish
with `<;> simp [eval, *]` — you may need `lia`, or `simp` alone may do. -/
theorem optimize_correct₂ (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  sorry

/-- 3. `fun_induction` + `grind`. One line. -/
theorem optimize_correct₃ (e : Expr) (σ : State) :
    e.optimize.eval σ = e.eval σ := by
  sorry

end Expr

/-! ## 5. `bv_decide`

`bv_decide` decides goals about fixed-width bitvectors by bit-blasting to
SAT. The SAT solver's answer is checked by a verified checker, so the
result is still a kernel-checked proof. Try to prove one of these by hand
first to appreciate what you are *not* doing. -/

example (x y : BitVec 32) : x ^^^ y ^^^ x = y := by
  sorry

/-- Two's complement negation. -/
example (x : BitVec 32) : -x = ~~~x + 1 := by
  sorry

/-- `x &&& (x - 1)` clears the lowest set bit; `x &&& -x` isolates it. -/
example (x : BitVec 32) : x &&& (x - 1) = x - (x &&& -x) := by
  sorry

/-- The xor-swap trick actually swaps. -/
def xorSwap (p : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  let x := p.1 ^^^ p.2
  let y := x ^^^ x        -- oops — this implementation has a bug. Fix it!
  (x, y)

/-- Fix `xorSwap` (implement the real three-xor trick) so this proof
succeeds. -/
theorem xorSwap_correct (x y : BitVec 32) : xorSwap (x, y) = (y, x) := by
  sorry

/-- *(harder)* A branch-free absolute value for 32-bit integers:
`(x ^^^ m) - m` where `m` is the arithmetic shift of `x` by 31 bits.
Show it agrees with the obvious definition. -/
example (x : BitVec 32) :
    (x ^^^ (x.sshiftRight 31)) - x.sshiftRight 31 =
      (if x.slt 0 then -x else x) := by
  sorry
