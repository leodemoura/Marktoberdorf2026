import Lean
/-
Lecture 4, part B — Shallow embedding: verifying monadic programs.

Part A (Lecture4.lean) used a *deep* embedding: Imp programs are data,
and the VC generator is a function over that data. Here we use a
*shallow* embedding: programs are ordinary Lean monadic code in
`StateM`, and verification proceeds by `apply`-ing one rule per program
step — symbolic execution. This is the idiom used by real Lean
verification tools (mvcgen, Velvet, Aeneas), and the loop that the
`SymM` framework is engineered to run at scale.

The judgment does not change: specifications are Hoare triples, exactly
as in part A. What changes is the semantics underneath. A `StateM`
program is a Lean function, so "every terminating run" becomes *the*
run: where part A quantified over `BigStep σ s σ'`, here we simply run
the program — `(k s).1` is the returned value and `(k s).2` the final
state. Two consequences:

- Every rule can be stated in part A's primed, apply-friendly form from
  the start (arbitrary precondition, no metavariables): `Triple.get`
  has the shape of `Triple.assign'`, and `Triple.bind` is
  `Triple.seq'` with the result value passed to the continuation.
- `StateM` programs are total and deterministic, so partial and total
  correctness coincide here.

Replace each `sorry`. Exercises get harder as you go; *(harder)* ones
are optional.
-/

/-- The Hoare triple for `StateM` programs — the same reading as part A:
from any state satisfying `P`, running `k` establishes `Q`. Running a
shallow program is function application, so no inductive semantics is
needed; the postcondition also receives the returned value. -/
def Triple (P : S → Prop) (k : StateM S α) (Q : α → S → Prop) : Prop :=
  ∀ s, P s → Q (k s).1 (k s).2

/-! ## 1. One rule per construct, in apply-friendly form

Each rule's conclusion is `Triple P ⟨construct⟩ Q` for *arbitrary* `P`
and `Q` — part A's primed-rule lesson, applied from the start: `apply`
selects the rule by the head of the program, and no goal shape can make
it fail. The proofs are one-liners: unfold the monad plumbing
(`simpa [...]`) and run the function; the content is in the
statements. -/

theorem Triple.pure (a : α) (h : ∀ s, P s → Q a s) : Triple P (pure a) Q := by
  intro s hP
  simpa [Pure.pure, StateT.pure] using h s hP

theorem Triple.get (h : ∀ s, P s → Q s s) : Triple P get Q := by
  intro s hP
  simpa [MonadState.get, getThe, MonadStateOf.get, StateT.get, Pure.pure] using
    h s hP

/-- Prove the rule for `set`. Hint: mirror `Triple.get`; the relevant
definitions are `MonadStateOf.set`, `StateT.set`, and `Pure.pure`. -/
theorem Triple.set (h : ∀ s, P s → Q () s') : Triple P (set s') Q := by
  sorry

theorem Triple.modify (h : ∀ s, P s → Q () (f s)) : Triple P (modify f) Q := by
  intro s hP
  simpa [_root_.modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    Pure.pure] using h s hP

/-- The key rule — `Triple.seq'` from part A, with the result value `a`
passed to the continuation: run `k₁` toward states from which the rest
of the program is verified, marked by the same singleton-precondition
encoding.

Hint: after `intro s hP`, the premise gives `h s hP`, a proof of the
continuation triple at `(k₁ s).1` and `(k₁ s).2`; apply it to the final
state and `rfl`. The whole proof is one more line — running `k₁ >>= k₂`
*is* running `k₂` from where `k₁` stopped, definitionally. -/
theorem Triple.bind (k₁ : StateM S α) (k₂ : α → StateM S β) (Q : β → S → Prop)
    (h : Triple P k₁ (fun a s => Triple (· = s) (k₂ a) Q)) :
    Triple P (k₁ >>= k₂) Q := by
  sorry

theorem Triple.ite {_ : Decidable c} (t e : StateM S α)
    (h₁ : c → Triple P t Q) (h₂ : ¬c → Triple P e Q) :
    Triple P (if c then t else e) Q := by
  split
  next h => exact h₁ h
  next h => exact h₂ h

/-- The consequence rule, exactly as in part A. Hint: a one-line term
proof — `Triple` is a definition, so `h s (hpre s hP)` is already a
proof about the run of `k`, and `hpost` finishes. -/
theorem Triple.consequence (h : Triple P' k Q')
    (hpre : ∀ s, P s → P' s) (hpost : ∀ a s, Q' a s → Q a s) :
    Triple P k Q :=
  sorry

/-! ## 2. Symbolic execution by hand -/

def double : StateM Nat Unit := do
  let s ← get
  set (s + s)

/-- Verify `double` by stepping through it — the same discipline as
`swap` and `copyProg` in part A: `unfold double`, `apply` the rule
matching the head of the program (`Triple.bind`, `Triple.get`,
`Triple.set`), and `intro` the reached state after each atomic step.
The leftover verification condition falls to `grind`. Watch the goal
after each `apply`: the program shrinks by one statement each time, and
the state expressions grow. -/
example (a : Nat) : Triple (· = a) double (fun _ s => s = 2 * a) := by
  sorry

def clampNeg : StateM Int Unit := do
  let s ← get
  if s < 0 then
    -- The ascription is needed: `set` is polymorphic in the state type
    -- (`MonadStateOf` supports lifting), so a bare `0` defaults to `Nat`.
    set (0 : Int)

/-- An `if` without `else` is sugar for `if ... then ... else pure ()`.
Use `Triple.ite`; each branch gets the test result (`intro h`), then
continues with `Triple.set` / `Triple.pure`, then `grind`. -/
example (a : Int) :
    Triple (· = a) clampNeg (fun _ s => 0 ≤ s ∧ (0 ≤ a → s = a)) := by
  sorry

/-! ## 3. The metaprogram: a symbolic executor (given)

The manual proofs above are completely mechanical — the rule to apply is
determined by the head of the program. So let a program do it.

The naive attempt is a macro: `repeat first | apply Triple.bind | apply
Triple.get | ...`. It does not work: when `apply Triple.bind` is tried
against a goal whose program is *not* a bind, the unifier starts
unfolding `>>=`, `StateM`, and `StateT` trying to make it one, and the
attempt times out instead of failing fast. The lesson generalizes:
searching by unification is expensive.

So we do what real symbolic execution engines do — *look at the goal and
dispatch on the head symbol*. `sym_step` is a small metaprogram: it
reads the `Triple` goal, inspects the head of the program, and applies
the one matching rule, introducing the reached state after each atomic
step (as we did by hand). `sym_run` iterates it (over all branches);
what remains are the verification conditions.

This is the promised glimpse of metaprogramming: tactics are ordinary
Lean programs that read goals and decide what to do. The industrial
version of this loop is the `SymM` framework in the Lean sources: the
same dispatch-and-apply structure, but with precompiled backward rules
(no unification search — the same lesson as above), maximally shared
terms, cached simplification, and `grind` state threaded from one VC to
the next. See the Lecture 4 slides, and the benchmark
https://github.com/leanprover/lean4/blob/master/tests/bench/sym/add_sub_cancel.lean
-/

open Lean Elab Tactic in
/-- Symbolic execution, one step: inspect the head of the program in the
`Triple` goal and apply the matching rule. -/
elab "sym_step" : tactic => do
  let goal ← getMainGoal
  let tgt ← goal.withContext do instantiateMVars (← goal.getType)
  let_expr Triple _ _ _ k _ := tgt.headBeta
    | throwError "sym_step: not a `Triple` goal"
  let app (r : Name) : TacticM Unit := do
    evalTactic (← `(tactic| apply $(mkIdent r) <;> intro _ _))
  match k.getAppFn.constName? with
  | some ``Bind.bind => evalTactic (← `(tactic| apply Triple.bind))
  | some ``get       => app ``Triple.get
  | some ``set       => app ``Triple.set
  | some ``modify    => app ``Triple.modify
  | some ``pure      => app ``Triple.pure
  | some ``ite       => evalTactic (← `(tactic| apply Triple.ite <;> intro _))
  | _ => throwError "sym_step: no rule for{indentExpr k}"

-- `repeat'` (not `repeat`): after an `if` splits the goal in two, the
-- executor must keep stepping in *all* branches, not just the first.
macro "sym_run" : tactic => `(tactic| repeat' sym_step)

/-- `double` and `clampNeg`, again: symbolic execution is now one word,
and only the verification conditions are left. One line each after the
`unfold`. -/
example (a : Nat) : Triple (· = a) double (fun _ s => s = 2 * a) := by
  sorry

example (a : Int) :
    Triple (· = a) clampNeg (fun _ s => 0 ≤ s ∧ (0 ≤ a → s = a)) := by
  sorry

/-- A contract with a *nontrivial precondition* — the first in this
file. The same one-liner works; watch where the precondition does its
work: `sym_run` still executes both branches of the `if`, but the VC of
the `set` branch is the test `s < 0` against the hypothesis `0 ≤ a` — a
contradiction, and `grind` closes it. Preconditions do not shrink the
execution; they discharge the obligations it produces. -/
example (a : Int) :
    Triple (fun s => s = a ∧ 0 ≤ a) clampNeg (fun _ s => s = a) := by
  sorry

/-! ## 4. Loops, one more time -/

def addN : Nat → StateM Nat Unit
  | 0 => pure ()
  | n + 1 => do
    modify (· + 1)
    addN n

/-- Recursion in the program becomes induction in the proof — the
shallow analogue of part A's `while` rule, with the induction hypothesis
playing the role of the loop invariant.

Hints: `generalizing a` is essential, for the same reason as in
`sumToTR` (Lecture 2): the recursive call starts from a *different*
state. In each case, `simp only [addN]` unfolds one step and `sym_run`
executes it, stopping at the recursive call (there is no rule for
`addN` — that is what the induction hypothesis is for).
`Triple.consequence` bridges the induction hypothesis to the goal, just
as it bridged rules to specifications in part A. -/
theorem addN_correct (n : Nat) (a : Nat) :
    Triple (· = a) (addN n) (fun _ s' => s' = a + n) := by
  sorry

/-- *(harder)* Gauss, again (compare `sumTo` in Lecture 2 and `copyProg`
in part A): `sumDown n` adds `n + (n-1) + ⋯ + 1` to the state. The
postcondition avoids division by stating `2 * s' = ...`. Same recipe as
`addN_correct`. -/
def sumDown : Nat → StateM Nat Unit
  | 0 => pure ()
  | n + 1 => do
    modify (· + (n + 1))
    sumDown n

theorem sumDown_correct (n : Nat) (a : Nat) :
    Triple (· = a) (sumDown n) (fun _ s' => 2 * s' = 2 * a + n * (n + 1)) := by
  sorry

/-! ## 5. Extend it *(harder)*

Ideas:

1. Add a program construct — e.g. `getModify` or a two-variable state
   via `StateM (Int × Int)` — with its `Triple` rule, and extend
   `sym_step` to dispatch on it.
2. The safe region, one more time: define the shallow
   `wlp k post : S → Prop := fun s => post (k s).1 (k s).2`
   (Dijkstra's weakest liberal precondition, pointwise because shallow
   programs are functions) and prove
   `Triple P k Q ↔ ∀ s, P s → wlp k Q s` — triples are inclusions into
   the safe region, here as in part A. Then connect the embeddings:
   using part A's `Stmt.wlp` (`Imp/Basic.lean`), prove
   `s.wlp Q σ ↔ ∀ σ', BigStep σ s σ' → Q σ'`.
3. Compare with part A: what does the deep embedding give you that the
   shallow one does not, and vice versa? (Think: writing an optimizer;
   quantifying over all programs; reusing Lean's own syntax and
   type checker.)
-/
