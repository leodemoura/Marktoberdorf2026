import Lean
/-
Solutions for Lecture 4, part B, with notes.

Part A (Lecture4.lean) used a *deep* embedding: Imp programs are data
(an inductive type), and the VC generator is a function over that data.
Here we use a *shallow* embedding: programs are ordinary Lean monadic
code in `StateM`, and verification proceeds by `apply`-ing one rule per
program step — symbolic execution. This is the idiom used by real Lean
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
-/

/-- The Hoare triple for `StateM` programs — the same reading as part A:
from any state satisfying `P`, running `k` establishes `Q`. Running a
shallow program is function application, so no inductive semantics is
needed; the postcondition also receives the returned value. -/
def Triple (P : S → Prop) (k : StateM S α) (Q : α → S → Prop) : Prop :=
  ∀ s, P s → Q (k s).1 (k s).2

/-! ## 1. One rule per construct, in apply-friendly form

Note: each rule's conclusion is `Triple P ⟨construct⟩ Q` for *arbitrary*
`P` and `Q` — part A's primed-rule lesson, applied from the start:
`apply` selects the rule by the head of the program, and no goal shape
can make it fail. The proofs are one-liners: unfold the monad plumbing
(`simpa [...]`) and run the function; the content is in the
statements. -/

theorem Triple.pure (a : α) (h : ∀ s, P s → Q a s) : Triple P (pure a) Q := by
  intro s hP
  simpa [Pure.pure, StateT.pure] using h s hP

theorem Triple.get (h : ∀ s, P s → Q s s) : Triple P get Q := by
  intro s hP
  simpa [MonadState.get, getThe, MonadStateOf.get, StateT.get, Pure.pure] using
    h s hP

theorem Triple.set (h : ∀ s, P s → Q () s') : Triple P (set s') Q := by
  intro s hP
  simpa [MonadStateOf.set, StateT.set, Pure.pure] using h s hP

theorem Triple.modify (h : ∀ s, P s → Q () (f s)) : Triple P (modify f) Q := by
  intro s hP
  simpa [_root_.modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    Pure.pure] using h s hP

/-- The key rule — `Triple.seq'` from part A, with the result value `a`
passed to the continuation: run `k₁` toward states from which the rest
of the program is verified, marked by the same singleton-precondition
encoding.

Note the proof: `h s hP` proves the continuation triple at `(k₁ s).1`
and `(k₁ s).2`; applying it to the final state and `rfl` *is* the
proof, because running `k₁ >>= k₂` is definitionally running `k₂` from
where `k₁` stopped. No case analysis, no simp set — the shallow
embedding's semantics is computation. -/
theorem Triple.bind (k₁ : StateM S α) (k₂ : α → StateM S β) (Q : β → S → Prop)
    (h : Triple P k₁ (fun a s => Triple (· = s) (k₂ a) Q)) :
    Triple P (k₁ >>= k₂) Q := by
  intro s hP
  exact h s hP (k₁ s).2 rfl

theorem Triple.ite {_ : Decidable c} (t e : StateM S α)
    (h₁ : c → Triple P t Q) (h₂ : ¬c → Triple P e Q) :
    Triple P (if c then t else e) Q := by
  split
  next h => exact h₁ h
  next h => exact h₂ h

/-- The consequence rule, exactly as in part A. Note the proof: `Triple`
is a definition, so `h s (hpre s hP)` is already a proof about the run
of `k`, and `hpost` finishes — a one-line term proof. -/
theorem Triple.consequence (h : Triple P' k Q')
    (hpre : ∀ s, P s → P' s) (hpost : ∀ a s, Q' a s → Q a s) :
    Triple P k Q :=
  fun s hP => hpost _ _ (h s (hpre s hP))

/-! ## 2. Symbolic execution by hand -/

def double : StateM Nat Unit := do
  let s ← get
  set (s + s)

/-- Note: the same stepping discipline as `swap` and `copyProg` in
part A — `apply` the rule for the head of the program, `intro` the
reached state after each atomic step. Read the proof as an execution
trace: `Triple.bind` splits off the first statement, `Triple.get` reads
the state (introducing `s` with `h : s = a`), `Triple.set` writes it,
and the leftover goal is the verification condition `s + s = 2 * a`.
Watch the goal after each `apply`: the program shrinks by one statement
each time, and the state expressions grow. (The logical variable `a`
names the initial state in the postcondition, exactly like `a` in
part A's `copyProg` spec.) -/
example (a : Nat) : Triple (· = a) double (fun _ s => s = 2 * a) := by
  unfold double
  apply Triple.bind
  apply Triple.get
  intro s h
  apply Triple.set
  intro s' h'
  grind

def clampNeg : StateM Int Unit := do
  let s ← get
  if s < 0 then
    -- The ascription is needed: `set` is polymorphic in the state type
    -- (`MonadStateOf` supports lifting), so a bare `0` defaults to `Nat`.
    set (0 : Int)

/-- Note: an `if` without `else` is sugar for `if ... then ... else
pure ()`. `Triple.ite` hands each branch the test result, like
`Triple.ite` in part A. -/
example (a : Int) :
    Triple (· = a) clampNeg (fun _ s => 0 ≤ s ∧ (0 ≤ a → s = a)) := by
  unfold clampNeg
  apply Triple.bind
  apply Triple.get
  intro s h
  apply Triple.ite
  · intro hc
    apply Triple.set
    intro s' h'
    grind
  · intro hc
    apply Triple.pure
    intro s' h'
    grind

/-! ## 3. The metaprogram: a symbolic executor

Note: the manual proofs above are completely mechanical — the rule to
apply is determined by the head of the program. So let a program do it.

The naive attempt is a macro: `repeat first | apply Triple.bind | apply
Triple.get | ...`. It does not work: when `apply Triple.bind` is tried
against a goal whose program is *not* a bind, the unifier starts
unfolding `>>=`, `StateM`, and `StateT` trying to make it one, and the
attempt times out instead of failing fast. The lesson generalizes:
searching by unification is expensive.

So we do what real symbolic execution engines do — *look at the goal
and dispatch on the head symbol*. `sym_step` is a small metaprogram: it
reads the `Triple` goal, inspects the head of the program, and applies
the one matching rule, introducing the reached state after each atomic
step (as we did by hand). `sym_run` iterates it; what remains are the
verification conditions.

This is the promised glimpse of metaprogramming: tactics are ordinary
Lean programs that read goals and decide what to do. The industrial
version of this loop is the `SymM` framework in the Lean sources: the
same dispatch-and-apply structure, but with precompiled backward rules
(no unification search — the same lesson as above), maximally shared
terms, cached simplification, and `grind` state threaded from one VC to
the next. That engineering is what turns this toy from "works on
`double`" into "discharges thousands of VCs" (see the Lecture 4
slides). -/

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

/-- `double`, again: symbolic execution is now one word, and only the VC
is left for `grind`. -/
example (a : Nat) : Triple (· = a) double (fun _ s => s = 2 * a) := by
  unfold double
  sym_run
  grind

/-- `clampNeg`, again. `sym_run` executes both branches of the `if`;
`<;> grind` discharges both VCs. -/
example (a : Int) :
    Triple (· = a) clampNeg (fun _ s => 0 ≤ s ∧ (0 ≤ a → s = a)) := by
  unfold clampNeg
  sym_run <;> grind

/-- A contract with a *nontrivial precondition* — the first in this
file. Note where the precondition does its work: `sym_run` still
executes both branches of the `if`, but the VC of the `set` branch is
the test `s < 0` against the hypothesis `0 ≤ a` — a contradiction, and
`grind` closes it. Preconditions do not shrink the execution; they
discharge the obligations it produces. -/
example (a : Int) :
    Triple (fun s => s = a ∧ 0 ≤ a) clampNeg (fun _ s => s = a) := by
  unfold clampNeg
  sym_run <;> grind

/-! ## 4. Loops, one more time -/

def addN : Nat → StateM Nat Unit
  | 0 => pure ()
  | n + 1 => do
    modify (· + 1)
    addN n

/-- Note: recursion in the program becomes induction in the proof — the
shallow analogue of part A's `while` rule. The induction hypothesis
plays the role of the loop invariant, and `generalizing a` is essential
for the same reason as in `sumToTR` (Lecture 2): the recursive call
starts from a *different* state. In each case, `simp only [addN]`
unfolds one step and `sym_run` executes it, stopping at the recursive
call (there is no rule for `addN` — that is what the induction
hypothesis is for). `Triple.consequence` bridges the induction
hypothesis to the goal — its precondition matches on the nose
(`fun _ h => h`), and the postconditions differ by the arithmetic
`grind` closes, using the hypothesis introduced by `sym_run`. -/
theorem addN_correct (n : Nat) (a : Nat) :
    Triple (· = a) (addN n) (fun _ s' => s' = a + n) := by
  induction n generalizing a with
  | zero => simp only [addN]; sym_run; grind
  | succ n ih =>
    simp only [addN]
    sym_run
    exact Triple.consequence (ih _) (fun _ h => h) (by grind)

def sumDown : Nat → StateM Nat Unit
  | 0 => pure ()
  | n + 1 => do
    modify (· + (n + 1))
    sumDown n

/-- Note: same recipe as `addN_correct` — induction generalizing the
initial state, `sym_run` to the recursive call, `Triple.consequence` to
bridge. The bridging step is now nonlinear arithmetic
(`(n + 1) * (n + 2)` expands against `n * (n + 1)`), which `grind`'s
ring solver normalizes. -/
theorem sumDown_correct (n : Nat) (a : Nat) :
    Triple (· = a) (sumDown n) (fun _ s' => 2 * s' = 2 * a + n * (n + 1)) := by
  induction n generalizing a with
  | zero => simp only [sumDown]; sym_run; grind
  | succ n ih =>
    simp only [sumDown]
    sym_run
    exact Triple.consequence (ih _) (fun _ h => h) (by grind)
