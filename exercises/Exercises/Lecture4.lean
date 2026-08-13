import Imp
/-
Lecture 4 — The project: a toy verification condition generator.

The given code is in `Imp/`: a small imperative language with concrete
syntax (`Imp/Syntax.lean`), a big-step semantics `BigStep σ s σ'`, an
interpreter (`Imp/Interp.lean`), and Hoare triples for partial
correctness:

    def Triple (P : Assertion) (s : Stmt) (Q : Assertion) : Prop :=
      ∀ σ σ', P σ → BigStep σ s σ' → Q σ'

Loops carry an invariant annotation (`while (c) invariant (I) { ... }`).
The semantics ignores it; it is input for the VC generator you build here.

Plan:
1. Prove the Hoare logic rules (skip, assign, seq, if, consequence, while).
2. Build the VC generator: `pre` computes preconditions backwards, using
   the annotated invariants; `vc` collects the proof obligations; and
   `vcgen_sound` says discharging the obligations verifies the program.
3. Verify programs — loop-free and looping — with `vcg` + `grind`.

The punchline: the resulting verifier is itself verified — its soundness
is a theorem, checked by Lean's kernel. No trusted code generator.
-/

/-! ## 1. Hoare logic rules -/

/-- `skip` changes nothing. Hint: `intro σ σ' hP h; cases h; ...` -/
theorem Triple.skip (Q : Assertion) : Triple Q .skip Q := by
  sorry

/-- The assignment rule: to get `Q` after `x := e`, it suffices that `Q`
holds *now* for the updated state. -/
theorem Triple.assign (Q : Assertion) (x : String) (e : Expr) :
    Triple (fun σ => Q (σ.set x (e.eval σ))) (.assign x e) Q := by
  sorry

/-- Sequencing composes triples. -/
theorem Triple.seq (h₁ : Triple P s₁ R) (h₂ : Triple R s₂ Q) :
    Triple P (.seq s₁ s₂) Q := by
  sorry

/-- Weaken the precondition, strengthen the postcondition. -/
theorem Triple.consequence (h : Triple P s Q)
    (hpre : ∀ σ, P' σ → P σ) (hpost : ∀ σ, Q σ → Q' σ) :
    Triple P' s Q' := by
  sorry

/-- The conditional rule: each branch gets to assume the test result. -/
theorem Triple.ite
    (h₁ : Triple (fun σ => P σ ∧ c.eval σ = true) s₁ Q)
    (h₂ : Triple (fun σ => P σ ∧ c.eval σ = false) s₂ Q) :
    Triple P (.ite c s₁ s₂) Q := by
  sorry

/-- *(harder)* The while rule: an invariant `I` preserved by the loop body
holds on exit, together with the negation of the test. The rule is stated
for an arbitrary annotation `inv` — the annotation has no semantic role.

This is the one tricky proof in this file. The `BigStep` derivation for a
`while` loop is built from `whileTrue` steps; a direct induction on it
does not go through because the statement changes. Hint: prove an
auxiliary lemma by induction on the derivation `BigStep σ s σ'` after
*generalizing* `s`: from `h : BigStep σ s σ'`, `s = .whileDo c inv body`,
and the invariant, conclude. The `generalize` tactic, or an explicit
helper lemma with `s` as a variable, both work. -/
theorem Triple.whileDo {inv : Assertion}
    (h : Triple (fun σ => I σ ∧ c.eval σ = true) body I) :
    Triple I (.whileDo c inv body) (fun σ => I σ ∧ c.eval σ = false) := by
  sorry

/-! ## 2. First verified programs

Verify concrete programs by chaining the rules. States are total maps, so
programs are straight-line manipulations of `State.get`/`State.set`; the
`grind` lemmas `State.get_set_same` and `State.get_set_ne` do the
bookkeeping.

Notation (from `Imp/Syntax.lean`): `σ⟦x⟧` is `State.get σ "x"` and
`σ⟦x := v⟧` is `State.set σ "x" v`. Goals display the same way. -/

def swapProg := [Imp|
  t := x;
  x := y;
  y := t;
]

/-- Hint: `Triple.seq` twice, `Triple.assign` three times — or wait for
Section 3, where the composition is computed for you. You can also invert
the derivation directly: `intro σ σ' hP hstep`, then `cases hstep`
repeatedly, then `grind`. -/
theorem swap_correct (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  sorry

/-- `Triple.assign` cannot be `apply`-ed to an arbitrary goal: its
precondition has the fixed shape `fun σ => Q (σ.set ...)`, and an
arbitrary `P` does not unify with it (try it on `swap_correct`!).
`Triple.assign'` fixes that: it applies to any pre/postcondition,
leaving an ordinary implication. Hint: fuse `Triple.assign` with
`Triple.consequence` — or prove it directly by inversion. -/
theorem Triple.assign' (P Q : Assertion) (x : String) (e : Expr) :
    (∀ σ, P σ → Q (σ.set x (e.eval σ))) →
    Triple P (.assign x e) Q := by
  sorry

/-- Sequencing in continuation style: prove `s₁` with the postcondition
"from exactly the state `s₁` produced, running `s₂` establishes `Q`".
Note that `fun s => Triple (· = s) s₂ Q` is an ordinary assertion —
assertions are arbitrary predicates on states — and it is definitionally
`s₂.wlp Q`, the safe region from `Imp/Basic.lean`. Unlike `Triple.seq`,
applying this rule invents no metavariable for the intermediate
assertion: it produces one goal, fully determined. Hint: invert the
`seq` derivation; the continuation is used at the intermediate state,
with `rfl` for the singleton precondition. -/
theorem Triple.seq' :
    Triple P s₁ (fun s => Triple (· = s) s₂ Q) →
    Triple P (.seq s₁ s₂) Q := by
  sorry

/-- The while rule has the same problem as `Triple.assign`: its
conclusion fixes the precondition (the invariant) and the shape of the
postcondition, so it cannot be `apply`-ed to an arbitrary goal.
`Triple.whileDo'` fixes that — and takes its invariant from the
*annotation*, which the goal's statement already carries, so `apply`
introduces no metavariable. Its three premises are entry, preservation,
and exit — exactly the verification conditions of Section 3.
Hint: fuse `Triple.whileDo` with `Triple.consequence`. -/
theorem Triple.whileDo' {inv : Assertion}
    (hpre : ∀ σ, P σ → inv σ)
    (hbody : Triple (fun σ => inv σ ∧ c.eval σ = true) body inv)
    (hpost : ∀ σ, inv σ → c.eval σ = false → Q σ) :
    Triple P (.whileDo c inv body) Q := by
  sorry

/-- `swap`, verified by *stepping through the program*: one rule
application per statement, receiving each intermediate state with
`intro`. Hint: alternate `Triple.seq'` and `Triple.assign'`, then
`simp [Expr.eval] at *` and `grind`. This style — the proof follows the
structure of the program — is symbolic execution; it returns in
Lecture 4b and is the loop the `SymM` framework runs at scale. -/
theorem swap_correct' (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  sorry

/-! ## 3. The VC generator

The rule composition from Section 2 is completely mechanical — so we
compute it. `pre` calculates the precondition of a statement *backwards*
from a postcondition; for a loop, its precondition is the *annotated
invariant* — the annotation we built into `Stmt` finally does its job.
`vc` collects the *verification conditions*: what remains to be proved.
`vcgen_sound` says: discharge the VCs and you have verified the program.

This construction is standard. Nipkow & Klein, *Concrete Semantics*,
§12.2.2 defines `pre` and `vc` (the same names) over invariant-annotated
commands, with soundness `vc C Q ⟹ {pre C Q} strip C {Q}`; Mike
Gordon's Cambridge notes on Hoare Logic (ch. 3) derive the same three
loop conditions; *Software Foundations* (Hoare2) does it with decorated
programs. Our one deviation: annotations live in `Stmt` itself and the
semantics ignores them, so there is no separate annotated syntax and no
`strip`/`erase` — the style of practical verifiers. -/

/-- Complete the definition: compute the precondition backwards, as in
the assignment rule and `Triple.seq`. The loop case is already there —
it returns the annotated invariant. -/
def Stmt.pre : Stmt → Assertion → Assertion
  | skip, Q => Q
  | assign x e, Q => sorry
  | seq s₁ s₂, Q => sorry
  | ite c s₁ s₂, Q => fun σ => if c.eval σ then s₁.pre Q σ else s₂.pre Q σ
  | whileDo _ inv _, _ => inv

/-- The verification conditions: what remains to be *proved*. For a loop:
the invariant must be preserved by the body, and must imply the
postcondition on exit. `skip` and `assign` contribute nothing — on
loop-free programs, `vc` is a conjunction of `True`s and `pre` alone
carries the meaning. -/
def Stmt.vc : Stmt → Assertion → Prop
  | skip, _ => True
  | assign _ _, _ => True
  | seq s₁ s₂, Q => s₁.vc (s₂.pre Q) ∧ s₂.vc Q
  | ite _ s₁ s₂, Q => s₁.vc Q ∧ s₂.vc Q
  | whileDo c inv body, Q =>
    (∀ σ, inv σ → c.eval σ = true → body.pre inv σ) ∧
    (∀ σ, inv σ → c.eval σ = false → Q σ) ∧
    body.vc inv

/-- Soundness of the VC generator.
Hint: induction on `s`, generalizing `Q`. Each case uses the
corresponding rule from Section 1; the loop case combines
`Triple.whileDo` and `Triple.consequence` with the two loop VCs. -/
theorem vcgen_sound (s : Stmt) (Q : Assertion) (h : s.vc Q) :
    Triple (s.pre Q) s Q := by
  sorry

/-- The user-facing entry: verify a program by discharging its VCs. -/
theorem Stmt.verify (s : Stmt) (P Q : Assertion)
    (hvc : s.vc Q) (hpre : ∀ σ, P σ → s.pre Q σ) :
    Triple P s Q :=
  Triple.consequence (vcgen_sound s Q hvc) hpre (fun _ h => h)

/-- A one-line VC-generating tactic (given): apply the verified entry
point, then unfold the computed `vc`/`pre` into plain proof obligations.
A macro like this is the smallest possible example of extending Lean's
tactic language; real VC generators are tactics built the same way, just
with `SymM` doing the heavy lifting. -/
macro "vcg" : tactic =>
  `(tactic| apply Stmt.verify <;> try simp [Stmt.vc, Stmt.pre, Expr.eval, BExpr.eval])

/-- `swap_correct`, again — this time the composition is computed. `swap`
is loop-free, so no verification condition survives; the one remaining
goal is the entailment between the specification and the computed
precondition. Once `pre` and `vcgen_sound` are done:
`unfold swapProg; vcg <;> grind`. Compare with your proof in
Section 2. -/
example (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  sorry

/-! ## 4. Verify a loop

`y := 0; while (0 < x) { x := x - 1; y := y + 1 }` copies (a nonnegative)
`x` into `y`. The invariant annotation says: `x + y` stays equal to the
initial value `a`, and `x` stays nonnegative. -/

def copyProg (a : Int) := [Imp|
  y := 0;
  while (0 < x) invariant (fun σ => σ⟦x⟧ + σ⟦y⟧ = a ∧ 0 ≤ σ⟦x⟧) {
    x := x - 1;
    y := y + 1;
  }
]

-- It runs: starting from x = 7, we end with y = 7.
#guard (Stmt.seq [Imp| x := 7;] (copyProg 7)).runGet "y" = some 7

/-- Verify the program. Hint: same as `swap` — `unfold copyProg`, then
`vcg <;> grind`. Look at the goals after `vcg` (before `grind` closes
them): this time obligations *do* survive — exactly the
invariant-preservation and exit conditions, with no trace of the Hoare
logic left. -/
theorem copy_correct (a : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ 0 ≤ a)
      (copyProg a)
      (fun σ => σ⟦y⟧ = a) := by
  sorry

/-- *(harder)* The same loop, verified by *stepping* — no VC generator.
Alternate `Triple.seq'` and `Triple.assign'`; at the loop, apply
`Triple.whileDo'` and notice that its three goals are the conditions
`vc` computed: entry, preservation, exit. `simp [Expr.eval, BExpr.eval]`
and `grind` finish each branch. -/
theorem copy_correct' (a : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ 0 ≤ a)
      (copyProg a)
      (fun σ => σ⟦y⟧ = a) := by
  sorry

/-! ## 5. The interpreter, verified *(harder)*

`Imp/Interp.lean` defines the fuel-bounded interpreter `Stmt.run`, and
we have been testing programs with it (`#guard`) since the start. But
nothing so far connects it to the semantics: the tests check the
interpreter, and the proofs are about `BigStep`. Close the gap — prove
the interpreter *sound* (whatever it computes, `BigStep` derives) and
*complete* (whatever `BigStep` derives, some fuel computes). Payoffs:
every `#guard` becomes a theorem about the semantics, and determinism
of `BigStep` — usually a fiddly double induction — falls out in four
lines.

A fact worth internalizing before you start: `Stmt.run` is defined by
*well-founded* recursion (`termination_by (fuel, s)`), and such
definitions do not compute by `rfl` — the kernel cannot reduce them
definitionally (compare `partial def`, which cannot be unfolded at
all — Lecture 2). `#guard` still works because it runs the *compiled*
code. In proofs, use `simp [Stmt.run]` to apply the equation lemmas. -/

/-- Fuel monotonicity: more fuel never hurts — the workhorse lemma for
completeness.

Hints: `fun_induction Stmt.run s σ fuel` follows the interpreter's own
case analysis. The `∀ {σ' fuel'}` must stay in the *goal* (do not
`intro` before the induction): the induction hypotheses must apply at
different final states and fuels than the current ones. In the `seq`
and `while` cases, `simp only [Option.bind_eq_some_iff] at h` turns
the `bind` equation into an intermediate state you can `obtain`; in
the `while` cases, `match fuel', hle with | fuel' + 1, hle => ...`
exposes the successor that `Stmt.run` needs. -/
theorem Stmt.run_mono {s : Stmt} {σ : State} {fuel : Nat} :
    ∀ {σ' fuel'}, s.run σ fuel = some σ' → fuel ≤ fuel' →
      s.run σ fuel' = some σ' := by
  sorry

/-- Soundness: if the interpreter answers, the semantics agrees.

Hints: `fun_induction` again — and notice that it has already reduced
`h` to the current branch, so most cases need no unfolding at all:
`cases h` dispatches the `some _ = some _` cases (substituting the
final state), and each goal is one `BigStep` constructor. When the
test is false, `simp at hc` turns `¬(_ = true)` into the `= false`
form the constructor expects. -/
theorem Stmt.run_sound {s : Stmt} {σ : State} {fuel : Nat} :
    ∀ {σ'}, s.run σ fuel = some σ' → BigStep σ s σ' := by
  sorry

/-- Completeness: every terminating run is computed by some fuel.

Hints: induction on the derivation `h`. Two sub-derivations give two
fuels — combine them with `max f₁ f₂` and bridge with `Stmt.run_mono`
(`Nat.le_max_left`/`Nat.le_max_right`). For the base cases remember:
`⟨0, rfl⟩` fails (well-founded recursion does not compute by `rfl`);
`⟨0, by simp [Stmt.run]⟩` works. The `whileTrue` case needs
`max f₁ f₂ + 1` — one more than its sub-runs. -/
theorem Stmt.run_complete {σ σ' : State} {s : Stmt} (h : BigStep σ s σ') :
    ∃ fuel, s.run σ fuel = some σ' := by
  sorry

/-- Determinism of the semantics, for free: run both derivations to
their fuels, bump both to `max f₁ f₂` with `Stmt.run_mono`, and the two
`some`s must agree.

Hint: after two `obtain`s and two `have`s, `grind` closes it. -/
theorem BigStep.deterministic {σ σ₁ σ₂ : State} {s : Stmt}
    (h₁ : BigStep σ s σ₁) (h₂ : BigStep σ s σ₂) : σ₁ = σ₂ := by
  sorry

/-- *(bonus)* Tests are theorems: every passing `runGet` test certifies
a genuine `BigStep` fact — this retroactively upgrades every `#guard`
in `Imp/Examples.lean`.

Hint: `unfold Stmt.runGet at h`, then
`match hr : s.run State.init fuel with` and use `Stmt.run_sound`. -/
theorem Stmt.runGet_sound {s : Stmt} {x : String} {v : Int} {fuel : Nat}
    (h : s.runGet x fuel = some v) :
    ∃ σ', BigStep State.init s σ' ∧ σ'.get x = v := by
  sorry

/-! ## 6. Extend the VC generator *(harder)*

Ideas, in increasing order of ambition:

1. Add an `assert` statement to `Stmt` (with a `BigStep` rule that
   requires the asserted condition to hold) and extend `pre`, `vc`, and
   `vcgen_sound`. Add surface syntax for it in `Imp/Syntax.lean`.
2. Total correctness: add a variant (a decreasing measure) to the loop
   annotation and prove termination, replacing `Triple` with a
   big-step-existence statement.
3. Make the VC generator a *tactic*, so programs and specifications are
   processed automatically. (This is what real Lean VC generators do,
   using the `SymM` framework.)
4. On loop-free programs, `pre` computes Dijkstra's *weakest liberal
   precondition* — weakest, not just sound. Make that a theorem: define
   `LoopFree : Stmt → Prop` and prove that `Triple P s Q` implies
   `∀ σ, P σ → s.pre Q σ` for loop-free `s`. (You will want inversion
   lemmas for `BigStep`.)
-/
