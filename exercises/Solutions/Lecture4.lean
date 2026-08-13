import Imp
/-
Solutions for Lecture 4, with notes.

Each solution comes with a note explaining *why* the proof works, not
just what to type. Read the notes even if your proof differs — several
of these proofs contain a technique worth remembering.
-/

/-! ## 1. Hoare logic rules

Note: all the rules in this section follow the same pattern. `Triple`
unfolds to a statement about `BigStep` derivations, so we `intro` the
states and the derivation, and then invert the derivation with `cases`:
for a fixed statement shape (say `.skip`), only the matching `BigStep`
constructors could have produced it, and `cases` gives us exactly those,
with their premises as hypotheses. -/

/-- Inverting the derivation for `.skip` leaves one case, `BigStep.skip`,
which forces `σ' = σ`. The goal becomes `Q σ`, which is the hypothesis. -/
theorem Triple.skip (Q : Assertion) : Triple Q .skip Q := by
  intro σ σ' h hstep
  cases hstep
  exact h

/-- Same inversion. `BigStep.assign` forces `σ' = σ.set x (e.eval σ)`,
which is exactly the state the precondition talks about. Note the rule's
direction: the precondition is the postcondition *pushed backwards*
through the assignment — there is nothing to compute forwards. -/
theorem Triple.assign (Q : Assertion) (x : String) (e : Expr) :
    Triple (fun σ => Q (σ.set x (e.eval σ))) (.assign x e) Q := by
  intro σ σ' h hstep
  cases hstep
  exact h

/-- Inverting a `.seq` derivation yields the intermediate state `σ'` and
derivations for both halves; we chain the two triples through it. -/
theorem Triple.seq (h₁ : Triple P s₁ R) (h₂ : Triple R s₂ Q) :
    Triple P (.seq s₁ s₂) Q := by
  intro σ σ' hP hstep
  cases hstep with
  | seq hs₁ hs₂ => exact h₂ _ _ (h₁ _ _ hP hs₁) hs₂

/-- The structural rule: no inversion needed, just function composition.
`consequence` is the glue in every VC generator: computed preconditions
rarely match the specification verbatim. -/
theorem Triple.consequence (h : Triple P s Q)
    (hpre : ∀ σ, P' σ → P σ) (hpost : ∀ σ, Q σ → Q' σ) :
    Triple P' s Q' := by
  intro σ σ' hP' hstep
  exact hpost _ (h _ _ (hpre _ hP') hstep)

/-- Two constructors can produce an `.ite` derivation; each hands us the
value of the test (`hc`), which we pass to the corresponding branch
triple. -/
theorem Triple.ite
    (h₁ : Triple (fun σ => P σ ∧ c.eval σ = true) s₁ Q)
    (h₂ : Triple (fun σ => P σ ∧ c.eval σ = false) s₂ Q) :
    Triple P (.ite c s₁ s₂) Q := by
  intro σ σ' hP hstep
  cases hstep with
  | ifTrue hc h => exact h₁ _ _ ⟨hP, hc⟩ h
  | ifFalse hc h => exact h₂ _ _ ⟨hP, hc⟩ h

/-!
Note on the while rule. The natural attempt

    intro σ σ' hI hstep
    induction hstep

fails: the induction motive fixes the statement to `.whileDo c inv body`,
but the `whileTrue` premise for the loop *body* is a derivation of a
different statement, so the induction principle rejects the motive (or
produces useless hypotheses). The standard fix — worth remembering, it
appears whenever you induct on a derivation with a fixed index — is to
*generalize the index*: prove the lemma for an arbitrary statement `ws`
together with an equation `ws = .whileDo c inv body`. Each case of the
induction then either refutes the equation (`nofun`: a `.skip` derivation
cannot be a `.whileDo` one) or uses it via `injection`.

The same technique appeared in Lecture 2 in miniature: generalizing the
accumulator before inducting (`sumToTR`). There the index was a value,
here it is a statement.
-/

/-- Auxiliary lemma: induction over the big-step derivation, with the
statement generalized so the induction goes through. -/
private theorem Triple.whileDo_aux {I : Assertion} {c : BExpr}
    {inv : Assertion} {body : Stmt}
    (hbody : Triple (fun σ => I σ ∧ c.eval σ = true) body I) :
    ∀ {σ ws σ'}, BigStep σ ws σ' → ws = .whileDo c inv body → I σ →
      I σ' ∧ c.eval σ' = false := by
  intro σ ws σ' hstep
  induction hstep with
  | whileTrue hc hb hrest ihb ihrest =>
    intro hws hI
    -- `injection` turns the constructor equation into equations on the
    -- fields (condition, invariant, body), which `subst` eliminates.
    injection hws with hc' hinv' hb'
    subst hc' hinv' hb'
    -- One loop iteration: the body preserves `I` (that is `hbody`), and
    -- the induction hypothesis for the remaining iterations finishes.
    exact ihrest rfl (hbody _ _ ⟨hI, hc⟩ hb)
  | whileFalse hc =>
    intro hws hI
    injection hws with hc' hinv' hb'
    subst hc'
    exact ⟨hI, hc⟩
  -- Every other constructor contradicts `ws = .whileDo ...`; `nofun`
  -- refutes the impossible equation in one word.
  | _ => nofun

/-- The while rule. Note the rule holds for an *arbitrary* annotation
`inv`: the annotation has no semantic content, so the rule cannot depend
on it. The VC generator (Section 3) is what ties the annotation to the
invariant actually used. -/
theorem Triple.whileDo {inv : Assertion}
    (h : Triple (fun σ => I σ ∧ c.eval σ = true) body I) :
    Triple I (.whileDo c inv body) (fun σ => I σ ∧ c.eval σ = false) := by
  intro σ σ' hI hstep
  exact Triple.whileDo_aux h hstep rfl hI

/-! ## 2. First verified programs

Note on notation: `σ⟦x⟧` is `State.get σ "x"` and `σ⟦x := v⟧` is
`State.set σ "x" v` (defined in `Imp/Syntax.lean`, with unexpanders so
goals display the same way). Specifications read like the programs they
specify. -/

def swapProg := [Imp|
  t := x;
  x := y;
  y := t;
]

/-- Note: the proof composes the rules from Section 1, starting from the
postcondition and working backwards. `Triple.assign` pushes the
postcondition through each assignment, `Triple.seq` chains the three
triples, and `Triple.consequence` closes the gap between the
specification and the computed precondition. That final entailment is
pure state bookkeeping: `grind` closes it using the `@[grind =]` lemmas
`State.get_set_same`/`State.get_set_ne` from `Imp/Basic.lean` (it decides
the string disequalities like `"x" ≠ "t"` on its own). Doing this by hand
for every program does not scale — that is the point of Section 3, where
the backwards composition becomes a *function*. -/
theorem swap_correct (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  have h := (Triple.assign _ "t" (.var "x")).seq
    ((Triple.assign _ "x" (.var "y")).seq
      (Triple.assign (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) "y" (.var "t")))
  refine Triple.consequence h ?_ (fun _ h => h)
  intro σ hσ
  simp only [Expr.eval]
  grind

/-- Note: `Triple.assign` has a *fixed-shape* precondition — the
postcondition pushed through the update — so `apply Triple.assign`
fails on goals whose precondition is anything else. `Triple.assign'`
fuses `assign` with `consequence`, and the proof term below *is* that
combination; the rule now applies to any pre/postcondition, leaving an
ordinary implication. The design rule generalizes: theorems meant for
`apply` must be stated for arbitrary goals. (Proving it directly by
inversion also works — `intro`, `cases`, done.) -/
theorem Triple.assign' (P Q : Assertion) (x : String) (e : Expr) :
    (∀ σ, P σ → Q (σ.set x (e.eval σ))) →
    Triple P (.assign x e) Q :=
  fun h => Triple.consequence (Triple.assign Q x e) h (fun _ h => h)

/-- Note: the continuation postcondition `fun s => Triple (· = s) s₂ Q`
says "from exactly the state `s₁` produced, the rest of the program
establishes `Q`" — and it is an ordinary assertion, because assertions
are arbitrary predicates on states. It is in fact a classical object:
the *safe region* of `s₂` (Dijkstra's weakest liberal precondition),
extracted from the universally quantified `Triple` by the singleton
precondition `(· = s)`, which records the "current state" of a symbolic
execution. Lecture 4b's shallow `wlp` makes this pointwise form
primitive — there, no encoding is needed. In the proof, the continuation is applied at
the intermediate state of the inverted `seq` derivation, with `rfl`
discharging the singleton.

Compare with `Triple.seq`: applying it invents a metavariable for the
intermediate assertion `R`, shared between two goals, and filling it
falls to unification and elaboration order. `seq'` produces one
goal and no metavariables — the property that matters when a tactic
(or `SymM`) drives thousands of such steps. -/
theorem Triple.seq' :
    Triple P s₁ (fun s => Triple (· = s) s₂ Q) →
    Triple P (.seq s₁ s₂) Q := by
  intro h₁ s s'' hp hb
  cases hb
  next s' h₂ h₃ => exact h₁ s s' hp h₂ s' s'' rfl h₃

/-- Note: the same fusion as `Triple.assign'`, one level up. The while
rule's fixed shape blocks `apply`; fusing with `consequence` frees the
pre- and postcondition, and the invariant comes from the *annotation* —
already present in the goal's statement, so `apply` introduces no
metavariable. The three premises are entry, preservation, and exit:
`whileDo'` is the VC generator's loop case as a standalone rule, and
`vcgen_sound` below now literally uses it. -/
theorem Triple.whileDo' {inv : Assertion}
    (hpre : ∀ σ, P σ → inv σ)
    (hbody : Triple (fun σ => inv σ ∧ c.eval σ = true) body inv)
    (hpost : ∀ σ, inv σ → c.eval σ = false → Q σ) :
    Triple P (.whileDo c inv body) Q :=
  Triple.consequence (Triple.whileDo hbody) hpre (fun σ h => hpost σ h.1 h.2)

/-- Note: read the proof as an execution trace — each
`seq'`/`assign'` pair steps one statement, and each `intro σᵢ hᵢ`
receives the intermediate state with the equation describing it. The
final `grind` chains the state equations through the get/set lemmas.
Compare all three `swap` proofs: backward composition (`swap_correct`),
forward stepping (this one), and computed (`vcg`, next section). The
forward-stepping style is symbolic execution; Lecture 4b does it in a
shallow embedding, and `SymM` is this loop industrialized — its
benchmark drives exactly this rule (there named `Exec.seq_cps`, for the
continuation-passing shape of the premise). -/
theorem swap_correct' (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  unfold swapProg
  apply Triple.seq'
  apply Triple.assign'
  intro σ₁ h₁
  apply Triple.seq'
  apply Triple.assign'
  intro σ₂ h₂
  apply Triple.assign'
  intro σ₃ h₃
  simp [Expr.eval] at *
  grind

/-! ## 3. The VC generator -/

/-- Note: `pre` computes preconditions *backwards* — the rule composition
from Section 2, as a function — and a loop's precondition is its
*annotated invariant*: the annotation we built into `Stmt` finally does
its job.

Restricted to loop-free programs, `pre` computes exactly Dijkstra's
*weakest liberal precondition* (wlp): the weakest `P` such that
`Triple P s Q` holds. Weakest-ness is a theorem, not part of the name —
extension idea 4 asks you to prove it. (*Liberal* means partial
correctness; Dijkstra's `wp` additionally requires termination.) On
loops, `pre` returns the annotation: sound by `vcgen_sound` below, but
only as weak as the invariant you wrote — choosing it is the human
step. -/
def Stmt.pre : Stmt → Assertion → Assertion
  | skip, Q => Q
  | assign x e, Q => fun σ => Q (σ.set x (e.eval σ))
  | seq s₁ s₂, Q => s₁.pre (s₂.pre Q)
  | ite c s₁ s₂, Q => fun σ => if c.eval σ then s₁.pre Q σ else s₂.pre Q σ
  | whileDo _ inv _, _ => inv

/-- Note: `vc` collects what remains to be *proved*: for each loop, the
invariant must be preserved by the body and must imply the postcondition
on exit. `skip` and `assign` contribute nothing, so on loop-free
programs `vc` is a conjunction of `True`s — no proof obligations at all;
`pre` alone carries the meaning. -/
def Stmt.vc : Stmt → Assertion → Prop
  | skip, _ => True
  | assign _ _, _ => True
  | seq s₁ s₂, Q => s₁.vc (s₂.pre Q) ∧ s₂.vc Q
  | ite _ s₁ s₂, Q => s₁.vc Q ∧ s₂.vc Q
  | whileDo c inv body, Q =>
    (∀ σ, inv σ → c.eval σ = true → body.pre inv σ) ∧
    (∀ σ, inv σ → c.eval σ = false → Q σ) ∧
    body.vc inv

/-- Note: the proof is by induction on the statement, generalizing `Q` —
in the `seq` case the induction hypothesis for `s₁` is used at
postcondition `s₂.pre Q`, not at `Q`. In each case we first `obtain` the
relevant conjuncts of `vc`; the `ite` case needs `consequence` to move
between the `if` in `pre` and the conjunction form `Triple.ite` expects
(`simpa [Stmt.pre, hc]` rewrites the `if` using the known test value).
The loop case is where the design pays off: `pre` of a loop *is* the
annotated invariant, so the entry premise of `Triple.whileDo'` is the
identity, the first VC turns the induction hypothesis into the
preservation premise, and the exit VC is the third premise verbatim —
the loop case *is* `whileDo'`. Nothing about this
proof is specific to our little language — this is the soundness
argument of every Floyd–Hoare VC generator. -/
theorem vcgen_sound (s : Stmt) (Q : Assertion) (h : s.vc Q) :
    Triple (s.pre Q) s Q := by
  induction s generalizing Q with
  | skip => exact Triple.skip Q
  | assign x e => exact Triple.assign Q x e
  | seq s₁ s₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact (ih₁ _ h₁).seq (ih₂ _ h₂)
  | ite c s₁ s₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    apply Triple.ite
    · apply Triple.consequence (ih₁ Q h₁) ?_ (fun _ h => h)
      intro σ hσ
      obtain ⟨hw, hc⟩ := hσ
      simpa [Stmt.pre, hc] using hw
    · apply Triple.consequence (ih₂ Q h₂) ?_ (fun _ h => h)
      intro σ hσ
      obtain ⟨hw, hc⟩ := hσ
      simpa [Stmt.pre, hc] using hw
  | whileDo c inv body ih =>
    obtain ⟨hpres, hexit, hbodyvc⟩ := h
    exact Triple.whileDo' (fun _ h => h)
      (Triple.consequence (ih inv hbodyvc) (fun σ h => hpres σ h.1 h.2)
        (fun _ h => h))
      hexit

theorem Stmt.verify (s : Stmt) (P Q : Assertion)
    (hvc : s.vc Q) (hpre : ∀ σ, P σ → s.pre Q σ) :
    Triple P s Q :=
  Triple.consequence (vcgen_sound s Q hvc) hpre (fun _ h => h)

/-- A one-line VC-generating tactic: apply the verified entry point, then
unfold the computed `vc`/`pre` into plain proof obligations. A macro like
this is the smallest possible example of extending Lean's tactic
language; real VC generators are tactics built the same way, just with
`SymM` doing the heavy lifting. -/
macro "vcg" : tactic =>
  `(tactic| apply Stmt.verify <;> try simp [Stmt.vc, Stmt.pre, Expr.eval, BExpr.eval])

/-- Note: `swap` is loop-free, so `vc` reduces to a conjunction of
`True`s and no proof obligation survives; `pre` computes the nested
state update. The one remaining goal is the entailment between the
specification and the computed precondition. Compare with the
rule-by-rule proof in Section 2: the program-specific part is now
computed, and the same `vcg <;> grind` will handle loops in the next
section. -/
example (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  unfold swapProg
  vcg <;> grind

/-! ## 4. Verify a loop -/

def copyProg (a : Int) := [Imp|
  y := 0;
  while (0 < x) invariant (fun σ => σ⟦x⟧ + σ⟦y⟧ = a ∧ 0 ≤ σ⟦x⟧) {
    x := x - 1;
    y := y + 1;
  }
]

#guard (Stmt.seq [Imp| x := 7;] (copyProg 7)).runGet "y" = some 7

/-- Note: after `Stmt.verify`, the proof is entirely generic: `simp`
unfolds the computed `vc`/`pre` into plain goals about integers and
`State.get`/`State.set`, and `grind` discharges them — the state
bookkeeping via the `@[grind =]` lemmas, the arithmetic (invariant
preservation needs `x + y = a ∧ 0 ≤ x` to survive `x := x - 1; y := y + 1`
under `0 < x`) via its linear integer arithmetic solver. Choosing the
invariant is the only creative step; everything after it is mechanical.
That division of labor is the whole message of this lecture. -/
theorem copy_correct (a : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ 0 ≤ a)
      (copyProg a)
      (fun σ => σ⟦y⟧ = a) := by
  unfold copyProg
  vcg <;> grind

/-- Note: the stepping style extends to loops because `whileDo'` is
apply-friendly: its invariant comes from the annotation, and its three
goals are exactly the verification conditions — entry (from the state
`y := 0` produced), preservation, and exit. Compare with
`copy_correct`: `vcg` computed these obligations; here they arrive one
`apply` at a time. Same facts, same `grind` finishers — the VC
generator is this stepping proof, mechanized. -/
theorem copy_correct' (a : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ 0 ≤ a)
      (copyProg a)
      (fun σ => σ⟦y⟧ = a) := by
  unfold copyProg
  apply Triple.seq'
  apply Triple.assign'
  intro σ₁ h₁
  apply Triple.whileDo'
  · intro σ h
    simp [Expr.eval] at *
    grind
  · apply Triple.seq'
    apply Triple.assign'
    intro σ₂ h₂
    apply Triple.assign'
    intro σ₃ h₃
    simp [Expr.eval, BExpr.eval] at *
    grind
  · intro σ hI hc
    simp [BExpr.eval, Expr.eval] at hc
    grind

/-! ## 5. The interpreter, verified -/

/-- Note: the statement keeps `∀ {σ' fuel'}` in the goal because the
induction hypotheses must be usable at *different* final states and
fuels — the `seq` case continues from an intermediate state, and the
`while` case at smaller fuel. `fun_induction Stmt.run` mirrors the
interpreter's own case analysis (eight cases: one per match arm), and
`Option.bind_eq_some_iff` converts "the bind produced `some`" into an
explicit intermediate state. Fuel monotonicity looks bureaucratic but
is the load-bearing lemma: completeness combines two sub-derivations
whose fuels differ, and this is what reconciles them. -/
theorem Stmt.run_mono {s : Stmt} {σ : State} {fuel : Nat} :
    ∀ {σ' fuel'}, s.run σ fuel = some σ' → fuel ≤ fuel' →
      s.run σ fuel' = some σ' := by
  fun_induction Stmt.run s σ fuel with
  | case1 => intro σ' fuel' h hle; simpa [Stmt.run] using h
  | case2 => intro σ' fuel' h hle; simpa [Stmt.run] using h
  | case3 σ s₁ s₂ fuel ih₁ ih₂ =>
    intro σ' fuel' h hle
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h₁, h₂⟩ := h
    simp only [Stmt.run, Option.bind_eq_some_iff]
    exact ⟨σ₁, ih₁ h₁ hle, ih₂ _ h₂ hle⟩
  | case4 σ c s₁ s₂ fuel hc ih =>
    intro σ' fuel' h hle
    simp only [Stmt.run, hc, if_true]
    exact ih h hle
  | case5 σ c s₁ s₂ fuel hc ih =>
    intro σ' fuel' h hle
    simp only [Stmt.run, hc, if_false, Bool.false_eq_true]
    exact ih h hle
  | case6 =>
    intro σ' fuel' h hle
    simp at h
  | case7 σ c inv body fuel hc ih₁ ih₂ =>
    intro σ' fuel' h hle
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h₁, h₂⟩ := h
    match fuel', hle with
    | fuel' + 1, hle =>
      simp only [Stmt.run, hc, if_true, Option.bind_eq_some_iff]
      exact ⟨σ₁, ih₁ h₁ (Nat.le_of_succ_le_succ hle),
        ih₂ _ h₂ (Nat.le_of_succ_le_succ hle)⟩
  | case8 σ c inv body fuel hc =>
    intro σ' fuel' h hle
    match fuel', hle with
    | fuel' + 1, _ =>
      simp only [Stmt.run, hc, if_false, Bool.false_eq_true]
      exact h

/-- Note: soundness is the easy direction — the interpreter's structure
already mirrors the derivation being built. `fun_induction` has reduced
`h` to the current branch on arrival, so most cases are `cases h` (which
substitutes the final state out of `some _ = some _`) followed by one
`BigStep` constructor. Only the boolean plumbing needs help: `simp at
hc` flips `¬(c.eval σ = true)` into `c.eval σ = false`. -/
theorem Stmt.run_sound {s : Stmt} {σ : State} {fuel : Nat} :
    ∀ {σ'}, s.run σ fuel = some σ' → BigStep σ s σ' := by
  fun_induction Stmt.run s σ fuel with
  | case1 =>
    intro σ' h
    cases h
    exact .skip
  | case2 =>
    intro σ' h
    cases h
    exact .assign
  | case3 σ s₁ s₂ fuel ih₁ ih₂ =>
    intro σ' h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h₁, h₂⟩ := h
    exact .seq (ih₁ h₁) (ih₂ _ h₂)
  | case4 σ c s₁ s₂ fuel hc ih =>
    intro σ' h
    exact .ifTrue hc (ih h)
  | case5 σ c s₁ s₂ fuel hc ih =>
    intro σ' h
    simp at hc
    exact .ifFalse hc (ih h)
  | case6 =>
    intro σ' h
    simp at h
  | case7 σ c inv body fuel hc ih₁ ih₂ =>
    intro σ' h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h₁, h₂⟩ := h
    exact .whileTrue hc (ih₁ h₁) (ih₂ _ h₂)
  | case8 σ c inv body fuel hc =>
    intro σ' h
    cases h
    simp at hc
    exact .whileFalse hc

/-- Note: completeness inducts on the *derivation*, and the interesting
step is fuel arithmetic: `seq` and `whileTrue` each hold two
sub-derivations with fuels `f₁` and `f₂`; `max f₁ f₂` serves both after
`Stmt.run_mono` bumps each up. `whileTrue` needs one unit more — the
loop head consumes it. The base cases are `⟨0, by simp [Stmt.run]⟩`,
not `⟨0, rfl⟩`: `Stmt.run` is well-founded recursion, which the kernel
cannot reduce definitionally — `simp` applies its equation lemmas
instead. (`#guard` never noticed because it runs compiled code — the
distinction between *evaluation* and *kernel reduction*, made visible.) -/
theorem Stmt.run_complete {σ σ' : State} {s : Stmt} (h : BigStep σ s σ') :
    ∃ fuel, s.run σ fuel = some σ' := by
  induction h with
  | skip => exact ⟨0, by simp [Stmt.run]⟩
  | assign => exact ⟨0, by simp [Stmt.run]⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    obtain ⟨f₁, h₁'⟩ := ih₁
    obtain ⟨f₂, h₂'⟩ := ih₂
    refine ⟨max f₁ f₂, ?_⟩
    simp only [Stmt.run, Option.bind_eq_some_iff]
    exact ⟨_, Stmt.run_mono h₁' (Nat.le_max_left f₁ f₂),
      Stmt.run_mono h₂' (Nat.le_max_right f₁ f₂)⟩
  | ifTrue hc h ih =>
    obtain ⟨f, h'⟩ := ih
    refine ⟨f, ?_⟩
    simp only [Stmt.run, hc, if_true]
    exact h'
  | ifFalse hc h ih =>
    obtain ⟨f, h'⟩ := ih
    refine ⟨f, ?_⟩
    simp only [Stmt.run, hc, if_false, Bool.false_eq_true]
    exact h'
  | whileTrue hc hbody hrest ihbody ihrest =>
    obtain ⟨f₁, h₁'⟩ := ihbody
    obtain ⟨f₂, h₂'⟩ := ihrest
    refine ⟨max f₁ f₂ + 1, ?_⟩
    simp only [Stmt.run, hc, if_true, Option.bind_eq_some_iff]
    exact ⟨_, Stmt.run_mono h₁' (Nat.le_max_left f₁ f₂),
      Stmt.run_mono h₂' (Nat.le_max_right f₁ f₂)⟩
  | whileFalse hc =>
    exact ⟨1, by simp [Stmt.run, hc]⟩

/-- Note: the classic proof of determinism is a double induction over
two derivations with an inversion in every case. The interpreter gives
it in four lines: functions are deterministic, and both derivations
factor through `Stmt.run` at fuel `max f₁ f₂`. A verified interpreter
is not just a testing tool — it is a *proof* tool. -/
theorem BigStep.deterministic {σ σ₁ σ₂ : State} {s : Stmt}
    (h₁ : BigStep σ s σ₁) (h₂ : BigStep σ s σ₂) : σ₁ = σ₂ := by
  obtain ⟨f₁, r₁⟩ := Stmt.run_complete h₁
  obtain ⟨f₂, r₂⟩ := Stmt.run_complete h₂
  have m₁ := Stmt.run_mono r₁ (Nat.le_max_left f₁ f₂)
  have m₂ := Stmt.run_mono r₂ (Nat.le_max_right f₁ f₂)
  grind

/-- Note: the payoff. Every `#guard prog.runGet "x" = some v` in
`Imp/Examples.lean` is, through this lemma, a witness that *some*
`BigStep` execution of `prog` ends with `x = v` — the tests were
theorems about the semantics all along. -/
theorem Stmt.runGet_sound {s : Stmt} {x : String} {v : Int} {fuel : Nat}
    (h : s.runGet x fuel = some v) :
    ∃ σ', BigStep State.init s σ' ∧ σ'.get x = v := by
  unfold Stmt.runGet at h
  match hr : s.run State.init fuel with
  | none => rw [hr] at h; simp at h
  | some σ' =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨σ', Stmt.run_sound hr, h⟩
