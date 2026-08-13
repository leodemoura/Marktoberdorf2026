import VersoSlides
import Verso.Doc.Concrete
open VersoSlides

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option verso.code.warnLineLength 100

#doc (Slides) "Software Verification in Lean" =>

# Software Verification in Lean

%%%
backgroundColor := "#0073A3"
%%%

Lecture 4 of 4

Leonardo de Moura

AWS | Lean FRO

# Recap

- Lecture 1: propositions are types; proofs are terms; the kernel checks
  everything.
- Lecture 2: inductive types, type classes, macros; proofs about
  programs; generalize the invariant.
- Lecture 3: `simp`, `grind`, `bv_decide`; AI writes proofs, the kernel
  checks them.

Today: put the pieces together — a verification framework, built inside
Lean, and the engineering required to make one scale.

# Today

1. Verification frameworks in industrial use, all built as Lean libraries.
2. A verification condition generator for a small imperative language —
   with a soundness theorem.
3. The same programs, shallowly embedded; symbolic execution as a
   metaprogram.
4. Scalability: where the time goes, and the `SymM` framework.

# Verification Frameworks as Lean Libraries

From the course abstract:

> Lean's extensibility enables the construction of entire domain-specific verification frameworks, including custom specification languages, proof strategies, and automation pipelines, all within Lean itself, with no need for external tools or trusted code generators.

# SampCert (AWS): Verified Differential Privacy

An open-source Lean library of formally verified differential privacy
primitives.

- The verified implementation replaced a previous one — and is *twice as
  fast*.
- The correctness arguments need real mathematics: Fourier analysis,
  number theory, topology — supplied by Mathlib.
- Deployed in [AWS Clean Rooms Differential Privacy](https://aws.amazon.com/clean-rooms/).
- PLDI 2025: "Verified Foundations for Differential Privacy."

> "I started using Lean because of Mathlib, but I realized that Lean isn't just an excellent proof assistant, it's also a very pleasant and efficient programming language with a great ecosystem." — Jean-Baptiste Tristan

# Waimea (AWS): a Verified Compiler for Trainium

CompCert-style verified compiler for AWS Trainium, Amazon's AI
accelerator. *~500,000 lines of Lean.*

- The ISA specification changes *several times per week* — not a fixed
  target like x86.
- The Lean model doubles as a simulator shared by hardware and
  verification engineers.
- *Used to find hardware and simulator bugs, and to prove the correctness
  of hardware optimizations.*
- Long-term goal: end-to-end compilation with a semantics-preservation
  proof.

# Kraken (Google): x64 Semantics in Lean

[Kraken](https://github.com/AeneasVerif/kraken): a formal model of x64
for verifying sequential machine code.
[Jonathan Protzenko](https://jonathan.protzenko.fr/) and
[Andres Erbsen](https://andres.systems/); started after the
[Lean@Google hackathon](https://sites.google.com/view/lean-at-googl-2025/home),
December 2025.

- This lecture's architecture, applied to an instruction set: embed the
  machine language, give it a semantics, verify against it.
- The semantics is *designed for proof automation*, with lessons from
  Bedrock2: the interpreter either computes a weakest precondition or a
  final state.
- x64 today; arm64 in progress; RISC-V on the roadmap.
- Status: pre-alpha — the tactic layer still needs Lean-side support to
  prove non-trivial programs. Andres returns in the scalability section,
  where exactly that Lean-side support is the subject.

# Veil: Verified Distributed Protocols

[Veil](https://veil.dev/): verification of distributed protocols,
built on Lean via metaprogramming. Pîrlea, Gladshtein, Kinsbruner,
Zhao, Sergey.

:::hstack
- Push-button verification through SMT (cvc5/Z3) for decidable fragments;
  full interactive Lean proofs when automation falls short.
- *Foundational*: Veil's VC generator is proven sound with respect to the
  specification language semantics.
- 16 distributed protocol case studies; all 16 verified (Ivy failed
  on 2); 87.5% verified in under 15 seconds.

{image "../static/images/veil-code.png" (width := "55%")}[Veil: ring leader election]
:::

# Strata (AWS): Language Syntax and Semantics

[Strata](https://strata-org.github.io/Strata/): an extensible platform
for formalizing language syntax and semantics. Open source.

- Organizing idea: *dialects* (inspired by MLIR) — composable building
  blocks for modeling programming constructs.
- Pipeline example: Python/Java/JavaScript → Laurel → Strata Core →
  VC generation → SMT.
- The dialect definition mechanism is an embedded DSL in Lean — the
  macro machinery from Lecture 2, at industrial scale.

{image "../static/images/strata-logo.png"}[Strata logo]

# A Common Structure

Each of these systems has the same architecture:

1. *Embed* the object language (Rust, a protocol language, an ISA) in
   Lean.
2. Give it a *semantics* — a function or an inductive relation.
3. Compute *verification conditions*.
4. Discharge them — `simp`, `grind`, `bv_decide`, interactive proofs.

[Signal Shot](https://www.beneficialaifoundation.org/blog/signal-shot) —
verifying the Signal protocol and its Rust implementation (Signal, the
Beneficial AI Foundation, and the Lean FRO) — is assembling exactly
these components: [Aeneas](https://aeneasverif.github.io/), [Mathlib](https://mathlib-initiative.org/) and [CSLib](https://www.cslib.io/), `grind` and `SymM`, AI.

# A Small Verifier, End to End

%%%
backgroundColor := "#0073A3"
%%%

The code is in the exercises project.

# The Language: Imp

```lean -show
private def State : Type := String → Int
private def State.init : State := fun _ => 0
private def State.get (σ : State) (x : String) : Int := σ x
private def State.set (σ : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else σ y
@[grind =] private theorem State.get_set_same (σ : State) (x : String) (v : Int) :
    (σ.set x v).get x = v := by
  simp [State.get, State.set]
@[grind =] private theorem State.get_set_ne (σ : State) (x y : String) (v : Int)
    (h : y ≠ x) : (σ.set x v).get y = σ.get y := by
  simp [State.get, State.set, h]
private inductive Expr where
  | const (n : Int)
  | var   (x : String)
  | add   (a b : Expr)
  | sub   (a b : Expr)
  | mul   (a b : Expr)
private def Expr.eval (σ : State) : Expr → Int
  | .const n => n
  | .var x   => σ.get x
  | .add a b => a.eval σ + b.eval σ
  | .sub a b => a.eval σ - b.eval σ
  | .mul a b => a.eval σ * b.eval σ
inductive BExpr where
  | tt
  | lt  (a b : Expr)
  | le  (a b : Expr)
  | eq  (a b : Expr)
  | not (c : BExpr)
  | and (c d : BExpr)
def BExpr.eval (σ : State) : BExpr → Bool
  | .tt      => true
  | .lt a b  => a.eval σ < b.eval σ
  | .le a b  => a.eval σ ≤ b.eval σ
  | .eq a b  => a.eval σ == b.eval σ
  | .not c   => !c.eval σ
  | .and c d => c.eval σ && d.eval σ
```

```lean
def Assertion : Type := State → Prop

inductive Stmt where
  | skip
  | assign  (x : String) (e : Expr)
  | seq     (s₁ s₂ : Stmt)
  | ite     (c : BExpr) (s₁ s₂ : Stmt)
  | whileDo (c : BExpr) (inv : Assertion) (body : Stmt)
```

- `State`, its `get`/`set` API and notation, and the expression
  evaluator are Lecture 2's, unchanged; `BExpr` adds boolean tests.
  Only `Stmt` is new.
- `whileDo` carries an *invariant annotation* `inv` — input for the
  verifier. The semantics will ignore it.

# The `[Imp| ...]` Grammar

```lean -show
syntax (name := exprScope) "[Expr|" term "]" : term
macro_rules
  | `([Expr| $n:num])   => `(Expr.const $n)
  | `([Expr| -$n:num])  => `(Expr.const (-$n))
  | `([Expr| $x:ident]) => `(Expr.var $(Lean.quote x.getId.toString))
  | `([Expr| ($e)])     => `([Expr| $e])
  | `([Expr| $a + $b])  => `(Expr.add [Expr| $a] [Expr| $b])
  | `([Expr| $a - $b])  => `(Expr.sub [Expr| $a] [Expr| $b])
  | `([Expr| $a * $b])  => `(Expr.mul [Expr| $a] [Expr| $b])
syntax "[BExpr|" term "]" : term
macro_rules
  | `([BExpr| true])     => `(BExpr.tt)
  | `([BExpr| ($c)])     => `([BExpr| $c])
  | `([BExpr| !$c])      => `(BExpr.not [BExpr| $c])
  | `([BExpr| $a && $b]) => `(BExpr.and [BExpr| $a] [BExpr| $b])
  | `([BExpr| $a < $b])  => `(BExpr.lt [Expr| $a] [Expr| $b])
  | `([BExpr| $a ≤ $b])  => `(BExpr.le [Expr| $a] [Expr| $b])
  | `([BExpr| $a == $b]) => `(BExpr.eq [Expr| $a] [Expr| $b])
```

```lean
declare_syntax_cat impStmt

syntax ident " := " term "; " : impStmt
syntax "if" " (" term ")" " {" impStmt* "}" " else" " {" impStmt* "}" : impStmt
syntax "while" " (" term ")" ppLine " {" impStmt* "}" : impStmt
syntax "while" " (" term ")" " invariant" " (" term ")" ppLine " {" impStmt* "}" : impStmt
syntax "[Imp|" impStmt* "]" : term

open Lean in
macro_rules
  | `([Imp| ]) => `(Stmt.skip)
  | `([Imp| $x:ident := $e:term;]) => `(Stmt.assign $(quote x.getId.toString) [Expr| $e])
  | `([Imp| if ($c) { $ts* } else { $es* }]) => `(Stmt.ite [BExpr| $c] [Imp| $ts*] [Imp| $es*])
  | `([Imp| while ($c) { $bs* }]) => `(Stmt.whileDo [BExpr| $c] (fun _ => True) [Imp| $bs*])
  | `([Imp| while ($c) invariant ($I) { $bs* }]) => `(Stmt.whileDo [BExpr| $c] $I [Imp| $bs*])
  | `([Imp| $s $ss*]) => `(Stmt.seq [Imp| $s] [Imp| $ss*])

```

- `declare_syntax_cat` creates a new *syntactic category*: statements
  are not terms — they get their own grammar, and `impStmt*` means "a
  sequence of them". Lecture 2's `[Expr|` extended the `term` grammar;
  a statement language needs its own.
- `[Imp| ...]` is the bridge back: a *term* whose contents are parsed
  with the statement grammar. (`[Expr|` and `[BExpr|` are analogous,
  and hidden here.)

# Concrete Syntax

```lean -show
section
open Lean
syntax:max (name := stateGet) term "⟦" ident "⟧" : term
macro_rules
  | `($s ⟦$x⟧) => `(State.get $s $(quote x.getId.toString))
@[app_unexpander State.get] meta def unexpandStateGet : PrettyPrinter.Unexpander
  | `($(_) $s:term $x:str) =>
    let id := mkIdent (Name.mkSimple x.getString)
    `($s ⟦$id⟧)
  | _ => throw ()
syntax:max (name := stateSet) term "⟦" ident " := " term "⟧" : term
macro_rules
  | `($s ⟦$x := $v⟧) => `(State.set $s $(quote x.getId.toString) $v)
@[app_unexpander State.set] meta def unexpandStateSet : PrettyPrinter.Unexpander
  | `($(_) $s:term $x:str $v:term) =>
    let id := mkIdent (Name.mkSimple x.getString)
    `($s ⟦$id := $v⟧)
  | _ => throw ()
end
section
open Lean PrettyPrinter

@[app_unexpander Expr.const] meta def unexpandExprConst : Unexpander
  | `($(_) $n:num) => `([Expr| $n:num])
  | _ => throw ()

@[app_unexpander Expr.var] meta def unexpandExprVar : Unexpander
  | `($(_) $x:str) =>
    let id := mkIdent (Name.mkSimple x.getString)
    `([Expr| $id:ident])
  | _ => throw ()

@[app_unexpander Expr.add] meta def unexpandExprAdd : Unexpander
  | `($(_) [Expr| $a] [Expr| $b]) => `([Expr| $a + $b])
  | _ => throw ()

@[app_unexpander Expr.sub] meta def unexpandExprSub : Unexpander
  | `($(_) [Expr| $a] [Expr| $b]) => `([Expr| $a - $b])
  | _ => throw ()

@[app_unexpander Expr.mul] meta def unexpandExprMul : Unexpander
  | `($(_) [Expr| $a] [Expr| $b]) => `([Expr| $a * $b])
  | _ => throw ()

@[app_unexpander BExpr.lt] meta def unexpandBExprLt : Unexpander
  | `($(_) [Expr| $a] [Expr| $b]) => `([BExpr| $a < $b])
  | _ => throw ()

@[app_unexpander BExpr.le] meta def unexpandBExprLe : Unexpander
  | `($(_) [Expr| $a] [Expr| $b]) => `([BExpr| $a ≤ $b])
  | _ => throw ()

@[app_unexpander BExpr.eq] meta def unexpandBExprEq : Unexpander
  | `($(_) [Expr| $a] [Expr| $b]) => `([BExpr| $a == $b])
  | _ => throw ()

@[app_unexpander BExpr.not] meta def unexpandBExprNot : Unexpander
  -- `!` binds at max precedence, so the argument is always parenthesized.
  | `($(_) [BExpr| $c]) => `([BExpr| !($c)])
  | _ => throw ()

@[app_unexpander BExpr.and] meta def unexpandBExprAnd : Unexpander
  | `($(_) [BExpr| $c] [BExpr| $d]) => `([BExpr| $c && $d])
  | _ => throw ()

@[app_unexpander Stmt.assign] meta def unexpandStmtAssign : Unexpander
  | `($(_) $x:str [Expr| $e]) =>
    let id := mkIdent (Name.mkSimple x.getString)
    `([Imp| $id:ident := $e; ])
  | _ => throw ()

@[app_unexpander Stmt.seq] meta def unexpandStmtSeq : Unexpander
  | `($(_) [Imp| $s1*] [Imp| $s2*]) => `([Imp| $s1* $s2*])
  | _ => throw ()

@[app_unexpander Stmt.ite] meta def unexpandStmtIte : Unexpander
  | `($(_) [BExpr| $c] [Imp| $t*] [Imp| $e*]) =>
    `([Imp| if ($c) { $t* } else { $e* }])
  | _ => throw ()

@[app_unexpander Stmt.whileDo] meta def unexpandStmtWhile : Unexpander
  -- Loops always display with their invariant clause (a trivial
  -- annotation shows as `invariant (fun x => True)` — honest, if noisy).
  | `($(_) [BExpr| $c] $inv [Imp| $b*]) =>
    `([Imp| while ($c) invariant ($inv) { $b* }])
  | _ => throw ()

end
```

```lean
def factorial : Stmt := [Imp|
  n := 10;
  r := 1;
  while (0 < n) {
    r := r * n;
    n := n - 1;
  }
]
```

- After elaboration the quotation is gone: `factorial : Stmt`,
  ordinary data built from `seq`, `assign`, and `whileDo`.
- `σ⟦x⟧`/`σ⟦x := v⟧` are Lecture 2's notation. Unexpanders print
  states *and programs* back in the same syntax — goals stay readable
  while stepping.

# Operational Semantics

```lean
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
```

- `BigStep σ s σ'`: executing `s` from state `σ` terminates in `σ'`.
- One constructor per rule; derivations are finite, so the
  relation captures *terminating* runs.
- The invariant annotation is ignored — it has no semantic content.

# Executing Programs

```lean -show
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
```

```lean
def Stmt.runGet (s : Stmt) (x : String) (fuel : Nat := 1000) : Option Int :=
  (s.run State.init fuel).map (·.get x)

#eval factorial.runGet "r"
#guard factorial.runGet "r" = some 3628800
#guard factorial.runGet "n" = some 0
```

- A fuel-bounded interpreter (Lecture 2's pattern for possibly
  nonterminating recursion) makes programs executable.
- `#guard` tests before proofs, as always.

# The Interpreter, Verified

```lean -show
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
theorem Stmt.run_sound {s : Stmt} {σ : State} {fuel : Nat} :
    ∀ {σ'}, s.run σ fuel = some σ' → BigStep σ s σ' := by
  fun_induction Stmt.run s σ fuel with
  | case1 => intro σ' h; cases h; exact .skip
  | case2 => intro σ' h; cases h; exact .assign
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
  | case6 => intro σ' h; simp at h
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
theorem BigStep.deterministic {σ σ₁ σ₂ : State} {s : Stmt}
    (h₁ : BigStep σ s σ₁) (h₂ : BigStep σ s σ₂) : σ₁ = σ₂ := by
  obtain ⟨f₁, r₁⟩ := Stmt.run_complete h₁
  obtain ⟨f₂, r₂⟩ := Stmt.run_complete h₂
  have m₁ := Stmt.run_mono r₁ (Nat.le_max_left f₁ f₂)
  have m₂ := Stmt.run_mono r₂ (Nat.le_max_right f₁ f₂)
  grind
```

```lean
#check Stmt.run_mono
#check Stmt.run_sound
#check Stmt.run_complete
#check BigStep.deterministic
```

- *Sound*: whatever the interpreter computes, the semantics derives.
  *Complete*: whatever the semantics derives, some fuel computes.
  Together: `run` and `BigStep` describe the same language, so every
  `#guard` on the previous slide is a theorem about the semantics.
- All of it is in the exercises, with hints; *fuel monotonicity* is
  the workhorse lemma.

# Specifications: Hoare Triples

```lean
def Triple (P : Assertion) (s : Stmt) (Q : Assertion) : Prop :=
  ∀ σ σ', P σ → BigStep σ s σ' → Q σ'

def Stmt.wlp (s : Stmt) (Q : Assertion) : Assertion :=
  fun σ => Triple (· = σ) s Q

theorem wlp_iff (s : Stmt) (Q : Assertion) (σ : State)
    : s.wlp Q σ ↔ ∀ σ', BigStep σ s σ' → Q σ' := by
  unfold Stmt.wlp Triple; simp; constructor
  · intro h σ';
    exact h σ σ' rfl
  · intro h σ' σ'' he hb
    subst σ'
    apply h σ'' hb

theorem Triple_iff_wlp (P : Assertion) (s : Stmt) (Q : Assertion)
    : Triple P s Q ↔ ∀ σ, P σ → s.wlp Q σ := by
  simp [wlp_iff, Triple]; grind
```

- Partial correctness: *if* `P` holds initially *and* `s` terminates,
  *then* `Q` holds finally.
- `s.wlp Q` is the *safe region* of `s` — every terminating run from `σ` establishes `Q`. This is Dijkstra's
  *weakest liberal precondition*.
- Not a new logic: `Triple` is a definition, and the "rules" of Hoare
  logic will be ordinary theorems about it.

# The Rules Are Theorems

```lean
theorem Triple.skip (Q : Assertion) : Triple Q .skip Q := by
  intro σ σ' h hstep
  cases hstep
  exact h

theorem Triple.assign (Q : Assertion) (x : String) (e : Expr) :
    Triple (fun σ => Q (σ.set x (e.eval σ))) (.assign x e) Q := by
  intro σ σ' h hstep
  cases hstep
  exact h

theorem Triple.consequence (h : Triple P s Q)
    (hpre : ∀ σ, P' σ → P σ) (hpost : ∀ σ, Q σ → Q' σ) :
    Triple P' s Q' := by
  intro σ σ' hP' hstep
  exact hpost _ (h _ _ (hpre _ hP') hstep)
```

```lean -show
theorem Triple.ite
    (h₁ : Triple (fun σ => P σ ∧ c.eval σ = true) s₁ Q)
    (h₂ : Triple (fun σ => P σ ∧ c.eval σ = false) s₂ Q) :
    Triple P (.ite c s₁ s₂) Q := by
  intro σ σ' hP hstep
  cases hstep with
  | ifTrue hc h => exact h₁ _ _ ⟨hP, hc⟩ h
  | ifFalse hc h => exact h₂ _ _ ⟨hP, hc⟩ h
```

- Proof method: unfold `Triple`, *invert* the derivation with `cases` —
  for a fixed statement shape, only matching `BigStep` constructors
  apply.
- `consequence` is the structural rule: weaken the precondition,
  strengthen the postcondition.
- The assignment rule pushes the postcondition *backwards* through the
  update — nothing is computed forwards.

# Applying the Assignment Rule

```lean +error
example (a : Int) :
    Triple (fun σ => σ⟦x⟧ = a)
      (.assign "y" (.const 0))
      (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = 0) := by
  apply Triple.assign


```

```lean
theorem Triple.assign' (P Q : Assertion) (x : String) (e : Expr) :
    (∀ σ, P σ → Q (σ.set x (e.eval σ))) →
    Triple P (.assign x e) Q :=
  fun h => Triple.consequence (Triple.assign Q x e) h (fun _ h => h)
```

- `Triple.assign`'s precondition has a *fixed shape* — the postcondition
  pushed through the update. An arbitrary precondition does not unify
  with it, so `apply` fails.
- `Triple.assign'` fuses `assign` with `consequence` — the proof term
  *is* the combination. It applies to any pre/postcondition, leaving an
  ordinary implication.
- The design rule: theorems meant for `apply` must be stated for
  arbitrary goals.

# Sequencing Without Metavariables

```lean
theorem Triple.seq (h₁ : Triple P s₁ R) (h₂ : Triple R s₂ Q) :
    Triple P (.seq s₁ s₂) Q := by
  intro σ σ' hP hstep
  cases hstep with
  | seq hs₁ hs₂ => exact h₂ _ _ (h₁ _ _ hP hs₁) hs₂

theorem Triple.seq' :
    Triple P s₁ (fun σ => Triple (· = σ) s₂ Q) →
    Triple P (.seq s₁ s₂) Q := by
  intro h₁ σ₁ σ₃ hp hb
  cases hb
  next σ₂ h₂ h₃ => exact h₁ σ₁ σ₂ hp h₂ σ₂ σ₃ rfl h₃
```

- Applying `seq` invents a *metavariable* for the intermediate assertion
  `R`, shared by two goals — filling it falls to unification and
  elaboration order.
- `seq'` produces *one* goal and no metavariables: its postcondition
  is definitionally `s₂.wlp Q` — the safe region of `s₂`, from the
  Triples slide.
- Intermediate states later enter as `intro`-bound variables, not holes.

# The While Rule

```lean -show
private theorem Triple.whileDo_aux {I : Assertion} {c : BExpr}
    {inv : Assertion} {body : Stmt}
    (hbody : Triple (fun σ => I σ ∧ c.eval σ = true) body I) :
    ∀ {σ ws σ'}, BigStep σ ws σ' → ws = .whileDo c inv body → I σ →
      I σ' ∧ c.eval σ' = false := by
  intro σ ws σ' hstep
  induction hstep with
  | whileTrue hc hb hrest ihb ihrest =>
    intro hws hI
    injection hws with hc' hinv' hb'
    subst hc' hinv' hb'
    exact ihrest rfl (hbody _ _ ⟨hI, hc⟩ hb)
  | whileFalse hc =>
    intro hws hI
    injection hws with hc' hinv' hb'
    subst hc'
    exact ⟨hI, hc⟩
  | skip => nofun
  | assign => nofun
  | seq _ _ _ _ => nofun
  | ifTrue _ _ _ => nofun
  | ifFalse _ _ _ => nofun
```

```lean
theorem Triple.whileDo {inv : Assertion}
    (h : Triple (fun σ => I σ ∧ c.eval σ = true) body I) :
    Triple I (.whileDo c inv body) (fun σ => I σ ∧ c.eval σ = false) := by
  intro σ σ' hI hstep
  exact Triple.whileDo_aux h hstep rfl hI

theorem Triple.whileDo' {inv : Assertion}
    (hpre : ∀ σ, P σ → inv σ)
    (hbody : Triple (fun σ => inv σ ∧ c.eval σ = true) body inv)
    (hpost : ∀ σ, inv σ → c.eval σ = false → Q σ) :
    Triple P (.whileDo c inv body) Q :=
  Triple.consequence (Triple.whileDo hbody) hpre (fun σ h => hpost σ h.1 h.2)
```

- The proof of `whileDo` needs the technique from Lecture 2:
  *generalize the statement* before inducting on the derivation.
- `whileDo` ignores its annotation (it has no semantic role), and its
  fixed shape blocks `apply` — the assignment story again.
- `Triple.whileDo'` fuses it with `consequence` and takes the invariant
  *from the annotation*: it applies to any goal, with no metavariable —
  and its three premises are entry, preservation, and exit: the loop's
  verification conditions, before we ever define `vc`.

# A First Verified Program

```lean
def swapProg := [Imp|
  t := x;
  x := y;
  y := t;
]

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
```

- Compose the rules backwards from the postcondition; `consequence`
  closes the gap to the specification; `grind` handles the state
  bookkeeping with the two `[grind =]` lemmas from Lecture 3.
- Correct, but manual — one rule application per statement.

# Stepping Through the Program

```lean
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
```

- Only the `apply`-friendly rules appear: `seq'` (no metavariables)
  and `assign'` (any precondition) — the design from the previous
  slides, in action.
- The proof *follows the structure of the program*, one rule application
  per statement, receiving each intermediate state with `intro` —
  symbolic execution, in the deep embedding.
- This style returns twice today: in the shallow embedding, and in
  `SymM`, whose benchmark drives exactly this `seq'` rule.

# The Precondition Transformer

```lean
def Stmt.pre : Stmt → Assertion → Assertion
  | .skip, Q => Q
  | .assign x e, Q => fun σ => Q (σ.set x (e.eval σ))
  | .seq s₁ s₂, Q => s₁.pre (s₂.pre Q)
  | .ite c s₁ s₂, Q => fun σ => if c.eval σ then s₁.pre Q σ else s₂.pre Q σ
  | .whileDo _ inv _, _ => inv
```

- The backwards composition of `swap_correct`, as a *function* — and
  a loop's precondition is its *annotated invariant*: the annotation
  we built into `Stmt` finally does its job.
- This is the textbook construction: Nipkow & Klein, *Concrete
  Semantics*, §12.2.2 defines `pre` and `vc` (same names) over annotated
  commands; Gordon's Hoare-logic notes (ch. 3) and *Software
  Foundations* (Hoare2) present the same generator.

# The Verification Conditions

```lean
def Stmt.vc : Stmt → Assertion → Prop
  | .skip, _ => True
  | .assign _ _, _ => True
  | .seq s₁ s₂, Q => s₁.vc (s₂.pre Q) ∧ s₂.vc Q
  | .ite _ s₁ s₂, Q => s₁.vc Q ∧ s₂.vc Q
  | .whileDo c inv body, Q =>
    (∀ σ, inv σ → c.eval σ = true → body.pre inv σ) ∧
    (∀ σ, inv σ → c.eval σ = false → Q σ) ∧
    body.vc inv
```

- `vc` collects what remains to be *proved*: for each loop, preservation
  of its invariant and the exit implication; `skip` and `assign`
  contribute nothing.
- On loop-free programs `vc` is a conjunction of `True`s — no proof
  obligations at all; `pre` alone carries the meaning.

# The Soundness Theorem

```lean -show
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
```

```lean
#check vcgen_sound
theorem Stmt.verify (s : Stmt) (P Q : Assertion)
    (hvc : s.vc Q) (hpre : ∀ σ, P σ → s.pre Q σ) : Triple P s Q :=
  Triple.consequence (vcgen_sound s Q hvc) hpre (fun _ h => h)
```

- `vcgen_sound`: discharge the VCs and the triple holds. Proved by
  induction; the loop case is `Triple.whileDo'` applied to the
  induction hypothesis.

# `swap`, Revisited

```lean
macro "vcg" : tactic => `(tactic|
  apply Stmt.verify <;>
    try simp [Stmt.vc, Stmt.pre, Expr.eval, BExpr.eval])

example (a b : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ σ⟦y⟧ = b)
      swapProg
      (fun σ => σ⟦x⟧ = b ∧ σ⟦y⟧ = a) := by
  unfold swapProg
  vcg <;> grind
```

- `vcg` is a two-line tactic macro: apply `Stmt.verify`, then unfold the
  computed `vc` and `pre`. `swap` is loop-free, so no verification
  conditions survive; the one remaining goal is the entailment between
  specification and computed precondition — `grind` discharges it.
- On the loop-free fragment, `pre` computes Dijkstra's *weakest liberal
  precondition* — weakest provably, not just by name (exercise
  extension); *liberal* means partial correctness, where Dijkstra's
  `wp` additionally requires termination.
- On loops, `pre` returns the annotation: *sound*,
  but only as weak as the invariant you wrote. Finding invariants is the
  creative step.

# A Loop, Verified

```lean
def copyProg (a : Int) := [Imp|
  y := 0;
  while (0 < x) invariant (fun σ => σ⟦x⟧ + σ⟦y⟧ = a ∧ 0 ≤ σ⟦x⟧) {
    x := x - 1;
    y := y + 1;
  }
]

theorem copy_correct (a : Int) :
    Triple (fun σ => σ⟦x⟧ = a ∧ 0 ≤ a)
      (copyProg a)
      (fun σ => σ⟦y⟧ = a) := by
  unfold copyProg
  vcg <;> grind
```

- The same `vcg <;> grind` as for `swap` — but this time obligations
  survive: the loop's verification conditions. `grind` discharges them —
  state bookkeeping by E-matching, arithmetic by `cutsat`.
- Choosing the invariant is the only creative step.

# Stepping Through the Loop

```lean
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
```

# Shallow Embeddings

%%%
backgroundColor := "#0073A3"
%%%

Removing the object language.

# Programs as Lean Programs

```lean -show
namespace Shallow
```

```lean
def Triple (P : S → Prop) (k : StateM S α) (Q : α → S → Prop) : Prop :=
  ∀ s, P s → Q (k s).1 (k s).2

def double : StateM Nat Unit := do
  let s ← get
  set (s + s)
```

- Imp was a *deep* embedding: programs are data, semantics is a
  relation. Shallow alternative: programs are ordinary monadic Lean
  code in Lecture 2's `StateM` — the style of mvcgen, Velvet, and
  Aeneas.
- The judgment is the same Hoare triple; only the semantics changed. A
  `StateM` program is a function, so "every terminating run" is *the*
  run: quantifying over `BigStep σ s σ'` becomes running the program —
  `(k s).1` the returned value, `(k s).2` the final state.
- No inductive semantics needed, and partial and total correctness
  coincide (`StateM` programs are total and deterministic).

# One Rule per Construct

```lean
theorem Triple.get (h : ∀ s, P s → Q s s) : Triple P get Q := by
  intro s hP
  simp [MonadState.get, getThe, MonadStateOf.get, StateT.get, Pure.pure]
  exact h _ hP

theorem Triple.bind (k₁ : StateM S α) (k₂ : α → StateM S β)
    (Q : β → S → Prop)
    (h : Triple P k₁ (fun a s => Triple (· = s) (k₂ a) Q)) : Triple P (k₁ >>= k₂) Q := by
  intro s hP
  exact h s hP (k₁ s).2 rfl
```

```lean -show
theorem Triple.pure (a : α) (h : ∀ s, P s → Q a s) : Triple P (pure a) Q := by
  intro s hP
  simp [Pure.pure, StateT.pure]
  exact h _ hP
theorem Triple.set (h : ∀ s, P s → Q () s') : Triple P (set s') Q := by
  intro s hP
  simp [MonadStateOf.set, StateT.set, Pure.pure]
  exact h _ hP
theorem Triple.modify (h : ∀ s, P s → Q () (f s)) : Triple P (modify f) Q := by
  intro s hP
  simp [_root_.modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Pure.pure]
  exact h _ hP
theorem Triple.ite {_ : Decidable c} (t e : StateM S α)
    (h₁ : c → Triple P t Q) (h₂ : ¬c → Triple P e Q) : Triple P (if c then t else e) Q := by
  split
  next h => exact h₁ h
  next h => exact h₂ h
theorem Triple.consequence (h : Triple P' k Q')
    (hpre : ∀ s, P s → P' s) (hpost : ∀ a s, Q' a s → Q a s) : Triple P k Q :=
  fun s hP => hpost _ _ (h s (hpre s hP))
```

- Part A's design carries over verbatim: every rule is primed —
  arbitrary `P`, no metavariables. `Triple.get` has the shape of
  `assign'`; `Triple.bind` *is* `seq'`, with the result value `a`
  passed to the continuation.
- The proofs are all simple.
- Rules for `pure`, `set`, `modify`, `ite`, and `consequence` complete
  the set.

# Symbolic Execution by `apply`

```lean
example (a : Nat) : Triple (· = a) double (fun _ s => s = 2 * a) := by
  unfold double
  apply Triple.bind
  apply Triple.get
  intro s h
  apply Triple.set
  intro s' h'
  grind
```

- The same stepping discipline as `swap` and `copyProg` in part A:
  `apply` the rule for the head of the program, `intro` the reached
  state.
- The final goal is the verification condition `s + s = 2 * a`, with
  `h : s = a` in context.
- Entirely mechanical — the rule is determined by the head of the
  program.

# A Metaprogram: Dispatch on the Head

```lean
open Lean Elab Tactic in
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

macro "sym_run" : tactic => `(tactic| repeat' sym_step)
```

- A tactic is a Lean program: read the goal, inspect the head, apply
  the matching rule — twenty lines. (Trying the rules blindly with
  `apply` would send the unifier unfolding `>>=` and `StateT`;
  dispatching on the head avoids the search.)
- This is the metaprogramming promised in the abstract, in its smallest
  useful form.

# Recursion Becomes Induction

```lean
def addN : Nat → StateM Nat Unit
  | 0 => pure ()
  | n + 1 => do
    modify (· + 1)
    addN n

theorem addN_correct (n : Nat) (a : Nat) :
    Triple (· = a) (addN n) (fun _ s' => s' = a + n) := by
  induction n generalizing a with
  | zero => simp only [addN]; sym_run; grind
  | succ n ih =>
    simp only [addN]
    sym_run
    exact Triple.consequence (ih _) (fun _ h => h) (by grind)
```

```lean -show
end Shallow
```

- `sym_run` executes up to the recursive call; the induction hypothesis
  plays the role of the loop invariant. `generalizing a` — Lecture 2's
  lesson, again: the recursive call starts from a different state.
- `Triple.consequence` bridges the induction hypothesis to the goal,
  the same role it played in part A.

# Scalability

%%%
backgroundColor := "#0073A3"
%%%

# VC Generation in Practice

A VC generator turns code and specifications into proof obligations.
Lean-based examples of the idiom we just built:

- *Aeneas* — Rust verification via translation to Lean.
- *Velvet* — a Dafny-style verifier built in Lean.
- *mvcgen* — Lean's VC generator for monadic programs.

{image "../static/images/vcgen-pipeline.svg"}[VC pipeline: code and specification into VC generator, proof obligations, tactics, kernel]

Verification condition generation with proof assistants has historically
not scaled — documented for Rocq by Chlipala's group, and the same held
in Lean.

# A Minimal Scaling Benchmark

[Andres Erbsen](https://andres.systems/) (Google; Bedrock2, Fiat
Cryptography) distilled the problem into a minimal challenge at the
Lean@Google hackathon: symbolically execute a generated `n`-step
program — the `apply`/`simp` loop from this lecture, at size `n`.

{image "../static/images/andres-scaling.svg" (height := "32vh")}[Andres' challenge: tactic time by goal size]

With Lean's general-purpose tactic framework (`MetaM`): *superlinear* —
2073 ms at n = 100, failure before n = 700.

# Where the Time Goes

The symbolic execution loop needs:

- efficient `apply` — no unification search (the reason `sym_step`
  dispatches on the head);
- efficient metavariable management;
- *term sharing* preserved by every operation — no copied trees;
- simplifier results *cached and reused* across obligations and steps;
- no repeated traversal of the same subterms.

General-purpose tactic frameworks pay for flexibility these loops do not
need — arbitrary proof-state surgery, full definitional unfolding in
matching.

# `SymM`

A monadic framework for symbolic simulation and VC generation, in the
Lean sources.

- The key invariant: the local context *grows monotonically* — no
  reverts, no deletions. Then pointer equality is a valid cache key, and
  automation state survives from one VC to the next.
- Precompiled backward rules; mostly-syntactic matching in the hot path.
- A new simplifier: pointer-keyed caches on maximally shared terms,
  binder traversal without quadratic cost.
- `grind` state threaded through the VC loop: facts learned once are
  reused across obligations.

# `SymM`: Measurements

:::hstack
{image "../static/images/symm-benchmark.png" (width := "80%")}[MetaM vs SymM tactic time]

{image "../static/images/symm-cache-reuse.png" (width := "80%")}[SymM with simplifier cache reuse]
:::

On the benchmark above: 16 ms at n = 100 (vs. 2073 ms) — about 100×;
linear out to n = 700.

# Ported Frameworks

:::hstack
{image "../static/images/mvcgen-tactic.svg" (height := "38vh")}[mvcgen tactic time]

{image "../static/images/mvcgen-kernel.svg" (height := "38vh")}[mvcgen kernel time]
:::

- *mvcgen* (Sebastian Graf): linear out to n = 1000 on the challenge.
- *Velvet* (V. Gladshtein): previously ~3× slower than Dafny; after the
  port, faster on 24 of 27 benchmarks. Dafny trusts its VC generator
  and an SMT solver; Velvet's chain is checked by the kernel.
- *DyLean* (T. Wallez, cryptographic protocols): `SymM` + incremental
  `grind` gave a 50× speedup in VC discharge.

# The Course, in Summary

1. *Foundations*: dependent type theory; propositions as types; the
   kernel as the single arbiter.
2. *Programming and proving*: inductive types, type classes, macros;
   design lemmas so proofs follow definitions.
3. *Automation*: `simp`, `grind`, `bv_decide` — inspectable,
   extensible, kernel-checked; AI as a user of the same machinery.
4. *Verification*: Hoare logic as theorems, VC generation as a verified
   function, symbolic execution as a metaprogram, and the engineering
   that scales it — all inside Lean: one kernel checks programs,
   specifications, proofs, and the verifier itself.

# Where to Go from Here

- Exercises: `Lecture4.lean` (the VC generator) and `Lecture4b.lean`
  (shallow embedding + `sym_step`) — both with full solutions and notes.
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) ·
  [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) ·
  [the reference manual](https://lean-lang.org/doc/reference/latest/)
- [CSLib](https://www.cslib.io/) — a growing library of computer
  science foundations; contributions welcome.
- [Mathlib](https://github.com/leanprover-community/mathlib4) — the mathematical library.
- [Iris Lean](https://leanprover-community.github.io/iris-lean/) —
  concurrent separation logic, being ported to Lean.
- [Software Foundations in Lean](https://github.com/plclub/sf-in-lean)
- [Lean Zulip](https://leanprover.zulipchat.com)

Material: [https://github.com/leodemoura/Marktoberdorf2026](https://github.com/leodemoura/Marktoberdorf2026)

# Thank You

%%%
backgroundColor := "#0073A3"
%%%

_Leo de Moura_

lean-lang.org | leanprover.zulipchat.com
