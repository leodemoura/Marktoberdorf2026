import Imp.Basic

/-! # Imp Concrete Syntax

Custom syntax quotations for writing Imp programs naturally:

- `` [Expr| ...] `` for arithmetic expressions,
- `` [BExpr| ...] `` for boolean expressions,
- `` [Imp| ...] `` for statements.

For example:

```
def euclid := [Imp|
  while (!(a == b)) {
    if (a < b) { b := b - a; } else { a := a - b; }
  }
]
```

These macros are ordinary Lean metaprograms — the same mechanism used to
build full domain-specific languages on top of Lean.
-/

/-! ## Expressions -/

syntax "[Expr|" term "]" : term

macro_rules
  | `([Expr| $n:num])   => `(Expr.const $n)
  | `([Expr| -$n:num])  => `(Expr.const (-$n))
  | `([Expr| $x:ident]) => `(Expr.var $(Lean.quote x.getId.toString))
  | `([Expr| ($e)])     => `([Expr| $e])
  | `([Expr| $a + $b])  => `(Expr.add [Expr| $a] [Expr| $b])
  | `([Expr| $a - $b])  => `(Expr.sub [Expr| $a] [Expr| $b])
  | `([Expr| $a * $b])  => `(Expr.mul [Expr| $a] [Expr| $b])

/-! ## Boolean expressions -/

syntax "[BExpr|" term "]" : term

macro_rules
  | `([BExpr| true])     => `(BExpr.tt)
  | `([BExpr| ($c)])     => `([BExpr| $c])
  | `([BExpr| !$c])      => `(BExpr.not [BExpr| $c])
  | `([BExpr| $a && $b]) => `(BExpr.and [BExpr| $a] [BExpr| $b])
  | `([BExpr| $a < $b])  => `(BExpr.lt [Expr| $a] [Expr| $b])
  -- `<=` parses to the same syntax node as `≤`, so this rule covers both.
  | `([BExpr| $a ≤ $b])  => `(BExpr.le [Expr| $a] [Expr| $b])
  | `([BExpr| $a == $b]) => `(BExpr.eq [Expr| $a] [Expr| $b])

/-! ## Statements -/

declare_syntax_cat impStmt

-- There is no surface syntax for `skip`: an empty block `{ }` (or an empty
-- quotation `` [Imp| ] ``) already produces `Stmt.skip`. Reserving `skip`
-- as a keyword would break `Stmt.skip` patterns everywhere else.
syntax ident " := " term ";" : impStmt
syntax "if" " (" term ")" " {" impStmt* "}" " else" " {" impStmt* "}" : impStmt
syntax "while" " (" term ")" " {" impStmt* "}" : impStmt
syntax "while" " (" term ")" " invariant" " (" term ")" " {" impStmt* "}" : impStmt

syntax "[Imp|" impStmt* "]" : term

macro_rules
  | `([Imp| ]) => `(Stmt.skip)
  | `([Imp| $x:ident := $e:term;]) =>
    `(Stmt.assign $(Lean.quote x.getId.toString) [Expr| $e])
  | `([Imp| if ($c) { $ts* } else { $es* }]) =>
    `(Stmt.ite [BExpr| $c] [Imp| $ts*] [Imp| $es*])
  -- A `while` loop without an annotation gets the trivial invariant.
  | `([Imp| while ($c) { $bs* }]) =>
    `(Stmt.whileDo [BExpr| $c] (fun _ => True) [Imp| $bs*])
  -- The invariant is an arbitrary Lean term of type `Assertion`.
  | `([Imp| while ($c) invariant ($I) { $bs* }]) =>
    `(Stmt.whileDo [BExpr| $c] $I [Imp| $bs*])
  | `([Imp| $s $ss*]) =>
    `(Stmt.seq [Imp| $s] [Imp| $ss*])

/-! ## State access notation

`σ⟦x⟧` reads the program variable `x` (a `String` under the hood), and
`σ⟦x := v⟧` updates it. The unexpanders make proof goals display in the
same notation, so specifications stay readable while you prove.
-/

open Lean

syntax:max term noWs "⟦" ident "⟧" : term

macro_rules
  | `($s⟦$x⟧) => `(State.get $s $(quote x.getId.toString))

@[app_unexpander State.get] meta def unexpandStateGet : PrettyPrinter.Unexpander
  | `($(_) $s:term $x:str) =>
    let id := mkIdent (Name.mkSimple x.getString)
    `($s⟦$id⟧)
  | _ => throw ()

syntax:max term noWs "⟦" ident " := " term "⟧" : term

macro_rules
  | `($s⟦$x := $v⟧) => `(State.set $s $(quote x.getId.toString) $v)

@[app_unexpander State.set] meta def unexpandStateSet : PrettyPrinter.Unexpander
  | `($(_) $s:term $x:str $v:term) =>
    let id := mkIdent (Name.mkSimple x.getString)
    `($s⟦$id := $v⟧)
  | _ => throw ()

/-! ## Displaying goals in the concrete syntax

Unexpanders: `Expr`, `BExpr`, and `Stmt` values print back as
quotations, so goals stay readable during stepping proofs. Each rule
matches children that have already been unexpanded and splices them
into the surrounding quotation.
-/

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
    `([Imp| $id:ident := $e;])
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
