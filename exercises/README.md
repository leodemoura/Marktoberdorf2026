# Exercises — Lean 4 for Program Verification in the Age of AI

Marktoberdorf Summer School 2026, Leonardo de Moura.

## Setup

1. Clone the course repository:

   ```
   git clone https://github.com/leodemoura/Marktoberdorf2026.git
   ```

2. Install Lean following the official instructions: https://lean-lang.org/install/

3. Open this folder (`exercises/`) in VS Code and open any file in `Exercises/`.
   The correct Lean toolchain is downloaded automatically on first use.

No libraries to download: the exercises use only the Lean standard library.

If you cannot install anything, you can paste individual exercises into
[live.lean-lang.org](https://live.lean-lang.org).

## Contents

- `Exercises/Lecture1.lean` — functions, propositions as types, quantifiers
- `Exercises/Lecture2.lean` — inductive types, type classes, first program proofs
- `Exercises/Lecture3.lean` — proof automation: `simp`, `grind`, `bv_decide`
- `Exercises/Lecture4.lean` — the project, part A: a toy verification condition
  generator over a deeply embedded language
- `Exercises/Lecture4b.lean` — the project, part B: symbolic execution of
  shallowly embedded monadic programs, and a small tactic metaprogram
- `Imp/` — a small imperative language (given code, used by Lecture 4):
  AST and big-step semantics, concrete syntax (`` `[Imp| ...] ``), a
  fuel-based interpreter, and executable examples
- `Solutions/` — full solutions, with notes explaining the proofs

Exercises are ordered by difficulty within each file; the ones marked *(harder)* are
optional. They are invitations to play with Lean — nobody is expected to finish
everything during the school. Ask for help, and use the tools: `apply?`, `simp?`,
`exact?`, and [Loogle](https://loogle.lean-lang.org).
