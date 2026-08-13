# Lean 4 for Program Verification in the Age of AI

Slides and exercises for the lecture series at the
[Marktoberdorf Summer School 2026](https://sites.google.com/view/marktoberdorf2026)
(August 11–22, 2026, Herrsching am Ammersee).

Leonardo de Moura, AWS | Lean FRO.

## Lectures

1. Introduction to Lean and Dependent Type Theory
2. Programming and Proving in Lean
3. Proof Automation and AI
4. Software Verification in Lean

Four lectures of 45 minutes. The slides are written in
[Verso](https://verso.lean-lang.org/), so every code example is checked by Lean.

## Structure

- `Lectures/` — one Verso slide deck per lecture
- `Main.lean` — renders the four decks into `_slides/`
- `exercises/` — standalone Lean project for students (no dependencies);
  see `exercises/README.md`

## Building the slides

```
lake build && lake exe marktoberdorf2026
python3 -m http.server 9090 --directory _slides
```

Then open http://localhost:9090.

## Exercises

Students only need the `exercises/` directory. It is a self-contained Lean
project using only the Lean standard library. See
[exercises/README.md](exercises/README.md) for setup instructions.

## License

Apache 2.0
