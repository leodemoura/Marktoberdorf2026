/-
Lecture 1 — Functions, propositions as types, quantifiers.

Replace each `sorry` with a definition or a proof. The file compiles as it
is; `sorry` marks the holes you should fill. Exercises get harder as you
go; the *(harder)* ones are optional.

Useful commands: `#check`, `#eval`, `#print`.
Useful tactics to discover things: `apply?`, `simp?`, `exact?`.
-/

/-! ## 1. Functions

Lean is a functional programming language: defining functions and applying
them is the core activity. -/

/-- Return twice the input. -/
def double (n : Nat) : Nat := sorry

-- Test your definition by uncommenting the next line:
-- #guard double 7 = 14

/-- Apply a function twice. -/
def twice (f : α → α) (x : α) : α := sorry

-- #guard twice (· + 3) 10 = 16
-- #guard twice double 1 = 4

/-- Function composition. -/
def compose (f : β → γ) (g : α → β) : α → γ := sorry

-- #guard compose (· * 2) (· + 1) 3 = 8

/-- One step of the Collatz function: `n / 2` if `n` is even, `3 * n + 1`
otherwise. Hint: the remainder function is `%`. -/
def collatzStep (n : Nat) : Nat := sorry

-- #guard collatzStep 6 = 3
-- #guard collatzStep 7 = 22

/-! ## 2. Propositions as types

A proposition is a type; a proof is a term of that type. Fill in the proof
terms below **without** using tactics. Remember:

- a proof of `p → q` is a function taking a proof of `p` to a proof of `q`
- a proof of `p ∧ q` is `⟨hp, hq⟩`
- from `h : p ∧ q` you get `h.1 : p` and `h.2 : q`
- a proof of `p ∨ q` is `Or.inl hp` or `Or.inr hq`
- from `h : p ∨ q` you can do case analysis: `h.elim (fun hp => _) (fun hq => _)`
- `¬p` unfolds to `p → False`
-/

example (p : Prop) (hp : p) : p := sorry

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := sorry

example (p q : Prop) (h : p ∧ q) : q ∧ p := sorry

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := sorry

example (p q : Prop) (h : p ∨ q) : q ∨ p := sorry

example (p : Prop) : ¬(p ∧ ¬p) := sorry

/-- *(harder)* -/
example (p q r : Prop) : (p → q → r) ↔ (p ∧ q → r) := sorry

/-! ## 3. The same proofs, with tactics

Now prove the same statements in tactic mode. Compare the proof terms
(`#print` them!) with what you wrote by hand above. Useful tactics:
`intro`, `exact`, `apply`, `constructor`, `cases`, `obtain`. -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  sorry

example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  sorry

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  sorry

example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  sorry

example (p : Prop) : ¬(p ∧ ¬p) := by
  sorry

/-! ## 4. Quantifiers

`∀` is the dependent function type: a proof of `∀ x, p x` is a function.
A proof of `∃ x, p x` is a pair `⟨witness, proof⟩`. -/

example (p q : α → Prop) (h : ∀ x, p x ∧ q x) : ∀ x, p x := by
  sorry

example (p : α → Prop) (a : α) (h : ∀ x, p x) : ∃ x, p x := by
  sorry

example (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  sorry

/-- *(harder)* -/
example (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := by
  sorry

/-! ## 5. Equality

`Eq` is reflexive (`rfl`), symmetric (`h.symm`), and transitive
(`h₁.trans h₂`). The `calc` block and the `rw`/`simp` tactics are the
everyday tools. -/

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  sorry

example (f : Nat → Nat) (h : ∀ x, f x = x + 1) : f (f 0) = 2 := by
  sorry

/-! ## 6. Formalizing statements

Write the following statements as propositions. Do **not** prove them —
some of them are false! The point is to practice saying precisely what
you mean. -/

def Even (n : Nat) : Prop := ∃ k, n = 2 * k
def Odd  (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-- "Every natural number is even or odd." -/
def statement₁ : Prop := sorry

/-- "There is a natural number strictly between 11 and 12." -/
def statement₂ : Prop := sorry

/-- "Addition of natural numbers is commutative." -/
def statement₃ : Prop := sorry

/-- "Every even natural number greater than 2 is the sum of two primes."
Use `Nat.Prime`... which does not exist in the core library. Define
primality yourself first. -/
def IsPrime (n : Nat) : Prop := sorry

def statement₄ : Prop := sorry

/-! ## 7. The barber paradox *(harder)*

In a certain town, the barber shaves exactly those who do not shave
themselves. Show that no such barber can exist. This is a two-line
tactic proof — or a puzzle, depending on how you look at it.
Hint: consider `h barber`, and case on whether the barber shaves himself
(`by_cases hs : shaves barber barber`). -/

example (Person : Type) (shaves : Person → Person → Prop) (barber : Person)
    (h : ∀ x, shaves barber x ↔ ¬ shaves x x) : False := by
  sorry
