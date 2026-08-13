/-
Solutions for Lecture 1, with notes.
-/

/-! ## 1. Functions -/

def double (n : Nat) : Nat := 2 * n

#guard double 7 = 14

def twice (f : α → α) (x : α) : α := f (f x)

#guard twice (· + 3) 10 = 16
#guard twice double 1 = 4

def compose (f : β → γ) (g : α → β) : α → γ := fun x => f (g x)

#guard compose (· * 2) (· + 1) 3 = 8

def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

#guard collatzStep 6 = 3
#guard collatzStep 7 = 22

/-! ## 2. Propositions as types

Note: every proof below is an ordinary term — a pair, a function, a
projection. There is no separate "proof language". This is the
Curry–Howard correspondence in practice; internalizing it now makes
tactics (Section 3) demystified rather than magical. -/

example (p : Prop) (hp : p) : p := hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example (p q : Prop) (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  fun hp => hqr (hpq hp)

example (p q : Prop) (h : p ∨ q) : q ∨ p := h.elim Or.inr Or.inl

example (p : Prop) : ¬(p ∧ ¬p) := fun h => h.2 h.1

example (p q r : Prop) : (p → q → r) ↔ (p ∧ q → r) :=
  ⟨fun h hpq => h hpq.1 hpq.2, fun h hp hq => h ⟨hp, hq⟩⟩

/-! ## 3. The same proofs, with tactics

Note: use `#print` on a tactic proof and compare with the terms you
wrote in Section 2 — tactics are programs that *construct* those same
terms. `constructor` builds the pair, `intro` builds the lambda, `cases`
is pattern matching. -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp

example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (p : Prop) : ¬(p ∧ ¬p) := by
  intro h
  exact h.2 h.1

/-! ## 4. Quantifiers -/

example (p q : α → Prop) (h : ∀ x, p x ∧ q x) : ∀ x, p x := by
  intro x
  exact (h x).1

example (p : α → Prop) (a : α) (h : ∀ x, p x) : ∃ x, p x := by
  exact ⟨a, h a⟩

example (p q : α → Prop) (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  obtain ⟨x, hp, hq⟩ := h
  exact ⟨x, hq, hp⟩

example (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := by
  intro y
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx y⟩

/-! ## 5. Equality -/

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁, h₂]

example (f : Nat → Nat) (h : ∀ x, f x = x + 1) : f (f 0) = 2 := by
  calc f (f 0) = f 0 + 1 := h (f 0)
    _ = 0 + 1 + 1 := by rw [h 0]
    _ = 2 := rfl

/-! ## 6. Formalizing statements

Note: `statement₂` is false and `statement₄` is open — and Lean accepts
both without complaint. Writing a proposition and proving it are separate
activities; a type checker validates that a statement is *well-formed*,
not that it is *true*. Getting the statement right is your
responsibility; this matters when AI writes the proofs. -/

def Even (n : Nat) : Prop := ∃ k, n = 2 * k
def Odd  (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-- "Every natural number is even or odd." (True.) -/
def statement₁ : Prop := ∀ n : Nat, Even n ∨ Odd n

/-- "There is a natural number strictly between 11 and 12." (False.) -/
def statement₂ : Prop := ∃ n : Nat, 11 < n ∧ n < 12

/-- "Addition of natural numbers is commutative." (True.) -/
def statement₃ : Prop := ∀ a b : Nat, a + b = b + a

/-- A number is prime if it is at least 2 and its only divisors are 1 and
itself. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

/-- Goldbach's conjecture. (Open!) -/
def statement₄ : Prop :=
  ∀ n : Nat, Even n → 2 < n → ∃ p q, IsPrime p ∧ IsPrime q ∧ n = p + q

/-! ## 7. The barber paradox

Note: instantiating the hypothesis at the barber himself gives
`shaves barber barber ↔ ¬ shaves barber barber`, and a proposition
equivalent to its own negation is absurd — both branches of the case
split refute themselves. This is Russell's paradox with barbers instead
of sets. -/

example (Person : Type) (shaves : Person → Person → Prop) (barber : Person)
    (h : ∀ x, shaves barber x ↔ ¬ shaves x x) : False := by
  have hb := h barber
  by_cases hs : shaves barber barber
  · exact hb.mp hs hs
  · exact hs (hb.mpr hs)
