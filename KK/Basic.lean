/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Tauto

/-
  This file provides a small Lean framework for formalising
  Smullyan-style 'knights and knaves' puzzles, and is inspired by
  https://adam.math.hhu.de/#/g/jadabouhawili/knightsandknaves-lean4game

  Much of the puzzles, and the general setup, are taken from:
  "What Is the Name of This Book?", Raymond M. Smullyan (1978).

  The setting is described in Smullyan (1978) as follows.
  > There is a wide variety of puzzles about an island in which
  > certain inhabitants called "knights" always tell the truth,
  > and others called "knaves" always lie. It is assumed that
  > every inhabitant of the island is either a knight or a knave.
-/

namespace KnightsAndKnaves

/--
A `World Person` specifies which inhabitants of type `Person` are knights.
-/
structure World (Person : Type) where
  /-- The predicate identifying the knights in this world. -/
  knight : Person → Prop

variable {Person : Type}

/--
`isKnight w p` means that `Q` is a knight in world `w`.
-/
def isKnight (w : World Person) (p : Person) : Prop :=
  w.knight p

/--
`isKnave w p` means that `Q` is a knave in world `w`.

By definition, a knave is someone who is not a knight.
-/
def isKnave (w : World Person) (p : Person) : Prop :=
  ¬ isKnight w p

/--
`said w p Q` means that it is compatible with the roles in world `w`
for `p` to have made a statement with content `Q`.

A knight may have said `Q` exactly when `Q` is true;
a knave may have said `Q` exactly when `Q` is false.
-/
def said (w : World Person) (p : Person) (Q : Prop) : Prop :=
  isKnight w p ↔ Q

notation "isKnight[" w "]" => KnightsAndKnaves.isKnight w
notation "isKnave[" w "]" => KnightsAndKnaves.isKnave w
notation "said[" w "]" => KnightsAndKnaves.said w
notation p " said[" w "] " P:200 => KnightsAndKnaves.said w p P

variable {w : World Person}
variable {p : Person} {Q : Prop}

/-- Unfolding lemma for `said`. -/
@[simp]
theorem said_iff : said w p Q ↔ (isKnight w p ↔ Q) := Iff.rfl

/-- Unfolding lemma for `isKnave`. -/
@[simp]
theorem isKnave_iff : isKnave w p ↔ ¬ isKnight w p := Iff.rfl

/-- No person can be both a knight and a knave. -/
@[simp]
theorem not_knight_and_knave : ¬ (isKnight w p ∧ isKnave w p) := by simp

/-- If `Q` said `Q` and `Q` is a knight, then `Q` is true. -/
theorem knight_said (h : said w p Q) (hp : isKnight w p) : Q := h.mp hp

/-- If `Q` said `Q` and `Q` is true, then `Q` is a knight. -/
theorem said_knight (h : said w p Q) (hQ : Q) : isKnight w p := h.mpr hQ

/-- If `Q` said `Q` and `Q` is a knave, then `Q` is false. -/
theorem knave_said (h : said w p Q) (hp : isKnave w p) : ¬ Q := by
  intro hQ
  exact hp (h.mpr hQ)

/-- If `Q` said `Q` and `Q` is false, then `Q` is a knave. -/
theorem said_knave (h : said w p Q) (hQ : ¬ Q) : isKnave w p := by
  intro hp
  exact hQ (h.mp hp)

/-- A person is a knight exactly when they are not a knave. -/
theorem knight_iff_not_knave : isKnight w p ↔ ¬ isKnave w p := by
  unfold isKnave
  simp

/-- A person is a knave exactly when they are not a knight. -/
theorem knave_iff_not_knight : isKnave w p ↔ ¬ isKnight w p := by
  unfold isKnave
  simp

/-- No person can consistently say of themselves: "I am a knave." -/
theorem i_am_not_a_knave_impossible (h : said w p (isKnave w p)) : False := by
  -- Hint: first show that `p` is a knave.
  -- [FILL IN THE PROOF]
  sorry

/-- A person's statement about whether they made a given statement has the same
truth value as the original proposition. -/
theorem said_said_iff : (said w p (said w p Q)) ↔ Q := by
  by_cases hp : isKnight w p <;> simp [hp]

/--
If `a` said that `a` is a knave or `Q` holds,
then `a` must be a knight and `Q` must hold
-/
theorem knight_and_of_said_knave_or {Q : Prop}
    (h : p said[w] (isKnave[w] p ∨ Q)) :
    isKnight[w] p ∧ Q := by
  -- Hint: first show that `p` is a knight.
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that `a` is a knave and `Q` holds,
then `a` must be a knave and `Q` must not hold.
-/
theorem knave_and_not_of_said_knave_and {Q : Prop}
    (h : p said[w] (isKnave[w] p ∧ Q)) :
    isKnave[w] p ∧ ¬ Q := by
  -- Hint: first show that `p` is a knave.
  -- [FILL IN THE PROOF]
  sorry


end KnightsAndKnaves
