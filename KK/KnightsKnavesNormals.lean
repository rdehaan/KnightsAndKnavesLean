/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Tauto

/-!
# Knights, Knaves, and Normals

This file provides a framework for formalising Smullyan-style puzzles with three types
of inhabitants: knights (always tell the truth), knaves (always lie), and normals
(who may independently tell the truth or lie on each utterance).
-/

namespace KnightsKnavesNormals

/-- The three possible behavioural roles of an island inhabitant. -/
inductive Role where
  | knight
  | knave
  | normal

/-- A world assigns one of the three roles to every person. -/
structure World (Person : Type) where
  role : Person → Role

variable {Person : Type}

/-- `isKnight w p` means that `p` is a knight in `w`. -/
def isKnight (w : World Person) (p : Person) : Prop := w.role p = .knight

/-- `isKnave w p` means that `p` is a knave in `w`. -/
def isKnave (w : World Person) (p : Person) : Prop := w.role p = .knave

/-- `isNormal w p` means that `p` is a normal in `w`. -/
def isNormal (w : World Person) (p : Person) : Prop := w.role p = .normal

notation "isKnight[" w "]" => isKnight w
notation "isKnave[" w "]" => isKnave w
notation "isNormal[" w "]" => isNormal w

/--
`said w p Q` means that it is compatible with the roles in world `w`
for `p` to have made a statement with content `Q`.

A knight may have said `Q` exactly when `Q` is true;
a knave may have said `Q` exactly when `Q` is false;
and a normal may have said `Q` regardless of whether `Q` is true or false.
-/
def said (w : World Person) (p : Person) (Q : Prop) : Prop :=
  isNormal w p ∨ (isKnight w p ↔ Q)

notation "said[" w "]" => said w
notation p " said[" w "] " Q:200 => said w p Q

variable {w : World Person}
variable {p q : Person}
variable {Q R : Prop}

@[simp] theorem isKnight_iff : isKnight w p ↔ w.role p = .knight := Iff.rfl
@[simp] theorem isKnave_iff  : isKnave w p  ↔ w.role p = .knave  := Iff.rfl
@[simp] theorem isNormal_iff : isNormal w p ↔ w.role p = .normal := Iff.rfl
@[simp] theorem said_iff : said w p Q ↔ (isNormal w p ∨ (isKnight w p ↔ Q)) := Iff.rfl

/-- Every person has one of the three roles. -/
theorem role_cases (w : World Person) (p : Person) :
    isKnight w p ∨ isKnave w p ∨ isNormal w p := by
  cases h : w.role p <;> simp [isKnight, isKnave, isNormal, h]

@[simp] theorem not_knight_and_knave : ¬ (isKnight w p ∧ isKnave w p) := by
  intro h
  rcases h with ⟨h1, h2⟩
  simp only [isKnight_iff, isKnave_iff] at h1 h2
  have : Role.knight = Role.knave := by rw [← h1, ← h2]
  contradiction

@[simp] theorem not_knight_and_normal : ¬ (isKnight w p ∧ isNormal w p) := by
  intro h
  rcases h with ⟨h1, h2⟩
  simp only [isKnight_iff, isNormal_iff] at h1 h2
  have : Role.knight = Role.normal := by rw [← h1, ← h2]
  contradiction

@[simp] theorem not_knave_and_normal : ¬ (isKnave w p ∧ isNormal w p) := by
  intro h
  rcases h with ⟨h1, h2⟩
  simp only [isKnave_iff, isNormal_iff] at h1 h2
  have : Role.knave = Role.normal := by rw [← h1, ← h2]
  contradiction

theorem not_knave_of_knight (h : isKnight w p) : ¬ isKnave w p := by
  intro hk; exact not_knight_and_knave ⟨h, hk⟩

theorem not_normal_of_knight (h : isKnight w p) : ¬ isNormal w p := by
  intro hn; exact not_knight_and_normal ⟨h, hn⟩

theorem not_knight_of_knave (h : isKnave w p) : ¬ isKnight w p := by
  intro hk; exact not_knight_and_knave ⟨hk, h⟩

theorem not_normal_of_knave (h : isKnave w p) : ¬ isNormal w p := by
  intro hn; exact not_knave_and_normal ⟨h, hn⟩

theorem not_knight_of_normal (h : isNormal w p) : ¬ isKnight w p := by
  intro hk; exact not_knight_and_normal ⟨hk, h⟩

theorem not_knave_of_normal (h : isNormal w p) : ¬ isKnave w p := by
  intro hk; exact not_knave_and_normal ⟨hk, h⟩

/-- A non-normal is either a knight or a knave. -/
theorem knight_or_knave_of_not_normal (h : ¬ isNormal w p) :
    isKnight w p ∨ isKnave w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A non-knave is either a knight or a normal. -/
theorem knight_or_normal_of_not_knave (h : ¬ isKnave w p) :
    isKnight w p ∨ isNormal w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A non-knight is either a knave or a normal. -/
theorem knave_or_normal_of_not_knight (h : ¬ isKnight w p) :
    isKnave w p ∨ isNormal w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A non-knight and non-knave is a normal. -/
theorem normal_of_not_knight_of_not_knave
    (hk : ¬ isKnight w p) (hn : ¬ isKnave w p) : isNormal w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A non-knight and non-normal is a knave. -/
theorem knave_of_not_knight_of_not_normal
    (hk : ¬ isKnight w p) (hn : ¬ isNormal w p) : isKnave w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A non-knave and non-normal is a knight. -/
theorem knight_of_not_knave_of_not_normal
    (hk : ¬ isKnave w p) (hn : ¬ isNormal w p) : isKnight w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A knight's utterance has true content. -/
theorem knight_said (h : said w p Q) (hp : isKnight w p) : Q := by
  rcases h with hn | h_iff
  · exact False.elim (not_normal_of_knight hp hn)
  · exact h_iff.mp hp

/-- A knave's utterance has false content. -/
theorem knave_said (h : said w p Q) (hp : isKnave w p) : ¬ Q := by
  intro hQ
  rcases h with hn | hiff
  · exact not_normal_of_knave hp hn
  · exact not_knight_of_knave hp (hiff.mpr hQ)

/-- If a person is non-normal, then their utterance is true iff they
are a knight.
-/
theorem said_iff_of_not_normal (hn : ¬ isNormal w p) :
    said w p Q ↔ (isKnight w p ↔ Q) := by
  -- Difficulty: very easy
  -- [FILL IN THE PROOF]
  sorry

/-- If a non-normal person makes a true statement, they are a knight. -/
theorem knight_of_said_of_truth_of_not_normal
    (h : said w p Q) (hQ : Q) (hn : ¬ isNormal w p) : isKnight w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- If a non-normal person makes a false statement, they are a knave. -/
theorem knave_of_said_of_false_of_not_normal
    (h : said w p Q) (hQ : ¬ Q) (hn : ¬ isNormal w p) : isKnave w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- `p` made the statement `Q`, and its content is true. -/
def tellsTruth (w : World Person) (p : Person) (Q : Prop) : Prop :=
  said w p Q ∧ Q

/-- `p` made the statement `Q`, and its content is false. -/
def lies (w : World Person) (p : Person) (Q : Prop) : Prop :=
  said w p Q ∧ ¬ Q

/--
If a person both tells the truth and lies (in separate statements),
then they are normal.
-/
theorem normal_of_tells_truth_and_lies
    (hTrue : tellsTruth w p Q) (hFalse : lies w p R) :
    isNormal w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/--
If a person said a true proposition and said a false proposition,
then they are normal.
-/
theorem normal_of_said_true_and_said_false
    (hQ : said w p Q) (hQTrue : Q)
    (hR : said w p R) (hRFalse : ¬ R) :
    isNormal w p :=
  normal_of_tells_truth_and_lies ⟨hQ, hQTrue⟩ ⟨hR, hRFalse⟩

/-- The rank of a role: knave < normal < knight. -/
def rank : Role → Nat
  | .knave  => 0
  | .normal => 1
  | .knight => 2

/-- If a person made a true statement,
then they are either a normal or a knight. -/
theorem normal_or_knight_of_said_of_truth
    (h : said w p Q) (hQ : Q) :
    isNormal w p ∨ isKnight w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- If a person made a false statement,
then they are either a normal or a knave. -/
theorem normal_or_knave_of_said_of_false
    (h : said w p Q) (hQ : ¬ Q) :
    isNormal w p ∨ isKnave w p := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A normal may make any statement. -/
theorem normal_said (hp : isNormal w p) : said w p Q :=
  Or.inl hp

/-- A knight may make any true statement. -/
theorem knight_said_of_truth (hp : isKnight w p) (hQ : Q) :
    said w p Q := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- A knave may make any false statement. -/
theorem knave_said_of_false (hp : isKnave w p) (hQ : ¬ Q) :
    said w p Q := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- `p` has lower rank than `q` in world `w`. -/
def hasLowerRank (w : World Person) (p q : Person) : Prop :=
  rank (w.role p) < rank (w.role q)

/-- `p` has higher rank than `q` in world `w`. -/
def hasHigherRank (w : World Person) (p q : Person) : Prop :=
  hasLowerRank w q p

/-- `p` and `q` have equal rank in world `w`. -/
def hasEqualRank (w : World Person) (p q : Person) : Prop :=
  rank (w.role p) = rank (w.role q)

@[simp] theorem rank_knave : rank Role.knave = 0 := rfl
@[simp] theorem rank_normal : rank Role.normal = 1 := rfl
@[simp] theorem rank_knight : rank Role.knight = 2 := rfl
@[simp] theorem hasHigherRank_iff :
    hasHigherRank w p q ↔ hasLowerRank w q p := Iff.rfl

/-- Lower rank is transitive. -/
theorem hasLowerRank_trans
    (hpq : hasLowerRank w p q) (hqr : hasLowerRank w q r) :
    hasLowerRank w p r :=
  Nat.lt_trans hpq hqr

/-- Lower rank is irreflexive. -/
theorem not_hasLowerRank_self : ¬ hasLowerRank w p p :=
  Nat.lt_irrefl _

/-- If `p` has higher rank than `q`,
then `p` does not have lower rank than `q`. -/
theorem not_hasLowerRank_of_hasHigherRank
    (hpq : hasHigherRank w p q) :
    ¬ hasLowerRank w p q := by
  intro hqp
  exact Nat.lt_asymm hqp hpq

/--
Simplify a rank-puzzle proof state using all local hypotheses.
-/
macro "rank_simp_all" : tactic =>
  `(tactic|
    simp_all [isKnight, isKnave, isNormal,
      hasHigherRank, hasLowerRank, rank])

/--
Split on the roles of each supplied inhabitant and simplify every resulting
branch with `rank_simp_all`.

Example: `rank_cases_simp_all w [a, b, c]`.
-/
syntax "rank_cases_simp_all " ident "[" ident,+ "]" : tactic

macro_rules
  | `(tactic| rank_cases_simp_all $w:ident [$x:ident]) =>
      `(tactic|
        rcases role_cases $w $x with h_knight | h_knave | h_normal <;>
          rank_simp_all)

  | `(tactic| rank_cases_simp_all $w:ident [$x:ident, $xs:ident,*]) =>
      `(tactic|
        rcases role_cases $w $x with h_knight | h_knave | h_normal <;>
          rank_cases_simp_all $w [$xs,*])


end KnightsKnavesNormals
