/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import Mathlib.Logic.Function.Defs
import KK.KnightsKnavesNormals

/-!
## Island 4

On this island, there are three inhabitants: `a`, `b` and `c`,
and all inhabitants are knights or knaves or normals.
-/

namespace Island4

open KnightsKnavesNormals

inductive Islander where
  | a
  | b
  | c

open Islander

/-! Fix an arbitrary world w. -/
variable (w : World Islander)

/-! Local notation where we fix the world w. -/
local notation "isKnight" => isKnight w
local notation "isKnave" => isKnave w
local notation "isNormal" => isNormal w
local notation p " said " Q:200 => said w p Q

local notation p " <rank " q => hasLowerRank w p q
local notation p " >rank " q => hasHigherRank w p q
local notation p " =rank " q => hasEqualRank w p q

/-- The three roles are all present among `a`, `b` and `c`. -/
def oneOfEach (w : World Islander) : Prop :=
  Function.Bijective w.role

lemma oneOfEach.cnf (h : oneOfEach w) :
    (isKnight a ∨ isKnight b ∨ isKnight c) ∧
    (isKnave a ∨ isKnave b ∨ isKnave c) ∧
    (isNormal a ∨ isNormal b ∨ isNormal c) := by
  refine ⟨?_, ?_, ?_⟩
  · refine Exists.elim (h.2 Role.knight) ?_
    intro x hx
    cases x <;> simp [KnightsKnavesNormals.isKnight, hx]
  · refine Exists.elim (h.2 Role.knave) ?_
    intro x hx
    cases x <;> simp [KnightsKnavesNormals.isKnave, hx]
  · refine Exists.elim (h.2 Role.normal) ?_
    intro x hx
    cases x <;> simp [KnightsKnavesNormals.isNormal, hx]

lemma oneOfEach.not_same_role
    {x y : Islander}
    (h : oneOfEach w)
    (h_xy : x ≠ y) :
    w.role x ≠ w.role y := by
  intro h_roles
  exact h_xy (h.1 h_roles)

/--
If all three roles are present among `a`, `b` and `c`,
then it is impossible
that `a` said that `a` is normal,
that `b` said that `a` is normal,
and that `c` said thatintro h_roles
  exact hxy (h.role_injective w h_roles) `c` is not normal.

From Smullyan (1978): Puzzle 39.
-/
example
    (h_one_each : oneOfEach w)
    (hA : a said (isNormal a))
    (hB : b said (isNormal a))
    (hC : c said (¬ isNormal c)) :
    isKnave a ∧ isNormal b ∧ isKnight c := by
  -- Hint: First show that `a` is a knave:
  -- if `a` were normal, then neither `b` nor `c` could be a knave;
  -- then show that `b` is normal.
  -- Difficulty: hard
  -- [FILL IN THE PROOF]
  sorry

/--
If all three roles are present among `a`, `b` and `c`,
if `a` said that `b` has higher rank than `c`,
and if `b` said that `c` has higher rank than `a`,
then `c` could say that `a` has lower rank than `b`
(but not the opposite statement).

From Smullyan (1978): Puzzle 43.
-/
example
    (h_one_each : oneOfEach w)
    (hA : a said (b >rank c))
    (hB : b said (c >rank a)) :
    c said (a <rank b) ∧ ¬ (c said (a >rank b)) := by
  -- Hint: first show that `b` is normal;
  -- then determine the two possible role assignments
  -- for `a` and `c`, and split on those.
  -- Difficulty: hard
  -- [FILL IN THE PROOF]
  sorry

/--
If all three roles are present among `a`, `b` and `c`,
if `a` said that `b` has lower rank than `c`,
then `b` is not normal.

From Smullyan (1978): Puzzle 98.
-/
example
    (h_one_each : oneOfEach w)
    (hA : a said (b <rank c)) :
    ¬ isNormal b := by
  -- Hint: split on the role of `a`;
  -- and for the case where `a` is a knight,
  -- show that `b` is a knave.
  -- Difficulty: hard
  -- [FILL IN THE PROOF]
  sorry


end Island4
