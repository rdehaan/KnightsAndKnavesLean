/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

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
def oneOfEach : Prop :=
  (isKnight a ∨ isKnight b ∨ isKnight c) ∧
  (isKnave a ∨ isKnave b ∨ isKnave c) ∧
  (isNormal a ∨ isNormal b ∨ isNormal c)

/--
If all three roles are present among `a`, `b` and `c`,
then it is impossible
that `a` said that `a` is normal,
that `b` said that `a` is normal,
and that `c` said that `c` is not normal.

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
  -- [FILL IN THE PROOF]
  sorry

end Island4
