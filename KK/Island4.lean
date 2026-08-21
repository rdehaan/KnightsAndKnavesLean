/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import KK.KnightsKnavesNormals

/-!
## Island 4

On this island, there are two inhabitants: `a` and `b`,
and all inhabitants are knights or knaves or normals.
-/

namespace Island4

open KnightsKnavesNormals

inductive Islander where
  | a
  | b

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

/-!
If `a` said that `b` is a knight,
and if `b` said that `a` is not a knight,
then there is at least one person that is truthful but not a knight.

From Smullyan (1978): Puzzle 40.
-/
example
    (hA : a said (isKnight b))
    (hB : b said (¬ isKnight a)) :
    (¬ isKnight a ∧ isKnight b) ∨
    (¬ isKnight b ∧ ¬ isKnight a) := by
  -- Hint: first prove that `a` is not a knight;
  -- then split on whether `b` is a knight.
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that `b` is a knight,
and if `b` said that `a` is a knave,
then at least one of them is normal.

From Smullyan (1978): Puzzle 41.
-/
example
    (hA : a said (isKnight b))
    (hB : b said (isKnave a)) :
    (isNormal a ∨ isNormal b) := by
  -- Hint: argue by contradiction, and suppose that neither is normal;
  -- then split on whether `b` is a knight or a knave.
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that they have lower rank than `b`,
and `b` said that this is not true,
then `a` is not a knight and `b` is not a knave,
and `a` does not have lower rank than `b`.

From Smullyan (1978): Puzzle 42.
-/
example
    (hA : a said (hasLowerRank w a b))
    (hB : b said (¬ hasLowerRank w a b)) :
    ¬ hasLowerRank w a b ∧ ¬ isKnight a ∧ ¬ isKnave b := by
  -- Hint: start with showing that `a` does not have lower rank than `b`
  -- by splitting on the three possible roles of both.
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that they have lower rank than `b`,
and `b` said that this is not true,
then `a` and `b` could both be normals.

From Smullyan (1978): Puzzle 42.
-/
example : ∃ w : World Islander,
    a said[w] (hasLowerRank w a b) ∧
    b said[w] (¬ hasLowerRank w a b) ∧
    isNormal[w] a ∧ isNormal[w] b := by
  refine ⟨{ role := fun | a => .normal | b => .normal }, ?_⟩
  rank_simp_all

/--
If `a` and `b` are either both normal or both non-normal,
and if `a` said that `b` is not normal,
and if `b` said that `a` is not normal,
then they must both be normal or both be knights.

From Smullyan (1978): Puzzle 44.
-/
example
    (h_iff : isNormal a ↔ isNormal b)
    (hA : a said (¬ isNormal b))
    (hB : b said (¬ isNormal a)) :
    (isNormal a ∧ isNormal b) ∨ (isKnight a ∧ isKnight b) := by
  -- Hint: split on whether `a` is normal.
  -- [FILL IN THE PROOF]
  sorry


end Island4
