/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import KK.KnightsAndKnaves

/-!
## Island 1

On this island, there are two inhabitants: `a` and `b`,
and all inhabitants are either knights or knaves.
-/

namespace Island1

open KnightsAndKnaves

inductive Islander where
  | a
  | b

open Islander

/-! Fix an arbitrary world w. -/
variable (w : World Islander)

/-! Local notation where we fix the world w. -/
local notation "isKnight" => isKnight w
local notation "isKnave" => isKnave w
local notation p " said " Q:200 => said w p Q

/--
If `a` said that `b` is a knave,
and if `b` said that both are knights,
then `a` must be a knight and `b` must be a knave.
-/
example (hA : a said isKnave b) (hB : b said (isKnight a ∧ isKnight b)) :
    isKnave b ∧ isKnight a := by
  -- Hint: first show that `b` is a knave.
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that at least one of `a` and `b` is a knave,
then `a` must be a knight and `b` must be a knave.

From Smullyan (1978): Puzzle 28.
-/
example (hA : a said (isKnave a ∨ isKnave b)) :
    isKnight a ∧ isKnave b := by
  -- Hint: use `knight_and_of_said_knave_or`
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that either `a` is a knave or `b` is a knight,
then they must both be knights.

From Smullyan (1978): Puzzle 29.
-/
example (hA : a said (isKnave a ∨ isKnight b)) :
    isKnight a ∧ isKnight b := by
  -- Hint: use `knight_and_of_said_knave_or`
  -- [FILL IN THE PROOF]
  sorry

/--
If `a` said that `a` is a knave and `b` is a knight,
then they must both be knaves.

From Smullyan (1978): Puzzle 33.
-/
example (hA : a said (isKnave a ∧ isKnight b)) :
    isKnave a ∧ isKnave b := by
  -- Hint: use `knave_and_not_of_said_knave_and`
  -- [FILL IN THE PROOF]
  sorry


end Island1
