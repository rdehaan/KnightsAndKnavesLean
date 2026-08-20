/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import KK.Basic

/-!
## Island 1

On this island, there are two inhabitants: `a` and `b`.
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
`a` said that `b` is a knave.
`b` said that both are knights.
Then `a` must be a knight and `b` must be a knave.
-/
example (hA : a said isKnave b) (hB : b said (isKnight a ∧ isKnight b)) :
    isKnave b ∧ isKnight a := by
  -- Hint: first show that `b` is a knave.
  -- [FILL IN THE PROOF]
  sorry

/--
`a` said that at least one of `a` and `b` is a knave.
Then `a` must be a knight and `b` must be a knave.

From Smullyan (1978): Question 28.
-/
example (hA : a said (isKnave a ∨ isKnave b)) :
    isKnight a ∧ isKnave b := by
  -- Hint: use `knight_and_of_said_knave_or`
  -- [FILL IN THE PROOF]
  sorry

/--
`a` said that either `a` is a knave or `b` is a knight.
Then they must both be knights.

From Smullyan (1978): Question 29.
-/
example (hA : a said (isKnave a ∨ isKnight b)) :
    isKnight a ∧ isKnight b := by
  -- Hint: use `knight_and_of_said_knave_or`
  -- [FILL IN THE PROOF]
  sorry

/--
`a` said that `a` is a knave and `b` is a knight.
Then they must both be knaves.

From Smullyan (1978): Question 33.
-/
example (hA : a said (isKnave a ∧ isKnight b)) :
    isKnave a ∧ isKnave b := by
  -- Hint: use `knave_and_not_of_said_knave_and`
  -- [FILL IN THE PROOF]
  sorry


end Island1
