/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import KK.KnightsAndKnaves

/-!
## Island 2

On this island, there are three inhabitants: `a`, `b` and `c`,
and all inhabitants are either knights or knaves.
-/

namespace Island2

open KnightsAndKnaves

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
local notation p " said " Q:200 => said w p Q

/--
If `b` said that `a` said that `a` is a knave,
and if `c` said that `b` is a knave,
then `b` is a knave and `c` is a knight.

From Smullyan (1978): Puzzle 26.
-/
example (hB : b said (a said isKnave a))
    (hC : c said isKnave b) :
    isKnave b ∧ isKnight c := by
  -- Hint: first show that `b` is a knave.
  -- Difficulty: medium
  -- [FILL IN THE PROOF]
  sorry

/--
If `b` said that `a` said that `a` is a knave,
and if `c` said that `b` is a knave,
then `a` could still be a knight.

From Smullyan (1978): Puzzle 26.
-/
example : ∃ w : World Islander,
      b said[w] (a said[w] (isKnave[w] a)) ∧
      c said[w] (isKnave[w] b) ∧
      isKnight[w] a := by
  -- Hint: use
  -- ```
  -- let w : World Islander :=
  --   { knight := fun
  --       | a => True/False
  --       | b => True/False
  --       | c => True/False }
  -- ```
  -- with appropriate choices for True/False.
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/--
If `b` said that `a` said that `a` is a knave,
and if `c` said that `b` is a knave,
then `a` could still be a knave.

From Smullyan (1978): Puzzle 26.
-/
example : ∃ w : World Islander,
      b said[w] (a said[w] (isKnave[w] a)) ∧
      c said[w] (isKnave[w] b) ∧
      isKnave[w] a := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/-- Exactly one of three propositions holds. -/
def exactlyOneOfThree (P Q R : Prop) : Prop :=
  (P ∧ ¬ Q ∧ ¬ R) ∨
  (¬ P ∧ Q ∧ ¬ R) ∨
  (¬ P ∧ ¬ Q ∧ R)

/-- Exactly one of `a`, `b`, and `c` is a knight. -/
def exactlyOneKnight : Prop :=
  exactlyOneOfThree (isKnight a) (isKnight b) (isKnight c)

/--
If `b` said that `a` said that exactly one of the three is a knight,
and if `c` said that `b` is a knave,
then `b` is a knave and `c` is a knight.

From Smullyan (1978): Puzzle 27.
-/
example
    (hB : b said (a said (exactlyOneKnight w)))
    (hC : c said (isKnave b)) :
    isKnave b ∧ isKnight c := by
  -- Hint: first show that `b` is a knave:
  -- assume that `b` is a knight and derive a contradiction by proving that
  -- `c` then must be a knave and splitting on whether `a` is a knight.
  -- Difficulty: medium–hard
  -- [FILL IN THE PROOF]
  sorry

/--
If `b` said that `a` said that exactly one of the three is a knight,
and if `c` said that `b` is a knave,
then `a` could still be a knight.

From Smullyan (1978): Puzzle 27.
-/
example : ∃ w : World Islander,
      b said[w] (a said[w] (exactlyOneKnight w)) ∧
      c said[w] (isKnave[w] b) ∧
      isKnight[w] a := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/--
If `b` said that `a` said that exactly one of the three is a knight,
and if `c` said that `b` is a knave,
then `a` could still be a knave.

From Smullyan (1978): Puzzle 27.
-/
example : ∃ w : World Islander,
      b said[w] (a said[w] (exactlyOneKnight w)) ∧
      c said[w] (isKnave[w] b) ∧
      isKnave[w] a := by
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry


end Island2
