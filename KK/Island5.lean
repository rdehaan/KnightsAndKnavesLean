/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import KK.BalDa

/-!
## Island 5

On this island, the inhabitants answer yes/no questions using the words
'bal' and 'da' meaning 'yes' and 'no' (but in an unknown order).
-/

namespace Island5

open KnightsAndKnaves
open BalDa
open BalDa.Reply

variable {Person : Type}
variable {p : Person}

/-! Fix an arbitrary world w and language L. -/
variable (w : World Person)
variable (L : Language)

/-! Local notation where we fix the world w and language L. -/
local notation "isKnight" => isKnight w
local notation "isKnave" => isKnave w
local notation p " said " Q:200 => said w p Q
local notation p " answered " Q:200 " with " word:200 => answeredWith w L p Q word

/--
A person who answers `bal` to "Does `bal` mean yes?" is a knight.

From Smullyan (1978): Puzzle 158.
-/
theorem isKnight_of_answered_bal_to_bal_means_yes
    (h : answeredWith w L p (wordMeansYes L bal) bal) :
    isKnight p := by
  -- Difficulty: very easy
  -- [FILL IN THE PROOF]
  sorry

/--
Any answer to "Are you a knight?" is the native yes-word.

From Smullyan (1978): Puzzle 159.
-/
theorem answer_to_are_you_a_knight_means_yes {actual : Reply}
    (h : answeredWith w L p (isKnight p) actual) :
    wordMeansYes L actual := by
  -- Hint: split on the yes-word and on the actual answer.
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/--
`answersBalToBalMeansYes w L p` means that under language `L` in world `w`,
`p` answers `bal` to "Does `bal` mean yes?".
-/
def answersBalToBalMeansYes (w : World Person) (L : Language) (p : Person) : Prop :=
  p answered[w, L] (wordMeansYes L bal) with bal

/--
After receiving the answer `bal` to "Does `bal` mean yes?", the language remains
undetermined: the observation is compatible with either choice of yes-word.

From Smullyan (1978): Puzzle 160.
-/
example (h : answeredWith w L p (wordMeansYes L bal) bal) :
    ∃ LBal LDa : Language,
      LBal.yesWord = bal ∧
      LDa.yesWord = da ∧
      answersBalToBalMeansYes w LBal p ∧
      answersBalToBalMeansYes w LDa p := by
  -- Hint: first show that the speaker is a knight;
  -- then use `refine ⟨{yesWord := bal}, {yesWord := da}, rfl, rfl, ?_, ?_⟩`
  -- Difficulty: medium
  -- [FILL IN THE PROOF]
  sorry

/--
The answer to "Does `bal` mean yes?" identifies the speaker's type:
they answer `bal` exactly when they are a knight, and `da` exactly
when they are a knave.

From Smullyan (1978): Puzzle 160.
-/
example {actual : Reply}
    (h : answeredWith w L p (wordMeansYes L bal) actual) :
    (actual = bal ↔ isKnight p) ∧
    (actual = da ↔ isKnave p) := by
  -- Hint: split on the yes-word and on the actual answer.
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/--
Any person answers `bal` to the question:
"Are you a knight if and only if `bal` means yes?"

From Smullyan (1978): Puzzle 161.
-/
example {actual : Reply}
    (h : answeredWith w L p (isKnight p ↔ wordMeansYes L bal) actual) :
    actual = bal := by
  -- Hint: split on the yes-word and on the actual answer.
  -- Difficulty: easy
  -- [FILL IN THE PROOF]
  sorry

/--
The answer to the question whether a person would answer `bal` to the
question of whether there is gold on the island, is `bal` exactly when
there is gold on the island. (All islanders know whether or not there
is gold on the island.)

From Smullyan (1978): Puzzle 162.
-/
example {goldOnIsland : Prop} {actual : Reply}
    (h : answeredWith w L p (answeredWith w L p goldOnIsland bal) actual) :
    goldOnIsland ↔ actual = bal :=
  -- Hint: use `response_bal_iff`
  -- Difficulty: very easy
  -- [FILL IN THE PROOF]
  by
    sorry


end Island5
