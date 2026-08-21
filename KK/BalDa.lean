/-
Copyright (c) 2026 Ronald de Haan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ronald de Haan
-/

import KK.Basic

/-!
A framework for puzzles with knights and knaves who answer yes/no
questions using the words 'bal' and 'da' meaning 'yes' and 'no'
(but in an unknown order).

The setting is described in Smullyan (1978) as follows.
> On a certain island near Haiti, half the inhabitants have
> been bewitched by voodoo magic and turned into zombies.
> The zombies of this island do not behave according to the
> conventional concept: they are not silent or deathlike---
> they move about and talk in as lively a fashion as do the
> humans. It's just that the zombies of this island always lie
> and the humans of this island always tell the truth.
> So far, this sounds like another knight-knave situation
> in a different dress, doesn't it? But it isn't! The situation is
> enormously complicated by the fact that although all the
> natives understand English perfectly, an ancient taboo of
> the island forbids them ever to use non-native words in
> their speech. Hence whenever you ask them a yes-no
> question, they reply "Bal" or "Da"---one of which means
> yes and the other no. The trouble is that we do not know
> which of "Bal" or "Da" means yes and which means no.
-/

namespace BalDa

open KnightsAndKnaves

/-- The two possible answer words. -/
inductive Reply where
  | bal
  | da
  deriving DecidableEq, Repr

open Reply

variable {Person : Type}

/-- The language used on the island, specifying which word means yes. -/
structure Language where
  yesWord : Reply

/-- `wordMeansYes L word` says that `word` is the native word for yes in language `L`. -/
def wordMeansYes (L : Language) (word : Reply) : Prop :=
  word = L.yesWord

/--
`answeredWith w L p Q word` says that `p` answered the yes/no question `Q` with `word`
in world `w` using language `L`.

A knight uses the yes-word exactly when `Q` is true;
a knave does so exactly when `Q` is false.
-/
def answeredWith (w : World Person) (L : Language) (p : Person) (Q : Prop) (word : Reply) : Prop :=
  said w p (wordMeansYes L word ↔ Q)

notation "answered[" w ", " L "]" => BalDa.answeredWith w L
notation p " answered[" w ", " L "] " Q:200 " with " word:200 =>
  BalDa.answeredWith w L p Q word

/--
If a person is asked whether they would say `bal` in response to `Q`,
then their actual response is `bal` exactly when `Q` is true.
-/
theorem response_bal_iff
    (w : World Person) (L : Language) {p : Person} {Q : Prop} {actual : Reply}
    (h : answeredWith w L p (answeredWith w L p Q bal) actual) :
    actual = bal ↔ Q := by
  -- Hint: split on which word means yes and on `actual`;
  -- in each case, determine whether `p` is a knight.
  -- [FILL IN THE PROOF]
  sorry

/--
If a person is asked whether they would say `bal` in response to `Q`,
then their actual response is `bal` exactly when `Q` is false.
-/
theorem response_da_iff_not
    (w : World Person) (L : Language) {p : Person} {Q : Prop} {actual : Reply}
    (h : answeredWith w L p (answeredWith w L p Q bal) actual) :
    actual = da ↔ ¬ Q := by
  -- Hint: first use `response_bal_iff`;
  -- then split on the two possible values of `actual`.
  -- [FILL IN THE PROOF]
  sorry

/--
Simplify a Bal/Da proof state using all local hypotheses.
-/
macro "balda_simp_all" : tactic =>
  `(tactic|
    simp_all [answeredWith, wordMeansYes, said_iff])

/--
Split on which reply word means yes in `L`, and on the supplied reply.

This produces the four possible combinations of the language's yes-word
and the actual reply, then simplifies each resulting branch with
`balda_simp_all`.

Example: `balda_cases_simp_all L actual`.
-/
macro "balda_cases_simp_all"
    L:ident actual:Lean.Parser.Tactic.elimTarget : tactic =>
  `(tactic|
    cases h_yes : ($L).yesWord <;>
      cases $actual <;>
        balda_simp_all)


end BalDa
