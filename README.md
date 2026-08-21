# Knights and Knaves in Lean

A collection of Lean 4 exercises based on Raymond Smullyan’s *Knights and Knaves* puzzles. The project includes a model of islands whose inhabitants are either truth-telling knights or lying knaves, and features some statements to be proven based on puzzles in this setting.

The exercises are intended for practising propositional reasoning, proof structure, case analysis, and working with a small custom Lean API.

## Contents

- `KK/KnightsAndKnaves.lean` — the core `World` model, predicates for knights and knaves, and reusable reasoning lemmas;
- `KK/Island1.lean` — two-inhabitant puzzles;
- `KK/Island2.lean` — three-inhabitant puzzles;
- `KK/KnightsKnavesNormals.lean` — a formalisation of the setting where there could be 'normals' (who may lie or be truthful) in addition to knights and knaves;
- `KK/Island3.lean` — two-inhabitant puzzles with normals.
- `KK/Island4.lean` — three-inhabitant puzzles with normals.
- `KK/BalDa.lean` — a formalisation of the `bal`/`da` yes–no language whose word for "yes" is unknown;
- `KK/Island5.lean` — puzzles using the `bal`/`da` setting.

The exercises are to complete the `sorry` proofs.

## Quickstart

You can clone this repository and run it using Lean on your local computer.
However, if you want to have a quick start and play with this in your browser,
you can do so as follows:
- Go to [Lean Live](https://live.lean-lang.org/)
- Copy the contents of both `KK/KnightsAndKnaves.lean` and `KK/Island1.lean` into the editor in Lean Live (without the line `import KK.KnightsAndKnaves`).
- Start proving!