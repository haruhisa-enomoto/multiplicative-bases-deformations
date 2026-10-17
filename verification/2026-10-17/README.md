# Verification record, 2026-10-17

Source: the files listed in [source-sync.json](source-sync.json), identical to
`formalization/multiplicative_basis_deformations` at research commit
`36f7a0d5700c6c072e59d56e7bb1feec56149e4c` (the build and axiom check below); the current manifest is for commit `83da26adada5490dfd41e1fe233ef6b1c13509ce`, which adds the independent statement. Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

## Build

`lake build` in a new checkout, with Mathlib from the precompiled cache and no
project build artifacts: `Build completed successfully (9254 jobs)`, exit 0,
no `sorry` warning. Wall clock 21 min 54 s; peak resident memory 8.7 GB
(Linux, WSL2).

## Axioms

`python3 scripts/audit_axioms.py`: all 11 queried declarations of
[`scripts/AxiomAudit.lean`](../../scripts/AxiomAudit.lean), including
`theoremA` and `theoremB`, depend only on `propext`, `Classical.choice` and
`Quot.sound`. Log: [axioms.log](axioms.log), summary: [axioms.json](axioms.json).

A source search finds no `sorry`, `admit` or `axiom` declaration.

## Independent replay

Comparator replayed `Challenge.lean` against `Solution.lean` (theorems
`MultiplicativeBasisDeformations.Challenge.theoremA` and `theoremB`): the
statements match, only the three standard axioms occur, and both NanoDa and
the Lean kernel accept the exported proof. Record: [comparator.json](comparator.json).
