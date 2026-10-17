# Verification record, 2026-10-17

Source: the files listed in [source-sync.json](source-sync.json), identical to
`formalization/multiplicative_basis_deformations` at research commit
`36f7a0d5700c6c072e59d56e7bb1feec56149e4c`. Lean `v4.33.1`, Mathlib
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

This record is a build and axiom check by the formalizing agent. It is not an
independent kernel replay (for example with Comparator or NanoDa).
