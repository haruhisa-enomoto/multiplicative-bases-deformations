# Verification record, 2026-10-23

Source: the files listed in [source-sync.json](source-sync.json), identical to
`formalization/multiplicative_basis_deformations` at research commit
`8e6e678dfa987e4e116de4ad09eda25249071084`. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`).

This record follows the move from Lean `v4.33.1` to `v4.35.0-rc3` and the port
of every file to the Lean module system, both required by the current
Palomar policy. Proofs were adapted; no statement changed.

## Build

`lake build MultiplicativeBasisDeformations MBDVendor Challenge Solution` with
Mathlib from the precompiled cache and no project build artifacts:
`Build completed successfully (9519 jobs)`, exit 0, wall clock 19 min 39 s
(Linux, WSL2, 20 threads). `scripts/check-lean-sources.py` passes: every Lean
file uses the module header and has at most 10,000 lines.

## Axioms

`python3 scripts/audit_axioms.py`: all 14 queried declarations of
[`scripts/AxiomAudit.lean`](../../scripts/AxiomAudit.lean), including
`theoremA`, `theoremB`, `Statement.theoremA` and `Statement.theoremB`, depend
only on `propext`, `Classical.choice` and `Quot.sound`. Log:
[axioms.log](axioms.log), summary: [axioms.json](axioms.json). In the research
package, a scan of all 23981 declarations of the library and the vendored
files found no other axiom.

## Statement check

`./scripts/verify-comparator.sh` runs the `lake comparator` bundled with Lean
`v4.35.0-rc3` on `Challenge.lean` and `Solution.lean` (theorems
`MultiplicativeBasisDeformations.Challenge.theoremA` and `theoremB`): the
statements match, only the three standard axioms occur, and the con-ron
checker (63933 declarations), NanoDa and the Lean kernel accept the exported
proof. `Your solution is okay!`, 7 min 4 s. Record: [comparator.json](comparator.json).
This is a local run, not a hosted Palomar preflight or registry acceptance.
