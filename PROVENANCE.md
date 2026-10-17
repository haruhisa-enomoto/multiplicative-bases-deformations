# Provenance

The Lean development is maintained by Haruhisa Enomoto. It formalizes the
manuscript *Multiplicative bases and deformations of representation-finite
algebras*; the [manuscript snapshot](docs/manuscript/README.md) is the revision
of October 17, 2026, from source commit
`a2b528715260a8733c77195ade440d6a2299d47e` of the private research repository
`homological-conjectures`. The [correspondence](docs/PAPER-CORRESPONDENCE.md)
describes formal coverage.

The Lean sources originate in `formalization/multiplicative_basis_deformations`
of the same research repository, at commit
`12182c4c29f0bf6d4ee499305eeba1c8466151ca`. The
[source manifest](verification/2026-10-17/source-sync.json) records the hash of
every copied file.

## Contributions

The formalization was developed with AI coding agents under Haruhisa Enomoto's
direction, mainly with GPT-6-Astra and Claude Opus 5.5. The manuscript's Use of
AI paragraph gives the author's account of AI contributions to the research,
the manuscript and the formalization. A complete model-by-model history of the
development has not been reconstructed.

## Dependencies and licences

The proof package pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib is the only external Lake
dependency. The [vendored-source record](VENDORED.md) identifies the
Auslander–Reiten library copied from the magnitude-conjecture formalization.
This repository is released under the [Apache License 2.0](LICENSE), the
licence of the vendored sources.
