# Multiplicative bases and deformations of representation-finite algebras

[Paper](docs/manuscript/main.pdf) ·
[Main theorems in Lean](MultiplicativeBasisDeformations/Statements/MainTheorems.lean) ·
[Paper correspondence](docs/PAPER-CORRESPONDENCE.md)

This repository contains a complete Lean 4 formalization of Haruhisa Enomoto's
manuscript *Multiplicative bases and deformations of representation-finite
algebras* (revision of October 17, 2026). The paper gives a new proof of two
classical results of Bautista, Gabriel, Roiter and Salmerón.

**Theorem A.** Every finite-dimensional representation-finite algebra over an
algebraically closed field, of any characteristic, has a normed multiplicative
basis.

**Theorem B.** Every basic finite-dimensional representation-finite algebra over
an algebraically closed field of characteristic different from two is
standard.

A basis is *multiplicative* if each product of two basis elements is zero or a
basis element. It is *normed* if it contains a complete set of primitive
orthogonal idempotents and meets every radical power `(rad A)^n` in a basis of
that power. An algebra is *standard* if there is a `k`-linear equivalence
`k(Γ_A) ≃ ind(mod A)` from the mesh category of its Auslander–Reiten quiver,
sending each vertex to its indecomposable module.

## Start reading

- [Main theorems](MultiplicativeBasisDeformations/Statements/MainTheorems.lean):
  `MultiplicativeBasisDeformations.theoremA` and `theoremB`, with Corollary 5.5
  (`awayFromTwoBasis`) and Theorem 11.8(2) (`standard_iff_rayLinearization`).
- [Normed multiplicative bases](MultiplicativeBasisDeformations/Foundations/NormedBasis.lean)
  (Definition 1.1) and [standardness](MultiplicativeBasisDeformations/Foundations/ARQuiver.lean)
  (Definition 1.2).
- [Independent statement](MultiplicativeBasisDeformations/Statement.lean): both
  theorems stated with Mathlib alone, proved as `Statement.theoremA` and
  `Statement.theoremB`. The [Challenge](Challenge.lean) is generated from it,
  and [Solution](Solution.lean) proves it; Comparator replay passes.
- [Paper correspondence](docs/PAPER-CORRESPONDENCE.md): every numbered statement
  of the manuscript with its Lean declarations.

All definitions and proofs are complete. Theorems A and B and the main
statements depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. The formalization proves the ordinary Auslander–Reiten theory
it uses; see [VENDORED.md](VENDORED.md).

## Coverage

Theorems A and B and all 96 numbered theorems, propositions, lemmas,
corollaries and remarks are proved, and all 22 numbered definitions,
constructions and settings are formalized. The three examples are not
formalized. Some statements are proved in an equivalent or more general form,
and some proofs take a shorter route than the paper; the docstrings of the
listed declarations explain these forms.

Conventions: modules are right modules, formalized as modules over the opposite
algebra. Composition is written left to right, as in the paper. The field `k`
and the algebra `A` live in one universe.

## Build and verify

Lean is pinned to `v4.33.1` and Mathlib to commit
`0df444a360eaa60ab8c11dca51a86af692955474`, the only external dependency.

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

or, with memory and timing records for each step,

```sh
python3 scripts/build_lean_serial.py --package . --output .build-audit/full \
  --max-rss-kib 12582912 MultiplicativeBasisDeformations
python3 scripts/audit_axioms.py
```

A fresh full build is substantial; use a machine with at least 16 GiB RAM.
Independent replay with Comparator is described in
[docs/VERIFICATION.md](docs/VERIFICATION.md), and the records are in
[verification](verification/).

## Website

The `website/` pages and the generated API form a mathematical website. Build
it locally with the commands in [docs/VERIFICATION.md](docs/VERIFICATION.md).

## Provenance

See [PROVENANCE.md](PROVENANCE.md) for the source of the Lean files, the
manuscript snapshot and contributions, and [VENDORED.md](VENDORED.md) for the
reused Auslander–Reiten library. Licensed under the [Apache License 2.0](LICENSE).
