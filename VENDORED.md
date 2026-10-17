# Vendored Lean source

The library `MBDVendor` contains general Auslander–Reiten theory copied from
the Lean formalization of the magnitude conjecture,
[`haruhisa-enomoto/magnitude-conjecture`](https://github.com/haruhisa-enomoto/magnitude-conjecture)
(Apache License 2.0). The copy was taken from the research repository's
`formalization/magnitude_conjecture` at commit
`52fbbfa2bb19203e426bbd12687a7fdf67af62ac`, the last change to that package.
That package in turn vendors foundations from
[`quotient-submodule-equidistribution`](https://github.com/haruhisa-enomoto/quotient-submodule-equidistribution),
some of them adapted from TauCeti; see the provenance records of those
repositories. Attribution in copied source headers is preserved.

The paper assumes this theory (existence of almost split sequences, the
Auslander–Reiten translate, irreducible maps). The main library
`MultiplicativeBasisDeformations` uses `MBDVendor` only through
`MultiplicativeBasisDeformations/Foundations/`.

The record below is `MBDVendor/README.md`.

These 120 files (plus one extracted glue file) are copied from the Lean
formalization of the magnitude conjecture
(<https://github.com/haruhisa-enomoto/magnitude-conjecture>), as developed in
the author's research repository at commit `52fbbfa2b`. They form the dependency
cone of its right-module Auslander--Reiten theory: existence of almost split
sequences on a finite skeleton of indecomposable right modules, the
translation bijection between nonprojective and noninjective labels, the
arrow-multiplicity identity across a mesh, and the comparison of irreducible
spaces with middle-term multiplicities over an algebraically closed field.

The only change is a mechanical rename of module paths and namespaces:
`MagnitudeConjecture` became `MBDVendor.Magnitude` and
`QuotientSubmoduleEquidistribution` became `MBDVendor.QSE`. Statements and
proofs are unchanged. This is general Auslander--Reiten theory, which the
manuscript assumes; it is not a proof of any manuscript statement. Comments in
these files keep their original wording, so references to "the manuscript"
there mean the magnitude paper. The package `MultiplicativeBasisDeformations` uses it
only through `MultiplicativeBasisDeformations/Foundations/`.

The file list is the import closure of
`Algebra.RightModuleTranslationMultiplicity`,
`CategoryTheory.AlgebraicallyClosedOccurrenceBasis`,
`CategoryTheory.ModuleIrreducibleSpaceComparison`,
`Algebra.RightModuleAlmostSplit`, `Algebra.RightModuleProjectiveBoundary`, and
`Algebra.RightModuleRightTau`, `CategoryTheory.AlmostSplitSummandIrreducible`, and
`CategoryTheory.IrreducibleAbelian`, and `CategoryTheory.FiniteTauIrreducible` inside the magnitude package.

`Magnitude/Algebra/RightModuleIntrinsicArrowMultiplicity.lean` is an extracted
glue file: it collects, unchanged, the few declarations of
`RightModuleStandardMesh.lean`, `RightModulePrimitiveDeletion.lean`, and
`RightModuleIntrinsicArrowMultiplicity.lean` needed to prove that the
irreducible space `rad/rad²` has dimension equal to the middle-term
multiplicity; its header lists them. The rest of those three files depends
on unrelated magnitude-specific machinery and is not copied.

`Magnitude/Algebra/RightModulePrimitiveIdempotent.lean` is a second extracted
glue file: lines 1–1245 of the magnitude file of the same name, unchanged up
to the rename, with its import of the magnitude-specific
`RightModulePrimitiveMultiplicity` replaced by the two general files that one
builds on (`Algebra.RightModuleFactorStrict`,
`RepresentationTheory.Trace`). It contains only general module theory for an
idempotent `e`: the right ideal `eA`, the module `D(Ae)`, the identifications
`Hom_A(eA, X) ≅ Xe` and `Hom_A(X, D(Ae)) ≅ D(Xe)`, and indecomposability of
both modules for a primitive `e`. The skeleton-specific remainder of that file
(primitive deletion and multiplicity data) is not copied.
