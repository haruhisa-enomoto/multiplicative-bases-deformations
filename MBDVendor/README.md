# Vendored Auslander--Reiten foundations

These 120 files (plus one extracted glue file) are copied from `formalization/magnitude_conjecture` at
repository commit `52fbbfa2b` (last change to that package), the dependency
cone of its right-module Auslander--Reiten theory: existence of almost split
sequences on a finite skeleton of indecomposable right modules, the
translation bijection between nonprojective and noninjective labels, the
arrow-multiplicity identity across a mesh, and the comparison of irreducible
spaces with middle-term multiplicities over an algebraically closed field.

The only change is a mechanical rename of module paths and namespaces:
`MagnitudeConjecture` became `MBDVendor.Magnitude` and
`QuotientSubmoduleEquidistribution` became `MBDVendor.QSE`. Statements and
proofs are unchanged. This is general Auslander--Reiten theory, which the
frozen manuscript assumes (`main.tex:399–400`); it is not a proof of any
manuscript statement. The package `MultiplicativeBasisDeformations` uses it
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
