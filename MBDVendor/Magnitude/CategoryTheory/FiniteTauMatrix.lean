import MBDVendor.Magnitude.Combinatorics.MeshMatrix
import MBDVendor.Magnitude.CategoryTheory.LinearBiproduct
import MBDVendor.Magnitude.CategoryTheory.TauExactDimension
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import MBDVendor.QSE.CategoryTheory.FiniteTauCategory

/-!
# Matrices attached to a finite tau-category

This file turns the chosen finite skeleton and right tau-sequences in
`FiniteTauCategoryData` into the concrete matrices used by the magnitude
argument.  The middle term of the right mesh ending at `Y` is decomposed into
chosen indecomposables.  Occurrences of `X` in that decomposition define the
arrow multiplicity from `X` to `Y`.

For a Hom-finite linear category we also record the integer Hom-dimension
matrix.  The next layer will prove, from tau-sequence exactness and the
one-dimensional residue division algebras, that the mesh and Hom matrices are
mutual inverses.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteRightTauCategoryData

variable (T : FiniteRightTauCategoryData C Ind)

/-- Projective labels for right-tau data are those whose chosen right mesh
has zero first term. -/
abbrev IsProjective (X : Ind) : Prop :=
  IsZero (T.rightMesh (T.obj X)).X₁

/-- The finite subtype of nonprojective labels in right-tau data. -/
abbrev Nonprojective : Type w :=
  {X : Ind // ¬ T.IsProjective X}

end FiniteRightTauCategoryData

end MBDVendor.QSE.Iyama

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE.Iyama

universe v u w t

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteRightTauCategoryData C Ind)

/-- Number of indecomposable occurrences in the chosen decomposition of the
middle term of the right mesh ending at `Y`. -/
def rightMiddleArity (Y : Ind) : ℕ :=
  Classical.choose (T.obj_decomposition (T.rightMesh (T.obj Y)).X₂)

/-- Labels in the chosen decomposition of the middle term of the right mesh
ending at `Y`. -/
def rightMiddleLabel (Y : Ind) : Fin (rightMiddleArity T Y) → Ind :=
  Classical.choose
    (Classical.choose_spec
      (T.obj_decomposition (T.rightMesh (T.obj Y)).X₂))

/-- The chosen middle-term decomposition really represents the middle term of
the right mesh. -/
theorem rightMiddleIso (Y : Ind) :
    Nonempty
      ((T.rightMesh (T.obj Y)).X₂ ≅
        ⨁ fun i ↦ T.obj (rightMiddleLabel T Y i)) :=
  Classical.choose_spec
    (Classical.choose_spec
      (T.obj_decomposition (T.rightMesh (T.obj Y)).X₂))

/-- Arrow-occurrence multiplicity from `source` to `target`, read from the
middle term of the right mesh ending at `target`. -/
def arrowMultiplicity (source target : Ind) : ℕ :=
  by
    classical
    exact ∑ i : Fin (rightMiddleArity T target),
      if rightMiddleLabel T target i = source then 1 else 0

/-- Summing incoming arrow occurrences at a target recovers the number of
indecomposable occurrences in its chosen right-mesh middle term. -/
theorem sum_arrowMultiplicity_source (target : Ind) :
    ∑ source, arrowMultiplicity T source target = rightMiddleArity T target := by
  classical
  simp only [arrowMultiplicity]
  rw [Finset.sum_comm]
  simp

/-- Regrouping a sum over middle-term occurrences by their indecomposable
labels introduces the arrow multiplicities. -/
theorem sum_arrowMultiplicity_mul (target : Ind) (weight : Ind → ℕ) :
    ∑ source, arrowMultiplicity T source target * weight source =
      ∑ i : Fin (rightMiddleArity T target),
        weight (rightMiddleLabel T target i) := by
  classical
  simp only [arrowMultiplicity, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- Auslander--Reiten translation on nonprojective labels. -/
def tau (U : FiniteTauCategoryData C Ind) (Y : U.Nonprojective) : Ind :=
  U.tauPlus Y

/-- The paper-oriented mesh matrix of the chosen finite tau-category. -/
def meshMatrix (U : FiniteTauCategoryData C Ind)
    [DecidableEq Ind] [DecidablePred U.IsProjective] :
    Matrix Ind Ind ℤ :=
  MBDVendor.Magnitude.ARCount.meshMatrix
    (arrowMultiplicity U.toFiniteRightTauCategoryData)
      U.IsProjective (tau U)

theorem meshMatrix_apply_of_projective
    (U : FiniteTauCategoryData C Ind)
    [DecidableEq Ind] [DecidablePred U.IsProjective]
    {source target : Ind} (hTarget : U.IsProjective target) :
    meshMatrix U source target =
      (if source = target then 1 else 0) -
        arrowMultiplicity U.toFiniteRightTauCategoryData source target := by
  change MBDVendor.Magnitude.ARCount.meshMatrix
    (arrowMultiplicity U.toFiniteRightTauCategoryData)
      U.IsProjective (tau U) source target = _
  exact MBDVendor.Magnitude.ARCount.meshMatrix_apply_of_projective
    (arrowMultiplicity U.toFiniteRightTauCategoryData)
      U.IsProjective (tau U)
      (source := source) (target := target) hTarget

theorem meshMatrix_apply_of_nonprojective
    (U : FiniteTauCategoryData C Ind)
    [DecidableEq Ind] [DecidablePred U.IsProjective]
    {source target : Ind} (hTarget : ¬ U.IsProjective target) :
    meshMatrix U source target =
      (if source = target then 1 else 0) -
          arrowMultiplicity U.toFiniteRightTauCategoryData source target +
        if source = tau U ⟨target, hTarget⟩ then 1 else 0 := by
  change MBDVendor.Magnitude.ARCount.meshMatrix
    (arrowMultiplicity U.toFiniteRightTauCategoryData)
      U.IsProjective (tau U) source target = _
  exact MBDVendor.Magnitude.ARCount.meshMatrix_apply_of_nonprojective
    (arrowMultiplicity U.toFiniteRightTauCategoryData)
      U.IsProjective (tau U)
      (source := source) (target := target) hTarget

/-- Integer Hom-dimension matrix of a Hom-finite linear finite tau-category. -/
def homDimensionMatrix
    (k : Type t) [Field k] [Linear k C]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] : Matrix Ind Ind ℤ :=
  fun X Y ↦ Module.finrank k (T.obj X ⟶ T.obj Y)

theorem homDimensionMatrix_nonnegative
    (k : Type t) [Field k] [Linear k C]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : Ind) :
    0 ≤ homDimensionMatrix T k X Y := by
  simp [homDimensionMatrix]

/-- Applying `Hom(obj X,-)` to the chosen middle-term decomposition gives the
sum of the Hom dimensions of all arrow occurrences ending at `Y`. -/
theorem finrank_hom_rightMiddle
    (k : Type t) [Field k] [Linear k C]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : Ind) :
    Module.finrank k (T.obj X ⟶ (T.rightMesh (T.obj Y)).X₂) =
      ∑ i : Fin (rightMiddleArity T Y),
        Module.finrank k
          (T.obj X ⟶ T.obj (rightMiddleLabel T Y i)) := by
  obtain ⟨e⟩ := rightMiddleIso T Y
  exact MBDVendor.Magnitude.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
    k (T.obj X) (T.rightMesh (T.obj Y)).X₂
      (fun i ↦ T.obj (rightMiddleLabel T Y i)) e

/-- The same middle-term formula regrouped by arrow multiplicity. -/
theorem finrank_hom_rightMiddle_eq_arrowSum
    (k : Type t) [Field k] [Linear k C]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : Ind) :
    Module.finrank k (T.obj X ⟶ (T.rightMesh (T.obj Y)).X₂) =
      ∑ source,
        arrowMultiplicity T source Y *
          Module.finrank k (T.obj X ⟶ T.obj source) := by
  rw [finrank_hom_rightMiddle T k X Y,
    sum_arrowMultiplicity_mul T Y
      (fun source ↦ Module.finrank k (T.obj X ⟶ T.obj source))]

end MBDVendor.Magnitude.FiniteTauMatrix
