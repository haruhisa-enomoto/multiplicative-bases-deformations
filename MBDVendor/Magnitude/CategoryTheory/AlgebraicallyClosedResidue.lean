import MBDVendor.Magnitude.CategoryTheory.ResidueDimension
import MBDVendor.Magnitude.LinearAlgebra.LocalAlgebraResidue

/-!
# Residue maps for chosen indecomposables over an algebraically closed field

The finite tau-category data already records that every chosen indecomposable
has a local endomorphism ring.  Over an algebraically closed field, the local
algebra residue construction supplies its unique scalar residue map.  The
categorical radical criterion identifies the kernel with the diagonal
categorical radical.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.Magnitude.LocalAlgebraResidue
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama

universe s v u w

variable {k : Type s} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

/-- The scalar residue map on the endomorphism algebra of a chosen
indecomposable. -/
def algebraicallyClosedResidueMap
    (T : FiniteRightTauCategoryData C Ind) (X : Ind) :
    (T.obj X ⟶ T.obj X) →ₗ[k] k := by
  letI : IsLocalRing (End (T.obj X)) := T.obj_end_local X
  letI : FiniteDimensional k (End (T.obj X)) := by
    change FiniteDimensional k (T.obj X ⟶ T.obj X)
    infer_instance
  exact residueLinearMap k (End (T.obj X))

omit [DecidableEq Ind] in
theorem algebraicallyClosedResidueMap_surjective
    (T : FiniteRightTauCategoryData C Ind) (X : Ind) :
    Function.Surjective (algebraicallyClosedResidueMap (k := k) T X) := by
  letI : IsLocalRing (End (T.obj X)) := T.obj_end_local X
  letI : FiniteDimensional k (End (T.obj X)) := by
    change FiniteDimensional k (T.obj X ⟶ T.obj X)
    infer_instance
  exact residueLinearMap_surjective (k := k) (E := End (T.obj X))

omit [DecidableEq Ind] in
theorem mem_ker_algebraicallyClosedResidueMap_iff_not_isUnit
    (T : FiniteRightTauCategoryData C Ind) (X : Ind)
    (f : T.obj X ⟶ T.obj X) :
    f ∈ LinearMap.ker (algebraicallyClosedResidueMap (k := k) T X) ↔
      ¬ IsUnit (End.of f) := by
  letI : IsLocalRing (End (T.obj X)) := T.obj_end_local X
  letI : FiniteDimensional k (End (T.obj X)) := by
    change FiniteDimensional k (T.obj X ⟶ T.obj X)
    infer_instance
  exact mem_ker_residueLinearMap_iff (k := k) (E := End (T.obj X)) f

omit [DecidableEq Ind] in
/-- The concrete scalar residue map has the categorical radical as kernel. -/
theorem radicalSubmodule_eq_ker_algebraicallyClosedResidueMap
    (T : FiniteRightTauCategoryData C Ind) (X : Ind) :
    MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
        k (T.obj X) (T.obj X) =
      LinearMap.ker (algebraicallyClosedResidueMap (k := k) T X) := by
  ext f
  change IsRadicalMorphism f ↔
    f ∈ LinearMap.ker (algebraicallyClosedResidueMap (k := k) T X)
  rw [mem_ker_algebraicallyClosedResidueMap_iff_not_isUnit]
  constructor
  · intro hf hunit
    have hNotSplit :=
      (T.isRadicalMorphism_iff_not_isSplitMono_from_obj f).mp hf
    haveI : IsIso f := (isUnit_iff_isIso (End.of f)).mp hunit
    exact hNotSplit inferInstance
  · intro hnonunit
    rw [T.isRadicalMorphism_iff_not_isSplitMono_from_obj]
    intro hsplit
    letI : IsSplitMono f := hsplit
    letI : IsIso f := isIso_of_isSplitMono_obj_obj T f
    exact hnonunit ((isUnit_iff_isIso (End.of f)).mpr inferInstance)

/-- Algebraic closedness automatically supplies all diagonal residue-field
data required by the Hom--mesh inverse theorem. -/
def ResidueFieldData.ofIsAlgClosed
    (T : FiniteRightTauCategoryData C Ind) : ResidueFieldData (k := k) T where
  residueMap := algebraicallyClosedResidueMap T
  residueMap_surjective := algebraicallyClosedResidueMap_surjective T
  radical_eq_ker := radicalSubmodule_eq_ker_algebraicallyClosedResidueMap T

/-- Over an algebraically closed field, right-mesh monicity is now the only
remaining input to the Hom--mesh inverse package. -/
theorem HomMeshInverseData.ofIsAlgClosed
    (T : FiniteTauCategoryData C Ind)
    (rightMono : ∀ Y : Ind, Mono (T.rightMesh (T.obj Y)).f) :
    HomMeshInverseData (k := k) T :=
  HomMeshInverseData.ofResidue T rightMono
    (ResidueFieldData.ofIsAlgClosed
      (T : FiniteRightTauCategoryData C Ind))

end MBDVendor.Magnitude.FiniteTauMatrix
