module

public import MBDVendor.Magnitude.Algebra.RightModuleFactorStrict
public import MBDVendor.Magnitude.CategoryTheory.AlgebraicallyClosedResidue
public import MBDVendor.Magnitude.CategoryTheory.FiniteTauTranslationMultiplicity

/-!
# Translation invariance of right-module arrow multiplicities

For a finite skeleton of indecomposable right modules, compatibility of the
canonical left and right Auslander--Reiten meshes identifies arrows out of a
noninjective label with arrows into its inverse translate.  This numerical
identity is independent of directedness and supplies the polarization of the
standard-form mesh category.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- In the ambient module skeleton, arrow multiplicity out of a
noninjective label equals arrow multiplicity into its inverse
Auslander--Reiten translate. -/
theorem arrowMultiplicity_eq_inverseTranslation
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)})
    (y : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x.1 y =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData y
          ((S.rightTranslationEquiv).symm x).1 := by
  classical
  let U := S.finiteTauCategoryData
  let hmono : ∀ z : Fin S.n, Mono (U.rightMesh (U.obj z)).f := by
    intro z
    change Mono (S.canonicalRightMesh (S.fgObj z)).f
    rw [S.canonicalRightMesh_at_label z]
    exact S.labelRightMesh_f_mono z
  let hinverse : FiniteTauMatrix.HomMeshInverseData (k := k) U :=
    FiniteTauMatrix.HomMeshInverseData.ofIsAlgClosed U hmono
  let hepi : ∀ z : Fin S.n, Epi (U.leftMesh (U.obj z)).g := by
    intro z
    change Epi (S.canonicalLeftMesh (S.fgObj z)).g
    rw [S.canonicalLeftMesh_at_label z]
    exact S.labelLeftMesh_g_epi z
  let xU : U.Noninjective :=
    S.canonicalLeftNonzeroEquivNoninjective.symm x
  have hxU : xU.1 = x.1 := rfl
  have htau : U.tauMinus xU =
      ((S.rightTranslationEquiv).symm x).1 := rfl
  simpa only [hxU, htau] using
    (FiniteTauMatrix.arrowMultiplicity_eq_translation
      U hinverse hepi xU y)

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
