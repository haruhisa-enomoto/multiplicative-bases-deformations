import MBDVendor.Magnitude.Algebra.RightModuleRadical
import MBDVendor.QSE.CategoryTheory.FiniteTauCategory

/-!
# The finite right-module category as finite tau-category data

This file packages the finite Krull--Schmidt and nilpotent-radical fields of the generic
`FiniteRightTauCategoryData` interface for the literal category of finitely
generated right modules over a representation-finite finite-dimensional
algebra.  After this construction, the remaining inputs are exactly the chosen
right and left Auslander--Reiten meshes and their translation compatibility.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule

open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The genuinely tau-theoretic inputs still needed after the finite
right-module skeleton, Krull--Schmidt properties, and nilpotent categorical
radical have been constructed. -/
structure RightTauInput
    (S : FiniteIndecomposableSkeleton k A) where
  rightMesh : FinitelyGeneratedCategory A →
    ShortComplex (FinitelyGeneratedCategory A)
  rightTermIso : ∀ X, (rightMesh X).X₃ ≅ X
  rightTau : ∀ X, RightTauSequence (rightMesh X)

/-- The remaining two-sided tau-theoretic input, after the finite
Krull--Schmidt module-category fields have been discharged. -/
structure TauInput
    (S : FiniteIndecomposableSkeleton k A) where
  right : RightTauInput S
  leftMesh : FinitelyGeneratedCategory A →
    ShortComplex (FinitelyGeneratedCategory A)
  leftTermIso : ∀ X, (leftMesh X).X₁ ≅ X
  leftTau : ∀ X, LeftTauSequence (leftMesh X)
  tauPlusEquiv :
    {X : Fin S.n // ¬ IsZero (right.rightMesh (S.fgObj X)).X₁} ≃
      {Y : Fin S.n // ¬ IsZero (leftMesh (S.fgObj Y)).X₃}
  rightLeftMeshIso :
    ∀ X : {X : Fin S.n //
        ¬ IsZero (right.rightMesh (S.fgObj X)).X₁},
      right.rightMesh (S.fgObj X.1) ≅
        leftMesh (S.fgObj ((tauPlusEquiv X).1))

namespace FiniteIndecomposableSkeleton

variable (S : FiniteIndecomposableSkeleton k A)

/-- A representation-finite finite-dimensional right-module category supplies
all finite Krull--Schmidt and nilpotent-radical fields of
`FiniteRightTauCategoryData`.  The input contains only chosen right AR meshes.
-/
def toFiniteRightTauCategoryData (D : RightTauInput S) :
    FiniteRightTauCategoryData
      (FinitelyGeneratedCategory A) (Fin S.n) where
  obj := S.fgObj
  obj_indec := S.fgObj_indecomposable
  obj_end_local := S.fgObj_end_isLocalRing
  obj_decomposition := S.fgObj_decomposition (k := k)
  obj_complete := S.fgObj_complete (k := k)
  obj_skeletal := S.fgObj_skeletal
  radical := S.fgNilpotentRadicalData
  rightMesh := D.rightMesh
  rightTermIso := D.rightTermIso
  rightTau := D.rightTau

/-- A two-sided AR-mesh input completes the literal finitely generated
right-module category to the generic finite tau-category interface. -/
def toFiniteTauCategoryData (D : TauInput S) :
    FiniteTauCategoryData
      (FinitelyGeneratedCategory A) (Fin S.n) where
  toFiniteRightTauCategoryData := S.toFiniteRightTauCategoryData D.right
  leftMesh := D.leftMesh
  leftTermIso := D.leftTermIso
  leftTau := D.leftTau
  tauPlusEquiv := D.tauPlusEquiv
  rightLeftMeshIso := D.rightLeftMeshIso

end FiniteIndecomposableSkeleton

end MBDVendor.Magnitude.RightModule
