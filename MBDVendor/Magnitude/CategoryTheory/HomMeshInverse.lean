import MBDVendor.Magnitude.CategoryTheory.FiniteTauMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The mesh matrix is the inverse Hom matrix

This file proves Iyama's finite radical-layer recurrence in matrix form.  Its
inputs are a finite tau-category, strictness of every chosen right tau-
sequence, Hom-finiteness, and the residue-dimension formula

`dim rad(X,Y) + delta(X,Y) = dim Hom(X,Y)`.

The first two categorical inputs turn each right tau-sequence into a short
exact sequence on Hom spaces.  The chosen middle-term decomposition supplies
the arrow multiplicities.  Column by column, the resulting recurrence is
exactly `H * K = 1`; finite square matrices over `ℤ` are Dedekind finite, so
also `K * H = 1`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE.Iyama

universe s v u w

variable {k : Type s} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

/-- The two additional properties needed to pass from finite tau-category
data to the integer Hom/mesh inverse relation.

For module categories over an algebraically closed field, `rightMono` comes
from strictness of almost-split sequences and `radicalFinrank_add_delta` from
the fact that every indecomposable has residue division algebra `k`. -/
structure HomMeshInverseData (T : FiniteTauCategoryData C Ind) : Prop where
  rightMono : ∀ Y : Ind, Mono (T.rightMesh (T.obj Y)).f
  radicalFinrank_add_delta :
    ∀ X Y : Ind,
      Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj X) (T.obj Y)) +
        (if X = Y then 1 else 0) =
      Module.finrank k (T.obj X ⟶ T.obj Y)

variable (T : FiniteTauCategoryData C Ind)

omit [DecidableEq Ind] in
theorem finrank_hom_rightMesh_left_of_projective
    (X Y : Ind) (hY : T.IsProjective Y) :
    Module.finrank k (T.obj X ⟶ (T.rightMesh (T.obj Y)).X₁) = 0 := by
  rw [finrank_zero_iff_forall_zero]
  intro f
  exact hY.eq_of_tgt f 0

omit [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [DecidableEq Ind] in
theorem finrank_hom_rightMesh_left_of_nonprojective
    (X Y : Ind) (hY : ¬ T.IsProjective Y) :
    Module.finrank k (T.obj X ⟶ (T.rightMesh (T.obj Y)).X₁) =
      Module.finrank k (T.obj X ⟶ T.obj (tau T ⟨Y, hY⟩)) := by
  let eShort := T.rightLeftMeshIso ⟨Y, hY⟩
  let eLeft :
      (T.rightMesh (T.obj Y)).X₁ ≅ T.obj (tau T ⟨Y, hY⟩) :=
    (asIso eShort.hom.τ₁).trans
      (T.leftTermIso (T.obj (tau T ⟨Y, hY⟩)))
  exact (CategoryTheory.Linear.homCongr k (Iso.refl (T.obj X)) eLeft).finrank_eq

theorem projective_column_recurrence
    (D : HomMeshInverseData (k := k) T)
    (X Y : Ind) (hY : T.IsProjective Y) :
    homDimensionMatrix T.toFiniteRightTauCategoryData k X Y -
        ∑ source,
          (arrowMultiplicity T.toFiniteRightTauCategoryData source Y : ℤ) *
            homDimensionMatrix T.toFiniteRightTauCategoryData k X source =
      if X = Y then 1 else 0 := by
  letI : Mono (T.rightMesh (T.obj Y)).f :=
    HomMeshInverseData.rightMono D Y
  have hTau :=
    MBDVendor.Magnitude.CategoryTheory.rightTauSequence_finrank
      k (T.rightMesh (T.obj Y)) (T.rightTau (T.obj Y)) (T.obj X)
  have hMiddle := finrank_hom_rightMiddle_eq_arrowSum
    T.toFiniteRightTauCategoryData k X Y
  have hLeft := finrank_hom_rightMesh_left_of_projective (k := k) T X Y hY
  have hRadical :
      Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj X) (T.rightMesh (T.obj Y)).X₃) =
        Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj X) (T.obj Y)) :=
    (MBDVendor.Magnitude.CategoryTheory.radicalTargetLinearEquiv
      k (T.obj X) (T.rightTermIso (T.obj Y))).finrank_eq
  have hResidue := HomMeshInverseData.radicalFinrank_add_delta D X Y
  have hNat :
      Module.finrank k (T.obj X ⟶ T.obj Y) =
        (∑ source,
          arrowMultiplicity T.toFiniteRightTauCategoryData source Y *
            Module.finrank k (T.obj X ⟶ T.obj source)) +
          (if X = Y then 1 else 0) := by
    omega
  have hInt := congrArg (fun n : ℕ ↦ (n : ℤ)) hNat
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero] at hInt
  simp only [homDimensionMatrix]
  omega

theorem nonprojective_column_recurrence
    (D : HomMeshInverseData (k := k) T)
    (X Y : Ind) (hY : ¬ T.IsProjective Y) :
    homDimensionMatrix T.toFiniteRightTauCategoryData k X Y -
        ∑ source,
          (arrowMultiplicity T.toFiniteRightTauCategoryData source Y : ℤ) *
            homDimensionMatrix T.toFiniteRightTauCategoryData k X source +
      homDimensionMatrix T.toFiniteRightTauCategoryData k X (tau T ⟨Y, hY⟩) =
        if X = Y then 1 else 0 := by
  letI : Mono (T.rightMesh (T.obj Y)).f :=
    HomMeshInverseData.rightMono D Y
  have hTau :=
    MBDVendor.Magnitude.CategoryTheory.rightTauSequence_finrank
      k (T.rightMesh (T.obj Y)) (T.rightTau (T.obj Y)) (T.obj X)
  have hMiddle := finrank_hom_rightMiddle_eq_arrowSum
    T.toFiniteRightTauCategoryData k X Y
  have hLeft := finrank_hom_rightMesh_left_of_nonprojective (k := k) T X Y hY
  have hRadical :
      Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj X) (T.rightMesh (T.obj Y)).X₃) =
        Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj X) (T.obj Y)) :=
    (MBDVendor.Magnitude.CategoryTheory.radicalTargetLinearEquiv
      k (T.obj X) (T.rightTermIso (T.obj Y))).finrank_eq
  have hResidue := HomMeshInverseData.radicalFinrank_add_delta D X Y
  have hNat :
      Module.finrank k (T.obj X ⟶ T.obj Y) +
          Module.finrank k (T.obj X ⟶ T.obj (tau T ⟨Y, hY⟩)) =
        (∑ source,
          arrowMultiplicity T.toFiniteRightTauCategoryData source Y *
            Module.finrank k (T.obj X ⟶ T.obj source)) +
          (if X = Y then 1 else 0) := by
    omega
  have hInt := congrArg (fun n : ℕ ↦ (n : ℤ)) hNat
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero] at hInt
  simp only [homDimensionMatrix]
  omega

/-- The radical-layer recurrence is the right-inverse equation `H * K = 1`.
-/
theorem homDimensionMatrix_mul_meshMatrix
    (D : HomMeshInverseData (k := k) T)
    [DecidablePred T.IsProjective] :
    homDimensionMatrix T.toFiniteRightTauCategoryData k * meshMatrix T = 1 := by
  classical
  ext X Y
  rw [Matrix.mul_apply, Matrix.one_apply]
  have indicatorSum (target : Ind) :
      ∑ source,
          homDimensionMatrix T.toFiniteRightTauCategoryData k X source *
            (if source = target then 1 else 0) =
        homDimensionMatrix T.toFiniteRightTauCategoryData k X target := by
    simp
  by_cases hY : T.IsProjective Y
  · simp_rw [meshMatrix_apply_of_projective T hY, mul_sub]
    rw [Finset.sum_sub_distrib, indicatorSum]
    simpa only [mul_comm] using projective_column_recurrence T D X Y hY
  · simp_rw [meshMatrix_apply_of_nonprojective T hY, mul_add, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      indicatorSum, indicatorSum]
    simpa only [mul_comm] using nonprojective_column_recurrence T D X Y hY

/-- Hence the mesh matrix is also a left inverse of the Hom-dimension matrix.
-/
theorem meshMatrix_mul_homDimensionMatrix
    (D : HomMeshInverseData (k := k) T)
    [DecidablePred T.IsProjective] :
    meshMatrix T * homDimensionMatrix T.toFiniteRightTauCategoryData k = 1 :=
  mul_eq_one_comm.mp (homDimensionMatrix_mul_meshMatrix T D)

/-- Complete matrix form of the magnitude formula for a finite strict tau-
category satisfying the residue-dimension condition. -/
theorem homMesh_inverse_and_total
    (D : HomMeshInverseData (k := k) T)
    [DecidablePred T.IsProjective] :
    homDimensionMatrix T.toFiniteRightTauCategoryData k * meshMatrix T = 1 ∧
      meshMatrix T * homDimensionMatrix T.toFiniteRightTauCategoryData k = 1 ∧
      MBDVendor.Magnitude.ARCount.matrixTotal (meshMatrix T) =
        MBDVendor.Magnitude.ARCount.eulerMagnitude
          (arrowMultiplicity T.toFiniteRightTauCategoryData) T.IsProjective := by
  refine ⟨homDimensionMatrix_mul_meshMatrix T D,
    meshMatrix_mul_homDimensionMatrix T D, ?_⟩
  exact MBDVendor.Magnitude.ARCount.matrixTotal_meshMatrix_eq_eulerMagnitude
    (arrowMultiplicity T.toFiniteRightTauCategoryData) T.IsProjective (tau T)

end MBDVendor.Magnitude.FiniteTauMatrix
