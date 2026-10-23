module

public import MBDVendor.Magnitude.CategoryTheory.HomUnitEquations

/-!
# Translation of arrow multiplicities in a finite tau-category

Compatibility of the chosen left and right meshes identifies the middle term
of the left mesh at a noninjective label `X` with the middle term of the right
mesh ending at `tauMinus X`.  Comparing the resulting left-mesh unit equation
with the corresponding row of the inverse Hom matrix proves the usual
translation identity for the official arrow multiplicities:

`a(X,Y) = a(Y,tauMinus X)`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
open scoped Matrix

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE.Iyama

universe s v u w

variable {k : Type s} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- The categorical left-mesh defect at a noninjective label, expressed using
the right-mesh decomposition at its negative translate. -/
theorem leftMeshLabelWeightDefect_eq_translationSum
    (weight : Ind → ℤ) (X : T.Noninjective) :
    leftMeshLabelWeightDefect T weight X.1 =
      weight X.1 -
          ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData Y (T.tauMinus X) : ℤ) * weight Y +
        weight (T.tauMinus X) := by
  let W := T.additiveObjectWeightOfLabelWeight weight
  let L := T.leftMesh (T.obj X.1)
  have hleft : W.weight L.X₁ = weight X.1 := by
    calc
      W.weight L.X₁ = W.weight (T.obj X.1) :=
        W.iso_invariant ⟨T.leftTermIso (T.obj X.1)⟩
      _ = weight X.1 := T.additiveObjectWeightOfLabelWeight_obj weight X.1
  have hmiddle : W.weight L.X₂ =
      ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData Y (T.tauMinus X) : ℤ) * weight Y := by
    calc
      W.weight L.X₂ =
          W.weight (T.rightMesh (T.obj (T.tauMinus X))).X₂ :=
        W.iso_invariant ⟨ShortComplex.π₂.mapIso (T.leftRightMeshIso X)⟩
      _ = ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData Y (T.tauMinus X) : ℤ) * weight Y :=
        additiveLabelWeight_rightMiddle T weight (T.tauMinus X)
  have hright : W.weight L.X₃ = weight (T.tauMinus X) := by
    calc
      W.weight L.X₃ = W.weight (T.obj (T.tauMinus X)) :=
        W.iso_invariant ⟨T.tauMinusIso X⟩
      _ = weight (T.tauMinus X) :=
        T.additiveObjectWeightOfLabelWeight_obj weight (T.tauMinus X)
  rw [leftMeshLabelWeightDefect]
  change W.weight L.X₁ - W.weight L.X₂ + W.weight L.X₃ = _
  rw [hleft, hmiddle, hright]

/-- The mesh contribution in the row of a noninjective label is the single
unit contribution ending at its negative translate. -/
theorem meshContribution_row_sum_of_noninjective
    [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (X : T.Noninjective) :
    ∑ target,
        MBDVendor.Magnitude.ARCount.meshContribution
            T.IsProjective (tau T) X.1 target * weight target =
      weight (T.tauMinus X) := by
  classical
  have hrow (Y : T.Nonprojective) :
      ∑ target,
          MBDVendor.Magnitude.ARCount.singletonMatrix
              (tau T Y) Y.1 X.1 target * weight target =
        if X.1 = tau T Y then weight Y.1 else 0 := by
    by_cases h : X.1 = tau T Y
    · simp [MBDVendor.Magnitude.ARCount.singletonMatrix, h]
    · simp [MBDVendor.Magnitude.ARCount.singletonMatrix, h]
  rw [MBDVendor.Magnitude.ARCount.meshContribution]
  simp only [Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hrow]
  rw [Finset.sum_eq_single (T.tauPlusEquiv.symm X)]
  · simp [tau]
  · intro Y _ hY
    have hne : X.1 ≠ tau T Y := by
      intro h
      apply hY
      have hYX : T.tauPlusEquiv Y = X := by
        apply Subtype.ext
        exact h.symm
      rw [← T.tauPlusEquiv.symm_apply_apply Y, hYX]
    simp [hne]
  · simp

/-- An injective label cannot occur as the translated source of a right mesh,
so its row has no mesh contribution. -/
theorem meshContribution_row_sum_of_injective
    [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (X : Ind) (hX : T.IsInjective X) :
    ∑ target,
        MBDVendor.Magnitude.ARCount.meshContribution
            T.IsProjective (tau T) X target * weight target = 0 := by
  classical
  have hrow (Y : T.Nonprojective) :
      ∑ target,
          MBDVendor.Magnitude.ARCount.singletonMatrix
              (tau T Y) Y.1 X target * weight target = 0 := by
    have hne : X ≠ tau T Y := by
      intro h
      apply (T.tauPlusEquiv Y).2
      change T.IsInjective (tau T Y)
      rw [← h]
      exact hX
    simp [MBDVendor.Magnitude.ARCount.singletonMatrix, hne]
  rw [MBDVendor.Magnitude.ARCount.meshContribution]
  simp only [Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hrow]
  simp

/-- A noninjective row of the mesh matrix is identity minus outgoing arrows
plus the unit entry at the negative translate. -/
theorem meshRowWeight_eq_of_noninjective
    [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (X : T.Noninjective) :
    meshRowWeight T weight X.1 =
      weight X.1 -
          ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Y : ℤ) * weight Y +
        weight (T.tauMinus X) := by
  classical
  have hmesh := meshContribution_row_sum_of_noninjective T weight X
  rw [meshRowWeight]
  simp only [meshMatrix, MBDVendor.Magnitude.ARCount.meshMatrix,
    Matrix.add_apply, Matrix.one_apply,
    MBDVendor.Magnitude.ARCount.arrowMatrix, add_mul,
    Finset.sum_add_distrib]
  rw [hmesh]
  simp
  abel

/-- An injective row of the mesh matrix is identity minus its outgoing arrow
row, with no translation contribution. -/
theorem meshRowWeight_eq_of_injective
    [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (X : Ind) (hX : T.IsInjective X) :
    meshRowWeight T weight X =
      weight X - ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData X Y : ℤ) * weight Y := by
  classical
  have hmesh := meshContribution_row_sum_of_injective T weight X hX
  rw [meshRowWeight]
  simp only [meshMatrix, MBDVendor.Magnitude.ARCount.meshMatrix,
    Matrix.add_apply, Matrix.one_apply,
    MBDVendor.Magnitude.ARCount.arrowMatrix, add_mul,
    Finset.sum_add_distrib]
  rw [hmesh]
  simp
  abel

/-- Every represented Hom column gives the same weighted sum for arrows out
of `X` and arrows into its negative translate. -/
theorem outgoingArrow_homToWeight_eq_translation
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T)
    (leftEpi : ∀ A : Ind, Epi (T.leftMesh (T.obj A)).g)
    (X : T.Noninjective) (I : Ind) :
    ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Y : ℤ) *
          homDimensionMatrix T.toFiniteRightTauCategoryData k Y I =
      ∑ Y, (arrowMultiplicity T.toFiniteRightTauCategoryData Y (T.tauMinus X) : ℤ) *
          homDimensionMatrix T.toFiniteRightTauCategoryData k Y I := by
  have hrow := meshRowWeight_homToWeight T D I X.1
  have hleft := leftMeshLabelWeightDefect_homToWeight T D leftEpi I X.1
  rw [meshRowWeight_eq_of_noninjective T
      (homToWeight (k := k) T I) X] at hrow
  rw [leftMeshLabelWeightDefect_eq_translationSum T
      (homToWeight (k := k) T I) X] at hleft
  simp only [homToWeight] at hrow hleft
  omega

/-- Arrow multiplicity is preserved by translation across a mesh:
`a(X,Y) = a(Y,tauMinus X)` for every noninjective `X`. -/
theorem arrowMultiplicity_eq_translation
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T)
    (leftEpi : ∀ A : Ind, Epi (T.leftMesh (T.obj A)).g)
    (X : T.Noninjective) (Y : Ind) :
    arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Y =
      arrowMultiplicity T.toFiniteRightTauCategoryData Y (T.tauMinus X) := by
  let outgoing : Ind → ℤ :=
    fun Z ↦ arrowMultiplicity T.toFiniteRightTauCategoryData X.1 Z
  let translated : Ind → ℤ :=
    fun Z ↦ arrowMultiplicity T.toFiniteRightTauCategoryData Z (T.tauMinus X)
  have hweighted :
      outgoing ᵥ* homDimensionMatrix T.toFiniteRightTauCategoryData k =
        translated ᵥ* homDimensionMatrix T.toFiniteRightTauCategoryData k := by
    funext I
    exact outgoingArrow_homToWeight_eq_translation T D leftEpi X I
  have hrightInverse := homDimensionMatrix_mul_meshMatrix T D
  have hvectors : outgoing = translated := by
    calc
      outgoing = outgoing ᵥ* (1 : Matrix Ind Ind ℤ) :=
        (Matrix.vecMul_one outgoing).symm
      _ = outgoing ᵥ*
          (homDimensionMatrix T.toFiniteRightTauCategoryData k * meshMatrix T) := by rw [hrightInverse]
      _ = (outgoing ᵥ* homDimensionMatrix T.toFiniteRightTauCategoryData k) ᵥ* meshMatrix T :=
        (Matrix.vecMul_vecMul outgoing
          (homDimensionMatrix T.toFiniteRightTauCategoryData k) (meshMatrix T)).symm
      _ = (translated ᵥ* homDimensionMatrix T.toFiniteRightTauCategoryData k) ᵥ* meshMatrix T := by
        rw [hweighted]
      _ = translated ᵥ*
          (homDimensionMatrix T.toFiniteRightTauCategoryData k * meshMatrix T) :=
        Matrix.vecMul_vecMul translated
          (homDimensionMatrix T.toFiniteRightTauCategoryData k) (meshMatrix T)
      _ = translated ᵥ* (1 : Matrix Ind Ind ℤ) := by rw [hrightInverse]
      _ = translated := Matrix.vecMul_one translated
  have hentry := congrFun hvectors Y
  dsimp only [outgoing, translated] at hentry
  exact_mod_cast hentry

end MBDVendor.Magnitude.FiniteTauMatrix
