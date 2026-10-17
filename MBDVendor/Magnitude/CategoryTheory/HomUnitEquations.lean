import MBDVendor.Magnitude.CategoryTheory.MeshWeight

/-!
# Hom-dimension weights and the two unit equations

Once the Hom-dimension matrix and the mesh matrix are inverse, a row represented
by a label `P` satisfies the paper's column equation `Phi^T d = e_P`, while a
column represented by `I` satisfies `Phi d = e_I`.  Nonzero maps from `P`, or
to `I`, make the corresponding integral weights strictly positive.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

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

/-- The integer Hom-dimension row represented by `P`. -/
def homFromWeight (P : Ind) : Ind → ℤ :=
  fun X ↦ homDimensionMatrix T.toFiniteRightTauCategoryData k P X

/-- The integer Hom-dimension column represented by `I`. -/
def homToWeight (I : Ind) : Ind → ℤ :=
  fun X ↦ homDimensionMatrix T.toFiniteRightTauCategoryData k X I

omit [DecidableEq Ind] in
/-- The additive extension of a represented Hom row evaluates every object
by the dimension of its Hom space from the representing object. -/
theorem additiveObjectWeight_homFromWeight (P : Ind) (X : C) :
    (T.additiveObjectWeightOfLabelWeight
      (homFromWeight (k := k) T P)).weight X =
        Module.finrank k (T.obj P ⟶ X) := by
  let W := T.additiveObjectWeightOfLabelWeight
    (homFromWeight (k := k) T P)
  let n := T.chosenDecompositionSize X
  let label : Fin n → Ind := T.chosenDecompositionLabel X
  let e : X ≅ ⨁ fun i ↦ T.obj (label i) := T.chosenDecompositionIso X
  calc
    W.weight X = W.weight (⨁ fun i ↦ T.obj (label i)) :=
      W.iso_invariant ⟨e⟩
    _ = ∑ i, W.weight (T.obj (label i)) := W.weight_biproduct _
    _ = ∑ i, (Module.finrank k (T.obj P ⟶ T.obj (label i)) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [W, homFromWeight, homDimensionMatrix]
    _ = (Module.finrank k (T.obj P ⟶ X) : ℤ) := by
      exact_mod_cast
        (MBDVendor.Magnitude.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
          k (T.obj P) X (fun i ↦ T.obj (label i)) e).symm

omit [DecidableEq Ind] in
/-- The additive extension of a represented Hom column evaluates every
object by the dimension of its Hom space to the representing object. -/
theorem additiveObjectWeight_homToWeight (I : Ind) (X : C) :
    (T.additiveObjectWeightOfLabelWeight
      (homToWeight (k := k) T I)).weight X =
        Module.finrank k (X ⟶ T.obj I) := by
  let W := T.additiveObjectWeightOfLabelWeight
    (homToWeight (k := k) T I)
  let n := T.chosenDecompositionSize X
  let label : Fin n → Ind := T.chosenDecompositionLabel X
  let e : X ≅ ⨁ fun i ↦ T.obj (label i) := T.chosenDecompositionIso X
  calc
    W.weight X = W.weight (⨁ fun i ↦ T.obj (label i)) :=
      W.iso_invariant ⟨e⟩
    _ = ∑ i, W.weight (T.obj (label i)) := W.weight_biproduct _
    _ = ∑ i, (Module.finrank k (T.obj (label i) ⟶ T.obj I) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [W, homToWeight, homDimensionMatrix]
    _ = (Module.finrank k (X ⟶ T.obj I) : ℤ) := by
      exact_mod_cast
        (MBDVendor.Magnitude.CategoryTheory.finrank_hom_eq_sum_of_biproduct_iso
          k X (T.obj I) (fun i ↦ T.obj (label i)) e).symm

omit [DecidableEq Ind] in
/-- A strictly positive label weight has zero additive extension exactly on
zero objects. -/
theorem additiveObjectWeight_eq_zero_iff_isZero
    (weight : Ind → ℤ) (hpos : ∀ i, 0 < weight i) (X : C) :
    (T.additiveObjectWeightOfLabelWeight weight).weight X = 0 ↔
      IsZero X := by
  let W := T.additiveObjectWeightOfLabelWeight weight
  constructor
  · intro hweight
    let n := T.chosenDecompositionSize X
    let label : Fin n → Ind := T.chosenDecompositionLabel X
    let e : X ≅ ⨁ fun i ↦ T.obj (label i) := T.chosenDecompositionIso X
    by_cases hn : n = 0
    · have hzero : IsZero (⨁ fun i : Fin n ↦ T.obj (label i)) := by
        rw [IsZero.iff_id_eq_zero]
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 (hn ▸ i)
      exact hzero.of_iso e
    · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
        ⟨i, Finset.mem_univ i⟩
      have hsumPos : 0 < ∑ j : Fin n, weight (label j) :=
        Finset.sum_pos (fun j _ ↦ hpos (label j)) huniv
      have hsum : W.weight X = ∑ j : Fin n, weight (label j) := by
        calc
          W.weight X = W.weight (⨁ fun j ↦ T.obj (label j)) :=
            W.iso_invariant ⟨e⟩
          _ = ∑ j, W.weight (T.obj (label j)) := W.weight_biproduct _
          _ = ∑ j, weight (label j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [W]
      rw [hweight] at hsum
      omega
  · exact fun hX ↦
      (T.additiveObjectWeightOfLabelWeight weight).weight_eq_zero_of_isZero hX

/-- The Euler defect of a label weight on the chosen left mesh. -/
def leftMeshLabelWeightDefect
    (weight : Ind → ℤ) (source : Ind) : ℤ :=
  let W := T.additiveObjectWeightOfLabelWeight weight
  W.weight (T.leftMesh (T.obj source)).X₁ -
    W.weight (T.leftMesh (T.obj source)).X₂ +
      W.weight (T.leftMesh (T.obj source)).X₃

/-- Weighted row sum of the paper-oriented mesh matrix. -/
def meshRowWeight [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (source : Ind) : ℤ :=
  ∑ target, meshMatrix T source target * weight target

/-- The row of Hom dimensions represented by `P` satisfies the manuscript's
unit-column equation `Phi^T d = e_P`. -/
theorem meshColumnWeight_homFromWeight
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T) (P target : Ind) :
    meshColumnWeight T (homFromWeight (k := k) T P) target =
      if target = P then 1 else 0 := by
  have h := congrArg (fun M : Matrix Ind Ind ℤ ↦ M P target)
    (homDimensionMatrix_mul_meshMatrix T D)
  simpa [meshColumnWeight, homFromWeight, Matrix.mul_apply, Matrix.one_apply,
    eq_comm] using h

/-- The column of Hom dimensions represented by `I` satisfies the manuscript's
unit-row equation `Phi d = e_I`. -/
theorem meshRowWeight_homToWeight
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T) (I source : Ind) :
    meshRowWeight T (homToWeight (k := k) T I) source =
      if source = I then 1 else 0 := by
  have h := congrArg (fun M : Matrix Ind Ind ℤ ↦ M source I)
    (meshMatrix_mul_homDimensionMatrix T D)
  simpa [meshRowWeight, homToWeight, Matrix.mul_apply, Matrix.one_apply,
    eq_comm] using h

/-- The categorical left-mesh defect of a represented Hom column is the
Kronecker delta at its representing label.  This is the literal opposite
unit equation used at Iyama's injective boundary. -/
theorem leftMeshLabelWeightDefect_homToWeight
    (D : HomMeshInverseData (k := k) T)
    (leftEpi : ∀ A : Ind, Epi (T.leftMesh (T.obj A)).g)
    (I A : Ind) :
    leftMeshLabelWeightDefect T (homToWeight (k := k) T I) A =
      if A = I then 1 else 0 := by
  let S := T.leftMesh (T.obj A)
  let W := T.additiveObjectWeightOfLabelWeight
    (homToWeight (k := k) T I)
  letI : Epi S.g := leftEpi A
  have hmiddle :=
    MBDVendor.Magnitude.CategoryTheory.leftTauSequence_finrank
      k S (T.leftTau (T.obj A)) (T.obj I)
  have hsource :
      Module.finrank k (S.X₁ ⟶ T.obj I) =
        Module.finrank k (T.obj A ⟶ T.obj I) :=
    (CategoryTheory.Linear.homCongr k
      (T.leftTermIso (T.obj A)) (Iso.refl (T.obj I))).finrank_eq
  have hradical :
      Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k S.X₁ (T.obj I)) =
        Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj A) (T.obj I)) :=
    (MBDVendor.Magnitude.CategoryTheory.radicalSourceLinearEquiv
      k (T.obj I) (T.leftTermIso (T.obj A))).finrank_eq
  have hresidue := D.radicalFinrank_add_delta A I
  have hmiddleZ :
      (Module.finrank k (S.X₂ ⟶ T.obj I) : ℤ) =
        Module.finrank k (S.X₃ ⟶ T.obj I) +
          Module.finrank k
            (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
              k S.X₁ (T.obj I)) := by
    exact_mod_cast hmiddle
  have hsourceZ :
      (Module.finrank k (S.X₁ ⟶ T.obj I) : ℤ) =
        Module.finrank k (T.obj A ⟶ T.obj I) := by
    exact_mod_cast hsource
  have hradicalZ :
      (Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k S.X₁ (T.obj I)) : ℤ) =
        Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj A) (T.obj I)) := by
    exact_mod_cast hradical
  have hresidueZ :
      (Module.finrank k
          (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj A) (T.obj I)) : ℤ) +
          (if A = I then 1 else 0) =
        Module.finrank k (T.obj A ⟶ T.obj I) := by
    exact_mod_cast hresidue
  rw [leftMeshLabelWeightDefect]
  change W.weight S.X₁ - W.weight S.X₂ + W.weight S.X₃ = _
  rw [additiveObjectWeight_homToWeight T I S.X₁,
    additiveObjectWeight_homToWeight T I S.X₂,
    additiveObjectWeight_homToWeight T I S.X₃]
  omega

/-- A single weight identified with both the source Hom row and the sink Hom
column satisfies the two unit equations in Proposition `factor-structure` of
the frozen manuscript. -/
theorem meshUnitEquations_of_homDimensionIdentities
    [DecidablePred T.IsProjective]
    (D : HomMeshInverseData (k := k) T)
    (P I : Ind) (weight : Ind → ℤ)
    (weight_eq_from : ∀ X, weight X = homFromWeight (k := k) T P X)
    (weight_eq_to : ∀ X, weight X = homToWeight (k := k) T I X) :
    (∀ target,
      meshColumnWeight T weight target = if target = P then 1 else 0) ∧
      ∀ source,
        meshRowWeight T weight source = if source = I then 1 else 0 := by
  have hFrom : weight = homFromWeight (k := k) T P := funext weight_eq_from
  have hTo : weight = homToWeight (k := k) T I := funext weight_eq_to
  constructor
  · intro target
    rw [hFrom]
    exact meshColumnWeight_homFromWeight T D P target
  · intro source
    rw [hTo]
    exact meshRowWeight_homToWeight T D I source

omit [DecidableEq Ind] in
/-- Nonzero maps from `P` to every chosen indecomposable make its Hom row a
strictly positive integral weight. -/
theorem homFromWeight_pos
    (P : Ind)
    (reachable : ∀ X : Ind, ∃ f : T.obj P ⟶ T.obj X, f ≠ 0) :
    ∀ X : Ind, 0 < homFromWeight (k := k) T P X := by
  intro X
  simp only [homFromWeight, homDimensionMatrix]
  exact_mod_cast
    (Module.finrank_pos_iff_exists_ne_zero.mpr (reachable X))

omit [DecidableEq Ind] in
/-- Nonzero maps from every chosen indecomposable to `I` make its Hom column a
strictly positive integral weight. -/
theorem homToWeight_pos
    (I : Ind)
    (coreachable : ∀ X : Ind, ∃ f : T.obj X ⟶ T.obj I, f ≠ 0) :
    ∀ X : Ind, 0 < homToWeight (k := k) T I X := by
  intro X
  simp only [homToWeight, homDimensionMatrix]
  exact_mod_cast
    (Module.finrank_pos_iff_exists_ne_zero.mpr (coreachable X))

end MBDVendor.Magnitude.FiniteTauMatrix
