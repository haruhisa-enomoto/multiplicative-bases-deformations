import MBDVendor.Magnitude.CategoryTheory.PositiveWeightStrictness

/-!
# Mesh-matrix evaluation of additive label weights

The categorical Euler defect of a label weight on a chosen right mesh is the
corresponding weighted column sum of the mesh matrix.  This identifies the
matrix unit equations in the frozen manuscript with Iyama's positive
right-additivity hypothesis.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE.Iyama

universe s v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- Regrouping an integral weight over middle-term occurrences by label. -/
theorem sum_arrowMultiplicity_mul_int (target : Ind) (weight : Ind → ℤ) :
    ∑ source, (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source =
      ∑ i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData target),
        weight (rightMiddleLabel T.toFiniteRightTauCategoryData target i) := by
  classical
  simp only [arrowMultiplicity, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- The additive extension of a label weight evaluates the chosen right
middle term by the arrow-occurrence sum. -/
theorem additiveLabelWeight_rightMiddle (weight : Ind → ℤ) (target : Ind) :
    (T.additiveObjectWeightOfLabelWeight weight).weight
        (T.rightMesh (T.obj target)).X₂ =
      ∑ source, (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source := by
  let W := T.additiveObjectWeightOfLabelWeight weight
  obtain ⟨e⟩ := rightMiddleIso T.toFiniteRightTauCategoryData target
  calc
    W.weight (T.rightMesh (T.obj target)).X₂ =
        W.weight (⨁ fun i ↦ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData target i)) :=
      W.iso_invariant ⟨e⟩
    _ = ∑ i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData target),
        W.weight (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData target i)) :=
      W.weight_biproduct _
    _ = ∑ i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData target),
        weight (rightMiddleLabel T.toFiniteRightTauCategoryData target i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact T.additiveObjectWeightOfLabelWeight_obj weight _
    _ = ∑ source,
        (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source :=
      (sum_arrowMultiplicity_mul_int T target weight).symm

/-- Weighted column sum of the paper-oriented mesh matrix. -/
def meshColumnWeight [DecidablePred T.IsProjective]
    (weight : Ind → ℤ) (target : Ind) : ℤ :=
  ∑ source, weight source * meshMatrix T source target

/-- The categorical right-mesh Euler defect equals the weighted mesh-matrix
column sum. -/
theorem rightMeshLabelWeightDefect_eq_meshColumnWeight
    [DecidablePred T.IsProjective] (weight : Ind → ℤ) (target : Ind) :
    rightMeshLabelWeightDefect T weight target =
      meshColumnWeight T weight target := by
  classical
  let W := T.additiveObjectWeightOfLabelWeight weight
  have hRight : W.weight (T.rightMesh (T.obj target)).X₃ = weight target := by
    calc
      W.weight (T.rightMesh (T.obj target)).X₃ = W.weight (T.obj target) :=
        W.iso_invariant ⟨T.rightTermIso (T.obj target)⟩
      _ = weight target := T.additiveObjectWeightOfLabelWeight_obj weight target
  have hMiddle : W.weight (T.rightMesh (T.obj target)).X₂ =
      ∑ source, weight source * (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) := by
    calc
      _ = ∑ source, (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) * weight source :=
        additiveLabelWeight_rightMiddle T weight target
      _ = ∑ source, weight source * (arrowMultiplicity T.toFiniteRightTauCategoryData source target : ℤ) := by
        apply Finset.sum_congr rfl
        intro source hsource
        exact mul_comm _ _
  have indicatorSum (x : Ind) :
      ∑ source, weight source * (if source = x then (1 : ℤ) else 0) =
        weight x := by
    simp
  by_cases hTarget : T.IsProjective target
  · have hLeft : W.weight (T.rightMesh (T.obj target)).X₁ = 0 :=
      W.weight_eq_zero_of_isZero hTarget
    rw [rightMeshLabelWeightDefect, hLeft, hMiddle, hRight, zero_sub]
    simp only [meshColumnWeight, meshMatrix_apply_of_projective T hTarget,
      mul_sub, Finset.sum_sub_distrib]
    rw [indicatorSum]
    abel
  · have hLeft : W.weight (T.rightMesh (T.obj target)).X₁ =
        weight (tau T ⟨target, hTarget⟩) := by
      calc
        W.weight (T.rightMesh (T.obj target)).X₁ =
            W.weight (T.obj (tau T ⟨target, hTarget⟩)) :=
          W.iso_invariant ⟨T.tauPlusIso ⟨target, hTarget⟩⟩
        _ = weight (tau T ⟨target, hTarget⟩) :=
          T.additiveObjectWeightOfLabelWeight_obj weight _
    rw [rightMeshLabelWeightDefect, hLeft, hMiddle, hRight]
    simp only [meshColumnWeight, meshMatrix_apply_of_nonprojective T hTarget,
      mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [indicatorSum, indicatorSum]
    abel

/-- Matrix-column nonnegativity and off-projective vanishing are exactly the
Euler clauses of a positive right-additive label weight. -/
theorem isPositiveRightAdditiveLabelWeight_of_meshColumnWeight
    [DecidablePred T.IsProjective] (weight : Ind → ℤ)
    (weight_pos : ∀ x, 0 < weight x)
    (column_nonnegative : ∀ x, 0 ≤ meshColumnWeight T weight x)
    (column_eq_zero_of_nonprojective :
      ∀ x, ¬ T.IsProjective x → meshColumnWeight T weight x = 0) :
    IsPositiveRightAdditiveLabelWeight T weight := by
  refine ⟨weight_pos, fun x ↦ ⟨?_, ?_⟩⟩
  · rw [rightMeshLabelWeightDefect_eq_meshColumnWeight]
    exact column_nonnegative x
  · intro hx
    rw [rightMeshLabelWeightDefect_eq_meshColumnWeight]
    exact column_eq_zero_of_nonprojective x hx

/-- A positive integral solution of the manuscript's unit-column equation is
automatically a positive right-additive label weight. -/
theorem isPositiveRightAdditiveLabelWeight_of_meshColumnUnit
    [DecidablePred T.IsProjective] (P : Ind) (hP : T.IsProjective P)
    (weight : Ind → ℤ) (weight_pos : ∀ x, 0 < weight x)
    (unitEquation : ∀ x,
      meshColumnWeight T weight x = if x = P then 1 else 0) :
    IsPositiveRightAdditiveLabelWeight T weight := by
  apply isPositiveRightAdditiveLabelWeight_of_meshColumnWeight T weight weight_pos
  · intro x
    rw [unitEquation]
    split <;> omega
  · intro x hx
    rw [unitEquation]
    have hne : x ≠ P := by
      intro h
      subst x
      exact hx hP
    simp [hne]

/-- Over an algebraically closed field, a positive solution of the unit-column
equation supplies the full Hom--mesh inverse package. -/
theorem HomMeshInverseData.ofMeshColumnUnit
    {k : Type s} [Field k] [IsAlgClosed k] [Linear k C]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    [DecidablePred T.IsProjective]
    (P : Ind) (hP : T.IsProjective P)
    (weight : Ind → ℤ) (weight_pos : ∀ x, 0 < weight x)
    (unitEquation : ∀ x,
      meshColumnWeight T weight x = if x = P then 1 else 0) :
    HomMeshInverseData (k := k) T :=
  HomMeshInverseData.ofPositiveRightAdditiveLabelWeight T weight
    (isPositiveRightAdditiveLabelWeight_of_meshColumnUnit
      T P hP weight weight_pos unitEquation)

end MBDVendor.Magnitude.FiniteTauMatrix
