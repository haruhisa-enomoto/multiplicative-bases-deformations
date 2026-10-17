import MBDVendor.Magnitude.CategoryTheory.AlgebraicallyClosedResidue
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtWeight
import MBDVendor.QSE.CategoryTheory.IyamaNakayamaExtraction

/-!
# Positive right-additive weights imply strictness

This is the finite tau-category form of Iyama's strictness argument.  A
positive label weight whose Euler defect is nonnegative at the projective
boundary and zero elsewhere forces every first right-mesh map to be monic.

The proof uses the source-faithful generic Nakayama-ladder extraction vendored
from the clean equidistribution formalization.  It contains no module
classification or OP-conjecture theorem layer.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE.Iyama

universe s v u w

variable {k : Type s} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

/-- The Euler defect of the chosen right mesh at one label, evaluated by the
canonical additive extension of a label weight. -/
def rightMeshLabelWeightDefect
    (T : FiniteTauCategoryData C Ind) (weight : Ind → ℤ) (x : Ind) : ℤ :=
  (T.additiveObjectWeightOfLabelWeight weight).weight
        (T.rightMesh (T.obj x)).X₁ -
    (T.additiveObjectWeightOfLabelWeight weight).weight
        (T.rightMesh (T.obj x)).X₂ +
    (T.additiveObjectWeightOfLabelWeight weight).weight
        (T.rightMesh (T.obj x)).X₃

/-- Iyama's positive right-additivity condition, expressed on the chosen
indecomposable labels. -/
def IsPositiveRightAdditiveLabelWeight
    (T : FiniteTauCategoryData C Ind) (weight : Ind → ℤ) : Prop :=
  (∀ x : Ind, 0 < weight x) ∧
    ∀ x : Ind,
      0 ≤ rightMeshLabelWeightDefect T weight x ∧
        (¬ T.IsProjective x →
          rightMeshLabelWeightDefect T weight x = 0)

omit [DecidableEq Ind] in
/-- A positive right-additive label weight makes every first map of the
chosen right tau-sequences monic. -/
theorem rightMesh_mono_of_positiveRightAdditiveLabelWeight
    (T : FiniteTauCategoryData C Ind) (weight : Ind → ℤ)
    (hweight : IsPositiveRightAdditiveLabelWeight T weight) :
    ∀ x : Ind, Mono (T.rightMesh (T.obj x)).f := by
  let W : AdditiveObjectWeight C :=
    T.additiveObjectWeightOfLabelWeight weight
  have hEuler : W.IsRightMeshEulerOffProjectives T := by
    apply W.isRightMeshEulerOffProjectives_of_obj
    intro x hx
    exact (hweight.2 x).2 hx
  intro x
  by_cases hx : T.IsProjective x
  · exact hx.mono (T.nuPlus x)
  · by_contra hmono
    let X : T.Nonprojective := ⟨x, hx⟩
    obtain ⟨y, hy, hpair⟩ :=
      T.exists_nakayamaPair_of_not_mono_nuPlus
        T.NakayamaPair T.hasMuMinusNakayamaExtraction X
        (T.not_isZero_thetaPlus X) hmono
    let Y : T.Nonprojective := ⟨y, hy⟩
    have hxEuler : W.IsRightMeshEulerAt T (T.obj x) :=
      hEuler (T.obj x)
        ⟨1, fun _ ↦ x,
          ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ T.obj x)).symm⟩,
          fun _ ↦ hx⟩
    have hyEuler : W.IsRightMeshEulerAt T (T.obj y) :=
      hEuler (T.obj y)
        ⟨1, fun _ ↦ y,
          ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ T.obj y)).symm⟩,
          fun _ ↦ hy⟩
    have hxRight :
        W.weight (T.rightMesh (T.obj x)).X₃ = weight x := by
      calc
        W.weight (T.rightMesh (T.obj x)).X₃ = W.weight (T.obj x) :=
          W.iso_invariant ⟨T.rightTermIso (T.obj x)⟩
        _ = weight x := T.additiveObjectWeightOfLabelWeight_obj weight x
    have hyLeft :
        W.weight (T.rightMesh (T.obj y)).X₁ =
          weight (T.tauPlus Y) := by
      calc
        W.weight (T.rightMesh (T.obj y)).X₁ =
            W.weight (T.obj (T.tauPlus Y)) :=
          W.iso_invariant ⟨T.tauPlusIso Y⟩
        _ = weight (T.tauPlus Y) :=
          T.additiveObjectWeightOfLabelWeight_obj weight (T.tauPlus Y)
    have hNu : W.morphismWeight (T.nuPlus x) = -weight x := by
      dsimp only [AdditiveObjectWeight.IsRightMeshEulerAt] at hxEuler
      dsimp only [AdditiveObjectWeight.morphismWeight]
      rw [hxRight] at hxEuler
      omega
    have hMu :
        W.morphismWeight (T.muPlus y) = weight (T.tauPlus Y) := by
      dsimp only [AdditiveObjectWeight.IsRightMeshEulerAt] at hyEuler
      dsimp only [AdditiveObjectWeight.morphismWeight]
      rw [hyLeft] at hyEuler
      omega
    have hFirst :
        W.morphismWeight (T.nuPlus x) =
          W.morphismWeight (T.muMinus (T.tauPlus X)) :=
      W.morphismWeight_eq_of_arrowIso (T.firstMapIso X)
    have hLadder :
        W.morphismWeight (T.muMinus (T.tauPlus X)) =
          W.morphismWeight (T.muPlus y) :=
      W.morphismWeight_muMinus_eq_muPlus_of_nakayamaPair_offProjectives
        hEuler NakayamaLadder.hasNonprojectiveRightSupport hpair
    have hEq : -weight x = weight (T.tauPlus Y) := by
      rw [← hNu, hFirst, hLadder, hMu]
    exact (by linarith [hweight.1 x, hweight.1 (T.tauPlus Y)] : False)

/-- Over an algebraically closed field, a positive right-additive label
weight supplies every hypothesis of the Hom--mesh inverse recurrence. -/
theorem HomMeshInverseData.ofPositiveRightAdditiveLabelWeight
    (T : FiniteTauCategoryData C Ind) (weight : Ind → ℤ)
    (hweight : IsPositiveRightAdditiveLabelWeight T weight) :
    HomMeshInverseData (k := k) T :=
  HomMeshInverseData.ofIsAlgClosed T
    (rightMesh_mono_of_positiveRightAdditiveLabelWeight T weight hweight)

end MBDVendor.Magnitude.FiniteTauMatrix
