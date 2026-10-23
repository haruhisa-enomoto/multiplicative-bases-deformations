module

public import MBDVendor.Magnitude.Algebra.RightModuleProjectiveBoundary
public import MBDVendor.Magnitude.Algebra.RightModuleTauData

/-!
# Right tau-sequences for the literal right-module category

At a nonprojective indecomposable, the chosen minimal right almost-split map
and its kernel form the usual Auslander--Reiten complex.  At a projective
indecomposable, the boundary complex is `0 ⟶ rad P ⟶ P`.  Finite
componentwise biproducts extend these label meshes to every finitely
generated right module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama
open scoped ModuleCat.Algebra ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The kernel--middle--endpoint complex at a nonprojective chosen
indecomposable. -/
def nonprojectiveRightMesh
    (x : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
  let B := S.minimalRightAlmostSplitAt x.1
  ShortComplex.mk (kernel.ι B.map) B.map (kernel.condition B.map)

/-- The nonprojective Auslander--Reiten complex is a right tau-sequence. -/
theorem nonprojectiveRightTau
    (x : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    RightTauSequence (S.nonprojectiveRightMesh x) := by
  let sigma := S.almostSplitSkeleton
  let B := S.minimalRightAlmostSplitAt x.1
  change RightTauSequence
    (ShortComplex.mk (kernel.ι B.map) B.map (kernel.condition B.map))
  have hkernel := B.kernel_ar_sequence sigma x.2
  have hfLeft : IsLeftAlmostSplit (kernel.ι B.map) := hkernel.1
  obtain ⟨y, ⟨e⟩⟩ := sigma.complete (kernel B.map) hkernel.2.2.1
  have htransportNot : ¬ IsSplitMono (e.inv ≫ kernel.ι B.map) := by
    intro hsplit
    letI : IsSplitMono (e.inv ≫ kernel.ι B.map) := hsplit
    apply hfLeft.not_isSplitMono
    rw [← e.hom_inv_id_assoc (kernel.ι B.map)]
    infer_instance
  have htransportRad : IsRadicalMorphism
      (e.inv ≫ kernel.ι B.map) :=
    (sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj
      (e.inv ≫ kernel.ι B.map)).2 htransportNot
  have hfRad : IsRadicalMorphism (kernel.ι B.map) := by
    simpa only [e.hom_inv_id_assoc] using
      isRadicalMorphism_precomp e.hom htransportRad
  have hgRad : IsRadicalMorphism B.map :=
    (sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj B.map).2
      B.rightAlmostSplit.not_isSplitEpi
  refine
    { f_radical := hfRad
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakKernel := ?_ }
  · intro W a ha
    have haTransport : IsRadicalMorphism (e.inv ≫ a) :=
      isRadicalMorphism_precomp e.inv ha
    have haTransportNot : ¬ IsSplitMono (e.inv ≫ a) :=
      (sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj
        (e.inv ≫ a)).1 haTransport
    have haNot : ¬ IsSplitMono a := by
      intro hsplit
      letI : IsSplitMono a := hsplit
      apply haTransportNot
      infer_instance
    exact hfLeft.factors a haNot
  · intro W a ha
    exact B.rightAlmostSplit.factors a
      ((sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj a).1 ha)
  · constructor
    · rw [ShortComplex.isWeakKernel_iff]
      intro W q hq
      exact ⟨kernel.lift B.map q hq, kernel.lift_ι B.map q hq⟩
    · intro e he
      have heq : e = 𝟙 _ := by
        apply (cancel_mono (kernel.ι B.map)).1
        simpa only [Category.id_comp] using he
      rw [heq]
      infer_instance

/-- The projective boundary complex `0 ⟶ rad P ⟶ P`. -/
def projectiveRightMesh
    (p : Fin S.n) (_hp : Projective (S.fgObj p)) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
  ShortComplex.mk
    (0 : (0 : RightModule.FinitelyGeneratedCategory A) ⟶
      S.projectiveBoundaryRadical p)
    (S.projectiveBoundaryRadicalInclusion p) (by simp)

/-- The projective boundary complex is a right tau-sequence. -/
theorem projectiveRightTau
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    RightTauSequence (S.projectiveRightMesh p hp) := by
  let sigma := S.almostSplitSkeleton
  let g := S.projectiveBoundaryRadicalInclusion p
  have hgmono : Mono g := by
    dsimp only [g, projectiveBoundaryRadicalInclusion]
    exact (IndecomposableSkeleton.fg_mono_iff_injective _).2
      (Module.jacobson Aᵐᵒᵖ (S.fgObj p)).subtype_injective
  letI : Mono g := hgmono
  have hgAlmost : IsRightAlmostSplit g :=
    S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp
  have hgRad : IsRadicalMorphism g :=
    (sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj g).2
      hgAlmost.not_isSplitEpi
  refine
    { f_radical := isRadicalMorphism_zero
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakKernel := ?_ }
  · intro W a _ha
    refine ⟨0, ?_⟩
    have ha : a = 0 :=
      (isZero_zero (RightModule.FinitelyGeneratedCategory A)).eq_of_src a 0
    change (0 : (0 : RightModule.FinitelyGeneratedCategory A) ⟶
      S.projectiveBoundaryRadical p) ≫ 0 = a
    rw [zero_comp]
    exact ha.symm
  · intro W a ha
    exact hgAlmost.factors a
      ((sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj a).1 ha)
  · constructor
    · rw [ShortComplex.isWeakKernel_iff]
      intro W q hq
      change q ≫ g = 0 at hq
      have hqzero : q = 0 := by
        apply (cancel_mono g).1
        change q ≫ g =
          (0 : W ⟶ S.projectiveBoundaryRadical p) ≫ g
        rw [zero_comp]
        exact hq
      refine ⟨0, ?_⟩
      rw [hqzero]
      simp
    · intro e _he
      have heq : e = 𝟙 _ :=
        (isZero_zero (RightModule.FinitelyGeneratedCategory A)).eq_of_src
          e (𝟙 _)
      rw [heq]
      infer_instance

/-- The unified right mesh at a chosen indecomposable label. -/
def labelRightMesh (x : Fin S.n) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) := by
  classical
  by_cases hx : Projective (S.fgObj x)
  · exact S.projectiveRightMesh x hx
  · exact S.nonprojectiveRightMesh ⟨x, hx⟩

/-- Every chosen-label right mesh is a right tau-sequence. -/
theorem labelRightTau (x : Fin S.n) :
    RightTauSequence (S.labelRightMesh x) := by
  classical
  by_cases hx : Projective (S.fgObj x)
  · simpa [labelRightMesh, hx] using S.projectiveRightTau x hx
  · simpa [labelRightMesh, hx] using
      S.nonprojectiveRightTau ⟨x, hx⟩

/-- The right endpoint of the unified label mesh is literally the selected
indecomposable. -/
theorem labelRightMesh_X₃ (x : Fin S.n) :
    (S.labelRightMesh x).X₃ = S.fgObj x := by
  classical
  by_cases hx : Projective (S.fgObj x) <;>
    simp [labelRightMesh, hx, projectiveRightMesh,
      nonprojectiveRightMesh, almostSplitSkeleton]

/-- A chosen decomposition of an arbitrary FG module into the fixed
indecomposable labels. -/
structure ChosenLabelDecomposition
    (X : RightModule.FinitelyGeneratedCategory A) where
  n : ℕ
  label : Fin n → Fin S.n
  iso : X ≅ ⨁ fun i ↦ S.fgObj (label i)

/-- Choose one finite label decomposition for every FG module. -/
def chosenLabelDecomposition
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.ChosenLabelDecomposition X := by
  let h := S.fgObj_decomposition (k := k) X
  let n := h.choose
  let label := h.choose_spec.choose
  let e := Classical.choice h.choose_spec.choose_spec
  exact { n := n, label := label, iso := e }

/-- Extend the labelwise right AR complexes to every module by finite
componentwise biproduct. -/
def moduleRightMesh (X : RightModule.FinitelyGeneratedCategory A) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
  let d := S.chosenLabelDecomposition X
  shortComplexBiproduct (fun i : Fin d.n ↦ S.labelRightMesh (d.label i))

/-- The chosen right mesh has the supplied module as its right endpoint. -/
def moduleRightTermIso (X : RightModule.FinitelyGeneratedCategory A) :
    (S.moduleRightMesh X).X₃ ≅ X :=
  let d := S.chosenLabelDecomposition X
  (biproduct.mapIso fun i : Fin d.n ↦
      eqToIso (S.labelRightMesh_X₃ (d.label i))).trans d.iso.symm

/-- Every modulewise right mesh is a right tau-sequence. -/
theorem moduleRightTau (X : RightModule.FinitelyGeneratedCategory A) :
    RightTauSequence (S.moduleRightMesh X) := by
  let d := S.chosenLabelDecomposition X
  exact rightTauSequence_shortComplexBiproduct S.fgNilpotentRadicalData
    (fun i : Fin d.n ↦ S.labelRightMesh (d.label i))
    (fun i ↦ S.labelRightTau (d.label i))

/-- Finite representation type constructs all right-mesh input required by
the generic finite right tau-category interface. -/
def rightTauInput : RightModule.RightTauInput S where
  rightMesh := S.moduleRightMesh
  rightTermIso := S.moduleRightTermIso
  rightTau := S.moduleRightTau

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
