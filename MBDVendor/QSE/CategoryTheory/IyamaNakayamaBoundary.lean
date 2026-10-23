module

public import MBDVendor.QSE.CategoryTheory.IyamaNakayamaPair
public import MBDVendor.QSE.CategoryTheory.IyamaLadderRadical
public import MBDVendor.QSE.CategoryTheory.SplitMorphismComplement

/-!
# Projective-free ladder support and the Nakayama boundary

This file proves the projective-free right support of every finite invertible
ladder directly from its left-mesh identifications.  It also identifies the
vertical arrow immediately before a zero-target terminal rung with a genuine
`muPlus` boundary map.  These are the abstract support and truncation inputs
in Iyama's Nakayama-pair extraction; no concrete algebra or classification is
used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

open CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteTauCategoryData

variable (T : FiniteTauCategoryData C Ind)

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The zero endomorphism can be invertible only on a zero object. -/
private theorem isZero_of_isIso_zero (X : C) [IsIso (0 : X ⟶ X)] :
    IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_epi (0 : X ⟶ X)]
  simp

/-- A chosen right mesh ending at a zero object is componentwise zero. -/
theorem rightMesh_components_isZero_of_isZero (Y : C) (hY : IsZero Y) :
    IsZero (T.rightMesh Y).X₁ ∧
      IsZero (T.rightMesh Y).X₂ ∧
        IsZero (T.rightMesh Y).X₃ := by
  have h₃ : IsZero (T.rightMesh Y).X₃ :=
    hY.of_iso (T.rightTermIso Y)
  have hg : (T.rightMesh Y).g = 0 := h₃.eq_of_tgt _ _
  haveI hzero₂ : IsIso (0 : (T.rightMesh Y).X₂ ⟶ (T.rightMesh Y).X₂) :=
    (T.rightTau Y).isRightMinimal_g 0 (by rw [zero_comp, hg])
  have h₂ : IsZero (T.rightMesh Y).X₂ :=
    isZero_of_isIso_zero (T.rightMesh Y).X₂
  have hf : (T.rightMesh Y).f = 0 := h₂.eq_of_tgt _ _
  haveI hzero₁ : IsIso (0 : (T.rightMesh Y).X₁ ⟶ (T.rightMesh Y).X₁) :=
    (T.rightTau Y).minimalWeakKernel.2 0 (by rw [zero_comp, hf])
  exact ⟨isZero_of_isIso_zero (T.rightMesh Y).X₁, h₂, h₃⟩

/-- A chosen left mesh starting at a zero object is componentwise zero. -/
theorem leftMesh_components_isZero_of_isZero (X : C) (hX : IsZero X) :
    IsZero (T.leftMesh X).X₁ ∧
      IsZero (T.leftMesh X).X₂ ∧
        IsZero (T.leftMesh X).X₃ := by
  have h₁ : IsZero (T.leftMesh X).X₁ :=
    hX.of_iso (T.leftTermIso X)
  have hf : (T.leftMesh X).f = 0 := h₁.eq_of_src _ _
  haveI hzero₂ : IsIso (0 : (T.leftMesh X).X₂ ⟶ (T.leftMesh X).X₂) :=
    (T.leftTau X).isLeftMinimal_f 0 (by rw [comp_zero, hf])
  have h₂ : IsZero (T.leftMesh X).X₂ :=
    isZero_of_isIso_zero (T.leftMesh X).X₂
  have hg : (T.leftMesh X).g = 0 := h₂.eq_of_src _ _
  haveI hzero₃ : IsIso (0 : (T.leftMesh X).X₃ ⟶ (T.leftMesh X).X₃) :=
    (T.leftTau X).minimalWeakCokernel.2 0 (by rw [comp_zero, hg])
  exact ⟨h₁, h₂, isZero_of_isIso_zero (T.leftMesh X).X₃⟩

/-- Compatibility identifies the second map of a noninjective left mesh
with the terminal map of the right mesh at its negative translate. -/
def secondMapIso (A : T.Noninjective) :
    Arrow.mk (T.nuMinus A.1) ≅
      Arrow.mk (T.muPlus (T.tauMinus A)) :=
  ShortComplex.gFunctor.mapIso (T.leftRightMeshIso A)

/-- A split monomorphism between two chosen indecomposables is an
isomorphism. -/
theorem isIso_of_isSplitMono_obj_obj
    {p q : Ind} (f : T.obj p ⟶ T.obj q) [IsSplitMono f] :
    IsIso f := by
  let d := splitMonoComplement f
  let e : T.obj q ≅ T.obj p ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hcomp : IsZero d.complement :=
    ((T.obj_indec q).2 (T.obj p) d.complement e).resolve_left
      (T.obj_indec p).1
  apply IsIso.mk
  refine ⟨retraction f, IsSplitMono.id f, ?_⟩
  rw [← d.total]
  have hp : d.projection = 0 := hcomp.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hcomp.eq_of_src _ _
  rw [hp, hi, zero_comp, add_zero]

/-- A split embedding of a chosen indecomposable into a finite biproduct has
a split-monic coordinate.  This is the local-ring form of finite
Krull--Schmidt support detection, and does not require the target factors to
be indecomposable. -/
theorem exists_isSplitMono_component_finBiproduct
    (p : Ind) (n : ℕ) (F : Fin n → C)
    (j : T.obj p ⟶ ⨁ F) [IsSplitMono j] :
    ∃ i : Fin n, IsSplitMono (j ≫ biproduct.π F i) := by
  classical
  by_contra hcomponentSplit
  push Not at hcomponentSplit
  have hcomponent (i : Fin n) :
      j ≫ biproduct.π F i ∈
        T.radical.ideal.hom (T.obj p) (F i) :=
    (T.radical.mem_ideal_iff _).2
      ((FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
        T.toFiniteRightTauCategoryData _).2
        (hcomponentSplit i))
  have hjmem :
      j ∈ T.radical.ideal.hom (T.obj p) (⨁ F) := by
    rw [show j = ∑ i : Fin n,
        (j ≫ biproduct.π F i) ≫ biproduct.ι F i by
      calc
        j = j ≫ 𝟙 _ := by simp
        _ = j ≫ ∑ i : Fin n,
              biproduct.π F i ≫ biproduct.ι F i := by
          rw [biproduct.total]
        _ = ∑ i : Fin n,
              (j ≫ biproduct.π F i) ≫ biproduct.ι F i := by
          rw [Preadditive.comp_sum]
          congr 1
          funext i
          rw [Category.assoc]]
    apply (T.radical.ideal.hom _ _).sum_mem (t := Finset.univ)
    intro i _
    exact T.radical.ideal.postcomp (biproduct.ι F i) (hcomponent i)
  exact ((FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
    T.toFiniteRightTauCategoryData j).1
      ((T.radical.mem_ideal_iff j).1 hjmem))
    (inferInstance : IsSplitMono j)

/-- A split embedding of a chosen indecomposable into a displayed finite
biproduct forces its label to occur among the displayed factors.  This is
the finite-skeleton support detector needed by the projective-free-prefix
argument. -/
theorem exists_label_eq_of_isSplitMono_finBiproduct
    (p : Ind) (n : ℕ) (label : Fin n → Ind)
    (j : T.obj p ⟶ ⨁ fun i ↦ T.obj (label i)) [IsSplitMono j] :
    ∃ i : Fin n, label i = p := by
  classical
  by_contra hoccurs
  push Not at hoccurs
  have hcomponent (i : Fin n) :
      j ≫ biproduct.π (fun t ↦ T.obj (label t)) i ∈
        T.radical.ideal.hom (T.obj p) (T.obj (label i)) := by
    apply (T.radical.mem_ideal_iff _).2
    apply (FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
      T.toFiniteRightTauCategoryData _).2
    intro hsplit
    letI : IsSplitMono
        (j ≫ biproduct.π (fun t ↦ T.obj (label t)) i) := hsplit
    letI : IsIso
        (j ≫ biproduct.π (fun t ↦ T.obj (label t)) i) :=
      T.isIso_of_isSplitMono_obj_obj _
    have hpq : p = label i := T.obj_skeletal
      ⟨asIso (j ≫ biproduct.π (fun t ↦ T.obj (label t)) i)⟩
    exact hoccurs i hpq.symm
  have hjmem :
      j ∈ T.radical.ideal.hom
        (T.obj p) (⨁ fun i ↦ T.obj (label i)) := by
    rw [show j = ∑ i : Fin n,
        (j ≫ biproduct.π (fun t ↦ T.obj (label t)) i) ≫
          biproduct.ι (fun t ↦ T.obj (label t)) i by
      calc
        j = j ≫ 𝟙 _ := by simp
        _ = j ≫ ∑ i : Fin n,
              biproduct.π (fun t ↦ T.obj (label t)) i ≫
                biproduct.ι (fun t ↦ T.obj (label t)) i := by
          rw [biproduct.total]
        _ = ∑ i : Fin n,
              (j ≫ biproduct.π (fun t ↦ T.obj (label t)) i) ≫
                biproduct.ι (fun t ↦ T.obj (label t)) i := by
          rw [Preadditive.comp_sum]
          congr 1
          funext i
          rw [Category.assoc]]
    apply (T.radical.ideal.hom _ _).sum_mem (t := Finset.univ)
    intro i _
    exact T.radical.ideal.postcomp
      (biproduct.ι (fun t ↦ T.obj (label t)) i) (hcomponent i)
  have hjrad : IsRadicalMorphism j :=
    (T.radical.mem_ideal_iff j).1 hjmem
  exact
    (FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
      T.toFiniteRightTauCategoryData j).1 hjrad
    (inferInstance : IsSplitMono j)

/-- Support on nonprojective labels is invariant under object isomorphism. -/
theorem SupportedOnNonprojectives.of_iso
    {X Y : C} (hX : T.SupportedOnNonprojectives X) (e : Y ≅ X) :
    T.SupportedOnNonprojectives Y := by
  obtain ⟨n, label, ⟨d⟩, hlabel⟩ := hX
  exact ⟨n, label, ⟨e.trans d⟩, hlabel⟩

/-- No projective chosen indecomposable can split-embed into the third term
of a chosen left mesh.  After decomposing the mesh, a nonzero split
component is either impossible (injective label, hence zero third term) or
lands in the negative translate, which is nonprojective. -/
theorem not_isProjective_of_isSplitMono_to_leftMesh_X₃
    (p : Ind) (X : C)
    (j : T.obj p ⟶ (T.leftMesh X).X₃) [IsSplitMono j] :
    ¬ T.IsProjective p := by
  obtain ⟨n, label, ⟨eMesh⟩⟩ := T.exists_leftMesh_decomposition X
  let F : Fin n → C := fun i ↦ (T.leftMesh (T.obj (label i))).X₃
  let e₃ : (T.leftMesh X).X₃ ≅ ⨁ F :=
    ShortComplex.π₃.mapIso eMesh
  let j' : T.obj p ⟶ ⨁ F := j ≫ e₃.hom
  letI : IsSplitMono j' := inferInstance
  obtain ⟨i, hi⟩ :=
    T.exists_isSplitMono_component_finBiproduct p n F j'
  let k : T.obj p ⟶ (T.leftMesh (T.obj (label i))).X₃ :=
    j' ≫ biproduct.π F i
  have hk : IsSplitMono k := hi
  letI : IsSplitMono k := hk
  by_cases hInjective : T.IsInjective (label i)
  · have hkzero : k = 0 := hInjective.eq_of_tgt _ _
    let r : (T.leftMesh (T.obj (label i))).X₃ ⟶ T.obj p :=
      retraction k
    have hpzero : IsZero (T.obj p) := by
      rw [IsZero.iff_id_eq_zero]
      calc
        𝟙 (T.obj p) = k ≫ r := (IsSplitMono.id k).symm
        _ = (0 : T.obj p ⟶ _) ≫ r :=
          congrArg (fun z : T.obj p ⟶ _ ↦ z ≫ r) hkzero
        _ = 0 := zero_comp
    exact ((T.obj_indec p).1 hpzero).elim
  · let A : T.Noninjective := ⟨label i, hInjective⟩
    let k' : T.obj p ⟶ T.obj (T.tauMinus A) :=
      k ≫ (T.tauMinusIso A).hom
    letI : IsSplitMono k' := inferInstance
    letI : IsIso k' := T.isIso_of_isSplitMono_obj_obj k'
    have hpEq : p = T.tauMinus A := T.obj_skeletal ⟨asIso k'⟩
    intro hp
    subst p
    exact (T.tauPlusEquiv.symm A).2 hp

/-- The third term of every chosen left mesh is supported entirely on
nonprojective labels. -/
theorem supportedOnNonprojectives_leftMesh_X₃ (X : C) :
    T.SupportedOnNonprojectives (T.leftMesh X).X₃ := by
  obtain ⟨n, label, e⟩ := T.obj_decomposition (T.leftMesh X).X₃
  refine ⟨n, label, e, ?_⟩
  obtain ⟨e'⟩ := e
  intro i
  let j : T.obj (label i) ⟶ (T.leftMesh X).X₃ :=
    biproduct.ι (fun t ↦ T.obj (label t)) i ≫ e'.inv
  letI : IsSplitMono j := inferInstance
  exact T.not_isProjective_of_isSplitMono_to_leftMesh_X₃
    (label i) X j

end FiniteTauCategoryData

namespace NakayamaLadder

variable {T : FiniteTauCategoryData C Ind}

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Removing a zero source summand from a binary-biproduct arrow. -/
def biprodDescIsoRightOfIsZero
    {Y X Z : C} (hY : IsZero Y) (f : Y ⟶ Z) (a : X ⟶ Z) :
    Arrow.mk (biprod.desc f a) ≅ Arrow.mk a :=
  Arrow.isoMk' (biprod.desc f a) a (isoZeroBiprod hY).symm
    (Iso.refl Z) (by
      apply biprod.hom_ext'
      · exact hY.eq_of_src _ _
      · simp)

/-- Iyama 6.2.1's projective-free-prefix consequence, derived directly
from the left-mesh identification in each invertible rung. -/
theorem hasNonprojectiveRightSupport :
    HasNonprojectiveRightSupport T := by
  intro n X Y a hstep i
  obtain ⟨f, g, comm, _, ⟨eLeft⟩⟩ := hstep i
  have e₃ : (T.leftMesh (X i.succ)).X₃ ≅ Y i.castSucc :=
    ShortComplex.π₃.mapIso eLeft
  exact FiniteTauCategoryData.SupportedOnNonprojectives.of_iso T
    (T.supportedOnNonprojectives_leftMesh_X₃ (X i.succ)) e₃.symm

/-- In an invertible rung, a nonzero next source forces the previous right
endpoint to be nonzero. -/
theorem not_isZero_previousTarget_of_step
    {XPrev YPrev XNext YNext : C}
    {aPrev : XPrev ⟶ YPrev} {aNext : XNext ⟶ YNext}
    (hstep : InvertibleLadderStep T aPrev aNext)
    (hXNext : ¬ IsZero XNext) :
    ¬ IsZero YPrev := by
  rintro hYPrev
  obtain ⟨f, g, comm, ⟨eRight⟩, _⟩ := hstep
  have hmesh := T.rightMesh_components_isZero_of_isZero YPrev hYPrev
  have hstepX₁ : IsZero
      (stepComplex (Arrow.mk aPrev) (Arrow.mk aNext) f g comm).X₁ :=
    hmesh.1.of_iso (ShortComplex.π₁.mapIso eRight).symm
  exact hXNext hstepX₁

/-- If the next source is a chosen indecomposable and the next target is
zero, the previous vertical arrow is the second map of that source's left
mesh, up to arrow isomorphism. -/
theorem nonempty_predecessor_iso_nuMinus_of_step_to_zeroTarget
    {XPrev YPrev YNext : C} {I : Ind}
    {aPrev : XPrev ⟶ YPrev} {aNext : T.obj I ⟶ YNext}
    (hstep : InvertibleLadderStep T aPrev aNext)
    (hYNext : IsZero YNext) :
    Nonempty (Arrow.mk aPrev ≅ Arrow.mk (T.nuMinus I)) := by
  obtain ⟨f, g, comm, _, ⟨eLeft⟩⟩ := hstep
  let eStep : Arrow.mk (biprod.desc f aPrev) ≅ Arrow.mk aPrev :=
    biprodDescIsoRightOfIsZero hYNext f aPrev
  have eLeftG :
      Arrow.mk (T.nuMinus I) ≅ Arrow.mk (biprod.desc f aPrev) :=
    ShortComplex.gFunctor.mapIso eLeft
  exact ⟨eStep.symm.trans eLeftG.symm⟩

/-- The chosen indecomposable source of an invertible rung is noninjective.
The proof uses both mesh identifications in the rung. -/
theorem not_isInjective_of_step_to_zeroTarget
    {XPrev YPrev YNext : C} {I : Ind}
    {aPrev : XPrev ⟶ YPrev} {aNext : T.obj I ⟶ YNext}
    (hstep : InvertibleLadderStep T aPrev aNext) :
    ¬ T.IsInjective I := by
  have hYPrev : ¬ IsZero YPrev :=
    not_isZero_previousTarget_of_step hstep (T.obj_indec I).1
  obtain ⟨f, g, comm, _, ⟨eLeft⟩⟩ := hstep
  intro hInjective
  apply hYPrev
  exact hInjective.of_iso
    (ShortComplex.π₃.mapIso eLeft).symm

/-- A terminal rung with chosen indecomposable source canonically exposes
the nonprojective label at the preceding vertical arrow. -/
theorem exists_nonprojective_muPlus_predecessor_of_step_to_zeroTarget
    {XPrev YPrev YNext : C} {I : Ind}
    {aPrev : XPrev ⟶ YPrev} {aNext : T.obj I ⟶ YNext}
    (hstep : InvertibleLadderStep T aPrev aNext)
    (hYNext : IsZero YNext) :
    ∃ B : Ind, ¬ T.IsProjective B ∧
      Nonempty (Arrow.mk aPrev ≅ Arrow.mk (T.muPlus B)) := by
  let A : T.Noninjective :=
    ⟨I, not_isInjective_of_step_to_zeroTarget hstep⟩
  refine ⟨T.tauMinus A, (T.tauPlusEquiv.symm A).2, ?_⟩
  obtain ⟨ePrev⟩ :=
    nonempty_predecessor_iso_nuMinus_of_step_to_zeroTarget hstep hYNext
  exact ⟨ePrev.trans (T.secondMapIso A)⟩

end NakayamaLadder

end MBDVendor.QSE.Iyama
