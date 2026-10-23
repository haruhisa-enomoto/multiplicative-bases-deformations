module

public import MBDVendor.Magnitude.CategoryTheory.IrreducibleRadicalSquare
public import MBDVendor.Magnitude.CategoryTheory.ResidueDimension

/-!
# Irreducible components of finite tau meshes

The middle term of a chosen right tau mesh is decomposed into the selected
indecomposable representatives when its arrow multiplicities are defined.
This file proves that every resulting summand-to-endpoint component is an
irreducible morphism.  The argument is intrinsic to a finite tau-category:
right almost-split factorization comes from the tau approximation, while
minimality of the second mesh map follows from its minimal weak kernel.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- A fixed representative of the chosen decomposition of a right-mesh
middle term. -/
def rightMiddleDecompositionIso (Y : Ind) :
    (T.rightMesh (T.obj Y)).X₂ ≅
      ⨁ fun i ↦ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) :=
  Classical.choice (rightMiddleIso T.toFiniteRightTauCategoryData Y)

/-- Inclusion of one chosen indecomposable occurrence into the right-mesh
middle term. -/
def rightMiddleInclusion (Y : Ind) (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y)) :
    T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) ⟶
      (T.rightMesh (T.obj Y)).X₂ :=
  biproduct.ι (fun j ↦ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y j)) i ≫
    (rightMiddleDecompositionIso T Y).inv

/-- Projection from the right-mesh middle term onto one chosen occurrence. -/
def rightMiddleProjection (Y : Ind) (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y)) :
    (T.rightMesh (T.obj Y)).X₂ ⟶
      T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) :=
  (rightMiddleDecompositionIso T Y).hom ≫
    biproduct.π (fun j ↦ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y j)) i

/-- The actual morphism from one displayed middle occurrence to the selected
endpoint representative. -/
def rightMiddleComponent (Y : Ind) (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y)) :
    T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) ⟶ T.obj Y :=
  rightMiddleInclusion T Y i ≫
    (T.rightMesh (T.obj Y)).g ≫ (T.rightTermIso (T.obj Y)).hom

@[simp]
theorem rightMiddleInclusion_projection
    (Y : Ind) (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y)) :
    rightMiddleInclusion T Y i ≫ rightMiddleProjection T Y i =
      𝟙 (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i)) := by
  simp [rightMiddleInclusion, rightMiddleProjection, Category.assoc]

/-- Every occurrence counted by `arrowMultiplicity` is represented by an
irreducible morphism between the corresponding selected indecomposables. -/
theorem rightMiddleComponent_isIrreducible
    (Y : Ind) (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y)) :
    IsIrreducibleMorphism (rightMiddleComponent T Y i) := by
  let S := T.rightMesh (T.obj Y)
  let inc : T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) ⟶ S.X₂ :=
    rightMiddleInclusion T Y i
  let proj : S.X₂ ⟶ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) :=
    rightMiddleProjection T Y i
  let e₃ : S.X₃ ≅ T.obj Y := T.rightTermIso (T.obj Y)
  let g : T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i) ⟶ T.obj Y :=
    inc ≫ S.g ≫ e₃.hom
  change IsIrreducibleMorphism g
  have hincproj : inc ≫ proj =
      𝟙 (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i)) := by
    exact rightMiddleInclusion_projection T Y i
  have hgrad : IsRadicalMorphism (S.g ≫ e₃.hom) :=
    isRadicalMorphism_postcomp e₃.hom (T.rightTau (T.obj Y)).g_radical
  have hnotepiMap : ¬ IsSplitEpi (S.g ≫ e₃.hom) :=
    (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (S.g ≫ e₃.hom)).1 hgrad
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    obtain ⟨se⟩ := hg.exists_splitEpi
    apply hnotepiMap
    exact IsSplitEpi.mk'
      { section_ := se.section_ ≫ inc
        id := by
          simpa only [g, Category.assoc] using se.id }
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    letI : IsSplitMono g := hg
    letI : IsIso g := isIso_of_isSplitMono_obj_obj
      (T : FiniteRightTauCategoryData C Ind) g
    exact hnotepi inferInstance
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  · have hbrad : IsRadicalMorphism b :=
      (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj b).2 hb
    have hbrad' : IsRadicalMorphism (b ≫ e₃.inv) :=
      isRadicalMorphism_postcomp e₃.inv hbrad
    obtain ⟨c, hc⟩ :=
      (T.rightTau (T.obj Y)).factors_into_right (b ≫ e₃.inv) hbrad'
    have hc' : c ≫ S.g ≫ e₃.hom = b := by
      rw [← Category.assoc, hc]
      simp
    let d : S.X₂ ⟶ S.X₂ :=
      𝟙 S.X₂ + proj ≫ (a ≫ c - inc)
    have hdfix : d ≫ S.g = S.g := by
      dsimp only [d]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, Preadditive.sub_comp]
      have hac : (a ≫ c) ≫ S.g = inc ≫ S.g := by
        rw [Category.assoc]
        apply (cancel_mono e₃.hom).1
        simp only [Category.assoc, hc', hab]
        rfl
      rw [hac, sub_self, comp_zero, add_zero]
    have hincd : inc ≫ d = a ≫ c := by
      dsimp only [d]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, hincproj, Category.id_comp]
      abel
    letI : IsIso d := (T.rightTau (T.obj Y)).isRightMinimal_g d hdfix
    exact Or.inl (IsSplitMono.mk'
      { retraction := c ≫ inv d ≫ proj
        id := by
          calc
            a ≫ (c ≫ inv d ≫ proj) =
                (a ≫ c) ≫ inv d ≫ proj := by
                  simp only [Category.assoc]
            _ = (inc ≫ d) ≫ inv d ≫ proj := by rw [hincd]
            _ = 𝟙 (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y i)) := by
                  simp only [Category.assoc,
                    IsIso.hom_inv_id_assoc, hincproj] })

/-- For a nonprojective endpoint, compatibility with the corresponding left
mesh makes the first map of the right mesh left minimal as well. -/
theorem rightMesh_f_isLeftMinimal
    (Y : T.Nonprojective) :
    IsLeftMinimal (T.rightMesh (T.obj Y.1)).f := by
  let S := T.rightMesh (T.obj Y.1)
  let L := T.leftMesh (T.obj (T.tauPlus Y))
  let E : S ≅ L := T.rightLeftMeshIso Y
  intro d hd
  have hE₂ : E.hom.τ₂ ≫ E.inv.τ₂ = 𝟙 S.X₂ := by
    have h := congrArg ShortComplex.Hom.τ₂ E.hom_inv_id
    change E.hom.τ₂ ≫ E.inv.τ₂ = 𝟙 S.X₂ at h
    exact h
  let dL : L.X₂ ⟶ L.X₂ := E.inv.τ₂ ≫ d ≫ E.hom.τ₂
  have hfix : L.f ≫ dL = L.f := by
    apply (cancel_epi E.hom.τ₁).1
    calc
      E.hom.τ₁ ≫ (L.f ≫ dL) =
          (E.hom.τ₁ ≫ L.f) ≫ dL :=
            (Category.assoc _ _ _).symm
      _ = (S.f ≫ E.hom.τ₂) ≫ dL := by
            rw [E.hom.comm₁₂]
      _ = S.f ≫ d ≫ E.hom.τ₂ := by
            dsimp only [dL]
            calc
              (S.f ≫ E.hom.τ₂) ≫
                    E.inv.τ₂ ≫ d ≫ E.hom.τ₂ =
                  S.f ≫ ((E.hom.τ₂ ≫ E.inv.τ₂) ≫
                    d ≫ E.hom.τ₂) := by
                      simp only [Category.assoc]
              _ = S.f ≫ d ≫ E.hom.τ₂ := by
                    rw [hE₂]
                    simp
      _ = S.f ≫ E.hom.τ₂ := by rw [← Category.assoc, hd]
      _ = E.hom.τ₁ ≫ L.f := E.hom.comm₁₂.symm
  letI : IsIso dL :=
    (T.leftTau (T.obj (T.tauPlus Y))).isLeftMinimal_f dL hfix
  have hdconj : d = E.hom.τ₂ ≫ dL ≫ E.inv.τ₂ := by
    symm
    dsimp only [dL]
    simp only [Category.assoc]
    rw [← Category.assoc, hE₂, Category.id_comp]
    exact Category.comp_id d
  rw [hdconj]
  infer_instance

/-- The component of the first right-mesh map from its translated source to
one occurrence of the chosen middle decomposition. -/
def rightMiddleSourceComponent
    (Y : T.Nonprojective)
    (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y.1)) :
    T.obj (T.tauPlus Y) ⟶ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i) :=
  (T.tauPlusIso Y).inv ≫ (T.rightMesh (T.obj Y.1)).f ≫
    rightMiddleProjection T Y.1 i

/-- At a nonprojective endpoint, the translated-source component to every
chosen middle occurrence is irreducible. -/
theorem rightMiddleSourceComponent_isIrreducible
    (Y : T.Nonprojective)
    (i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y.1)) :
    IsIrreducibleMorphism (rightMiddleSourceComponent T Y i) := by
  let S := T.rightMesh (T.obj Y.1)
  let inc : T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i) ⟶ S.X₂ :=
    rightMiddleInclusion T Y.1 i
  let proj : S.X₂ ⟶ T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i) :=
    rightMiddleProjection T Y.1 i
  let e₁ : S.X₁ ≅ T.obj (T.tauPlus Y) := T.tauPlusIso Y
  let f : T.obj (T.tauPlus Y) ⟶ S.X₂ := e₁.inv ≫ S.f
  let g : T.obj (T.tauPlus Y) ⟶
      T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i) :=
    rightMiddleSourceComponent T Y i
  change IsIrreducibleMorphism g
  have hgdef : g = f ≫ proj := by
    simp [g, f, proj, rightMiddleSourceComponent, S, e₁, Category.assoc]
  have hincproj : inc ≫ proj =
      𝟙 (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i)) := by
    exact rightMiddleInclusion_projection T Y.1 i
  have hfrad : IsRadicalMorphism f :=
    isRadicalMorphism_precomp e₁.inv (T.rightTau (T.obj Y.1)).f_radical
  have hnotmonoMap : ¬ IsSplitMono f :=
    (T.isRadicalMorphism_iff_not_isSplitMono_from_obj f).1 hfrad
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    obtain ⟨sm⟩ := hg.exists_splitMono
    apply hnotmonoMap
    exact IsSplitMono.mk'
      { retraction := proj ≫ sm.retraction
        id := by
          calc
            f ≫ proj ≫ sm.retraction = g ≫ sm.retraction := by
              simpa only [Category.assoc] using congrArg
                (fun q : T.obj (T.tauPlus Y) ⟶
                    T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i) ↦
                  q ≫ sm.retraction) hgdef.symm
            _ = 𝟙 (T.obj (T.tauPlus Y)) := sm.id }
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    obtain ⟨se⟩ := hg.exists_splitEpi
    let s : T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i) ⟶ T.obj (T.tauPlus Y) :=
      se.section_
    letI : IsSplitMono s := IsSplitMono.mk'
      { retraction := g
        id := se.id }
    letI : IsIso s := isIso_of_isSplitMono_obj_obj
      (T : FiniteRightTauCategoryData C Ind) s
    have hsg : s ≫ g = 𝟙 (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i)) := se.id
    letI : IsIso (s ≫ g) := hsg ▸ inferInstance
    haveI : IsIso g := IsIso.of_isIso_comp_left s g
    exact hnotmono inferInstance
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  · have harad : IsRadicalMorphism a :=
      (T.isRadicalMorphism_iff_not_isSplitMono_from_obj a).2 ha
    have harad' : IsRadicalMorphism (e₁.hom ≫ a) :=
      isRadicalMorphism_precomp e₁.hom harad
    obtain ⟨c, hc⟩ :=
      (T.rightTau (T.obj Y.1)).factors_from_left (e₁.hom ≫ a) harad'
    have hc' : f ≫ c = a := by
      dsimp only [f]
      rw [Category.assoc, hc]
      simp
    let d : S.X₂ ⟶ S.X₂ :=
      𝟙 S.X₂ + (c ≫ b - proj) ≫ inc
    have hdfix : S.f ≫ d = S.f := by
      dsimp only [d]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, Preadditive.comp_sub]
      have hcb' : f ≫ (c ≫ b) = f ≫ proj := by
        rw [← Category.assoc, hc', hab, hgdef]
      have hcb : S.f ≫ (c ≫ b) = S.f ≫ proj := by
        apply (cancel_epi e₁.inv).1
        simpa only [f, Category.assoc] using hcb'
      rw [hcb, sub_self, zero_comp, add_zero]
    have hdproj : d ≫ proj = c ≫ b := by
      dsimp only [d]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, hincproj, Category.comp_id]
      abel
    letI : IsIso d := rightMesh_f_isLeftMinimal T Y d hdfix
    exact Or.inr (IsSplitEpi.mk'
      { section_ := inc ≫ inv d ≫ c
        id := by
          calc
            (inc ≫ inv d ≫ c) ≫ b =
                inc ≫ inv d ≫ (c ≫ b) := by
                  simp only [Category.assoc]
            _ = inc ≫ inv d ≫ (d ≫ proj) := by rw [← hdproj]
            _ = 𝟙 (T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i)) := by
                  simp only [IsIso.inv_hom_id_assoc, hincproj] })

/-- A nonprojective right mesh has at least one occurrence in its chosen
middle decomposition. -/
theorem rightMiddleArity_pos_of_nonprojective
    (Y : T.Nonprojective) :
    0 < rightMiddleArity T.toFiniteRightTauCategoryData Y.1 := by
  by_contra hpos
  have hn : rightMiddleArity T.toFiniteRightTauCategoryData Y.1 = 0 := by omega
  apply T.not_isZero_thetaPlus Y
  have hzero : IsZero
      (⨁ fun i : Fin (rightMiddleArity T.toFiniteRightTauCategoryData Y.1) ↦
        T.obj (rightMiddleLabel T.toFiniteRightTauCategoryData Y.1 i)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 (hn ▸ i)
  exact hzero.of_iso (rightMiddleDecompositionIso T Y.1)

end MBDVendor.Magnitude.FiniteTauMatrix
