import MBDVendor.Magnitude.Algebra.RightModuleLeftTau

/-!
# Two-sided tau-data assembly for finite right-module categories

This file makes the modulewise mesh choices canonical on the selected
indecomposable objects, identifies the nonzero mesh boundaries with the
nonprojective and noninjective labels, and assembles the two-sided
translation data required by the generic finite tau-category interface.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.Iyama
open scoped ModuleCat.Algebra ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Use the literal selected-label right mesh whenever the supplied module
is one of the selected indecomposables, and the componentwise construction
otherwise. -/
def canonicalRightMesh (X : RightModule.FinitelyGeneratedCategory A) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) := by
  classical
  by_cases h : ∃ x : Fin S.n, X = S.fgObj x
  · exact S.labelRightMesh (Classical.choose h)
  · exact S.moduleRightMesh X

/-- The canonical right mesh has the supplied module as right endpoint. -/
def canonicalRightTermIso (X : RightModule.FinitelyGeneratedCategory A) :
    (S.canonicalRightMesh X).X₃ ≅ X := by
  classical
  by_cases h : ∃ x : Fin S.n, X = S.fgObj x
  · rw [canonicalRightMesh]
    simp only [dif_pos h]
    let x := Classical.choose h
    exact (eqToIso (S.labelRightMesh_X₃ x)).trans
      (eqToIso (Classical.choose_spec h).symm)
  · rw [canonicalRightMesh]
    simp only [dif_neg h]
    exact S.moduleRightTermIso X

/-- Every canonical right mesh is a right tau-sequence. -/
theorem canonicalRightTau (X : RightModule.FinitelyGeneratedCategory A) :
    RightTauSequence (S.canonicalRightMesh X) := by
  classical
  by_cases h : ∃ x : Fin S.n, X = S.fgObj x
  · simpa [canonicalRightMesh, h] using
      S.labelRightTau (Classical.choose h)
  · simpa [canonicalRightMesh, h] using S.moduleRightTau X

/-- On a selected object, the canonical right mesh is its literal label
mesh. -/
theorem canonicalRightMesh_at_label (x : Fin S.n) :
    S.canonicalRightMesh (S.fgObj x) = S.labelRightMesh x := by
  classical
  let h : ∃ y : Fin S.n, S.fgObj x = S.fgObj y := ⟨x, rfl⟩
  rw [canonicalRightMesh]
  simp only [dif_pos h]
  apply congrArg S.labelRightMesh
  apply S.fgObj_skeletal
  exact ⟨eqToIso (Classical.choose_spec h).symm⟩

/-- Use the literal selected-label left mesh whenever the supplied module
is one of the selected indecomposables, and the componentwise construction
otherwise. -/
def canonicalLeftMesh (X : RightModule.FinitelyGeneratedCategory A) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) := by
  classical
  by_cases h : ∃ x : Fin S.n, X = S.fgObj x
  · exact S.labelLeftMesh (Classical.choose h)
  · exact S.moduleLeftMesh X

/-- The canonical left mesh has the supplied module as left endpoint. -/
def canonicalLeftTermIso (X : RightModule.FinitelyGeneratedCategory A) :
    (S.canonicalLeftMesh X).X₁ ≅ X := by
  classical
  by_cases h : ∃ x : Fin S.n, X = S.fgObj x
  · rw [canonicalLeftMesh]
    simp only [dif_pos h]
    let x := Classical.choose h
    exact (eqToIso (S.labelLeftMesh_X₁ x)).trans
      (eqToIso (Classical.choose_spec h).symm)
  · rw [canonicalLeftMesh]
    simp only [dif_neg h]
    exact S.moduleLeftTermIso X

/-- Every canonical left mesh is a left tau-sequence. -/
theorem canonicalLeftTau (X : RightModule.FinitelyGeneratedCategory A) :
    LeftTauSequence (S.canonicalLeftMesh X) := by
  classical
  by_cases h : ∃ x : Fin S.n, X = S.fgObj x
  · simpa [canonicalLeftMesh, h] using
      S.labelLeftTau (Classical.choose h)
  · simpa [canonicalLeftMesh, h] using S.moduleLeftTau X

/-- On a selected object, the canonical left mesh is its literal label
mesh. -/
theorem canonicalLeftMesh_at_label (x : Fin S.n) :
    S.canonicalLeftMesh (S.fgObj x) = S.labelLeftMesh x := by
  classical
  let h : ∃ y : Fin S.n, S.fgObj x = S.fgObj y := ⟨x, rfl⟩
  rw [canonicalLeftMesh]
  simp only [dif_pos h]
  apply congrArg S.labelLeftMesh
  apply S.fgObj_skeletal
  exact ⟨eqToIso (Classical.choose_spec h).symm⟩

/-- The first term of a selected right mesh is zero exactly at a
projective label. -/
theorem labelRightMesh_X₁_isZero_iff_projective (x : Fin S.n) :
    IsZero (S.labelRightMesh x).X₁ ↔ Projective (S.fgObj x) := by
  classical
  by_cases hx : Projective (S.fgObj x)
  · simp only [hx, iff_true]
    simpa [labelRightMesh, hx, projectiveRightMesh] using
      (isZero_zero (RightModule.FinitelyGeneratedCategory A))
  · simp only [hx, iff_false]
    intro hzero
    let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
      (RightModule.Category A)
    have hzero' : IsZero
        (U.obj (kernel (S.minimalRightAlmostSplitAt x).map)) :=
      U.map_isZero (by
        simpa [labelRightMesh, hx, nonprojectiveRightMesh] using hzero)
    have hsub : Subsingleton
        (kernel (S.minimalRightAlmostSplitAt x).map :
          RightModule.FinitelyGeneratedCategory A) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero'
    exact (not_subsingleton_iff_nontrivial.mpr
      (S.chosenRight_kernel_ar_sequence ⟨x, hx⟩).2.2.1.nontrivial) hsub

/-- The third term of a selected left mesh is zero exactly at an injective
label. -/
theorem labelLeftMesh_X₃_isZero_iff_injective (x : Fin S.n) :
    IsZero (S.labelLeftMesh x).X₃ ↔ Injective (S.fgObj x) := by
  classical
  by_cases hx : Injective (S.fgObj x)
  · simp only [hx, iff_true]
    simp only [labelLeftMesh, hx, ↓reduceDIte, injectiveLeftMesh]
    let L := S.minimalLeftAlmostSplitAt x
    letI : Injective (S.almostSplitSkeleton.obj x) := by
      change Injective (S.fgObj x)
      exact hx
    have hfEpi : Epi L.map :=
      MBDVendor.Magnitude.CategoryTheory.leftAlmostSplit_epi_of_injective_source
        L.map L.leftAlmostSplit L.leftMinimal
    letI : Epi L.map := hfEpi
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi (cokernel.π L.map)).1
    have hgzero : cokernel.π L.map = 0 := by
      apply (cancel_epi L.map).1
      rw [cokernel.condition, comp_zero]
    rw [Category.comp_id, hgzero, zero_comp]
  · simp only [hx, iff_false]
    let z := (S.rightTranslationEquiv).symm ⟨x, hx⟩
    intro hzero
    let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
      (RightModule.Category A)
    have hzero' : IsZero (U.obj (S.fgObj z.1)) :=
      U.map_isZero (by
        simpa [labelLeftMesh, hx, noninjectiveLeftMesh,
          almostSplitSkeleton] using hzero)
    have hsub : Subsingleton (S.fgObj z.1) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero'
    exact (not_subsingleton_iff_nontrivial.mpr
      (S.almostSplitSkeleton.indecomposable z.1).nontrivial) hsub

/-- Nonzero first terms of the canonical right meshes are exactly the
nonprojective selected labels. -/
def canonicalRightNonzeroEquivNonprojective :
    {x : Fin S.n //
        ¬ IsZero (S.canonicalRightMesh (S.fgObj x)).X₁} ≃
      {x : Fin S.n // ¬ Projective (S.fgObj x)} where
  toFun x := ⟨x.1, by
    intro hx
    apply x.2
    rw [S.canonicalRightMesh_at_label x.1]
    exact (S.labelRightMesh_X₁_isZero_iff_projective x.1).2 hx⟩
  invFun x := ⟨x.1, by
    rw [S.canonicalRightMesh_at_label x.1]
    intro hx
    exact x.2
      ((S.labelRightMesh_X₁_isZero_iff_projective x.1).1 hx)⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- Nonzero third terms of the canonical left meshes are exactly the
noninjective selected labels. -/
def canonicalLeftNonzeroEquivNoninjective :
    {x : Fin S.n //
        ¬ IsZero (S.canonicalLeftMesh (S.fgObj x)).X₃} ≃
      {x : Fin S.n // ¬ Injective (S.fgObj x)} where
  toFun x := ⟨x.1, by
    intro hx
    apply x.2
    rw [S.canonicalLeftMesh_at_label x.1]
    exact (S.labelLeftMesh_X₃_isZero_iff_injective x.1).2 hx⟩
  invFun x := ⟨x.1, by
    rw [S.canonicalLeftMesh_at_label x.1]
    intro hx
    exact x.2
      ((S.labelLeftMesh_X₃_isZero_iff_injective x.1).1 hx)⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- Translation on the nonzero boundaries of the canonical module
meshes. -/
def canonicalTauPlusEquiv :
    {x : Fin S.n //
        ¬ IsZero (S.canonicalRightMesh (S.fgObj x)).X₁} ≃
      {x : Fin S.n //
        ¬ IsZero (S.canonicalLeftMesh (S.fgObj x)).X₃} :=
  (S.canonicalRightNonzeroEquivNonprojective.trans
    S.rightTranslationEquiv).trans
      S.canonicalLeftNonzeroEquivNoninjective.symm

/-- Transporting both endpoints of a dependent family of morphisms
commutes with the family morphism. -/
theorem eqToHom_comp_dependent_morphism
    {C : Type u} [CategoryTheory.Category C]
    {J : Type*} (X Y : J → C) (f : ∀ j, X j ⟶ Y j)
    {i j : J} (h : i = j) :
    eqToHom (congrArg X h) ≫ f j =
      f i ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

/-- A dependent family of isomorphisms commutes with equality transport. -/
theorem dependent_iso_hom_naturality
    {C : Type u} [CategoryTheory.Category C]
    {J : Type*} (X Y : J → C) (e : ∀ j, X j ≅ Y j)
    {i j : J} (h : i = j) :
    (e i).hom ≫ eqToHom (congrArg Y h) =
      eqToHom (congrArg X h) ≫ (e j).hom := by
  subst j
  simp

/-- A nonprojective right mesh is the left mesh at its
Auslander--Reiten translate. -/
def nonprojectiveRightMeshIso_labelLeftMesh
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.nonprojectiveRightMesh z ≅
      S.labelLeftMesh (S.rightTranslationEquiv z).1 := by
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    S.rightTranslationEquiv z
  have hx : ¬ Injective (S.fgObj x.1) := x.2
  let y : {y : Fin S.n // ¬ Projective (S.fgObj y)} :=
    (S.rightTranslationEquiv).symm x
  let hz : z = y :=
    ((S.rightTranslationEquiv).symm_apply_apply z).symm
  let Bz := S.minimalRightAlmostSplitAt z.1
  let By := S.minimalRightAlmostSplitAt y.1
  let e₁ : kernel Bz.map ≅ S.fgObj x.1 :=
    S.rightTranslationKernelIso z
  let e₂ : Bz.middle ≅ By.middle :=
    eqToIso (congrArg
      (fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
        (S.minimalRightAlmostSplitAt t.1).middle) hz)
  let e₃ : S.almostSplitSkeleton.obj z.1 ≅
      S.almostSplitSkeleton.obj y.1 :=
    eqToIso (congrArg
      (fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
        S.almostSplitSkeleton.obj t.1) hz)
  have hsource : (S.noninjectiveLeftSourceIso x).hom =
      eqToHom (congrArg
        (fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
          S.fgObj (S.rightTranslation t).1) hz) := by
    simp only [noninjectiveLeftSourceIso, eqToIso.hom]
    apply eq_of_heq
    exact (eqToHom_heq_id_dom _ _ _).trans
      (eqToHom_heq_id_dom _ _ _).symm
  rw [show S.labelLeftMesh x.1 = S.noninjectiveLeftMesh x by
    simp [labelLeftMesh, hx]]
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · dsimp only [nonprojectiveRightMesh, noninjectiveLeftMesh]
    rw [hsource]
    let K := fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
      kernel (S.minimalRightAlmostSplitAt t.1).map
    let T := fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
      S.fgObj (S.rightTranslation t).1
    let M := fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
      (S.minimalRightAlmostSplitAt t.1).middle
    have hiso :
        (S.rightTranslationKernelIso z).hom ≫
            eqToHom (congrArg T hz) =
          eqToHom (congrArg K hz) ≫
            (S.rightTranslationKernelIso y).hom :=
      dependent_iso_hom_naturality K T
        (S.rightTranslationKernelIso) hz
    have hkernel :
        eqToHom (congrArg K hz) ≫
            kernel.ι (S.minimalRightAlmostSplitAt y.1).map =
          kernel.ι (S.minimalRightAlmostSplitAt z.1).map ≫
            eqToHom (congrArg M hz) :=
      eqToHom_comp_dependent_morphism K M
        (fun t ↦ kernel.ι (S.minimalRightAlmostSplitAt t.1).map) hz
    change
      (S.rightTranslationKernelIso z).hom ≫
          eqToHom (congrArg T hz) ≫
            (S.rightTranslationKernelIso y).inv ≫
              kernel.ι (S.minimalRightAlmostSplitAt y.1).map =
        kernel.ι (S.minimalRightAlmostSplitAt z.1).map ≫
          eqToHom (congrArg M hz)
    calc
      (S.rightTranslationKernelIso z).hom ≫
            eqToHom (congrArg T hz) ≫
              (S.rightTranslationKernelIso y).inv ≫
                kernel.ι (S.minimalRightAlmostSplitAt y.1).map =
          ((S.rightTranslationKernelIso z).hom ≫
              eqToHom (congrArg T hz)) ≫
            (S.rightTranslationKernelIso y).inv ≫
              kernel.ι (S.minimalRightAlmostSplitAt y.1).map := by
                simp only [Category.assoc]
      _ = (eqToHom (congrArg K hz) ≫
              (S.rightTranslationKernelIso y).hom) ≫
            (S.rightTranslationKernelIso y).inv ≫
              kernel.ι (S.minimalRightAlmostSplitAt y.1).map := by
                conv_lhs => rw [hiso]
                rfl
      _ = eqToHom (congrArg K hz) ≫
            kernel.ι (S.minimalRightAlmostSplitAt y.1).map := by
              simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = kernel.ι (S.minimalRightAlmostSplitAt z.1).map ≫
            eqToHom (congrArg M hz) := hkernel
  · dsimp only [nonprojectiveRightMesh, noninjectiveLeftMesh]
    change e₂.hom ≫ (S.minimalRightAlmostSplitAt y.1).map =
      (S.minimalRightAlmostSplitAt z.1).map ≫ e₃.hom
    simpa only [e₂, e₃, eqToIso.hom] using
      eqToHom_comp_dependent_morphism
        (fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
          (S.minimalRightAlmostSplitAt t.1).middle)
        (fun t : {t : Fin S.n // ¬ Projective (S.fgObj t)} ↦
          S.almostSplitSkeleton.obj t.1)
        (fun t ↦ (S.minimalRightAlmostSplitAt t.1).map) hz

/-- The canonical translation has the same underlying label as the
Auslander--Reiten translation after identifying its source boundary. -/
theorem canonicalTauPlusEquiv_val
    (X : {x : Fin S.n //
      ¬ IsZero (S.canonicalRightMesh (S.fgObj x)).X₁}) :
    (S.canonicalTauPlusEquiv X).1 =
      (S.rightTranslationEquiv
        (S.canonicalRightNonzeroEquivNonprojective X)).1 := rfl

/-- The canonical right mesh at a nonzero boundary agrees with the
canonical left mesh at its translated boundary. -/
def canonicalRightLeftMeshIso
    (X : {x : Fin S.n //
      ¬ IsZero (S.canonicalRightMesh (S.fgObj x)).X₁}) :
    S.canonicalRightMesh (S.fgObj X.1) ≅
      S.canonicalLeftMesh
        (S.fgObj (S.canonicalTauPlusEquiv X).1) := by
  let z := S.canonicalRightNonzeroEquivNonprojective X
  let x := S.rightTranslationEquiv z
  have hnp : ¬ Projective (S.fgObj X.1) := z.2
  have hright : S.canonicalRightMesh (S.fgObj X.1) =
      S.nonprojectiveRightMesh z := by
    rw [S.canonicalRightMesh_at_label X.1]
    simp only [labelRightMesh, hnp, ↓reduceDIte]
    rfl
  have hleft : S.labelLeftMesh x.1 =
      S.canonicalLeftMesh (S.fgObj (S.canonicalTauPlusEquiv X).1) := by
    rw [S.canonicalTauPlusEquiv_val X]
    exact (S.canonicalLeftMesh_at_label x.1).symm
  exact (eqToIso hright).trans
    ((S.nonprojectiveRightMeshIso_labelLeftMesh z).trans
      (eqToIso hleft))

/-- The two-sided tau-category input constructed from a finite
indecomposable skeleton of finitely generated right modules. -/
def tauInput : RightModule.TauInput S where
  right := {
    rightMesh := S.canonicalRightMesh
    rightTermIso := S.canonicalRightTermIso
    rightTau := S.canonicalRightTau }
  leftMesh := S.canonicalLeftMesh
  leftTermIso := S.canonicalLeftTermIso
  leftTau := S.canonicalLeftTau
  tauPlusEquiv := S.canonicalTauPlusEquiv
  rightLeftMeshIso := S.canonicalRightLeftMeshIso

/-- The finite tau-category carried by a finite indecomposable skeleton of
finitely generated right modules. -/
def finiteTauCategoryData :
    FiniteTauCategoryData
      (RightModule.FinitelyGeneratedCategory A) (Fin S.n) :=
  S.toFiniteTauCategoryData S.tauInput

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
