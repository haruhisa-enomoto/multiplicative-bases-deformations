import MBDVendor.Magnitude.Algebra.RightModuleFactorCategory

/-!
# Right tau-sequences in literal finite-module factor categories

This file descends the chosen ambient right Auslander--Reiten meshes through
the literal quotient by maps factoring through selected labels.  The raw
quotient mesh retains the radical approximation and weak-kernel properties;
only its possibly zero left boundary requires minimalization.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama
open scoped ModuleCat.Algebra ZeroObject

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

private theorem isZero_target_of_radical_splitEpi
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    {X Y : C} {f : X ⟶ Y} (hf : IsRadicalMorphism f)
    (s : SplitEpi f) : IsZero Y := by
  letI : IsSplitEpi f := IsSplitEpi.mk' s
  let sec : Y ⟶ X := section_ f
  have hs : sec ≫ f = 𝟙 Y := IsSplitEpi.id f
  have hi : IsIso (𝟙 X - f ≫ sec) := hf sec
  have hzero : sec ≫ (𝟙 X - f ≫ sec) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hs,
      Category.id_comp, sub_self]
  have hsection : sec = 0 := by
    rw [← cancel_mono (𝟙 X - f ≫ sec)]
    simpa using hzero
  rw [IsZero.iff_id_eq_zero, ← hs, hsection, zero_comp]

private theorem isZero_source_of_radical_splitMono
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    {X Y : C} {f : X ⟶ Y} (hf : IsRadicalMorphism f)
    (s : SplitMono f) : IsZero X := by
  letI : IsSplitMono f := IsSplitMono.mk' s
  let r : Y ⟶ X := retraction f
  have hr : f ≫ r = 𝟙 X := IsSplitMono.id f
  have hi : IsIso (𝟙 X - f ≫ r) := hf r
  have hzero : 𝟙 X - f ≫ r = 0 := by rw [hr, sub_self]
  haveI : IsIso (0 : X ⟶ X) := hzero ▸ hi
  exact (IsZero.iff_isSplitEpi_eq_zero (0 : X ⟶ X)).2 rfl

/-- The literal image of the selected ambient right mesh in the factor
category. -/
def factorRawRightMesh (K : Set (Fin S.n)) (x : Fin S.n) :
    ShortComplex (S.FactorCategory K) :=
  (S.labelRightMesh x).map (S.factorModuleFunctor K)

/-- Both maps in the raw quotient mesh remain radical. -/
theorem factorRawRightMesh_radical
    (K : Set (Fin S.n)) (x : Fin S.n) :
    IsRadicalMorphism (S.factorRawRightMesh K x).f ∧
      IsRadicalMorphism (S.factorRawRightMesh K x).g := by
  let I := S.factorThroughSelectedIdeal K
  let A := S.labelRightTau x
  constructor
  · exact I.map_isRadicalMorphism _
      (S.selectedAdd_isRadicalMorphism_of_hom _ A.f_radical)
  · exact I.map_isRadicalMorphism _
      (S.selectedAdd_isRadicalMorphism_of_hom _ A.g_radical)

/-- The raw quotient mesh at a surviving label ends at its literal factor
object. -/
theorem factorRawRightMesh_X₃
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorRawRightMesh K x.1).X₃ = S.factorObject K x := by
  change (S.factorModuleFunctor K).obj (S.labelRightMesh x.1).X₃ =
    S.factorObject K x
  rw [S.labelRightMesh_X₃]
  rfl

/-- Radical maps into a surviving endpoint factor through the raw quotient
right-mesh map. -/
theorem factorRawRightMesh_factors_into_right
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ∀ {W : S.FactorCategory K}
      (a : W ⟶ (S.factorRawRightMesh K x.1).X₃),
      IsRadicalMorphism a →
        ∃ b : W ⟶ (S.factorRawRightMesh K x.1).X₂,
          b ≫ (S.factorRawRightMesh K x.1).g = a := by
  let F := S.factorFunctor K
  let T := S.labelRightMesh x.1
  let Aτ := S.labelRightTau x.1
  intro W a ha
  obtain ⟨a', rfl⟩ := F.map_surjective a
  have hnot : ¬ IsSplitEpi a'.hom := by
    intro hsplit
    letI : IsSplitEpi a'.hom := hsplit
    let se : SplitEpi a' :=
      { section_ := ObjectProperty.homMk (section_ a'.hom)
        id := by
          apply ObjectProperty.hom_ext
          exact IsSplitEpi.id a'.hom }
    have hz : IsZero (S.factorRawRightMesh K x.1).X₃ :=
      isZero_target_of_radical_splitEpi ha (se.map F)
    rw [S.factorRawRightMesh_X₃ K x] at hz
    exact S.factorObject_not_isZero K x hz
  let eX : T.X₃ ≅ S.fgObj x.1 := eqToIso (S.labelRightMesh_X₃ x.1)
  let aX : W.as.obj ⟶ S.fgObj x.1 := a'.hom ≫ eX.hom
  have hnotX : ¬ IsSplitEpi aX := by
    intro hsplit
    letI : IsSplitEpi aX := hsplit
    letI : IsSplitEpi eX.inv := inferInstance
    have hs : IsSplitEpi (aX ≫ eX.inv) := inferInstance
    have heq : aX ≫ eX.inv = a'.hom := by simp [aX]
    exact hnot (heq ▸ hs)
  have haRad : IsRadicalMorphism a'.hom := by
    have haXRad : IsRadicalMorphism aX :=
      (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
        aX).2 hnotX
    have h := isRadicalMorphism_postcomp eX.inv haXRad
    simpa [aX] using h
  obtain ⟨b, hb⟩ := Aτ.factors_into_right a'.hom haRad
  refine ⟨F.map (ObjectProperty.homMk b), ?_⟩
  change F.map (ObjectProperty.homMk b) ≫
      F.map (S.ambientAddFunctor.map T.g) = F.map a'
  rw [← F.map_comp]
  apply congrArg F.map
  apply ObjectProperty.hom_ext
  exact hb

/-- Radical maps out of the raw quotient mesh's left endpoint factor through
its first map. -/
theorem factorRawRightMesh_factors_from_left
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ∀ {W : S.FactorCategory K}
      (a : (S.factorRawRightMesh K x.1).X₁ ⟶ W),
      IsRadicalMorphism a →
        ∃ b : (S.factorRawRightMesh K x.1).X₂ ⟶ W,
          (S.factorRawRightMesh K x.1).f ≫ b = a := by
  let F := S.factorFunctor K
  let T := S.labelRightMesh x.1
  let Aτ := S.labelRightTau x.1
  intro W a ha
  classical
  by_cases hx : Projective (S.fgObj x.1)
  · have hT₁ : IsZero T.X₁ :=
      (S.labelRightMesh_X₁_isZero_iff_projective x.1).2 hx
    have hQ₁ : IsZero (S.factorRawRightMesh K x.1).X₁ :=
      (S.factorModuleFunctor K).map_isZero hT₁
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := hQ₁.eq_of_src a 0
    rw [ha0]
    simp
  · let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨x.1, hx⟩
    let y₀ : Fin S.n := S.rightTranslationLabel z
    let eT : T.X₁ ≅ S.fgObj y₀ := by
      simpa [T, labelRightMesh, hx, nonprojectiveRightMesh, z, y₀] using
        S.rightTranslationKernelIso z
    let eQ : (S.factorRawRightMesh K x.1).X₁ ≅
        (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
      (S.factorModuleFunctor K).mapIso eT
    by_cases hy : y₀ ∈ K
    · have htarget : IsZero ((S.factorModuleFunctor K).obj (S.fgObj y₀)) :=
        (S.factorObject_isZero_of_mem K hy).of_iso
          (S.factorAmbientPointIsoFactorModule K y₀)
      have hQ₁ : IsZero (S.factorRawRightMesh K x.1).X₁ :=
        htarget.of_iso eQ
      refine ⟨0, ?_⟩
      have ha0 : a = 0 := hQ₁.eq_of_src a 0
      rw [ha0]
      simp
    · let y : S.SurvivingLabel K := ⟨y₀, hy⟩
      obtain ⟨a', rfl⟩ := F.map_surjective a
      have hnot : ¬ IsSplitMono a'.hom := by
        intro hsplit
        letI : IsSplitMono a'.hom := hsplit
        let sm : SplitMono a' :=
          { retraction := ObjectProperty.homMk (retraction a'.hom)
            id := by
              apply ObjectProperty.hom_ext
              exact IsSplitMono.id a'.hom }
        have hz : IsZero (S.factorRawRightMesh K x.1).X₁ :=
          isZero_source_of_radical_splitMono ha (sm.map F)
        have hyzero : IsZero (S.factorObject K y) := by
          apply hz.of_iso
          exact (eQ.trans (eqToIso (by rfl))).symm
        exact S.factorObject_not_isZero K y hyzero
      let aY : S.fgObj y₀ ⟶ W.as.obj := eT.inv ≫ a'.hom
      have hnotY : ¬ IsSplitMono aY := by
        intro hsplit
        letI : IsSplitMono aY := hsplit
        letI : IsSplitMono eT.hom := inferInstance
        have hs : IsSplitMono (eT.hom ≫ aY) := inferInstance
        have heq : eT.hom ≫ aY = a'.hom := by simp [aY]
        exact hnot (heq ▸ hs)
      have haRad : IsRadicalMorphism a'.hom := by
        have haYRad : IsRadicalMorphism aY :=
          (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitMono_from_obj
            aY).2 hnotY
        have hr := isRadicalMorphism_precomp eT.hom haYRad
        simpa [aY] using hr
      obtain ⟨b, hb⟩ := Aτ.factors_from_left a'.hom haRad
      refine ⟨F.map (S.ambientAddFunctor.map b), ?_⟩
      change F.map (S.ambientAddFunctor.map T.f) ≫
          F.map (S.ambientAddFunctor.map b) = F.map a'
      rw [← F.map_comp]
      apply congrArg F.map
      apply ObjectProperty.hom_ext
      exact hb

/-- The raw quotient mesh retains the weak-kernel property. -/
theorem factorRawRightMesh_isWeakKernel
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Iyama.ShortComplex.IsWeakKernel (S.factorRawRightMesh K x.1) := by
  let I := S.factorThroughSelectedIdeal K
  let F := S.factorFunctor K
  let T := S.labelRightMesh x.1
  let Aτ := S.labelRightTau x.1
  rw [Iyama.ShortComplex.isWeakKernel_iff]
  intro W q hq
  obtain ⟨q', rfl⟩ := F.map_surjective q
  let gAdd := S.ambientAddFunctor.map T.g
  have hqmap : F.map (q' ≫ gAdd) = 0 := by
    change F.map q' ≫ F.map gAdd = 0 at hq
    simpa only [← F.map_comp] using hq
  have hfac := (I.map_eq_zero_iff (q' ≫ gAdd)).1 hqmap
  rcases hfac with ⟨M, hM, left, right, hcomp⟩
  have hrightNot : ¬ IsSplitEpi right := by
    intro hsplit
    letI : IsSplitEpi right := hsplit
    let eX : T.X₃ ≅ S.fgObj x.1 := eqToIso (S.labelRightMesh_X₃ x.1)
    let rt : Retract (S.fgObj x.1) M :=
      { i := eX.inv ≫ section_ right
        r := right ≫ eX.hom
        retract := by simp }
    exact x.2
      (S.almostSplitSkeleton.index_mem_of_retract_inAdd rt hM)
  let eX : T.X₃ ≅ S.fgObj x.1 := eqToIso (S.labelRightMesh_X₃ x.1)
  let rightX : M ⟶ S.fgObj x.1 := right ≫ eX.hom
  have hrightXNot : ¬ IsSplitEpi rightX := by
    intro hsplit
    letI : IsSplitEpi rightX := hsplit
    letI : IsSplitEpi eX.inv := inferInstance
    have hs : IsSplitEpi (rightX ≫ eX.inv) := inferInstance
    have heq : rightX ≫ eX.inv = right := by simp [rightX]
    exact hrightNot (heq ▸ hs)
  have hrightRad : IsRadicalMorphism right := by
    have hrX : IsRadicalMorphism rightX :=
      (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
        rightX).2 hrightXNot
    have hr := isRadicalMorphism_postcomp eX.inv hrX
    simpa [rightX] using hr
  obtain ⟨v, hv⟩ := Aτ.factors_into_right right hrightRad
  let q₀ : W.as.obj ⟶ T.X₂ := q'.hom - left ≫ v
  have hq₀ : q₀ ≫ T.g = 0 := by
    dsimp only [q₀]
    rw [Preadditive.sub_comp, Category.assoc, hv]
    have hc : left ≫ right = q'.hom ≫ T.g := by
      change left ≫ right = q'.hom ≫ T.g at hcomp
      exact hcomp
    rw [hc, sub_self]
  obtain ⟨l, hl⟩ :=
    (Iyama.ShortComplex.isWeakKernel_iff T).1 Aτ.minimalWeakKernel.1 q₀ hq₀
  refine ⟨F.map (S.ambientAddFunctor.map l), ?_⟩
  change F.map (S.ambientAddFunctor.map l) ≫
      F.map (S.ambientAddFunctor.map T.f) = F.map q'
  rw [← F.map_comp, ← sub_eq_zero, ← F.map_sub]
  apply (I.map_eq_zero_iff _).2
  refine ⟨M, hM, -left, v, ?_⟩
  change (-left) ≫ v = (l ≫ T.f) - q'.hom
  rw [hl]
  dsimp only [q₀]
  simp

/-- The raw quotient mesh satisfies the radical approximation part of a right
tau-sequence. -/
theorem factorRawRightMesh_tauApproximation
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    TauApproximation (S.factorRawRightMesh K x.1) where
  f_radical := (S.factorRawRightMesh_radical K x.1).1
  g_radical := (S.factorRawRightMesh_radical K x.1).2
  factors_from_left := S.factorRawRightMesh_factors_from_left K x
  factors_into_right := S.factorRawRightMesh_factors_into_right K x

/-- The source of a raw quotient mesh is either zero or isomorphic to a
surviving selected indecomposable. -/
theorem factorRawRightMesh_X₁_zero_or_exists_factorObject_iso
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      ∃ y : S.SurvivingLabel K,
        Nonempty ((S.factorRawRightMesh K x.1).X₁ ≅
          S.factorObject K y) := by
  classical
  let T := S.labelRightMesh x.1
  by_cases hx : Projective (S.fgObj x.1)
  · left
    exact (S.factorModuleFunctor K).map_isZero
      ((S.labelRightMesh_X₁_isZero_iff_projective x.1).2 hx)
  · let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨x.1, hx⟩
    let y₀ : Fin S.n := S.rightTranslationLabel z
    let eT : T.X₁ ≅ S.fgObj y₀ := by
      simpa [T, labelRightMesh, hx, nonprojectiveRightMesh, z, y₀] using
        S.rightTranslationKernelIso z
    let eQ : (S.factorRawRightMesh K x.1).X₁ ≅
        (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
      (S.factorModuleFunctor K).mapIso eT
    by_cases hy : y₀ ∈ K
    · left
      have htarget : IsZero ((S.factorModuleFunctor K).obj (S.fgObj y₀)) :=
        (S.factorObject_isZero_of_mem K hy).of_iso
          (S.factorAmbientPointIsoFactorModule K y₀)
      exact htarget.of_iso eQ
    · right
      let y : S.SurvivingLabel K := ⟨y₀, hy⟩
      exact ⟨y, ⟨eQ.trans (eqToIso (by rfl))⟩⟩

/-- If an ambient label is nonprojective and its right translate survives,
then the source of its raw quotient right mesh is nonzero. -/
theorem factorRawRightMesh_X₁_not_isZero_of_translation_survives
    (K : Set (Fin S.n)) (x : Fin S.n)
    (hx : ¬ Projective (S.fgObj x))
    (hy : S.rightTranslationLabel ⟨x, hx⟩ ∉ K) :
    ¬ IsZero (S.factorRawRightMesh K x).X₁ := by
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨x, hx⟩
  let y₀ : Fin S.n := S.rightTranslationLabel z
  let T := S.labelRightMesh x
  let eT : T.X₁ ≅ S.fgObj y₀ := by
    simpa [T, labelRightMesh, hx, nonprojectiveRightMesh, z, y₀] using
      S.rightTranslationKernelIso z
  let eQ : (S.factorRawRightMesh K x).X₁ ≅
      (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
    (S.factorModuleFunctor K).mapIso eT
  let y : S.SurvivingLabel K := ⟨y₀, by simpa [z, y₀] using hy⟩
  intro hzero
  apply S.factorObject_not_isZero K y
  exact (hzero.of_iso eQ.symm).of_iso
    (S.factorAmbientPointIsoFactorModule K y₀).symm

private def endRingEquivOfIso
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    {X Y : C} (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := by
      intro f g
      apply End.ext
      change e.inv ≫ (End.asHom f + End.asHom g) ≫ e.hom =
        e.inv ≫ End.asHom f ≫ e.hom +
          e.inv ≫ End.asHom g ≫ e.hom
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

/-- If its source and first map survive, the raw quotient mesh is already a
right tau-sequence. -/
theorem factorRawRightTau_of_nonzero
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (hsource : ¬ IsZero (S.factorRawRightMesh K x.1).X₁)
    (hf : (S.factorRawRightMesh K x.1).f ≠ 0) :
    RightTauSequence (S.factorRawRightMesh K x.1) := by
  rcases S.factorRawRightMesh_X₁_zero_or_exists_factorObject_iso K x with
    hzero | ⟨y, ⟨e⟩⟩
  · exact (hsource hzero).elim
  · letI : IsLocalRing (End (S.factorObject K y)) :=
      S.factorObject_end_isLocalRing K y
    letI : IsLocalRing (End (S.factorRawRightMesh K x.1).X₁) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
        (endRingEquivOfIso e).symm
    exact
      { toTauApproximation := S.factorRawRightMesh_tauApproximation K x
        minimalWeakKernel :=
          ⟨S.factorRawRightMesh_isWeakKernel K x,
            isRightMinimal_of_localEnd_of_ne_zero _ hf⟩ }

/-- A chosen zero object in the factor category. -/
def factorZeroObject (K : Set (Fin S.n)) : S.FactorCategory K :=
  (S.factorModuleFunctor K).obj
    (0 : RightModule.FinitelyGeneratedCategory A)

theorem factorZeroObject_isZero (K : Set (Fin S.n)) :
    IsZero (S.factorZeroObject K) :=
  (S.factorModuleFunctor K).map_isZero
    (isZero_zero (RightModule.FinitelyGeneratedCategory A))

/-- The raw quotient mesh with its left term replaced by a chosen zero
object. -/
def factorZeroLeftRightMesh
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ShortComplex (S.FactorCategory K) :=
  let T := S.factorRawRightMesh K x.1
  ShortComplex.mk (0 : S.factorZeroObject K ⟶ T.X₂) T.g (by simp)

/-- Replacing the left term by zero gives a right tau-sequence whenever the
raw source is zero or the raw first map vanishes. -/
theorem factorZeroLeftRightTau
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (hzero : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      (S.factorRawRightMesh K x.1).f = 0) :
    RightTauSequence (S.factorZeroLeftRightMesh K x) := by
  let T := S.factorRawRightMesh K x.1
  let Aτ := S.factorRawRightMesh_tauApproximation K x
  have hZ : IsZero (S.factorZeroObject K) := S.factorZeroObject_isZero K
  refine
    { f_radical := isRadicalMorphism_zero
      g_radical := Aτ.g_radical
      factors_from_left := ?_
      factors_into_right := Aτ.factors_into_right
      minimalWeakKernel := ?_ }
  · intro W a _ha
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := hZ.eq_of_src a 0
    rw [ha0]
    simp
  · constructor
    · rw [Iyama.ShortComplex.isWeakKernel_iff]
      intro W q hq
      obtain ⟨l, hl⟩ :=
        (Iyama.ShortComplex.isWeakKernel_iff T).1
          (S.factorRawRightMesh_isWeakKernel K x) q hq
      have hq0 : q = 0 := by
        rcases hzero with hsource | hf
        · have hl0 : l = 0 := hsource.eq_of_tgt l 0
          rw [hl0, zero_comp] at hl
          exact hl.symm
        · rw [hf, comp_zero] at hl
          exact hl.symm
      refine ⟨0, ?_⟩
      rw [hq0]
      simp
    · intro e _he
      have heq : e = 𝟙 _ := hZ.eq_of_src e (𝟙 _)
      rw [heq]
      infer_instance

/-- The minimal right mesh at a surviving quotient label. -/
def factorLabelRightMesh
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ShortComplex (S.FactorCategory K) := by
  classical
  by_cases h : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      (S.factorRawRightMesh K x.1).f = 0
  · exact S.factorZeroLeftRightMesh K x
  · exact S.factorRawRightMesh K x.1

/-- Every surviving-label factor mesh is a right tau-sequence. -/
theorem factorLabelRightTau
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    RightTauSequence (S.factorLabelRightMesh K x) := by
  classical
  by_cases h : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      (S.factorRawRightMesh K x.1).f = 0
  · simpa [factorLabelRightMesh, h] using S.factorZeroLeftRightTau K x h
  · simpa [factorLabelRightMesh, h] using
      S.factorRawRightTau_of_nonzero K x
        (fun hz ↦ h (Or.inl hz)) (fun hf ↦ h (Or.inr hf))

/-- The minimal factor right mesh still ends at its selected factor object. -/
theorem factorLabelRightMesh_X₃
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorLabelRightMesh K x).X₃ = S.factorObject K x := by
  classical
  by_cases h : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      (S.factorRawRightMesh K x.1).f = 0 <;>
    simp [factorLabelRightMesh, factorZeroLeftRightMesh, h,
      S.factorRawRightMesh_X₃ K x]

/-- Minimalizing the raw factor mesh changes only its left term; its middle
term remains the image of the ambient right-mesh middle term. -/
theorem factorLabelRightMesh_X₂
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorLabelRightMesh K x).X₂ =
      (S.factorRawRightMesh K x.1).X₂ := by
  classical
  by_cases h : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      (S.factorRawRightMesh K x.1).f = 0 <;>
    simp [factorLabelRightMesh, factorZeroLeftRightMesh, h]

/-- The surviving subtype inherits a finite enumeration from the ambient
finite skeleton. -/
noncomputable instance survivingLabelFintype (K : Set (Fin S.n)) :
    Fintype (S.SurvivingLabel K) :=
  Fintype.ofFinite _

/-- A chosen decomposition of a factor-category object into the surviving
indecomposable representatives. -/
structure ChosenFactorLabelDecomposition
    (K : Set (Fin S.n)) (X : S.FactorCategory K) where
  n : ℕ
  label : Fin n → S.SurvivingLabel K
  iso : X ≅ ⨁ fun i ↦ S.factorObject K (label i)

/-- Choose one surviving-label decomposition for every quotient object. -/
def chosenFactorLabelDecomposition
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    S.ChosenFactorLabelDecomposition K X := by
  let h := S.factorCategory_obj_decomposition K X
  let n := h.choose
  let label := h.choose_spec.choose
  let e := Classical.choice h.choose_spec.choose_spec
  exact { n := n, label := label, iso := e }

/-- Extend the surviving-label right meshes to every quotient object by
finite componentwise biproduct. -/
def factorRightMesh (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    ShortComplex (S.FactorCategory K) :=
  let d := S.chosenFactorLabelDecomposition K X
  shortComplexBiproduct
    (fun i : Fin d.n ↦ S.factorLabelRightMesh K (d.label i))

/-- The assembled factor right mesh ends at the supplied quotient object. -/
def factorRightTermIso (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    (S.factorRightMesh K X).X₃ ≅ X :=
  let d := S.chosenFactorLabelDecomposition K X
  (biproduct.mapIso fun i : Fin d.n ↦
      eqToIso (S.factorLabelRightMesh_X₃ K (d.label i))).trans
    d.iso.symm

/-- Every assembled quotient-object right mesh is a right tau-sequence. -/
theorem factorRightTau (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    RightTauSequence (S.factorRightMesh K X) := by
  let d := S.chosenFactorLabelDecomposition K X
  exact rightTauSequence_shortComplexBiproduct
    (S.factorNilpotentRadicalData K)
    (fun i : Fin d.n ↦ S.factorLabelRightMesh K (d.label i))
    (fun i ↦ S.factorLabelRightTau K (d.label i))

/-- The literal quotient by any selected labels carries all finite
right-tau-category data, with the surviving skeleton as its labels. -/
def factorFiniteRightTauCategoryData (K : Set (Fin S.n)) :
    FiniteRightTauCategoryData
      (S.FactorCategory K) (S.SurvivingLabel K) where
  obj := S.factorObject K
  obj_indec := S.factorObject_indecomposable K
  obj_end_local := S.factorObject_end_isLocalRing K
  obj_decomposition := S.factorCategory_obj_decomposition K
  obj_complete := S.factorCategory_obj_complete K
  obj_skeletal := S.factorObject_skeletal K
  radical := S.factorNilpotentRadicalData K
  rightMesh := S.factorRightMesh K
  rightTermIso := S.factorRightTermIso K
  rightTau := S.factorRightTau K

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
