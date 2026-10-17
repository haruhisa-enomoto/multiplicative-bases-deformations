import MBDVendor.Magnitude.Algebra.RightModuleFactorRightTau

/-!
# Left tau-sequences in literal finite-module factor categories

This file descends the chosen ambient left Auslander--Reiten meshes through
the literal quotient by maps factoring through selected labels.  It is the
left-right dual of the direct right-mesh descent, with an explicit quotient
weak-cokernel correction and minimalization of the possibly zero right
boundary.
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

/-- The literal image of the selected ambient left mesh in the factor
category. -/
def factorRawLeftMesh (K : Set (Fin S.n)) (x : Fin S.n) :
    ShortComplex (S.FactorCategory K) :=
  (S.labelLeftMesh x).map (S.factorModuleFunctor K)

/-- Both maps in the raw quotient left mesh remain radical. -/
theorem factorRawLeftMesh_radical
    (K : Set (Fin S.n)) (x : Fin S.n) :
    IsRadicalMorphism (S.factorRawLeftMesh K x).f ∧
      IsRadicalMorphism (S.factorRawLeftMesh K x).g := by
  let I := S.factorThroughSelectedIdeal K
  let Aτ := S.labelLeftTau x
  constructor
  · exact I.map_isRadicalMorphism _
      (S.selectedAdd_isRadicalMorphism_of_hom _ Aτ.f_radical)
  · exact I.map_isRadicalMorphism _
      (S.selectedAdd_isRadicalMorphism_of_hom _ Aτ.g_radical)

/-- The raw quotient left mesh at a surviving label starts at its literal
factor object. -/
theorem factorRawLeftMesh_X₁
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorRawLeftMesh K x.1).X₁ = S.factorObject K x := by
  change (S.factorModuleFunctor K).obj (S.labelLeftMesh x.1).X₁ =
    S.factorObject K x
  rw [S.labelLeftMesh_X₁]
  rfl

/-- Radical maps out of a surviving source factor through the raw quotient
left-mesh map. -/
theorem factorRawLeftMesh_factors_from_left
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ∀ {W : S.FactorCategory K}
      (a : (S.factorRawLeftMesh K x.1).X₁ ⟶ W),
      IsRadicalMorphism a →
        ∃ b : (S.factorRawLeftMesh K x.1).X₂ ⟶ W,
          (S.factorRawLeftMesh K x.1).f ≫ b = a := by
  let F := S.factorFunctor K
  let T := S.labelLeftMesh x.1
  let Aτ := S.labelLeftTau x.1
  intro W a ha
  obtain ⟨a', rfl⟩ := F.map_surjective a
  have hnot : ¬ IsSplitMono a'.hom := by
    intro hsplit
    letI : IsSplitMono a'.hom := hsplit
    let sm : SplitMono a' :=
      { retraction := ObjectProperty.homMk (retraction a'.hom)
        id := by
          apply ObjectProperty.hom_ext
          exact IsSplitMono.id a'.hom }
    have hz : IsZero (S.factorRawLeftMesh K x.1).X₁ :=
      isZero_source_of_radical_splitMono ha (sm.map F)
    rw [S.factorRawLeftMesh_X₁ K x] at hz
    exact S.factorObject_not_isZero K x hz
  let eX : T.X₁ ≅ S.fgObj x.1 := eqToIso (S.labelLeftMesh_X₁ x.1)
  let aX : S.fgObj x.1 ⟶ W.as.obj := eX.inv ≫ a'.hom
  have hnotX : ¬ IsSplitMono aX := by
    intro hsplit
    letI : IsSplitMono aX := hsplit
    letI : IsSplitMono eX.hom := inferInstance
    have hs : IsSplitMono (eX.hom ≫ aX) := inferInstance
    have heq : eX.hom ≫ aX = a'.hom := by simp [aX]
    exact hnot (heq ▸ hs)
  have haRad : IsRadicalMorphism a'.hom := by
    have haXRad : IsRadicalMorphism aX :=
      (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitMono_from_obj
        aX).2 hnotX
    have h := isRadicalMorphism_precomp eX.hom haXRad
    simpa [aX] using h
  obtain ⟨b, hb⟩ := Aτ.factors_from_left a'.hom haRad
  refine ⟨F.map (S.ambientAddFunctor.map b), ?_⟩
  change F.map (S.ambientAddFunctor.map T.f) ≫
      F.map (S.ambientAddFunctor.map b) = F.map a'
  rw [← F.map_comp]
  apply congrArg F.map
  apply ObjectProperty.hom_ext
  exact hb

/-- Radical maps into the raw quotient left mesh's right endpoint factor
through its second map. -/
theorem factorRawLeftMesh_factors_into_right
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ∀ {W : S.FactorCategory K}
      (a : W ⟶ (S.factorRawLeftMesh K x.1).X₃),
      IsRadicalMorphism a →
        ∃ b : W ⟶ (S.factorRawLeftMesh K x.1).X₂,
          b ≫ (S.factorRawLeftMesh K x.1).g = a := by
  let F := S.factorFunctor K
  let T := S.labelLeftMesh x.1
  let Aτ := S.labelLeftTau x.1
  intro W a ha
  classical
  by_cases hx : Injective (S.fgObj x.1)
  · have hT₃ : IsZero T.X₃ :=
      (S.labelLeftMesh_X₃_isZero_iff_injective x.1).2 hx
    have hQ₃ : IsZero (S.factorRawLeftMesh K x.1).X₃ :=
      (S.factorModuleFunctor K).map_isZero hT₃
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := hQ₃.eq_of_tgt a 0
    rw [ha0]
    simp
  · let z : {z : Fin S.n // ¬ Injective (S.fgObj z)} := ⟨x.1, hx⟩
    let y := (S.rightTranslationEquiv).symm z
    let y₀ : Fin S.n := y.1
    let eT : T.X₃ ≅ S.fgObj y₀ := by
      convert Iso.refl (S.fgObj y₀) using 1
      simp [T, labelLeftMesh, hx, noninjectiveLeftMesh, y, y₀, z,
        almostSplitSkeleton]
    let eQ : (S.factorRawLeftMesh K x.1).X₃ ≅
        (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
      (S.factorModuleFunctor K).mapIso eT
    by_cases hy : y₀ ∈ K
    · have htarget : IsZero
          ((S.factorModuleFunctor K).obj (S.fgObj y₀)) :=
        (S.factorObject_isZero_of_mem K hy).of_iso
          (S.factorAmbientPointIsoFactorModule K y₀)
      have hQ₃ : IsZero (S.factorRawLeftMesh K x.1).X₃ :=
        htarget.of_iso eQ
      refine ⟨0, ?_⟩
      have ha0 : a = 0 := hQ₃.eq_of_tgt a 0
      rw [ha0]
      simp
    · let sy : S.SurvivingLabel K := ⟨y₀, hy⟩
      obtain ⟨a', rfl⟩ := F.map_surjective a
      have hnot : ¬ IsSplitEpi a'.hom := by
        intro hsplit
        letI : IsSplitEpi a'.hom := hsplit
        let se : SplitEpi a' :=
          { section_ := ObjectProperty.homMk (section_ a'.hom)
            id := by
              apply ObjectProperty.hom_ext
              exact IsSplitEpi.id a'.hom }
        have hz : IsZero (S.factorRawLeftMesh K x.1).X₃ :=
          isZero_target_of_radical_splitEpi ha (se.map F)
        have hyzero : IsZero (S.factorObject K sy) := by
          apply hz.of_iso
          exact (eQ.trans (eqToIso (by rfl))).symm
        exact S.factorObject_not_isZero K sy hyzero
      let aY : W.as.obj ⟶ S.fgObj y₀ := a'.hom ≫ eT.hom
      have hnotY : ¬ IsSplitEpi aY := by
        intro hsplit
        letI : IsSplitEpi aY := hsplit
        letI : IsSplitEpi eT.inv := inferInstance
        have hs : IsSplitEpi (aY ≫ eT.inv) := inferInstance
        have heq : aY ≫ eT.inv = a'.hom := by simp [aY]
        exact hnot (heq ▸ hs)
      have haRad : IsRadicalMorphism a'.hom := by
        have haYRad : IsRadicalMorphism aY :=
          (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
            aY).2 hnotY
        have hr := isRadicalMorphism_postcomp eT.inv haYRad
        simpa [aY] using hr
      obtain ⟨b, hb⟩ := Aτ.factors_into_right a'.hom haRad
      refine ⟨F.map (S.ambientAddFunctor.map b), ?_⟩
      change F.map (S.ambientAddFunctor.map b) ≫
          F.map (S.ambientAddFunctor.map T.g) = F.map a'
      rw [← F.map_comp]
      apply congrArg F.map
      apply ObjectProperty.hom_ext
      exact hb

/-- The raw quotient left mesh retains the weak-cokernel property. -/
theorem factorRawLeftMesh_isWeakCokernel
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Iyama.ShortComplex.IsWeakCokernel (S.factorRawLeftMesh K x.1) := by
  let I := S.factorThroughSelectedIdeal K
  let F := S.factorFunctor K
  let T := S.labelLeftMesh x.1
  let Aτ := S.labelLeftTau x.1
  rw [Iyama.ShortComplex.isWeakCokernel_iff]
  intro W q hq
  obtain ⟨q', rfl⟩ := F.map_surjective q
  let fAdd := S.ambientAddFunctor.map T.f
  have hqmap : F.map (fAdd ≫ q') = 0 := by
    change F.map fAdd ≫ F.map q' = 0 at hq
    simpa only [← F.map_comp] using hq
  have hfac := (I.map_eq_zero_iff (fAdd ≫ q')).1 hqmap
  rcases hfac with ⟨M, hM, left, right, hcomp⟩
  have hleftNot : ¬ IsSplitMono left := by
    intro hsplit
    letI : IsSplitMono left := hsplit
    let eX : T.X₁ ≅ S.fgObj x.1 := eqToIso (S.labelLeftMesh_X₁ x.1)
    let rt : Retract (S.fgObj x.1) M :=
      { i := eX.inv ≫ left
        r := retraction left ≫ eX.hom
        retract := by simp }
    exact x.2
      (S.almostSplitSkeleton.index_mem_of_retract_inAdd rt hM)
  let eX : T.X₁ ≅ S.fgObj x.1 := eqToIso (S.labelLeftMesh_X₁ x.1)
  let leftX : S.fgObj x.1 ⟶ M := eX.inv ≫ left
  have hleftXNot : ¬ IsSplitMono leftX := by
    intro hsplit
    letI : IsSplitMono leftX := hsplit
    letI : IsSplitMono eX.hom := inferInstance
    have hs : IsSplitMono (eX.hom ≫ leftX) := inferInstance
    have heq : eX.hom ≫ leftX = left := by simp [leftX]
    exact hleftNot (heq ▸ hs)
  have hleftRad : IsRadicalMorphism left := by
    have hlX : IsRadicalMorphism leftX :=
      (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitMono_from_obj
        leftX).2 hleftXNot
    have hl := isRadicalMorphism_precomp eX.hom hlX
    simpa [leftX] using hl
  obtain ⟨v, hv⟩ := Aτ.factors_from_left left hleftRad
  let q₀ : T.X₂ ⟶ W.as.obj := q'.hom - v ≫ right
  have hq₀ : T.f ≫ q₀ = 0 := by
    dsimp only [q₀]
    rw [Preadditive.comp_sub, ← Category.assoc, hv]
    have hc : left ≫ right = T.f ≫ q'.hom := by
      change left ≫ right = T.f ≫ q'.hom at hcomp
      exact hcomp
    rw [hc, sub_self]
  obtain ⟨l, hl⟩ :=
    (Iyama.ShortComplex.isWeakCokernel_iff T).1
      Aτ.minimalWeakCokernel.1 q₀ hq₀
  refine ⟨F.map (S.ambientAddFunctor.map l), ?_⟩
  change F.map (S.ambientAddFunctor.map T.g) ≫
      F.map (S.ambientAddFunctor.map l) = F.map q'
  rw [← F.map_comp, ← sub_eq_zero, ← F.map_sub]
  apply (I.map_eq_zero_iff _).2
  refine ⟨M, hM, v, -right, ?_⟩
  change v ≫ (-right) = (T.g ≫ l) - q'.hom
  rw [hl]
  dsimp only [q₀]
  simp

/-- The raw quotient left mesh satisfies the radical approximation part of a
left tau-sequence. -/
theorem factorRawLeftMesh_tauApproximation
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    TauApproximation (S.factorRawLeftMesh K x.1) where
  f_radical := (S.factorRawLeftMesh_radical K x.1).1
  g_radical := (S.factorRawLeftMesh_radical K x.1).2
  factors_from_left := S.factorRawLeftMesh_factors_from_left K x
  factors_into_right := S.factorRawLeftMesh_factors_into_right K x

/-- The target of a raw quotient left mesh is either zero or isomorphic to a
surviving selected indecomposable. -/
theorem factorRawLeftMesh_X₃_zero_or_exists_factorObject_iso
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
      ∃ y : S.SurvivingLabel K,
        Nonempty ((S.factorRawLeftMesh K x.1).X₃ ≅
          S.factorObject K y) := by
  classical
  let T := S.labelLeftMesh x.1
  by_cases hx : Injective (S.fgObj x.1)
  · left
    exact (S.factorModuleFunctor K).map_isZero
      ((S.labelLeftMesh_X₃_isZero_iff_injective x.1).2 hx)
  · let z : {z : Fin S.n // ¬ Injective (S.fgObj z)} := ⟨x.1, hx⟩
    let y := (S.rightTranslationEquiv).symm z
    let y₀ : Fin S.n := y.1
    let eT : T.X₃ ≅ S.fgObj y₀ := by
      convert Iso.refl (S.fgObj y₀) using 1
      simp [T, labelLeftMesh, hx, noninjectiveLeftMesh, y, y₀, z,
        almostSplitSkeleton]
    let eQ : (S.factorRawLeftMesh K x.1).X₃ ≅
        (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
      (S.factorModuleFunctor K).mapIso eT
    by_cases hy : y₀ ∈ K
    · left
      have htarget : IsZero
          ((S.factorModuleFunctor K).obj (S.fgObj y₀)) :=
        (S.factorObject_isZero_of_mem K hy).of_iso
          (S.factorAmbientPointIsoFactorModule K y₀)
      exact htarget.of_iso eQ
    · right
      let sy : S.SurvivingLabel K := ⟨y₀, hy⟩
      exact ⟨sy, ⟨eQ.trans (eqToIso (by rfl))⟩⟩

/-- If an ambient label is noninjective and its inverse right translate
survives, then the target of its raw quotient left mesh is nonzero. -/
theorem factorRawLeftMesh_X₃_not_isZero_of_inverse_translation_survives
    (K : Set (Fin S.n)) (x : Fin S.n)
    (hx : ¬ Injective (S.fgObj x))
    (hy : ((S.rightTranslationEquiv).symm
      (⟨x, hx⟩ : {y : Fin S.n // ¬ Injective (S.fgObj y)})).1 ∉ K) :
    ¬ IsZero (S.factorRawLeftMesh K x).X₃ := by
  let z : {z : Fin S.n // ¬ Injective (S.fgObj z)} := ⟨x, hx⟩
  let y := (S.rightTranslationEquiv).symm z
  let y₀ : Fin S.n := y.1
  let T := S.labelLeftMesh x
  let eT : T.X₃ ≅ S.fgObj y₀ := by
    convert Iso.refl (S.fgObj y₀) using 1
    simp [T, labelLeftMesh, hx, noninjectiveLeftMesh, y, y₀, z,
      almostSplitSkeleton]
  let eQ : (S.factorRawLeftMesh K x).X₃ ≅
      (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
    (S.factorModuleFunctor K).mapIso eT
  let sy : S.SurvivingLabel K := ⟨y₀, by simpa [z, y, y₀] using hy⟩
  intro hzero
  apply S.factorObject_not_isZero K sy
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

private theorem isLeftMinimal_of_localEnd_of_ne_zero
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    {X Y : C} [IsLocalRing (End Y)] (f : X ⟶ Y) (hf : f ≠ 0) :
    IsLeftMinimal f := by
  intro e he
  have hsum : IsUnit (End.of e + (1 - End.of e)) := by
    rw [add_sub_cancel]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with heUnit | hsubUnit
  · exact (isUnit_iff_isIso (End.of e)).1 heUnit
  · have hsubIso : IsIso (𝟙 Y - e) :=
      (isUnit_iff_isIso (1 - End.of e)).1 hsubUnit
    letI : IsIso (𝟙 Y - e) := hsubIso
    have hzero : f ≫ (𝟙 Y - e) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id, he, sub_self]
    exfalso
    apply hf
    apply (cancel_mono (𝟙 Y - e)).1
    simpa using hzero

/-- If its target and second map survive, the raw quotient left mesh is
already a left tau-sequence. -/
theorem factorRawLeftTau_of_nonzero
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (htarget : ¬ IsZero (S.factorRawLeftMesh K x.1).X₃)
    (hg : (S.factorRawLeftMesh K x.1).g ≠ 0) :
    LeftTauSequence (S.factorRawLeftMesh K x.1) := by
  rcases S.factorRawLeftMesh_X₃_zero_or_exists_factorObject_iso K x with
    hzero | ⟨y, ⟨e⟩⟩
  · exact (htarget hzero).elim
  · letI : IsLocalRing (End (S.factorObject K y)) :=
      S.factorObject_end_isLocalRing K y
    letI : IsLocalRing (End (S.factorRawLeftMesh K x.1).X₃) :=
      MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
        (endRingEquivOfIso e).symm
    exact
      { toTauApproximation := S.factorRawLeftMesh_tauApproximation K x
        minimalWeakCokernel :=
          ⟨S.factorRawLeftMesh_isWeakCokernel K x,
            isLeftMinimal_of_localEnd_of_ne_zero _ hg⟩ }

/-- The raw quotient left mesh with its right term replaced by the chosen
zero object. -/
def factorZeroRightLeftMesh
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ShortComplex (S.FactorCategory K) :=
  let T := S.factorRawLeftMesh K x.1
  ShortComplex.mk T.f (0 : T.X₂ ⟶ S.factorZeroObject K) (by simp)

/-- Replacing the right term by zero gives a left tau-sequence whenever the
raw target is zero or the raw second map vanishes. -/
theorem factorZeroRightLeftTau
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (hzero : IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
      (S.factorRawLeftMesh K x.1).g = 0) :
    LeftTauSequence (S.factorZeroRightLeftMesh K x) := by
  let T := S.factorRawLeftMesh K x.1
  let Aτ := S.factorRawLeftMesh_tauApproximation K x
  have hZ : IsZero (S.factorZeroObject K) := S.factorZeroObject_isZero K
  refine
    { f_radical := Aτ.f_radical
      g_radical := isRadicalMorphism_zero
      factors_from_left := Aτ.factors_from_left
      factors_into_right := ?_
      minimalWeakCokernel := ?_ }
  · intro W a _ha
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := hZ.eq_of_tgt a 0
    rw [ha0]
    simp
  · constructor
    · rw [Iyama.ShortComplex.isWeakCokernel_iff]
      intro W q hq
      obtain ⟨l, hl⟩ :=
        (Iyama.ShortComplex.isWeakCokernel_iff T).1
          (S.factorRawLeftMesh_isWeakCokernel K x) q hq
      have hq0 : q = 0 := by
        rcases hzero with htarget | hg
        · have hl0 : l = 0 := htarget.eq_of_src l 0
          rw [hl0, comp_zero] at hl
          exact hl.symm
        · rw [hg, zero_comp] at hl
          exact hl.symm
      refine ⟨0, ?_⟩
      rw [hq0]
      simp
    · intro e _he
      have heq : e = 𝟙 _ := hZ.eq_of_src e (𝟙 _)
      rw [heq]
      infer_instance

/-- The minimal left mesh at a surviving quotient label. -/
def factorLabelLeftMesh
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ShortComplex (S.FactorCategory K) := by
  classical
  by_cases h : IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
      (S.factorRawLeftMesh K x.1).g = 0
  · exact S.factorZeroRightLeftMesh K x
  · exact S.factorRawLeftMesh K x.1

/-- Every surviving-label factor left mesh is a left tau-sequence. -/
theorem factorLabelLeftTau
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    LeftTauSequence (S.factorLabelLeftMesh K x) := by
  classical
  by_cases h : IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
      (S.factorRawLeftMesh K x.1).g = 0
  · simpa [factorLabelLeftMesh, h] using S.factorZeroRightLeftTau K x h
  · simpa [factorLabelLeftMesh, h] using
      S.factorRawLeftTau_of_nonzero K x
        (fun hz ↦ h (Or.inl hz)) (fun hg ↦ h (Or.inr hg))

/-- The minimal factor left mesh still starts at its selected factor object. -/
theorem factorLabelLeftMesh_X₁
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorLabelLeftMesh K x).X₁ = S.factorObject K x := by
  classical
  by_cases h : IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
      (S.factorRawLeftMesh K x.1).g = 0 <;>
    simp [factorLabelLeftMesh, factorZeroRightLeftMesh, h,
      S.factorRawLeftMesh_X₁ K x]

/-- Extend the surviving-label left meshes to every quotient object by
finite componentwise biproduct. -/
def factorLeftMesh (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    ShortComplex (S.FactorCategory K) :=
  let d := S.chosenFactorLabelDecomposition K X
  shortComplexBiproduct
    (fun i : Fin d.n ↦ S.factorLabelLeftMesh K (d.label i))

/-- The assembled factor left mesh starts at the supplied quotient object. -/
def factorLeftTermIso (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    (S.factorLeftMesh K X).X₁ ≅ X :=
  let d := S.chosenFactorLabelDecomposition K X
  (biproduct.mapIso fun i : Fin d.n ↦
      eqToIso (S.factorLabelLeftMesh_X₁ K (d.label i))).trans
    d.iso.symm

/-- Every assembled quotient-object left mesh is a left tau-sequence. -/
theorem factorLeftTau (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    LeftTauSequence (S.factorLeftMesh K X) := by
  let d := S.chosenFactorLabelDecomposition K X
  exact leftTauSequence_shortComplexBiproduct
    (S.factorNilpotentRadicalData K)
    (fun i : Fin d.n ↦ S.factorLabelLeftMesh K (d.label i))
    (fun i ↦ S.factorLabelLeftTau K (d.label i))

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
