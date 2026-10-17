import MBDVendor.Magnitude.Algebra.RightModuleFactorLeftTau

/-!
# Two-sided tau-data assembly for literal finite-module factor categories

The right and left factor meshes are made canonical on surviving selected
indecomposables.  The remaining declarations identify their nonzero
boundaries by restricting the ambient Auslander--Reiten translation and map
the ambient mesh isomorphisms through the literal quotient.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.Iyama
open scoped ModuleCat.Algebra ZeroObject

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Use the literal surviving-label right mesh on a selected factor object
and the componentwise construction otherwise. -/
def canonicalFactorRightMesh
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    ShortComplex (S.FactorCategory K) := by
  classical
  by_cases h : ∃ x : S.SurvivingLabel K, X = S.factorObject K x
  · exact S.factorLabelRightMesh K (Classical.choose h)
  · exact S.factorRightMesh K X

/-- The canonical factor right mesh ends at the supplied object. -/
def canonicalFactorRightTermIso
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    (S.canonicalFactorRightMesh K X).X₃ ≅ X := by
  classical
  by_cases h : ∃ x : S.SurvivingLabel K, X = S.factorObject K x
  · rw [canonicalFactorRightMesh]
    simp only [dif_pos h]
    let x := Classical.choose h
    exact (eqToIso (S.factorLabelRightMesh_X₃ K x)).trans
      (eqToIso (Classical.choose_spec h).symm)
  · rw [canonicalFactorRightMesh]
    simp only [dif_neg h]
    exact S.factorRightTermIso K X

/-- Every canonical factor right mesh is a right tau-sequence. -/
theorem canonicalFactorRightTau
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    RightTauSequence (S.canonicalFactorRightMesh K X) := by
  classical
  by_cases h : ∃ x : S.SurvivingLabel K, X = S.factorObject K x
  · simpa [canonicalFactorRightMesh, h] using
      S.factorLabelRightTau K (Classical.choose h)
  · simpa [canonicalFactorRightMesh, h] using S.factorRightTau K X

/-- On a surviving selected object, the canonical factor right mesh is its
literal label mesh. -/
theorem canonicalFactorRightMesh_at_label
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.canonicalFactorRightMesh K (S.factorObject K x) =
      S.factorLabelRightMesh K x := by
  classical
  let h : ∃ y : S.SurvivingLabel K,
      S.factorObject K x = S.factorObject K y := ⟨x, rfl⟩
  rw [canonicalFactorRightMesh]
  simp only [dif_pos h]
  apply congrArg (S.factorLabelRightMesh K)
  apply S.factorObject_skeletal K
  exact ⟨eqToIso (Classical.choose_spec h).symm⟩

/-- Use the literal surviving-label left mesh on a selected factor object
and the componentwise construction otherwise. -/
def canonicalFactorLeftMesh
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    ShortComplex (S.FactorCategory K) := by
  classical
  by_cases h : ∃ x : S.SurvivingLabel K, X = S.factorObject K x
  · exact S.factorLabelLeftMesh K (Classical.choose h)
  · exact S.factorLeftMesh K X

/-- The canonical factor left mesh starts at the supplied object. -/
def canonicalFactorLeftTermIso
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    (S.canonicalFactorLeftMesh K X).X₁ ≅ X := by
  classical
  by_cases h : ∃ x : S.SurvivingLabel K, X = S.factorObject K x
  · rw [canonicalFactorLeftMesh]
    simp only [dif_pos h]
    let x := Classical.choose h
    exact (eqToIso (S.factorLabelLeftMesh_X₁ K x)).trans
      (eqToIso (Classical.choose_spec h).symm)
  · rw [canonicalFactorLeftMesh]
    simp only [dif_neg h]
    exact S.factorLeftTermIso K X

/-- Every canonical factor left mesh is a left tau-sequence. -/
theorem canonicalFactorLeftTau
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    LeftTauSequence (S.canonicalFactorLeftMesh K X) := by
  classical
  by_cases h : ∃ x : S.SurvivingLabel K, X = S.factorObject K x
  · simpa [canonicalFactorLeftMesh, h] using
      S.factorLabelLeftTau K (Classical.choose h)
  · simpa [canonicalFactorLeftMesh, h] using S.factorLeftTau K X

/-- On a surviving selected object, the canonical factor left mesh is its
literal label mesh. -/
theorem canonicalFactorLeftMesh_at_label
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.canonicalFactorLeftMesh K (S.factorObject K x) =
      S.factorLabelLeftMesh K x := by
  classical
  let h : ∃ y : S.SurvivingLabel K,
      S.factorObject K x = S.factorObject K y := ⟨x, rfl⟩
  rw [canonicalFactorLeftMesh]
  simp only [dif_pos h]
  apply congrArg (S.factorLabelLeftMesh K)
  apply S.factorObject_skeletal K
  exact ⟨eqToIso (Classical.choose_spec h).symm⟩

/-- Mapping the ambient right/left mesh identification through the literal
quotient identifies the corresponding raw factor meshes. -/
def factorRawRightLeftMeshIso
    (K : Set (Fin S.n))
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.factorRawRightMesh K z.1 ≅
      S.factorRawLeftMesh K (S.rightTranslationEquiv z).1 := by
  let e : S.labelRightMesh z.1 ≅
      S.labelLeftMesh (S.rightTranslationEquiv z).1 :=
    (eqToIso (by
      simp [labelRightMesh, z.2])).trans
      (S.nonprojectiveRightMeshIso_labelLeftMesh z)
  exact (S.factorModuleFunctor K).mapShortComplex.mapIso e

/-- A nonzero canonical factor-right boundary is precisely in the raw branch
of the labelwise minimalization. -/
theorem factorRightBoundary_raw_condition
    (K : Set (Fin S.n))
    (X : {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁}) :
    ¬ IsZero (S.factorRawRightMesh K X.1.1).X₁ ∧
      (S.factorRawRightMesh K X.1.1).f ≠ 0 := by
  have hX := X.2
  rw [S.canonicalFactorRightMesh_at_label K X.1] at hX
  by_cases h : IsZero (S.factorRawRightMesh K X.1.1).X₁ ∨
      (S.factorRawRightMesh K X.1.1).f = 0
  · exfalso
    apply hX
    rw [factorLabelRightMesh]
    simp only [dif_pos h, factorZeroLeftRightMesh]
    exact S.factorZeroObject_isZero K
  · exact ⟨fun hz ↦ h (Or.inl hz), fun hf ↦ h (Or.inr hf)⟩

/-- A nonzero canonical factor-left boundary is precisely in the raw branch
of the labelwise minimalization. -/
theorem factorLeftBoundary_raw_condition
    (K : Set (Fin S.n))
    (Y : {y : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorLeftMesh K (S.factorObject K y)).X₃}) :
    ¬ IsZero (S.factorRawLeftMesh K Y.1.1).X₃ ∧
      (S.factorRawLeftMesh K Y.1.1).g ≠ 0 := by
  have hY := Y.2
  rw [S.canonicalFactorLeftMesh_at_label K Y.1] at hY
  by_cases h : IsZero (S.factorRawLeftMesh K Y.1.1).X₃ ∨
      (S.factorRawLeftMesh K Y.1.1).g = 0
  · exfalso
    apply hY
    rw [factorLabelLeftMesh]
    simp only [dif_pos h, factorZeroRightLeftMesh]
    exact S.factorZeroObject_isZero K
  · exact ⟨fun hz ↦ h (Or.inl hz), fun hg ↦ h (Or.inr hg)⟩

/-- In a surviving raw right mesh, a nonzero first map forces the second map
to remain nonzero. -/
theorem factorRawRightMesh_g_ne_zero
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (hsource : ¬ IsZero (S.factorRawRightMesh K x.1).X₁)
    (hf : (S.factorRawRightMesh K x.1).f ≠ 0) :
    (S.factorRawRightMesh K x.1).g ≠ 0 := by
  let T := S.factorRawRightMesh K x.1
  let Aτ := S.factorRawRightTau_of_nonzero K x hsource hf
  intro hg
  have hmiddle : ¬ IsZero T.X₂ :=
    Aτ.not_isZero_X₂_of_not_isZero_X₁ hsource
  apply hmiddle
  haveI : IsIso (0 : T.X₂ ⟶ T.X₂) :=
    Aτ.isRightMinimal_g 0 (by simp [hg])
  exact (IsZero.iff_isSplitEpi_eq_zero (0 : T.X₂ ⟶ T.X₂)).2 rfl

/-- In a surviving raw left mesh, a nonzero second map forces the first map
to remain nonzero. -/
theorem factorRawLeftMesh_f_ne_zero
    (K : Set (Fin S.n)) (y : S.SurvivingLabel K)
    (htarget : ¬ IsZero (S.factorRawLeftMesh K y.1).X₃)
    (hg : (S.factorRawLeftMesh K y.1).g ≠ 0) :
    (S.factorRawLeftMesh K y.1).f ≠ 0 := by
  let T := S.factorRawLeftMesh K y.1
  let Aτ := S.factorRawLeftTau_of_nonzero K y htarget hg
  have hmiddle : ¬ IsZero T.X₂ := by
    intro hzero
    have hg0 : T.g = 0 := hzero.eq_of_src T.g 0
    haveI : IsIso (0 : T.X₃ ⟶ T.X₃) :=
      Aτ.minimalWeakCokernel.2 0 (by simpa using hg0.symm)
    apply htarget
    exact (IsZero.iff_isSplitEpi_eq_zero (0 : T.X₃ ⟶ T.X₃)).2 rfl
  intro hf
  apply hmiddle
  haveI : IsIso (0 : T.X₂ ⟶ T.X₂) :=
    Aτ.isLeftMinimal_f 0 (by simp [hf])
  exact (IsZero.iff_isSplitEpi_eq_zero (0 : T.X₂ ⟶ T.X₂)).2 rfl

/-- Restrict ambient positive translation to a nonzero factor-right
boundary. -/
def factorRightBoundaryToLeft
    (K : Set (Fin S.n))
    (X : {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁}) :
    {y : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorLeftMesh K (S.factorObject K y)).X₃} := by
  let hraw := S.factorRightBoundary_raw_condition K X
  have hnp : ¬ Projective (S.fgObj X.1.1) := by
    intro hp
    apply hraw.1
    exact (S.factorModuleFunctor K).map_isZero
      ((S.labelRightMesh_X₁_isZero_iff_projective X.1.1).2 hp)
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨X.1.1, hnp⟩
  let y₀ : Fin S.n := (S.rightTranslationEquiv z).1
  have hy : y₀ ∉ K := by
    intro hyK
    let eT : (S.labelRightMesh X.1.1).X₁ ≅ S.fgObj y₀ := by
      simpa [labelRightMesh, hnp, nonprojectiveRightMesh, z, y₀,
        rightTranslationEquiv, rightTranslation] using
        S.rightTranslationKernelIso z
    let eQ : (S.factorRawRightMesh K X.1.1).X₁ ≅
        (S.factorModuleFunctor K).obj (S.fgObj y₀) :=
      (S.factorModuleFunctor K).mapIso eT
    have htarget : IsZero
        ((S.factorModuleFunctor K).obj (S.fgObj y₀)) :=
      (S.factorObject_isZero_of_mem K hyK).of_iso
        (S.factorAmbientPointIsoFactorModule K y₀)
    exact hraw.1 (htarget.of_iso eQ)
  let y : S.SurvivingLabel K := ⟨y₀, hy⟩
  refine ⟨y, ?_⟩
  let e := S.factorRawRightLeftMeshIso K z
  have hrightTarget : ¬ IsZero (S.factorRawRightMesh K X.1.1).X₃ := by
    rw [S.factorRawRightMesh_X₃ K X.1]
    exact S.factorObject_not_isZero K X.1
  have hleftTarget : ¬ IsZero (S.factorRawLeftMesh K y.1).X₃ := by
    intro hzero
    apply hrightTarget
    exact hzero.of_iso (ShortComplex.π₃.mapIso e)
  have hrightg : (S.factorRawRightMesh K X.1.1).g ≠ 0 :=
    S.factorRawRightMesh_g_ne_zero K X.1 hraw.1 hraw.2
  have hleftg : (S.factorRawLeftMesh K y.1).g ≠ 0 := by
    intro hg
    apply hrightg
    rw [← cancel_mono e.hom.τ₃]
    rw [← e.hom.comm₂₃, hg, comp_zero, zero_comp]
  rw [S.canonicalFactorLeftMesh_at_label K y]
  simpa [factorLabelLeftMesh, hleftTarget, hleftg] using hleftTarget

/-- Restrict ambient negative translation to a nonzero factor-left
boundary. -/
def factorLeftBoundaryToRight
    (K : Set (Fin S.n))
    (Y : {y : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorLeftMesh K (S.factorObject K y)).X₃}) :
    {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁} := by
  let hraw := S.factorLeftBoundary_raw_condition K Y
  have hni : ¬ Injective (S.fgObj Y.1.1) := by
    intro hi
    apply hraw.1
    exact (S.factorModuleFunctor K).map_isZero
      ((S.labelLeftMesh_X₃_isZero_iff_injective Y.1.1).2 hi)
  let y : {y : Fin S.n // ¬ Injective (S.fgObj y)} := ⟨Y.1.1, hni⟩
  let z := (S.rightTranslationEquiv).symm y
  let x₀ : Fin S.n := z.1
  have hx : x₀ ∉ K := by
    intro hxK
    let eT : (S.labelLeftMesh Y.1.1).X₃ ≅ S.fgObj x₀ := by
      convert Iso.refl (S.fgObj x₀) using 1
      simp [labelLeftMesh, hni, noninjectiveLeftMesh, y, z, x₀,
        almostSplitSkeleton]
    let eQ : (S.factorRawLeftMesh K Y.1.1).X₃ ≅
        (S.factorModuleFunctor K).obj (S.fgObj x₀) :=
      (S.factorModuleFunctor K).mapIso eT
    have htarget : IsZero
        ((S.factorModuleFunctor K).obj (S.fgObj x₀)) :=
      (S.factorObject_isZero_of_mem K hxK).of_iso
        (S.factorAmbientPointIsoFactorModule K x₀)
    exact hraw.1 (htarget.of_iso eQ)
  let x : S.SurvivingLabel K := ⟨x₀, hx⟩
  refine ⟨x, ?_⟩
  have hval : (S.rightTranslationEquiv z).1 = Y.1.1 := by
    exact congrArg Subtype.val (S.rightTranslationEquiv.apply_symm_apply y)
  let e : S.factorRawRightMesh K x.1 ≅
      S.factorRawLeftMesh K Y.1.1 :=
    (S.factorRawRightLeftMeshIso K z).trans
      (eqToIso (congrArg (S.factorRawLeftMesh K) hval))
  have hleftSource : ¬ IsZero (S.factorRawLeftMesh K Y.1.1).X₁ := by
    rw [S.factorRawLeftMesh_X₁ K Y.1]
    exact S.factorObject_not_isZero K Y.1
  have hrightSource : ¬ IsZero (S.factorRawRightMesh K x.1).X₁ := by
    intro hzero
    apply hleftSource
    exact hzero.of_iso (ShortComplex.π₁.mapIso e).symm
  have hleftf : (S.factorRawLeftMesh K Y.1.1).f ≠ 0 :=
    S.factorRawLeftMesh_f_ne_zero K Y.1 hraw.1 hraw.2
  have hrightf : (S.factorRawRightMesh K x.1).f ≠ 0 := by
    intro hf
    apply hleftf
    rw [← cancel_epi e.hom.τ₁]
    rw [e.hom.comm₁₂, hf, zero_comp, comp_zero]
  rw [S.canonicalFactorRightMesh_at_label K x]
  simpa [factorLabelRightMesh, hrightSource, hrightf] using hrightSource

/-- The underlying label of restricted positive factor translation is the
ambient positive translation label. -/
theorem factorRightBoundaryToLeft_val
    (K : Set (Fin S.n))
    (X : {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁}) :
    ∃ z : {z : Fin S.n // ¬ Projective (S.fgObj z)},
      z.1 = X.1.1 ∧
        (S.factorRightBoundaryToLeft K X).1.1 =
          (S.rightTranslationEquiv z).1 := by
  let hraw := S.factorRightBoundary_raw_condition K X
  have hnp : ¬ Projective (S.fgObj X.1.1) := by
    intro hp
    apply hraw.1
    exact (S.factorModuleFunctor K).map_isZero
      ((S.labelRightMesh_X₁_isZero_iff_projective X.1.1).2 hp)
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨X.1.1, hnp⟩
  refine ⟨z, rfl, ?_⟩
  rfl

/-- The underlying label of restricted negative factor translation is the
ambient negative translation label. -/
theorem factorLeftBoundaryToRight_val
    (K : Set (Fin S.n))
    (Y : {y : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorLeftMesh K (S.factorObject K y)).X₃}) :
    ∃ y : {y : Fin S.n // ¬ Injective (S.fgObj y)},
      y.1 = Y.1.1 ∧
        (S.factorLeftBoundaryToRight K Y).1.1 =
          ((S.rightTranslationEquiv).symm y).1 := by
  let hraw := S.factorLeftBoundary_raw_condition K Y
  have hni : ¬ Injective (S.fgObj Y.1.1) := by
    intro hi
    apply hraw.1
    exact (S.factorModuleFunctor K).map_isZero
      ((S.labelLeftMesh_X₃_isZero_iff_injective Y.1.1).2 hi)
  let y : {y : Fin S.n // ¬ Injective (S.fgObj y)} := ⟨Y.1.1, hni⟩
  refine ⟨y, rfl, ?_⟩
  rfl

/-- Positive and negative translation restrict to mutually inverse
equivalences on the nonzero boundaries of the canonical factor meshes. -/
def factorTauPlusEquiv (K : Set (Fin S.n)) :
    {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁} ≃
    {y : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorLeftMesh K (S.factorObject K y)).X₃} where
  toFun := S.factorRightBoundaryToLeft K
  invFun := S.factorLeftBoundaryToRight K
  left_inv := by
    intro X
    obtain ⟨z, hz, hto⟩ := S.factorRightBoundaryToLeft_val K X
    obtain ⟨y, hy, hinv⟩ :=
      S.factorLeftBoundaryToRight_val K
        (S.factorRightBoundaryToLeft K X)
    have hyz : y = S.rightTranslationEquiv z := by
      apply Subtype.ext
      exact hy.trans hto
    apply Subtype.ext
    apply Subtype.ext
    calc
      (S.factorLeftBoundaryToRight K
          (S.factorRightBoundaryToLeft K X)).1.1 =
          ((S.rightTranslationEquiv).symm y).1 := hinv
      _ = ((S.rightTranslationEquiv).symm
          (S.rightTranslationEquiv z)).1 := by rw [hyz]
      _ = z.1 := congrArg Subtype.val
        (S.rightTranslationEquiv.symm_apply_apply z)
      _ = X.1.1 := hz
  right_inv := by
    intro Y
    obtain ⟨y, hy, hinv⟩ := S.factorLeftBoundaryToRight_val K Y
    obtain ⟨z, hz, hto⟩ :=
      S.factorRightBoundaryToLeft_val K
        (S.factorLeftBoundaryToRight K Y)
    have hzy : z = (S.rightTranslationEquiv).symm y := by
      apply Subtype.ext
      exact hz.trans hinv
    apply Subtype.ext
    apply Subtype.ext
    calc
      (S.factorRightBoundaryToLeft K
          (S.factorLeftBoundaryToRight K Y)).1.1 =
          (S.rightTranslationEquiv z).1 := hto
      _ = (S.rightTranslationEquiv
          ((S.rightTranslationEquiv).symm y)).1 := by rw [hzy]
      _ = y.1 := congrArg Subtype.val
        (S.rightTranslationEquiv.apply_symm_apply y)
      _ = Y.1.1 := hy

/-- The canonical factor right mesh at a nonzero boundary agrees with the
canonical factor left mesh at its restricted translate. -/
def factorRightLeftMeshIso
    (K : Set (Fin S.n))
    (X : {x : S.SurvivingLabel K //
      ¬ IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁}) :
    S.canonicalFactorRightMesh K (S.factorObject K X.1) ≅
      S.canonicalFactorLeftMesh K
        (S.factorObject K ((S.factorTauPlusEquiv K X).1)) := by
  change S.canonicalFactorRightMesh K (S.factorObject K X.1) ≅
    S.canonicalFactorLeftMesh K
      (S.factorObject K (S.factorRightBoundaryToLeft K X).1)
  let Y := S.factorRightBoundaryToLeft K X
  let hright := S.factorRightBoundary_raw_condition K X
  let hleft := S.factorLeftBoundary_raw_condition K Y
  let hv := S.factorRightBoundaryToLeft_val K X
  let z := Classical.choose hv
  let hz := (Classical.choose_spec hv).1
  let hto := (Classical.choose_spec hv).2
  let eRaw : S.factorRawRightMesh K X.1.1 ≅
      S.factorRawLeftMesh K Y.1.1 :=
    (eqToIso (congrArg (S.factorRawRightMesh K) hz)).symm |>.trans
      ((S.factorRawRightLeftMeshIso K z).trans
        (eqToIso (congrArg (S.factorRawLeftMesh K) hto.symm)))
  have hcanonicalRight :
      S.canonicalFactorRightMesh K (S.factorObject K X.1) =
        S.factorRawRightMesh K X.1.1 := by
    calc
      S.canonicalFactorRightMesh K (S.factorObject K X.1) =
          S.factorLabelRightMesh K X.1 :=
        S.canonicalFactorRightMesh_at_label K X.1
      _ = S.factorRawRightMesh K X.1.1 := by
        simp [factorLabelRightMesh, hright.1, hright.2]
  have hcanonicalLeft :
      S.canonicalFactorLeftMesh K (S.factorObject K Y.1) =
        S.factorRawLeftMesh K Y.1.1 := by
    calc
      S.canonicalFactorLeftMesh K (S.factorObject K Y.1) =
          S.factorLabelLeftMesh K Y.1 :=
        S.canonicalFactorLeftMesh_at_label K Y.1
      _ = S.factorRawLeftMesh K Y.1.1 := by
        simp [factorLabelLeftMesh, hleft.1, hleft.2]
  exact (eqToIso hcanonicalRight).trans
    (eRaw.trans (eqToIso hcanonicalLeft).symm)

/-- Every literal quotient by selected labels carries compatible two-sided
finite tau-category data on its surviving skeleton. -/
def factorFiniteTauCategoryData (K : Set (Fin S.n)) :
    FiniteTauCategoryData
      (S.FactorCategory K) (S.SurvivingLabel K) where
  obj := S.factorObject K
  obj_indec := S.factorObject_indecomposable K
  obj_end_local := S.factorObject_end_isLocalRing K
  obj_decomposition := S.factorCategory_obj_decomposition K
  obj_complete := S.factorCategory_obj_complete K
  obj_skeletal := S.factorObject_skeletal K
  radical := S.factorNilpotentRadicalData K
  rightMesh := S.canonicalFactorRightMesh K
  rightTermIso := S.canonicalFactorRightTermIso K
  rightTau := S.canonicalFactorRightTau K
  leftMesh := S.canonicalFactorLeftMesh K
  leftTermIso := S.canonicalFactorLeftTermIso K
  leftTau := S.canonicalFactorLeftTau K
  tauPlusEquiv := S.factorTauPlusEquiv K
  rightLeftMeshIso := S.factorRightLeftMeshIso K

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
