module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import MBDVendor.QSE.CategoryTheory.IyamaTauBiproduct
public import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Finite tau-category data for Iyama's extraction theorem

This file records the finite Krull--Schmidt skeleton, chosen right and left
tau-sequences, nilpotent radical, and mesh compatibility needed to state
Iyama's Nakayama-pair extraction theorem.  It then proves that the left-mesh
form of that theorem formally implies the right-mesh form.

The relation `NakayamaPair` remains an external parameter here.  Its genuine
definition by finite invertible ladders belongs to the next layer.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w x

/-- An idempotent-complete finite Krull--Schmidt skeleton equipped with chosen
right tau-sequences.

The chosen categorical radical is globally aligned with
`CategoricalRadical.IsRadicalMorphism` and nilpotent.  Nilpotence is stronger
than the separated-radical hypothesis in Iyama's general theorem, but is the
finite input intended for the manuscript's acyclic word mesh category. -/
structure FiniteRightTauCategoryData
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C]
    [IsIdempotentComplete C]
    (Ind : Type w) [Fintype Ind] where
  /-- Chosen representative of an indecomposable label. -/
  obj : Ind → C
  /-- Every chosen representative is indecomposable. -/
  obj_indec : ∀ A : Ind, Indecomposable (obj A)
  /-- The chosen representatives have local endomorphism rings. -/
  obj_end_local : ∀ A : Ind, IsLocalRing (End (obj A))
  /-- Every object is a finite biproduct of chosen representatives. -/
  obj_decomposition :
    ∀ X : C, ∃ (n : ℕ) (label : Fin n → Ind),
      Nonempty (X ≅ ⨁ fun i ↦ obj (label i))
  /-- The labels contain every indecomposable object up to isomorphism. -/
  obj_complete :
    ∀ (X : C), Indecomposable X →
      ∃ A : Ind, Nonempty (X ≅ obj A)
  /-- Distinct labels do not represent isomorphic objects. -/
  obj_skeletal :
    ∀ {A B : Ind}, Nonempty (obj A ≅ obj B) → A = B
  /-- A nilpotent Hom ideal realizing the categorical radical. -/
  radical : CategoricalRadical.NilpotentRadicalData C
  /-- Chosen right mesh ending at every object. -/
  rightMesh : C → ShortComplex C
  /-- The right endpoint really is the supplied object. -/
  rightTermIso : ∀ X : C, (rightMesh X).X₃ ≅ X
  /-- Every chosen right mesh is a right tau-sequence. -/
  rightTau : ∀ X : C, RightTauSequence (rightMesh X)

/-- A finite right tau-category together with compatible chosen left
tau-sequences and the two-sided Auslander--Reiten translation. -/
structure FiniteTauCategoryData
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C]
    [IsIdempotentComplete C]
    (Ind : Type w) [Fintype Ind]
    extends FiniteRightTauCategoryData C Ind where
  /-- Chosen left mesh starting at every object. -/
  leftMesh : C → ShortComplex C
  /-- The left endpoint really is the supplied object. -/
  leftTermIso : ∀ A : C, (leftMesh A).X₁ ≅ A
  /-- Every chosen left mesh is a left tau-sequence. -/
  leftTau : ∀ A : C, LeftTauSequence (leftMesh A)
  /-- Positive and negative translation are mutually inverse between the
  nonprojective and noninjective indecomposable labels. -/
  tauPlusEquiv :
    {X : Ind // ¬ IsZero (rightMesh (obj X)).X₁} ≃
      {A : Ind // ¬ IsZero (leftMesh (obj A)).X₃}
  /-- Iyama's compatibility `(X] ≅ [tauPlus X)` between the chosen right and
  left meshes. -/
  rightLeftMeshIso :
    ∀ X : {X : Ind // ¬ IsZero (rightMesh (obj X)).X₁},
      rightMesh (obj X.1) ≅ leftMesh (obj ((tauPlusEquiv X).1))

/-- A two-sided finite tau-category structure extending fixed chosen right
tau-category data.  This is the source-faithful interface for results, such
as Iyama, *Tau-categories II*, 1.4(2), which promote an ideal quotient with
specified right meshes to a tau-category. -/
structure FiniteTauCategoryExtension
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C]
    [IsIdempotentComplete C]
    {Ind : Type w} [Fintype Ind]
    (T : FiniteRightTauCategoryData C Ind) where
  data : FiniteTauCategoryData C Ind
  right_eq : data.toFiniteRightTauCategoryData = T

instance {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C]
    [IsIdempotentComplete C]
    {Ind : Type w} [Fintype Ind] :
    Coe (FiniteTauCategoryData C Ind) (FiniteRightTauCategoryData C Ind) :=
  ⟨FiniteTauCategoryData.toFiniteRightTauCategoryData⟩

namespace FiniteRightTauCategoryData

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteRightTauCategoryData C Ind)

/-- The chosen right mesh of an object is, up to isomorphism, the
componentwise biproduct of the chosen right meshes in any displayed finite
biproduct decomposition of that object. -/
theorem nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
    {J : Type x} [Fintype J] (F : J → C) (X : C)
    (e : X ≅ ⨁ F) :
    Nonempty
      (T.rightMesh X ≅
        shortComplexBiproduct (fun j ↦ T.rightMesh (F j))) := by
  apply RightTauSequence.nonempty_iso_of_iso_X₃
    (T.rightTau X)
    (rightTauSequence_shortComplexBiproduct T.radical
      (fun j ↦ T.rightMesh (F j)) (fun j ↦ T.rightTau (F j)))
  exact (T.rightTermIso X).trans
    (e.trans
      (biproduct.mapIso (fun j ↦ T.rightTermIso (F j))).symm)

/-- The chosen right mesh commutes with every finite biproduct, up to a
nonempty type of isomorphisms of short complexes. -/
theorem nonempty_rightMesh_biproduct_iso
    {J : Type x} [Fintype J] (F : J → C) :
    Nonempty
      (T.rightMesh (⨁ F) ≅
        shortComplexBiproduct (fun j ↦ T.rightMesh (F j))) :=
  T.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso F (⨁ F) (Iso.refl _)

/-- Every recorded indecomposable decomposition of an object induces the
corresponding decomposition of its chosen right mesh. -/
theorem exists_rightMesh_decomposition (X : C) :
    ∃ (n : ℕ) (label : Fin n → Ind),
      Nonempty
        (T.rightMesh X ≅
          shortComplexBiproduct
            (fun i ↦ T.rightMesh (T.obj (label i)))) := by
  obtain ⟨n, label, ⟨e⟩⟩ := T.obj_decomposition X
  exact ⟨n, label,
    T.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
      (fun i ↦ T.obj (label i)) X e⟩

end FiniteRightTauCategoryData

namespace FiniteTauCategoryData

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- The chosen right mesh of an object is, up to isomorphism, the
componentwise biproduct of the chosen right meshes in any displayed finite
biproduct decomposition of that object. -/
theorem nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
    {J : Type x} [Fintype J] (F : J → C) (X : C)
    (e : X ≅ ⨁ F) :
    Nonempty
      (T.rightMesh X ≅
        shortComplexBiproduct (fun j ↦ T.rightMesh (F j))) := by
  apply RightTauSequence.nonempty_iso_of_iso_X₃
    (T.rightTau X)
    (rightTauSequence_shortComplexBiproduct T.radical
      (fun j ↦ T.rightMesh (F j)) (fun j ↦ T.rightTau (F j)))
  exact (T.rightTermIso X).trans
    (e.trans
      (biproduct.mapIso (fun j ↦ T.rightTermIso (F j))).symm)

/-- The chosen right mesh commutes with every finite biproduct, up to a
nonempty type of isomorphisms of short complexes. -/
theorem nonempty_rightMesh_biproduct_iso
    {J : Type x} [Fintype J] (F : J → C) :
    Nonempty
      (T.rightMesh (⨁ F) ≅
        shortComplexBiproduct (fun j ↦ T.rightMesh (F j))) :=
  FiniteTauCategoryData.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
    T F (⨁ F) (Iso.refl _)

/-- Every recorded indecomposable decomposition of an object induces the
corresponding decomposition of its chosen right mesh. -/
theorem exists_rightMesh_decomposition (X : C) :
    ∃ (n : ℕ) (label : Fin n → Ind),
      Nonempty
        (T.rightMesh X ≅
          shortComplexBiproduct
            (fun i ↦ T.rightMesh (T.obj (label i)))) := by
  obtain ⟨n, label, ⟨e⟩⟩ := T.obj_decomposition X
  exact ⟨n, label,
    FiniteTauCategoryData.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso T
      (fun i ↦ T.obj (label i)) X e⟩

/-- The chosen left mesh of an object is, up to isomorphism, the
componentwise biproduct of the chosen left meshes in any displayed finite
biproduct decomposition of that object. -/
theorem nonempty_leftMesh_iso_shortComplexBiproduct_of_iso
    {J : Type x} [Fintype J] (F : J → C) (X : C)
    (e : X ≅ ⨁ F) :
    Nonempty
      (T.leftMesh X ≅
        shortComplexBiproduct (fun j ↦ T.leftMesh (F j))) := by
  apply LeftTauSequence.nonempty_iso_of_iso_X₁
    (T.leftTau X)
    (leftTauSequence_shortComplexBiproduct T.radical
      (fun j ↦ T.leftMesh (F j)) (fun j ↦ T.leftTau (F j)))
  exact (T.leftTermIso X).trans
    (e.trans
      (biproduct.mapIso (fun j ↦ T.leftTermIso (F j))).symm)

/-- The chosen left mesh commutes with every finite biproduct, up to a
nonempty type of isomorphisms of short complexes. -/
theorem nonempty_leftMesh_biproduct_iso
    {J : Type x} [Fintype J] (F : J → C) :
    Nonempty
      (T.leftMesh (⨁ F) ≅
        shortComplexBiproduct (fun j ↦ T.leftMesh (F j))) :=
  T.nonempty_leftMesh_iso_shortComplexBiproduct_of_iso F (⨁ F) (Iso.refl _)

/-- Every recorded indecomposable decomposition of an object induces the
corresponding decomposition of its chosen left mesh. -/
theorem exists_leftMesh_decomposition (X : C) :
    ∃ (n : ℕ) (label : Fin n → Ind),
      Nonempty
        (T.leftMesh X ≅
          shortComplexBiproduct
            (fun i ↦ T.leftMesh (T.obj (label i)))) := by
  obtain ⟨n, label, ⟨e⟩⟩ := T.obj_decomposition X
  exact ⟨n, label,
    T.nonempty_leftMesh_iso_shortComplexBiproduct_of_iso
      (fun i ↦ T.obj (label i)) X e⟩

/-- Projective labels are exactly those whose right mesh has zero left term. -/
abbrev IsProjective (X : Ind) : Prop :=
  IsZero (T.rightMesh (T.obj X)).X₁

/-- The finite type of nonprojective labels. -/
abbrev Nonprojective : Type w :=
  {X : Ind // ¬ T.IsProjective X}

/-- Injective labels are exactly those whose left mesh has zero right term. -/
abbrev IsInjective (A : Ind) : Prop :=
  IsZero (T.leftMesh (T.obj A)).X₃

/-- The finite type of noninjective labels. -/
abbrev Noninjective : Type w :=
  {A : Ind // ¬ T.IsInjective A}

/-- An object is supported on nonprojectives when it has a finite biproduct
decomposition using only nonprojective labels.  The zero object is allowed
through the empty decomposition. -/
def SupportedOnNonprojectives (Y : C) : Prop :=
  ∃ (n : ℕ) (label : Fin n → Ind),
    Nonempty (Y ≅ ⨁ fun i ↦ T.obj (label i)) ∧
      ∀ i : Fin n, ¬ T.IsProjective (label i)

/-- Positive translation on a nonprojective label. -/
abbrev tauPlus (X : T.Nonprojective) : Ind :=
  (T.tauPlusEquiv X).1

/-- Negative translation on a noninjective label. -/
abbrev tauMinus (A : T.Noninjective) : Ind :=
  (T.tauPlusEquiv.symm A).1

/-- Positive and negative translation cancel on nonprojective labels. -/
@[simp]
theorem tauMinus_tauPlus (X : T.Nonprojective) :
    T.tauMinus (T.tauPlusEquiv X) = X.1 := by
  change (T.tauPlusEquiv.symm (T.tauPlusEquiv X)).1 = X.1
  rw [T.tauPlusEquiv.symm_apply_apply]

/-- Negative and positive translation cancel on noninjective labels. -/
@[simp]
theorem tauPlus_tauMinus (A : T.Noninjective) :
    T.tauPlus (T.tauPlusEquiv.symm A) = A.1 := by
  change (T.tauPlusEquiv (T.tauPlusEquiv.symm A)).1 = A.1
  rw [T.tauPlusEquiv.apply_symm_apply]

/-- The left term of a nonprojective right mesh is the chosen representative
of its positive translate.  This identification is derived from mesh
compatibility, rather than stored as a second potentially incoherent choice. -/
def tauPlusIso (X : T.Nonprojective) :
    (T.rightMesh (T.obj X.1)).X₁ ≅ T.obj (T.tauPlus X) :=
  (ShortComplex.π₁.mapIso (T.rightLeftMeshIso X)).trans
    (T.leftTermIso (T.obj (T.tauPlus X)))

/-- Compatibility read in the reverse direction: the left mesh at a
noninjective label is the right mesh at its negative translate. -/
def leftRightMeshIso (A : T.Noninjective) :
    T.leftMesh (T.obj A.1) ≅ T.rightMesh (T.obj (T.tauMinus A)) :=
  (eqToIso (by rw [T.tauPlusEquiv.apply_symm_apply]) :
      T.leftMesh (T.obj A.1) ≅
        T.leftMesh
          (T.obj ((T.tauPlusEquiv (T.tauPlusEquiv.symm A)).1))).trans
    (T.rightLeftMeshIso (T.tauPlusEquiv.symm A)).symm

/-- The right term of a noninjective left mesh is the chosen representative
of its negative translate. -/
def tauMinusIso (A : T.Noninjective) :
    (T.leftMesh (T.obj A.1)).X₃ ≅ T.obj (T.tauMinus A) :=
  (ShortComplex.π₃.mapIso (T.leftRightMeshIso A)).trans
    (T.rightTermIso (T.obj (T.tauMinus A)))

/-- First and second maps of the chosen right mesh. -/
abbrev nuPlus (X : Ind) := (T.rightMesh (T.obj X)).f
abbrev muPlus (X : Ind) := (T.rightMesh (T.obj X)).g

/-- First and second maps of the chosen left mesh. -/
abbrev muMinus (A : Ind) := (T.leftMesh (T.obj A)).f
abbrev nuMinus (A : Ind) := (T.leftMesh (T.obj A)).g

/-- Middle objects of the chosen right and left meshes. -/
abbrev thetaPlus (X : Ind) : C := (T.rightMesh (T.obj X)).X₂
abbrev thetaMinus (A : Ind) : C := (T.leftMesh (T.obj A)).X₂

/-- The middle term of the chosen right mesh at a nonprojective label is
nonzero.  This follows from minimality of the first mesh map. -/
theorem not_isZero_thetaPlus (X : T.Nonprojective) :
    ¬ IsZero (T.thetaPlus X.1) :=
  (T.rightTau (T.obj X.1)).not_isZero_X₂_of_not_isZero_X₁ X.2

/-- Compatibility identifies the first maps of the right mesh at `X` and the
left mesh at `tauPlus X` as objects of the arrow category. -/
def firstMapIso (X : T.Nonprojective) :
    Arrow.mk (T.nuPlus X.1) ≅
      Arrow.mk (T.muMinus (T.tauPlus X)) :=
  ShortComplex.fFunctor.mapIso (T.rightLeftMeshIso X)

/-- Compatibility identifies the two middle terms. -/
def middleIso (X : T.Nonprojective) :
    T.thetaPlus X.1 ≅ T.thetaMinus (T.tauPlus X) :=
  ShortComplex.π₂.mapIso (T.rightLeftMeshIso X)

/-- Monicity of the two compatible first mesh maps is equivalent. -/
theorem mono_nuPlus_iff_mono_muMinus (X : T.Nonprojective) :
    Mono (T.nuPlus X.1) ↔
      Mono (T.muMinus (T.tauPlus X)) :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (T.firstMapIso X)

/-- A nonzero right middle term remains nonzero after mesh compatibility. -/
theorem not_isZero_thetaMinus_of_not_isZero_thetaPlus
    (X : T.Nonprojective)
    (hX : ¬ IsZero (T.thetaPlus X.1)) :
    ¬ IsZero (T.thetaMinus (T.tauPlus X)) := by
  intro hzero
  exact hX ((T.middleIso X).isZero_iff.mpr hzero)

/-- Nonmonicity of `nuPlus X` transports to `muMinus (tauPlus X)`. -/
theorem not_mono_muMinus_of_not_mono_nuPlus
    (X : T.Nonprojective)
    (hX : ¬ Mono (T.nuPlus X.1)) :
    ¬ Mono (T.muMinus (T.tauPlus X)) :=
  fun hmono ↦ hX ((T.mono_nuPlus_iff_mono_muMinus X).mpr hmono)

/-- The exact theorem boundary supplied by Iyama's ladder argument.

No ladder theorem is assumed as a field of `FiniteTauCategoryData`; instead,
this proposition can later be proved for the actual ladder-defined
`NakayamaPair` relation. -/
def MuMinusNakayamaExtraction
    (NakayamaPair : Ind → Ind → Prop) : Prop :=
  ∀ (A : Ind),
    ¬ IsZero (T.thetaMinus A) →
    ¬ Mono (T.muMinus A) →
      ∃ B : Ind,
        ¬ T.IsProjective B ∧ NakayamaPair A B

/-- The right-mesh formulation follows formally from the `muMinus` theorem
and right/left mesh compatibility. -/
theorem exists_nakayamaPair_of_not_mono_nuPlus
    (NakayamaPair : Ind → Ind → Prop)
    (hExtract : T.MuMinusNakayamaExtraction NakayamaPair)
    (X : T.Nonprojective)
    (hMiddle : ¬ IsZero (T.thetaPlus X.1))
    (hmono : ¬ Mono (T.nuPlus X.1)) :
    ∃ B : Ind,
      ¬ T.IsProjective B ∧ NakayamaPair (T.tauPlus X) B :=
  hExtract (T.tauPlus X)
    (T.not_isZero_thetaMinus_of_not_isZero_thetaPlus X hMiddle)
    (T.not_mono_muMinus_of_not_mono_nuPlus X hmono)

end FiniteTauCategoryData

end MBDVendor.QSE.Iyama
