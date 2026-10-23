module

public import MBDVendor.QSE.CategoryTheory.IyamaMeshSplitLifting

/-!
# Mixed split-component lifting between chosen meshes

This file proves the left-mesh-to-right-mesh case of Iyama,
*Tau-categories I*, 3.5.2(1)(ii).  It realizes the right-tau core of a
chosen left mesh from finite Krull--Schmidt decomposition and mesh
compatibility, then reduces mixed split lifting to the right-right theorem.
The construction is entirely categorical.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.TauSequenceComparison

open CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ## The precise mixed interface -/

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

open scoped ZeroObject

/-- The componentwise biproduct of a finite family of short-complex
morphisms. -/
def shortComplexBiproductHom
    {J : Type w} [Fintype J]
    {S R : J → ShortComplex C} (φ : ∀ j, S j ⟶ R j) :
    shortComplexBiproduct S ⟶ shortComplexBiproduct R where
  τ₁ := biproduct.map fun j ↦ (φ j).τ₁
  τ₂ := biproduct.map fun j ↦ (φ j).τ₂
  τ₃ := biproduct.map fun j ↦ (φ j).τ₃
  comm₁₂ := by
    change
      (biproduct.map fun j ↦ (φ j).τ₁) ≫
          (biproduct.map fun j ↦ (R j).f) =
        (biproduct.map fun j ↦ (S j).f) ≫
          (biproduct.map fun j ↦ (φ j).τ₂)
    ext i j
    by_cases hij : i = j
    · subst j
      simpa using (φ i).comm₁₂
    · simp [Ne.symm hij]
  comm₂₃ := by
    change
      (biproduct.map fun j ↦ (φ j).τ₂) ≫
          (biproduct.map fun j ↦ (R j).g) =
        (biproduct.map fun j ↦ (S j).g) ≫
          (biproduct.map fun j ↦ (φ j).τ₃)
    ext i j
    by_cases hij : i = j
    · subst j
      simpa using (φ i).comm₂₃
    · simp [Ne.symm hij]

omit [HasBinaryBiproducts C] [IsIdempotentComplete C] in
/-- A componentwise biproduct morphism is invertible in degree three when
all of its degree-three components are invertible. -/
theorem isIso_shortComplexBiproductHom_τ₃
    {J : Type w} [Fintype J]
    {S R : J → ShortComplex C} (φ : ∀ j, S j ⟶ R j)
    (hφ : ∀ j, IsIso (φ j).τ₃) :
    IsIso (shortComplexBiproductHom φ).τ₃ := by
  letI componentIso (j : J) : IsIso (φ j).τ₃ := hφ j
  change IsIso (biproduct.map fun j ↦ (φ j).τ₃)
  let e := biproduct.mapIso fun j ↦ asIso (φ j).τ₃
  change IsIso e.hom
  infer_instance

omit [HasBinaryBiproducts C] [IsIdempotentComplete C] in
/-- A componentwise biproduct morphism is split monic in degree one when
all of its degree-one components are split monic. -/
theorem isSplitMono_shortComplexBiproductHom_τ₁
    {J : Type w} [Fintype J]
    {S R : J → ShortComplex C} (φ : ∀ j, S j ⟶ R j)
    (hφ : ∀ j, IsSplitMono (φ j).τ₁) :
    IsSplitMono (shortComplexBiproductHom φ).τ₁ := by
  letI componentSplitMono (j : J) : IsSplitMono (φ j).τ₁ := hφ j
  apply IsSplitMono.mk'
  exact
    { retraction := biproduct.map (fun j ↦ retraction (φ j).τ₁)
      id := by
        change
          biproduct.map (fun j ↦ (φ j).τ₁) ≫
              biproduct.map (fun j ↦ retraction (φ j).τ₁) =
            𝟙 _
        apply biproduct.hom_ext'
        intro j
        apply biproduct.hom_ext
        intro k
        by_cases hjk : j = k
        · subst k
          simp
        · simp [hjk] }

/-- A right-tau piece mapping to the left mesh of one indecomposable, with
an invertible map on third terms. -/
structure RightCorePiece
    (T : FiniteTauCategoryData C Ind) (A : Ind) where
  S : ShortComplex C
  rightTau : RightTauSequence S
  inclusion : S ⟶ T.leftMesh (T.obj A)
  third_isIso : IsIso inclusion.τ₃

/-- For a noninjective label use the compatible right mesh.  For an
injective label use the zero right mesh; both source and target third terms
are then zero. -/
def rightCorePiece
    (T : FiniteTauCategoryData C Ind) (A : Ind) : RightCorePiece T A := by
  classical
  by_cases h : ¬ T.IsInjective A
  · let e := (T.leftRightMeshIso ⟨A, h⟩).symm
    exact
      { S := T.rightMesh (T.obj (T.tauMinus ⟨A, h⟩))
        rightTau := T.rightTau _
        inclusion := e.hom
        third_isIso := by
          change IsIso (ShortComplex.π₃.map e.hom)
          infer_instance }
  · have hi : T.IsInjective A := not_not.mp h
    have hzero :=
      T.rightMesh_components_isZero_of_isZero (0 : C) (isZero_zero C)
    let e₃ : (T.rightMesh (0 : C)).X₃ ≅
        (T.leftMesh (T.obj A)).X₃ :=
      hzero.2.2.iso hi
    let φ : T.rightMesh (0 : C) ⟶ T.leftMesh (T.obj A) :=
      { τ₁ := 0
        τ₂ := 0
        τ₃ := e₃.hom
        comm₁₂ := hzero.1.eq_of_src _ _
        comm₂₃ := hzero.2.1.eq_of_src _ _ }
    exact
      { S := T.rightMesh (0 : C)
        rightTau := T.rightTau _
        inclusion := φ
        third_isIso := by
          change IsIso e₃.hom
          infer_instance }

/-- A right tau-sequence mapping into a chosen left mesh, and exhausting its
third term up to isomorphism.  This packages Iyama's decomposition
`[X) ≅ [I) ⊕ (X₃]` at exactly the strength needed for split lifting. -/
structure RightCoreDecomposition
    (T : FiniteTauCategoryData C Ind) (X : C) where
  S : ShortComplex C
  rightTau : RightTauSequence S
  inclusion : S ⟶ T.leftMesh X
  third_isIso : IsIso inclusion.τ₃

/-- Finite Krull--Schmidt decomposition and mesh compatibility construct the
right core of every chosen left mesh. -/
theorem exists_rightCoreDecomposition
    (T : FiniteTauCategoryData C Ind) (X : C) :
    Nonempty (RightCoreDecomposition T X) := by
  classical
  obtain ⟨n, label, ⟨e⟩⟩ := T.exists_leftMesh_decomposition X
  let P : ∀ i : Fin n, RightCorePiece T (label i) :=
    fun i ↦ rightCorePiece T (label i)
  let S : ShortComplex C := shortComplexBiproduct fun i ↦ (P i).S
  let R : ShortComplex C :=
    shortComplexBiproduct fun i ↦ T.leftMesh (T.obj (label i))
  let ι : S ⟶ R := shortComplexBiproductHom fun i ↦ (P i).inclusion
  have hι : IsIso ι.τ₃ := by
    apply isIso_shortComplexBiproductHom_τ₃
    intro i
    exact (P i).third_isIso
  letI : IsIso ι.τ₃ := hι
  let ψ : S ⟶ T.leftMesh X := ι ≫ e.inv
  have hψ : IsIso ψ.τ₃ := by
    change IsIso (ι.τ₃ ≫ e.inv.τ₃)
    infer_instance
  exact ⟨
    { S := S
      rightTau :=
        rightTauSequence_shortComplexBiproduct T.radical
          (fun i ↦ (P i).S) (fun i ↦ (P i).rightTau)
      inclusion := ψ
      third_isIso := hψ }⟩

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- A split-epic composite makes its second factor split epic. -/
theorem isSplitEpi_of_isSplitEpi_precomp
    {X Y Z : C} (r : X ⟶ Y) (f : Y ⟶ Z) [IsSplitEpi (r ≫ f)] :
    IsSplitEpi f := by
  apply IsSplitEpi.mk'
  exact
    { section_ := section_ (r ≫ f) ≫ r
      id := by simp [Category.assoc] }

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- A split-monic composite makes its first factor split monic. -/
theorem isSplitMono_of_isSplitMono_postcomp
    {X Y Z : C} (f : X ⟶ Y) (r : Y ⟶ Z) [IsSplitMono (f ≫ r)] :
    IsSplitMono f := by
  apply IsSplitMono.mk'
  exact
    { retraction := r ≫ retraction (f ≫ r)
      id := by rw [← Category.assoc, IsSplitMono.id] }

/-- A left tau-sequence receiving a map from one indecomposable right mesh,
split monic at the left endpoint. -/
structure LeftReplacement
    (T : FiniteTauCategoryData C Ind) (A : Ind) where
  S : ShortComplex C
  leftTau : LeftTauSequence S
  projection : T.rightMesh (T.obj A) ⟶ S
  first_splitMono : IsSplitMono projection.τ₁

/-- A nonprojective label uses mesh compatibility. At a projective boundary
the zero chain map is split monic in degree one because its source is zero. -/
def leftReplacement
    (T : FiniteTauCategoryData C Ind) (A : Ind) : LeftReplacement T A := by
  classical
  by_cases h : ¬ T.IsProjective A
  · exact
      { S := T.leftMesh (T.obj (T.tauPlus ⟨A, h⟩))
        leftTau := T.leftTau _
        projection := (T.rightLeftMeshIso ⟨A, h⟩).hom
        first_splitMono := inferInstance }
  · have hA : T.IsProjective A := not_not.mp h
    refine
      { S := T.leftMesh (T.obj A)
        leftTau := T.leftTau _
        projection := 0
        first_splitMono := ?_ }
    apply IsSplitMono.mk'
    exact
      { retraction := 0
        id := hA.eq_of_src _ _ }

/-- Mixed left-to-right split lifting, Tau I, 3.5.2(1)(ii), for the chosen
meshes of a finite tau category. -/
theorem splitEpi_components_of_leftMesh_hom_rightMesh
    (T : FiniteTauCategoryData C Ind) (X Y : C)
    (phi : T.leftMesh X ⟶ T.rightMesh Y)
    (hphi₃ : IsSplitEpi phi.τ₃) :
    IsSplitEpi phi.τ₁ ∧ IsSplitEpi phi.τ₂ := by
  letI : IsSplitEpi phi.τ₃ := hphi₃
  obtain ⟨D⟩ := exists_rightCoreDecomposition T X
  letI : IsIso D.inclusion.τ₃ := D.third_isIso
  let χ : D.S ⟶ T.rightMesh Y := D.inclusion ≫ phi
  have hχ₃ : IsSplitEpi χ.τ₃ := by
    change IsSplitEpi (D.inclusion.τ₃ ≫ phi.τ₃)
    infer_instance
  letI : IsSplitEpi χ.τ₃ := hχ₃
  have hχ := RightTauSequence.splitEpi_components_of_splitEpi_τ₃
    D.rightTau (T.rightTau Y) χ
  letI : IsSplitEpi χ.τ₁ := hχ.1
  letI : IsSplitEpi χ.τ₂ := hχ.2
  have hcomp₁ : IsSplitEpi (D.inclusion.τ₁ ≫ phi.τ₁) := by
    change IsSplitEpi χ.τ₁
    infer_instance
  have hcomp₂ : IsSplitEpi (D.inclusion.τ₂ ≫ phi.τ₂) := by
    change IsSplitEpi χ.τ₂
    infer_instance
  letI : IsSplitEpi (D.inclusion.τ₁ ≫ phi.τ₁) := hcomp₁
  letI : IsSplitEpi (D.inclusion.τ₂ ≫ phi.τ₂) := hcomp₂
  constructor
  · exact isSplitEpi_of_isSplitEpi_precomp D.inclusion.τ₁ phi.τ₁
  · exact isSplitEpi_of_isSplitEpi_precomp D.inclusion.τ₂ phi.τ₂

/-- Exact dual mixed lifting: a chain map from a chosen left mesh to a
chosen right mesh which is split monic at the left endpoint is split monic
in the other two degrees. -/
theorem splitMono_components_of_leftMesh_hom_rightMesh
    (T : FiniteTauCategoryData C Ind) (X Y : C)
    (phi : T.leftMesh X ⟶ T.rightMesh Y)
    (hphi₁ : IsSplitMono phi.τ₁) :
    IsSplitMono phi.τ₂ ∧ IsSplitMono phi.τ₃ := by
  classical
  letI : IsSplitMono phi.τ₁ := hphi₁
  obtain ⟨n, label, ⟨eMesh⟩⟩ := T.exists_rightMesh_decomposition Y
  let S : Fin n → ShortComplex C := fun i ↦
    (leftReplacement T (label i)).S
  let qComponent : ∀ i : Fin n,
      T.rightMesh (T.obj (label i)) ⟶ S i := fun i ↦
    (leftReplacement T (label i)).projection
  have hS : LeftTauSequence (shortComplexBiproduct S) :=
    leftTauSequence_shortComplexBiproduct T.radical S (fun i ↦ by
      simpa [S] using (leftReplacement T (label i)).leftTau)
  let qBiproduct :
      shortComplexBiproduct (fun i ↦ T.rightMesh (T.obj (label i))) ⟶
        shortComplexBiproduct S :=
    shortComplexBiproductHom qComponent
  have hqBiproduct : IsSplitMono qBiproduct.τ₁ := by
    apply isSplitMono_shortComplexBiproductHom_τ₁ qComponent
    intro i
    exact (leftReplacement T (label i)).first_splitMono
  letI : IsSplitMono qBiproduct.τ₁ := hqBiproduct
  let q : T.rightMesh Y ⟶ shortComplexBiproduct S :=
    eMesh.hom ≫ qBiproduct
  have hq : IsSplitMono q.τ₁ := by
    change IsSplitMono (eMesh.hom.τ₁ ≫ qBiproduct.τ₁)
    infer_instance
  letI : IsSplitMono q.τ₁ := hq
  let psi : T.leftMesh X ⟶ shortComplexBiproduct S := phi ≫ q
  have hpsi₁ : IsSplitMono psi.τ₁ := by
    change IsSplitMono (phi.τ₁ ≫ q.τ₁)
    infer_instance
  letI : IsSplitMono psi.τ₁ := hpsi₁
  obtain ⟨h₂, h₃⟩ :=
    LeftTauSequence.splitMono_components_of_splitMono_τ₁
      (T.leftTau X) hS psi
  have hcomp₂ : IsSplitMono (phi.τ₂ ≫ q.τ₂) := by
    change IsSplitMono psi.τ₂
    exact h₂
  have hcomp₃ : IsSplitMono (phi.τ₃ ≫ q.τ₃) := by
    change IsSplitMono psi.τ₃
    exact h₃
  letI : IsSplitMono (phi.τ₂ ≫ q.τ₂) := hcomp₂
  letI : IsSplitMono (phi.τ₃ ≫ q.τ₃) := hcomp₃
  exact ⟨isSplitMono_of_isSplitMono_postcomp phi.τ₂ q.τ₂,
    isSplitMono_of_isSplitMono_postcomp phi.τ₃ q.τ₃⟩

/-- The mixed split-lifting statement, Tau I, 3.5.2(1)(ii), packaged as a
property of the chosen finite tau-category meshes. -/
def HasMixedSplitEpiLifting (T : FiniteTauCategoryData C Ind) : Prop :=
  ∀ (X Y : C) (phi : T.leftMesh X ⟶ T.rightMesh Y),
    IsSplitEpi phi.τ₃ → IsSplitEpi phi.τ₁ ∧ IsSplitEpi phi.τ₂

/-- The finite tau-category data prove the mixed split-lifting interface. -/
theorem hasMixedSplitEpiLifting (T : FiniteTauCategoryData C Ind) :
    HasMixedSplitEpiLifting T :=
  fun X Y phi hphi₃ ↦
    splitEpi_components_of_leftMesh_hom_rightMesh T X Y phi hphi₃

/-- The dual mixed split-lifting interface. -/
def HasMixedSplitMonoLifting (T : FiniteTauCategoryData C Ind) : Prop :=
  ∀ (X Y : C) (phi : T.leftMesh X ⟶ T.rightMesh Y),
    IsSplitMono phi.τ₁ → IsSplitMono phi.τ₂ ∧ IsSplitMono phi.τ₃

/-- Finite tau-category data prove the dual mixed split-lifting interface. -/
theorem hasMixedSplitMonoLifting (T : FiniteTauCategoryData C Ind) :
    HasMixedSplitMonoLifting T :=
  fun X Y phi hphi₁ ↦
    splitMono_components_of_leftMesh_hom_rightMesh T X Y phi hphi₁

end MBDVendor.QSE.Iyama.TauSequenceComparison
