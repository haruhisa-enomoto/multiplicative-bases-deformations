import MBDVendor.Magnitude.Algebra.RightModuleFactorTauAssembly
import MBDVendor.Magnitude.CategoryTheory.HomUnitEquations

/-!
# Strictness criteria for literal finite-module factors

The primitive deletion in the frozen manuscript has a distinguished
projective source `P` whose covariant representable functor on the factor is
faithful and which has no maps to killed modules.  This file isolates the
exact categorical consequences of those two facts: quotient images of
ambient monomorphisms remain monic, and hence all chosen factor right meshes
are strict.  The dual criterion treats a distinguished injective sink.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.Iyama
open scoped ModuleCat.Algebra ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A selected source label has no nonzero maps to any killed selected
indecomposable. -/
def NoMapsFromKilled
    (K : Set (Fin S.n)) (p : S.SurvivingLabel K) : Prop :=
  ∀ (i : Fin S.n), i ∈ K → ∀ f : S.fgObj p.1 ⟶ S.fgObj i, f = 0

/-- A selected sink label receives no nonzero maps from any killed selected
indecomposable. -/
def NoMapsToKilled
    (K : Set (Fin S.n)) (i : S.SurvivingLabel K) : Prop :=
  ∀ (x : Fin S.n), x ∈ K → ∀ f : S.fgObj x ⟶ S.fgObj i.1, f = 0

/-- Covariant representability by a selected factor object is faithful. -/
def FactorRepresentableFaithful
    (K : Set (Fin S.n)) (p : S.SurvivingLabel K) : Prop :=
  ∀ {X Y : S.FactorCategory K} (f g : X ⟶ Y),
    (∀ a : S.factorObject K p ⟶ X, a ≫ f = a ≫ g) → f = g

/-- Contravariant representability by a selected factor object is faithful. -/
def FactorCorepresentableFaithful
    (K : Set (Fin S.n)) (i : S.SurvivingLabel K) : Prop :=
  ∀ {X Y : S.FactorCategory K} (f g : X ⟶ Y),
    (∀ a : Y ⟶ S.factorObject K i, f ≫ a = g ≫ a) → f = g

/-- Labelwise vanishing from a source extends to the complete additive
closure of the killed labels. -/
theorem hom_eq_zero_of_inAdd_of_noMapsFromKilled
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    {M : RightModule.FinitelyGeneratedCategory A}
    (hM : S.almostSplitSkeleton.InAdd K M)
    (f : S.fgObj p.1 ⟶ M) : f = 0 := by
  classical
  obtain ⟨P⟩ := hM
  apply (cancel_mono P.iso.hom).1
  apply biproduct.hom_ext
  intro j
  have hj :
      f ≫ P.iso.hom ≫ biproduct.π
        (fun t : P.index ↦ S.almostSplitSkeleton.obj (P.label t)) j = 0 := by
    change f ≫ P.iso.hom ≫ biproduct.π
      (fun t : P.index ↦ S.fgObj (P.label t)) j = 0
    exact hvanish (P.label j) (P.mem j) _
  simpa [Category.assoc] using hj

/-- Labelwise vanishing into a sink extends to the complete additive closure
of the killed labels. -/
theorem hom_eq_zero_of_inAdd_of_noMapsToKilled
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    {M : RightModule.FinitelyGeneratedCategory A}
    (hM : S.almostSplitSkeleton.InAdd K M)
    (f : M ⟶ S.fgObj i.1) : f = 0 := by
  classical
  obtain ⟨P⟩ := hM
  apply (cancel_epi P.iso.inv).1
  apply biproduct.hom_ext'
  intro j
  have hj :
      biproduct.ι
          (fun t : P.index ↦ S.almostSplitSkeleton.obj (P.label t)) j ≫
        P.iso.inv ≫ f = 0 := by
    change biproduct.ι (fun t : P.index ↦ S.fgObj (P.label t)) j ≫
      P.iso.inv ≫ f = 0
    exact hvanish (P.label j) (P.mem j) _
  simpa [Category.assoc] using hj

/-- Under source-to-killed vanishing, postcomposition by the quotient image
of an ambient monomorphism is injective on Hom from the distinguished source.
-/
theorem factor_map_injective_on_hom_from
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    {X Y : S.SelectedAddCategory Set.univ} (f : X ⟶ Y)
    (hf : Mono f.hom)
    (a b : S.factorObject K p ⟶ (S.factorFunctor K).obj X)
    (hab : a ≫ (S.factorFunctor K).map f =
      b ≫ (S.factorFunctor K).map f) : a = b := by
  let F := S.factorFunctor K
  let I := S.factorThroughSelectedIdeal K
  obtain ⟨a', rfl⟩ := F.map_surjective a
  obtain ⟨b', rfl⟩ := F.map_surjective b
  have hmap : F.map ((a' - b') ≫ f) = 0 := by
    rw [F.map_comp, F.map_sub, Preadditive.sub_comp, hab, sub_self]
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff ((a' - b') ≫ f)).1 hmap
  have hleft : left = 0 := by
    exact S.hom_eq_zero_of_inAdd_of_noMapsFromKilled
      hvanish hM left
  have hcomp : (a'.hom - b'.hom) ≫ f.hom = 0 := by
    change left ≫ right = (a'.hom - b'.hom) ≫ f.hom at hfactor
    rw [hleft, zero_comp] at hfactor
    exact hfactor.symm
  have hab' : a' = b' := by
    apply ObjectProperty.hom_ext
    rw [← sub_eq_zero]
    apply (cancel_mono f.hom).1
    simpa only [Preadditive.sub_comp, zero_comp] using hcomp
  rw [hab']

/-- A faithful distinguished source promotes the quotient image of an
ambient monomorphism to a monomorphism. -/
theorem factor_map_mono_of_representableFaithful
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (hfaithful : S.FactorRepresentableFaithful K p)
    {X Y : S.SelectedAddCategory Set.univ} (f : X ⟶ Y)
    (hf : Mono f.hom) : Mono ((S.factorFunctor K).map f) := by
  constructor
  intro Z a b hab
  apply hfaithful a b
  intro q
  apply S.factor_map_injective_on_hom_from hvanish f hf
  simpa only [Category.assoc] using congrArg (fun t ↦ q ≫ t) hab

/-- The first map of every ambient selected-label right mesh is monic. -/
theorem labelRightMesh_f_mono (x : Fin S.n) :
    Mono (S.labelRightMesh x).f := by
  classical
  by_cases hx : Projective (S.fgObj x)
  · rw [show S.labelRightMesh x = S.projectiveRightMesh x hx by
      simp [labelRightMesh, hx]]
    dsimp only [projectiveRightMesh]
    exact (isZero_zero (RightModule.FinitelyGeneratedCategory A)).mono _
  · rw [show S.labelRightMesh x =
      S.nonprojectiveRightMesh ⟨x, hx⟩ by
      simp [labelRightMesh, hx]]
    dsimp only [nonprojectiveRightMesh]
    infer_instance

/-- Under the distinguished-source hypotheses, every raw factor right mesh
has a monic first map. -/
theorem factorRawRightMesh_f_mono
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (hfaithful : S.FactorRepresentableFaithful K p)
    (x : Fin S.n) : Mono (S.factorRawRightMesh K x).f := by
  change Mono ((S.factorFunctor K).map
    (S.ambientAddFunctor.map (S.labelRightMesh x).f))
  apply S.factor_map_mono_of_representableFaithful hvanish hfaithful
  exact S.labelRightMesh_f_mono x

/-- Under the distinguished-source hypotheses, every minimal surviving-label
factor right mesh is strict. -/
theorem factorLabelRightMesh_f_mono
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (hfaithful : S.FactorRepresentableFaithful K p)
    (x : S.SurvivingLabel K) : Mono (S.factorLabelRightMesh K x).f := by
  classical
  by_cases h : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
      (S.factorRawRightMesh K x.1).f = 0
  · rw [show S.factorLabelRightMesh K x =
      S.factorZeroLeftRightMesh K x by
      simp [factorLabelRightMesh, h]]
    dsimp only [factorZeroLeftRightMesh]
    exact (S.factorZeroObject_isZero K).mono _
  · rw [show S.factorLabelRightMesh K x =
      S.factorRawRightMesh K x.1 by
      simp [factorLabelRightMesh, h]]
    exact S.factorRawRightMesh_f_mono hvanish hfaithful x.1

/-- The componentwise factor right mesh is strict at every quotient object.
-/
theorem factorRightMesh_f_mono
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (hfaithful : S.FactorRepresentableFaithful K p)
    (X : S.FactorCategory K) : Mono (S.factorRightMesh K X).f := by
  let d := S.chosenFactorLabelDecomposition K X
  letI (j : Fin d.n) : Mono (S.factorLabelRightMesh K (d.label j)).f :=
    S.factorLabelRightMesh_f_mono hvanish hfaithful (d.label j)
  change Mono (biproduct.map
    (fun j : Fin d.n ↦ (S.factorLabelRightMesh K (d.label j)).f))
  infer_instance

/-- The canonical factor right mesh is strict at every surviving label. -/
theorem canonicalFactorRightMesh_f_mono
    {K : Set (Fin S.n)} {p : S.SurvivingLabel K}
    (hvanish : S.NoMapsFromKilled K p)
    (hfaithful : S.FactorRepresentableFaithful K p)
    (x : S.SurvivingLabel K) :
    Mono (S.canonicalFactorRightMesh K (S.factorObject K x)).f := by
  rw [S.canonicalFactorRightMesh_at_label K x]
  exact S.factorLabelRightMesh_f_mono hvanish hfaithful x

/-- Under killed-to-sink vanishing, precomposition by the quotient image of
an ambient epimorphism is injective on Hom into the distinguished sink. -/
theorem factor_map_injective_on_hom_to
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    {X Y : S.SelectedAddCategory Set.univ} (f : X ⟶ Y)
    (hf : Epi f.hom)
    (a b : (S.factorFunctor K).obj Y ⟶ S.factorObject K i)
    (hab : (S.factorFunctor K).map f ≫ a =
      (S.factorFunctor K).map f ≫ b) : a = b := by
  let F := S.factorFunctor K
  let I := S.factorThroughSelectedIdeal K
  obtain ⟨a', rfl⟩ := F.map_surjective a
  obtain ⟨b', rfl⟩ := F.map_surjective b
  have hmap : F.map (f ≫ (a' - b')) = 0 := by
    rw [F.map_comp, F.map_sub, Preadditive.comp_sub, hab, sub_self]
  obtain ⟨M, hM, left, right, hfactor⟩ :=
    (I.map_eq_zero_iff (f ≫ (a' - b'))).1 hmap
  have hright : right = 0 :=
    S.hom_eq_zero_of_inAdd_of_noMapsToKilled hvanish hM right
  have hcomp : f.hom ≫ (a'.hom - b'.hom) = 0 := by
    change left ≫ right = f.hom ≫ (a'.hom - b'.hom) at hfactor
    rw [hright, comp_zero] at hfactor
    exact hfactor.symm
  have hab' : a' = b' := by
    apply ObjectProperty.hom_ext
    rw [← sub_eq_zero]
    apply (cancel_epi f.hom).1
    simpa only [Preadditive.comp_sub, comp_zero] using hcomp
  rw [hab']

/-- A faithful distinguished sink promotes the quotient image of an ambient
epimorphism to an epimorphism. -/
theorem factor_map_epi_of_corepresentableFaithful
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (hfaithful : S.FactorCorepresentableFaithful K i)
    {X Y : S.SelectedAddCategory Set.univ} (f : X ⟶ Y)
    (hf : Epi f.hom) : Epi ((S.factorFunctor K).map f) := by
  constructor
  intro Z a b hab
  apply hfaithful a b
  intro q
  apply S.factor_map_injective_on_hom_to hvanish f hf
  simpa only [← Category.assoc] using congrArg (fun t ↦ t ≫ q) hab

/-- The second map of every ambient selected-label left mesh is epic. -/
theorem labelLeftMesh_g_epi (x : Fin S.n) :
    Epi (S.labelLeftMesh x).g := by
  classical
  by_cases hx : Injective (S.fgObj x)
  · have hzero : IsZero (S.labelLeftMesh x).X₃ :=
      (S.labelLeftMesh_X₃_isZero_iff_injective x).2 hx
    exact hzero.epi _
  · let z := (S.rightTranslationEquiv).symm
      (⟨x, hx⟩ : {y : Fin S.n // ¬ Injective (S.fgObj y)})
    let B := S.minimalRightAlmostSplitAt z.1
    have hBEpi : Epi B.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
    rw [show S.labelLeftMesh x =
        S.noninjectiveLeftMesh
          (⟨x, hx⟩ : {y : Fin S.n // ¬ Injective (S.fgObj y)}) by
      simp [labelLeftMesh, hx]]
    change Epi B.map
    exact hBEpi

/-- Under the distinguished-sink hypotheses, every raw factor left mesh has
an epic second map. -/
theorem factorRawLeftMesh_g_epi
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (hfaithful : S.FactorCorepresentableFaithful K i)
    (x : Fin S.n) : Epi (S.factorRawLeftMesh K x).g := by
  change Epi ((S.factorFunctor K).map
    (S.ambientAddFunctor.map (S.labelLeftMesh x).g))
  apply S.factor_map_epi_of_corepresentableFaithful hvanish hfaithful
  exact S.labelLeftMesh_g_epi x

/-- Under the distinguished-sink hypotheses, every minimal surviving-label
factor left mesh is strict. -/
theorem factorLabelLeftMesh_g_epi
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (hfaithful : S.FactorCorepresentableFaithful K i)
    (x : S.SurvivingLabel K) : Epi (S.factorLabelLeftMesh K x).g := by
  classical
  by_cases h : IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
      (S.factorRawLeftMesh K x.1).g = 0
  · rw [show S.factorLabelLeftMesh K x =
      S.factorZeroRightLeftMesh K x by
      simp [factorLabelLeftMesh, h]]
    dsimp only [factorZeroRightLeftMesh]
    exact (S.factorZeroObject_isZero K).epi _
  · rw [show S.factorLabelLeftMesh K x =
      S.factorRawLeftMesh K x.1 by
      simp [factorLabelLeftMesh, h]]
    exact S.factorRawLeftMesh_g_epi hvanish hfaithful x.1

/-- The componentwise factor left mesh is strict at every quotient object. -/
theorem factorLeftMesh_g_epi
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (hfaithful : S.FactorCorepresentableFaithful K i)
    (X : S.FactorCategory K) : Epi (S.factorLeftMesh K X).g := by
  let d := S.chosenFactorLabelDecomposition K X
  letI (j : Fin d.n) : Epi (S.factorLabelLeftMesh K (d.label j)).g :=
    S.factorLabelLeftMesh_g_epi hvanish hfaithful (d.label j)
  change Epi (biproduct.map
    (fun j : Fin d.n ↦ (S.factorLabelLeftMesh K (d.label j)).g))
  infer_instance

/-- The canonical factor left mesh is strict at every surviving label. -/
theorem canonicalFactorLeftMesh_g_epi
    {K : Set (Fin S.n)} {i : S.SurvivingLabel K}
    (hvanish : S.NoMapsToKilled K i)
    (hfaithful : S.FactorCorepresentableFaithful K i)
    (x : S.SurvivingLabel K) :
    Epi (S.canonicalFactorLeftMesh K (S.factorObject K x)).g := by
  rw [S.canonicalFactorLeftMesh_at_label K x]
  exact S.factorLabelLeftMesh_g_epi hvanish hfaithful x

/-- Exact categorical input supplied by a primitive directed deletion after
the projective cover, injective envelope, and multiplicity weight have been
identified. -/
structure PrimitiveFactorInput (K : Set (Fin S.n)) where
  source : S.SurvivingLabel K
  sink : S.SurvivingLabel K
  source_projective : Projective (S.fgObj source.1)
  sink_injective : Injective (S.fgObj sink.1)
  noMapsFromKilled : S.NoMapsFromKilled K source
  noMapsToKilled : S.NoMapsToKilled K sink
  representableFaithful : S.FactorRepresentableFaithful K source
  corepresentableFaithful : S.FactorCorepresentableFaithful K sink
  weight : S.SurvivingLabel K → ℤ
  weight_pos : ∀ x, 0 < weight x
  weight_eq_from : ∀ x,
    weight x =
      MBDVendor.Magnitude.FiniteTauMatrix.homFromWeight
        (k := k) (S.factorFiniteTauCategoryData K) source x
  weight_eq_to : ∀ x,
    weight x =
      MBDVendor.Magnitude.FiniteTauMatrix.homToWeight
        (k := k) (S.factorFiniteTauCategoryData K) sink x

/-- Projectivity of a surviving factor label is decidable because the label
type is finite. -/
noncomputable instance factorIsProjectiveDecidablePred
    (K : Set (Fin S.n)) :
    DecidablePred (S.factorFiniteTauCategoryData K).IsProjective :=
  Classical.decPred _

/-- The distinguished ambient projective becomes tau-projective in the
literal factor category. -/
theorem PrimitiveFactorInput.source_isProjective
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K) :
    (S.factorFiniteTauCategoryData K).IsProjective D.source := by
  change IsZero
    (S.canonicalFactorRightMesh K (S.factorObject K D.source)).X₁
  rw [S.canonicalFactorRightMesh_at_label K D.source]
  have hraw : IsZero (S.factorRawRightMesh K D.source.1).X₁ :=
    (S.factorModuleFunctor K).map_isZero
      ((S.labelRightMesh_X₁_isZero_iff_projective D.source.1).2
        D.source_projective)
  rw [show S.factorLabelRightMesh K D.source =
      S.factorZeroLeftRightMesh K D.source by
    simp [factorLabelRightMesh, hraw]]
  exact S.factorZeroObject_isZero K

/-- The distinguished ambient injective becomes tau-injective in the literal
factor category. -/
theorem PrimitiveFactorInput.sink_isInjective
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K) :
    (S.factorFiniteTauCategoryData K).IsInjective D.sink := by
  change IsZero
    (S.canonicalFactorLeftMesh K (S.factorObject K D.sink)).X₃
  rw [S.canonicalFactorLeftMesh_at_label K D.sink]
  have hraw : IsZero (S.factorRawLeftMesh K D.sink.1).X₃ :=
    (S.factorModuleFunctor K).map_isZero
      ((S.labelLeftMesh_X₃_isZero_iff_injective D.sink.1).2
        D.sink_injective)
  rw [show S.factorLabelLeftMesh K D.sink =
      S.factorZeroRightLeftMesh K D.sink by
    simp [factorLabelLeftMesh, hraw]]
  exact S.factorZeroObject_isZero K

/-- Every canonical factor right mesh is strict under the primitive-factor
input. -/
theorem PrimitiveFactorInput.rightMesh_mono
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x : S.SurvivingLabel K) :
    Mono ((S.factorFiniteTauCategoryData K).rightMesh
      ((S.factorFiniteTauCategoryData K).obj x)).f :=
  S.canonicalFactorRightMesh_f_mono
    D.noMapsFromKilled D.representableFaithful x

/-- Every canonical factor left mesh is strict under the primitive-factor
input. -/
theorem PrimitiveFactorInput.leftMesh_epi
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x : S.SurvivingLabel K) :
    Epi ((S.factorFiniteTauCategoryData K).leftMesh
      ((S.factorFiniteTauCategoryData K).obj x)).g :=
  S.canonicalFactorLeftMesh_g_epi
    D.noMapsToKilled D.corepresentableFaithful x

/-- Over an algebraically closed field, the strict primitive factor has the
manuscript's Hom--mesh inverse data. -/
theorem PrimitiveFactorInput.homMeshInverseData
    [IsAlgClosed k] {K : Set (Fin S.n)}
    (D : S.PrimitiveFactorInput K) :
    MBDVendor.Magnitude.FiniteTauMatrix.HomMeshInverseData
      (k := k) (S.factorFiniteTauCategoryData K) := by
  classical
  exact MBDVendor.Magnitude.FiniteTauMatrix.HomMeshInverseData.ofIsAlgClosed
    (S.factorFiniteTauCategoryData K) D.rightMesh_mono

/-- The primitive multiplicity weight satisfies both unit equations of the
factor-structure proposition. -/
theorem PrimitiveFactorInput.meshUnitEquations
    [IsAlgClosed k] {K : Set (Fin S.n)}
    (D : S.PrimitiveFactorInput K) :
    (∀ target,
      MBDVendor.Magnitude.FiniteTauMatrix.meshColumnWeight
          (S.factorFiniteTauCategoryData K) D.weight target =
        if target = D.source then 1 else 0) ∧
      ∀ source,
        MBDVendor.Magnitude.FiniteTauMatrix.meshRowWeight
            (S.factorFiniteTauCategoryData K) D.weight source =
          if source = D.sink then 1 else 0 := by
  classical
  exact
    MBDVendor.Magnitude.FiniteTauMatrix.meshUnitEquations_of_homDimensionIdentities
      (S.factorFiniteTauCategoryData K) D.homMeshInverseData
      D.source D.sink D.weight D.weight_eq_from D.weight_eq_to

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
