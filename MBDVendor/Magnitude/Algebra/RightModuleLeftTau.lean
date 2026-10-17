import MBDVendor.Magnitude.Algebra.RightModuleTranslation

/-!
# Left tau-sequences for the finite right-module category

At a noninjective selected module, the chosen minimal left almost-split
monomorphism and its cokernel form the left Auslander--Reiten complex.  At
an injective selected module, the chosen minimal left almost-split map is
epic, so its cokernel is zero.  Finite componentwise biproducts extend these
meshes to every finitely generated right module.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama
open scoped ModuleCat.Algebra ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The chosen kernel inclusion rewritten with its selected translation
representative as source. -/
def rightKernelMap
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.fgObj (S.rightTranslation z).1 ⟶
      (S.minimalRightAlmostSplitAt z.1).middle :=
  (S.rightTranslationKernelIso z).inv ≫
    kernel.ι (S.minimalRightAlmostSplitAt z.1).map

/-- The transported kernel inclusion is left almost split. -/
theorem rightKernelMap_leftAlmostSplit
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsLeftAlmostSplit (S.rightKernelMap z) :=
  (S.chosenRight_kernel_ar_sequence z).1.precomp_iso
    (S.rightTranslationKernelIso z).symm

/-- The transported kernel inclusion is left minimal. -/
theorem rightKernelMap_leftMinimal
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsLeftMinimal (S.rightKernelMap z) :=
  (S.chosenRight_kernel_ar_sequence z).2.1.precomp_iso
    (S.rightTranslationKernelIso z).symm

/-- Identify a noninjective label with the source of the corresponding
chosen right Auslander--Reiten sequence. -/
def noninjectiveLeftSourceIso
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)}) :
    S.fgObj x.1 ≅
      S.fgObj (S.rightTranslation
        ((S.rightTranslationEquiv).symm x)).1 := by
  let z := (S.rightTranslationEquiv).symm x
  have hτ : S.rightTranslationEquiv z = x :=
    S.rightTranslationEquiv.apply_symm_apply x
  exact eqToIso (congrArg S.fgObj
    (congrArg Subtype.val hτ).symm)

/-- Rotate the corresponding chosen right Auslander--Reiten complex at a
noninjective selected module. -/
def noninjectiveLeftMesh
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)}) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) := by
  let z := (S.rightTranslationEquiv).symm x
  let B := S.minimalRightAlmostSplitAt z.1
  let f : S.fgObj x.1 ⟶ B.middle :=
    (S.noninjectiveLeftSourceIso x).hom ≫ S.rightKernelMap z
  exact ShortComplex.mk f B.map (by
    dsimp only [f, rightKernelMap]
    rw [Category.assoc, Category.assoc, kernel.condition,
      comp_zero, comp_zero])

/-- The noninjective left Auslander--Reiten complex is a left tau-sequence. -/
theorem noninjectiveLeftTau
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)}) :
    LeftTauSequence (S.noninjectiveLeftMesh x) := by
  let sigma := S.almostSplitSkeleton
  let z := (S.rightTranslationEquiv).symm x
  let B := S.minimalRightAlmostSplitAt z.1
  let e : S.fgObj x.1 ≅ S.fgObj (S.rightTranslation z).1 :=
    S.noninjectiveLeftSourceIso x
  let f : S.fgObj x.1 ⟶ B.middle := e.hom ≫ S.rightKernelMap z
  change LeftTauSequence
    (ShortComplex.mk f B.map (by
      dsimp only [f, rightKernelMap]
      rw [Category.assoc, Category.assoc, kernel.condition,
        comp_zero, comp_zero]))
  have hfLeft : IsLeftAlmostSplit f :=
    (S.rightKernelMap_leftAlmostSplit z).precomp_iso e
  have hfRad : IsRadicalMorphism f :=
    (sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj f).2
      hfLeft.not_isSplitMono
  have hgRad : IsRadicalMorphism B.map :=
    (sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj B.map).2
      B.rightAlmostSplit.not_isSplitEpi
  have hBEpi : Epi B.map :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      sigma B.map B.rightAlmostSplit z.2
  letI : Epi B.map := hBEpi
  refine
    { f_radical := hfRad
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakCokernel := ?_ }
  · intro W a ha
    exact hfLeft.factors a
      ((sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj a).1 ha)
  · intro W a ha
    exact B.rightAlmostSplit.factors a
      ((sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj a).1 ha)
  · constructor
    · rw [ShortComplex.isWeakCokernel_iff]
      intro W a ha
      have hk : kernel.ι B.map ≫ a = 0 := by
        rw [← cancel_epi (S.rightTranslationKernelIso z).inv]
        change S.rightKernelMap z ≫ a = 0
        rw [← cancel_epi e.hom]
        exact ha
      exact ⟨Abelian.epiDesc B.map a hk,
        Abelian.comp_epiDesc B.map a hk⟩
    · intro q hq
      have hqeq : q = 𝟙 _ := by
        apply (cancel_epi B.map).1
        simpa only [Category.comp_id] using hq
      rw [hqeq]
      infer_instance

/-- The chosen left almost-split map and its canonical cokernel at an
injective selected module. -/
def injectiveLeftMesh
    (x : {x : Fin S.n // Injective (S.fgObj x)}) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
  let L := S.minimalLeftAlmostSplitAt x.1
  ShortComplex.mk L.map (cokernel.π L.map) (cokernel.condition L.map)

/-- The injective-boundary left complex is a left tau-sequence. -/
theorem injectiveLeftTau
    (x : {x : Fin S.n // Injective (S.fgObj x)}) :
    LeftTauSequence (S.injectiveLeftMesh x) := by
  let sigma := S.almostSplitSkeleton
  let L := S.minimalLeftAlmostSplitAt x.1
  change LeftTauSequence
    (ShortComplex.mk L.map (cokernel.π L.map)
      (cokernel.condition L.map))
  letI : Injective (S.almostSplitSkeleton.obj x.1) := by
    change Injective (S.fgObj x.1)
    exact x.2
  have hfEpi : Epi L.map :=
    MBDVendor.Magnitude.CategoryTheory.leftAlmostSplit_epi_of_injective_source
      L.map L.leftAlmostSplit L.leftMinimal
  letI : Epi L.map := hfEpi
  have hgzero : cokernel.π L.map = 0 := by
    apply (cancel_epi L.map).1
    rw [cokernel.condition, comp_zero]
  have hCok : IsZero (cokernel L.map) := by
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi (cokernel.π L.map)).1
    rw [Category.comp_id, hgzero, zero_comp]
  have hfRad : IsRadicalMorphism L.map :=
    (sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj L.map).2
      L.leftAlmostSplit.not_isSplitMono
  have hgRad : IsRadicalMorphism (cokernel.π L.map) := by
    rw [hgzero]
    exact isRadicalMorphism_zero
  refine
    { f_radical := hfRad
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakCokernel := ?_ }
  · intro W a ha
    exact L.leftAlmostSplit.factors a
      ((sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj a).1 ha)
  · intro W a _ha
    refine ⟨0, ?_⟩
    rw [zero_comp]
    exact (hCok.eq_of_tgt a 0).symm
  · constructor
    · rw [ShortComplex.isWeakCokernel_iff]
      intro W a ha
      exact ⟨cokernel.desc L.map a ha, cokernel.π_desc _ _ _⟩
    · intro e _he
      have heq : e = 𝟙 _ := hCok.eq_of_src e (𝟙 _)
      rw [heq]
      infer_instance

/-- The unified left mesh at a selected indecomposable label. -/
def labelLeftMesh (x : Fin S.n) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) := by
  classical
  by_cases hx : Injective (S.fgObj x)
  · exact S.injectiveLeftMesh ⟨x, hx⟩
  · exact S.noninjectiveLeftMesh ⟨x, hx⟩

/-- Every selected-label left mesh is a left tau-sequence. -/
theorem labelLeftTau (x : Fin S.n) :
    LeftTauSequence (S.labelLeftMesh x) := by
  classical
  by_cases hx : Injective (S.fgObj x)
  · simpa [labelLeftMesh, hx] using S.injectiveLeftTau ⟨x, hx⟩
  · simpa [labelLeftMesh, hx] using S.noninjectiveLeftTau ⟨x, hx⟩

/-- The left endpoint of the unified label mesh is literally the selected
indecomposable. -/
theorem labelLeftMesh_X₁ (x : Fin S.n) :
    (S.labelLeftMesh x).X₁ = S.fgObj x := by
  classical
  by_cases hx : Injective (S.fgObj x) <;>
    simp [labelLeftMesh, hx, injectiveLeftMesh,
      noninjectiveLeftMesh, almostSplitSkeleton]

/-- Extend the labelwise left AR complexes to every module by finite
componentwise biproduct. -/
def moduleLeftMesh (X : RightModule.FinitelyGeneratedCategory A) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
  let d := S.chosenLabelDecomposition X
  shortComplexBiproduct (fun i : Fin d.n ↦ S.labelLeftMesh (d.label i))

/-- The chosen left mesh has the supplied module as its left endpoint. -/
def moduleLeftTermIso (X : RightModule.FinitelyGeneratedCategory A) :
    (S.moduleLeftMesh X).X₁ ≅ X :=
  let d := S.chosenLabelDecomposition X
  (biproduct.mapIso fun i : Fin d.n ↦
      eqToIso (S.labelLeftMesh_X₁ (d.label i))).trans d.iso.symm

/-- Every modulewise left mesh is a left tau-sequence. -/
theorem moduleLeftTau (X : RightModule.FinitelyGeneratedCategory A) :
    LeftTauSequence (S.moduleLeftMesh X) := by
  let d := S.chosenLabelDecomposition X
  exact leftTauSequence_shortComplexBiproduct S.fgNilpotentRadicalData
    (fun i : Fin d.n ↦ S.labelLeftMesh (d.label i))
    (fun i ↦ S.labelLeftTau (d.label i))

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
