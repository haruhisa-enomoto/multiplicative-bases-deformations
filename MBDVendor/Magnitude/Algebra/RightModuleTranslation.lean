import MBDVendor.Magnitude.Algebra.RightModuleLeftAlmostSplit

/-!
# Auslander--Reiten translation on the finite right-module skeleton

The kernel of the chosen minimal right almost-split map defines translation
from nonprojective to noninjective labels.  Injectivity follows from
uniqueness of minimal left almost-split maps.  Surjectivity follows from the
dual cokernel construction at every noninjective label and uniqueness of
minimal right almost-split maps.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The chosen right almost-split map at a nonprojective label has an
indecomposable noninjective kernel. -/
theorem chosenRight_kernel_ar_sequence
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    IsLeftAlmostSplit
        (kernel.ι (S.minimalRightAlmostSplitAt z.1).map) ∧
      IsLeftMinimal
        (kernel.ι (S.minimalRightAlmostSplitAt z.1).map) ∧
      Foundation.IsIndecomposableModule Aᵐᵒᵖ
        (kernel (S.minimalRightAlmostSplitAt z.1).map :
          RightModule.FinitelyGeneratedCategory A) ∧
      ¬ Injective (kernel (S.minimalRightAlmostSplitAt z.1).map) :=
  (S.minimalRightAlmostSplitAt z.1).kernel_ar_sequence
    S.almostSplitSkeleton z.2

/-- Skeleton label of the kernel of the chosen nonprojective right
almost-split map. -/
def rightTranslationLabel
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) : Fin S.n :=
  Classical.choose
    (S.almostSplitSkeleton.complete
      (kernel (S.minimalRightAlmostSplitAt z.1).map)
      (S.chosenRight_kernel_ar_sequence z).2.2.1)

/-- The chosen kernel-to-skeleton isomorphism. -/
def rightTranslationKernelIso
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    kernel (S.minimalRightAlmostSplitAt z.1).map ≅
      S.fgObj (S.rightTranslationLabel z) :=
  (Classical.choose_spec
    (S.almostSplitSkeleton.complete
      (kernel (S.minimalRightAlmostSplitAt z.1).map)
      (S.chosenRight_kernel_ar_sequence z).2.2.1)).some

/-- Auslander--Reiten translation from nonprojective to noninjective
selected labels. -/
def rightTranslation
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
  ⟨S.rightTranslationLabel z, by
    intro h
    apply (S.chosenRight_kernel_ar_sequence z).2.2.2
    exact Injective.of_iso (S.rightTranslationKernelIso z).symm h⟩

/-- Equality of translation labels identifies the original nonprojective
endpoints. -/
theorem rightTranslation_injective :
    Function.Injective S.rightTranslation := by
  intro z₁ z₂ hτ
  let B₁ := S.minimalRightAlmostSplitAt z₁.1
  let B₂ := S.minimalRightAlmostSplitAt z₂.1
  have hval : (S.rightTranslation z₁).1 =
      (S.rightTranslation z₂).1 :=
    congrArg Subtype.val hτ
  let eobj : S.fgObj (S.rightTranslation z₁).1 ≅
      S.fgObj (S.rightTranslation z₂).1 :=
    eqToIso (congrArg S.fgObj hval)
  let ek : kernel B₁.map ≅ kernel B₂.map :=
    (S.rightTranslationKernelIso z₁).trans
      (eobj.trans (S.rightTranslationKernelIso z₂).symm)
  let k₁' : kernel B₂.map ⟶ B₁.middle :=
    ek.inv ≫ kernel.ι B₁.map
  have hk₁as : IsLeftAlmostSplit k₁' :=
    (S.chosenRight_kernel_ar_sequence z₁).1.precomp_iso ek.symm
  have hk₁min : IsLeftMinimal k₁' :=
    (S.chosenRight_kernel_ar_sequence z₁).2.1.precomp_iso ek.symm
  obtain ⟨emid, hemid⟩ := exists_leftAlmostSplit_middleIso
    hk₁as hk₁min
    (S.chosenRight_kernel_ar_sequence z₂).1
    (S.chosenRight_kernel_ar_sequence z₂).2.1
  let ec : cokernel k₁' ≅ cokernel (kernel.ι B₂.map) :=
    cokernel.mapIso k₁'
      (kernel.ι B₂.map)
      (Iso.refl (kernel B₂.map)) emid
      (by simpa using hemid)
  let ec₁ : cokernel k₁' ≅ cokernel (kernel.ι B₁.map) :=
    cokernel.mapIso k₁'
      (kernel.ι B₁.map)
      ek.symm (Iso.refl B₁.middle)
      (by simp [k₁'])
  haveI : Epi B₁.map :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton B₁.map B₁.rightAlmostSplit z₁.2
  haveI : Epi B₂.map :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton B₂.map B₂.rightAlmostSplit z₂.2
  let e₁ : cokernel k₁' ≅ S.fgObj z₁.1 :=
    ec₁.trans (cokernelKernelIsoTarget B₁.map)
  let e₂ : cokernel (kernel.ι B₂.map) ≅ S.fgObj z₂.1 :=
    cokernelKernelIsoTarget B₂.map
  apply Subtype.ext
  apply S.almostSplitSkeleton.eq_of_iso
  exact ⟨e₁.symm.trans (ec.trans e₂)⟩

/-- Every noninjective selected label is the translate of a nonprojective
selected label. -/
theorem rightTranslation_surjective :
    Function.Surjective S.rightTranslation := by
  intro x
  let L := S.minimalLeftAlmostSplitAt x.1
  letI : Mono L.map := S.noninjectiveLeftAlmostSplit_mono x
  let q := cokernel.π L.map
  have hqAS : IsRightAlmostSplit q :=
    S.noninjectiveLeftCokernel_rightAlmostSplit x
  have hqMin : IsRightMinimal q :=
    S.noninjectiveLeftCokernel_rightMinimal x
  have hqIndec : Foundation.IsIndecomposableModule Aᵐᵒᵖ
      (cokernel L.map : RightModule.FinitelyGeneratedCategory A) :=
    rightAlmostSplit_target_isIndecomposableModule q hqAS
  obtain ⟨z, ⟨ez⟩⟩ :=
    S.almostSplitSkeleton.complete (cokernel L.map) hqIndec
  let qz : L.middle ⟶ S.fgObj z := q ≫ ez.hom
  have hqzAS : IsRightAlmostSplit qz :=
    hqAS.postcomp_iso ez
  have hqzMin : IsRightMinimal qz :=
    IsRightMinimal.postcomp_iso ez hqMin
  have hqzEpi : Epi qz := by
    dsimp only [qz]
    infer_instance
  letI : Epi qz := hqzEpi
  have hzNotProjective : ¬ Projective (S.fgObj z) :=
    MBDVendor.Magnitude.IsRightAlmostSplit.not_projective_target qz hqzAS
  let znp : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    ⟨z, hzNotProjective⟩
  let B := S.minimalRightAlmostSplitAt z
  have hkernelUnique : Nonempty (kernel qz ≅ kernel B.map) :=
    nonempty_kernelIso_of_rightAlmostSplit
      hqzAS hqzMin B.rightAlmostSplit B.rightMinimal
  let eqKernel : kernel q ≅ kernel qz :=
    kernel.mapIso q qz (Iso.refl L.middle) ez (by simp [qz])
  let ex : S.fgObj x.1 ≅ kernel q :=
    (kernelCokernelIsoSource L.map).symm
  let etau : kernel B.map ≅ S.fgObj (S.rightTranslation znp).1 :=
    S.rightTranslationKernelIso znp
  have hlabel : x.1 = (S.rightTranslation znp).1 := by
    apply S.almostSplitSkeleton.eq_of_iso
    exact ⟨ex.trans (eqKernel.trans
      ((Classical.choice hkernelUnique).trans etau))⟩
  refine ⟨znp, ?_⟩
  apply Subtype.ext
  exact hlabel.symm

/-- Auslander--Reiten translation is an equivalence between nonprojective
and noninjective selected labels. -/
def rightTranslationEquiv :
    {z : Fin S.n // ¬ Projective (S.fgObj z)} ≃
      {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
  Equiv.ofBijective S.rightTranslation
    ⟨S.rightTranslation_injective, S.rightTranslation_surjective⟩

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
