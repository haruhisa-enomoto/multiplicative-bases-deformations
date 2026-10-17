import MBDVendor.QSE.RepresentationTheory.AlmostSplitKernel

/-!
# Uniqueness and transport of minimal almost-split morphisms

Minimal right almost-split morphisms with a common target have isomorphic
sources, and minimal left almost-split morphisms with a common source have
isomorphic targets.  This file also records the isomorphism-transport and
kernel/cokernel consequences used to identify Auslander--Reiten translates
inside a chosen indecomposable skeleton.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe u v

variable {C : Type u} [Category.{v} C]

/-- Minimal right almost-split morphisms with the same target have
isomorphic sources, compatibly with their structure maps. -/
theorem exists_rightAlmostSplit_middleIso
    {E E' Z : C} {f : E ⟶ Z} {g : E' ⟶ Z}
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g) :
    ∃ e : E ≅ E', e.hom ≫ g = f := by
  obtain ⟨a, ha⟩ := hg.factors f hf.not_isSplitEpi
  obtain ⟨b, hb⟩ := hf.factors g hg.not_isSplitEpi
  have hab : (a ≫ b) ≫ f = f := by
    simp only [Category.assoc, hb, ha]
  have hba : (b ≫ a) ≫ g = g := by
    simp only [Category.assoc, ha, hb]
  letI : IsIso (a ≫ b) := hfmin (a ≫ b) hab
  letI : IsIso (b ≫ a) := hgmin (b ≫ a) hba
  letI : IsSplitMono a := IsSplitMono.mk'
    { retraction := b ≫ inv (a ≫ b)
      id := by simp only [← Category.assoc, IsIso.hom_inv_id] }
  letI : IsSplitEpi a := IsSplitEpi.mk'
    { section_ := inv (b ≫ a) ≫ b
      id := by simp only [Category.assoc, IsIso.inv_hom_id] }
  letI : IsIso a := isIso_of_mono_of_isSplitEpi a
  exact ⟨asIso a, ha⟩

/-- Minimal left almost-split morphisms with the same source have
isomorphic targets, compatibly with their structure maps. -/
theorem exists_leftAlmostSplit_middleIso
    {Z E E' : C} {f : Z ⟶ E} {g : Z ⟶ E'}
    (hf : IsLeftAlmostSplit f) (hfmin : IsLeftMinimal f)
    (hg : IsLeftAlmostSplit g) (hgmin : IsLeftMinimal g) :
    ∃ e : E ≅ E', f ≫ e.hom = g := by
  obtain ⟨a, ha⟩ := hf.factors g hg.not_isSplitMono
  obtain ⟨b, hb⟩ := hg.factors f hf.not_isSplitMono
  have hab : f ≫ (a ≫ b) = f := by
    simp only [← Category.assoc, ha, hb]
  have hba : g ≫ (b ≫ a) = g := by
    simp only [← Category.assoc, hb, ha]
  letI : IsIso (a ≫ b) := hfmin (a ≫ b) hab
  letI : IsIso (b ≫ a) := hgmin (b ≫ a) hba
  letI : IsSplitMono a := IsSplitMono.mk'
    { retraction := b ≫ inv (a ≫ b)
      id := by simp only [← Category.assoc, IsIso.hom_inv_id] }
  letI : IsSplitEpi a := IsSplitEpi.mk'
    { section_ := inv (b ≫ a) ≫ b
      id := by simp only [Category.assoc, IsIso.inv_hom_id] }
  letI : IsIso a := isIso_of_mono_of_isSplitEpi a
  exact ⟨asIso a, ha⟩

/-- Precomposition by an isomorphism preserves left almost-splitness. -/
theorem IsLeftAlmostSplit.precomp_iso
    {X' X E : C} (i : X' ≅ X) {f : X ⟶ E}
    (hf : IsLeftAlmostSplit f) :
    IsLeftAlmostSplit (i.hom ≫ f) := by
  constructor
  · intro hs
    apply hf.not_isSplitMono
    letI : IsSplitMono (i.hom ≫ f) := hs
    rw [← i.inv_hom_id_assoc f]
    infer_instance
  · intro Y g hg
    have hg' : ¬ IsSplitMono (i.inv ≫ g) := by
      intro hs
      apply hg
      letI : IsSplitMono (i.inv ≫ g) := hs
      rw [← i.hom_inv_id_assoc g]
      infer_instance
    obtain ⟨h, hh⟩ := hf.factors (i.inv ≫ g) hg'
    refine ⟨h, ?_⟩
    rw [Category.assoc, hh, Iso.hom_inv_id_assoc]

/-- Precomposition by an isomorphism preserves left minimality. -/
theorem IsLeftMinimal.precomp_iso
    {X' X E : C} (i : X' ≅ X) {f : X ⟶ E}
    (hf : IsLeftMinimal f) :
    IsLeftMinimal (i.hom ≫ f) := by
  intro e he
  apply hf e
  apply (cancel_epi i.hom).1
  simpa only [Category.assoc] using he

/-- Postcomposition by an isomorphism preserves right almost-splitness. -/
theorem IsRightAlmostSplit.postcomp_iso
    {E Z Z' : C} {f : E ⟶ Z} (i : Z ≅ Z')
    (hf : IsRightAlmostSplit f) :
    IsRightAlmostSplit (f ≫ i.hom) := by
  constructor
  · intro hs
    apply hf.not_isSplitEpi
    obtain ⟨s⟩ := hs.exists_splitEpi
    exact IsSplitEpi.mk'
      { section_ := i.hom ≫ s.section_
        id := by
          apply (cancel_mono i.hom).1
          simp only [Category.assoc, s.id, Category.id_comp,
            Category.comp_id] }
  · intro X g hg
    have hg' : ¬ IsSplitEpi (g ≫ i.inv) := by
      intro hs
      apply hg
      obtain ⟨s⟩ := hs.exists_splitEpi
      exact IsSplitEpi.mk'
        { section_ := i.inv ≫ s.section_
          id := by
            apply (cancel_mono i.inv).1
            simp only [Category.assoc, s.id, Category.id_comp,
              Category.comp_id] }
    obtain ⟨h, hh⟩ := hf.factors (g ≫ i.inv) hg'
    refine ⟨h, ?_⟩
    rw [← Category.assoc, hh, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

/-- Uniqueness of a minimal right almost-split map identifies its kernels. -/
theorem nonempty_kernelIso_of_rightAlmostSplit
    [HasZeroMorphisms C] [HasKernels C]
    {E E' Z : C} {f : E ⟶ Z} {g : E' ⟶ Z}
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g) :
    Nonempty (kernel f ≅ kernel g) := by
  obtain ⟨e, he⟩ :=
    exists_rightAlmostSplit_middleIso hf hfmin hg hgmin
  exact ⟨kernel.mapIso f g e (Iso.refl Z) (by simpa using he.symm)⟩

/-- Uniqueness of a minimal left almost-split map identifies its
cokernels. -/
theorem nonempty_cokernelIso_of_leftAlmostSplit
    [HasZeroMorphisms C] [HasCokernels C]
    {Z E E' : C} {f : Z ⟶ E} {g : Z ⟶ E'}
    (hf : IsLeftAlmostSplit f) (hfmin : IsLeftMinimal f)
    (hg : IsLeftAlmostSplit g) (hgmin : IsLeftMinimal g) :
    Nonempty (cokernel f ≅ cokernel g) := by
  obtain ⟨e, he⟩ :=
    exists_leftAlmostSplit_middleIso hf hfmin hg hgmin
  exact ⟨cokernel.mapIso f g (Iso.refl Z) e (by simpa using he)⟩

section Abelian

variable [Abelian C]

/-- The canonical cokernel of the kernel inclusion of an epimorphism is
isomorphic to its target. -/
def cokernelKernelIsoTarget
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    cokernel (kernel.ι f) ≅ Y :=
  colimit.isoColimitCocone
    { cocone := CokernelCofork.ofπ f (kernel.condition f)
      isColimit := Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι f) (kernel.condition f))
        (kernelIsKernel f) }

/-- Dually, the canonical kernel of the cokernel projection of a
monomorphism is isomorphic to its source. -/
def kernelCokernelIsoSource
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    kernel (cokernel.π f) ≅ X :=
  limit.isoLimitCone
    { cone := KernelFork.ofι f (cokernel.condition f)
      isLimit := Abelian.monoIsKernelOfCokernel
        (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f))
        (cokernelIsCokernel f) }

end Abelian

end MBDVendor.QSE
