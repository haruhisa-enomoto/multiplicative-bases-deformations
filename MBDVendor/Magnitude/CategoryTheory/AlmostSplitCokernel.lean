import MBDVendor.Magnitude.CategoryTheory.ProjectiveCover
import MBDVendor.QSE.RepresentationTheory.AlmostSplitUniqueness
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Simple

/-!
# Cokernels of minimal left almost-split monomorphisms

This file derives the cokernel half of the abstract Auslander--Reiten
sequence theorem from the already-vendored kernel half by passage to the
opposite category.  Keeping the transport explicit avoids duplicating the
pushout argument used for kernels.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MBDVendor.QSE

namespace MBDVendor.Magnitude.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A left almost-split morphism becomes right almost split after taking its
opposite. -/
theorem leftAlmostSplit_op {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f) : IsRightAlmostSplit f.op := by
  constructor
  · intro h
    apply hf.not_isSplitMono
    let s := h.exists_splitEpi.some
    exact IsSplitMono.mk'
      { retraction := s.section_.unop
        id := Quiver.Hom.op_inj (by simp [s.id]) }
  · intro Z g hg
    have hgn : ¬ IsSplitMono g.unop := by
      intro h
      let s := h.exists_splitMono.some
      exact hg (IsSplitEpi.mk'
        { section_ := s.retraction.op
          id := Quiver.Hom.unop_inj (by simp [s.id]) })
    obtain ⟨h, hh⟩ := hf.factors g.unop hgn
    exact ⟨h.op, Quiver.Hom.unop_inj (by simp [hh])⟩

/-- A left almost-split morphism in an opposite category becomes right
almost split after taking its underlying morphism. -/
theorem leftAlmostSplit_unop {X Y : Cᵒᵖ} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f) : IsRightAlmostSplit f.unop := by
  constructor
  · intro h
    apply hf.not_isSplitMono
    let s := h.exists_splitEpi.some
    exact IsSplitMono.mk'
      { retraction := s.section_.op
        id := Quiver.Hom.unop_inj (by simp [s.id]) }
  · intro Z g hg
    have hgn : ¬ IsSplitMono g.op := by
      intro h
      let s := h.exists_splitMono.some
      exact hg (IsSplitEpi.mk'
        { section_ := s.retraction.unop
          id := Quiver.Hom.op_inj (by simp [s.id]) })
    obtain ⟨h, hh⟩ := hf.factors g.op hgn
    exact ⟨h.unop, Quiver.Hom.op_inj (by simp [hh])⟩

/-- Left minimality becomes right minimality on the opposite morphism. -/
theorem leftMinimal_op {X Y : C} {f : X ⟶ Y}
    (hf : IsLeftMinimal f) : IsRightMinimal f.op := by
  intro e he
  have he' : f ≫ e.unop = f :=
    Quiver.Hom.op_inj (by simp [he])
  letI : IsIso e.unop := hf e.unop he'
  exact (isIso_unop_iff e).1 inferInstance

/-- Precomposition by an isomorphism preserves right almost-splitness. -/
theorem rightAlmostSplit_precomp_iso
    {E' E Z : C} (i : E' ≅ E) {f : E ⟶ Z}
    (hf : IsRightAlmostSplit f) :
    IsRightAlmostSplit (i.hom ≫ f) := by
  constructor
  · intro hs
    apply hf.not_isSplitEpi
    letI : IsSplitEpi (i.hom ≫ f) := hs
    rw [← i.inv_hom_id_assoc f]
    infer_instance
  · intro X g hg
    obtain ⟨h, hh⟩ := hf.factors g hg
    exact ⟨h ≫ i.inv, by
      simp only [Category.assoc, i.inv_hom_id_assoc, hh]⟩

variable [Abelian C]

/-- A left-minimal left almost-split morphism with injective source is
epic. -/
theorem leftAlmostSplit_epi_of_injective_source
    {X Y : C} (f : X ⟶ Y) [Injective X]
    (hf : IsLeftAlmostSplit f) (hmin : IsLeftMinimal f) :
    Epi f := by
  let p : X ⟶ Abelian.image f := Abelian.factorThruImage f
  let i : Abelian.image f ⟶ Y := Abelian.image.ι f
  have hpnot : ¬ IsSplitMono p := by
    intro hp
    letI : IsSplitMono p := hp
    haveI : IsIso p := isIso_of_epi_of_isSplitMono p
    have hmono : Mono f := by
      rw [← Abelian.image.fac f]
      infer_instance
    letI : Mono f := hmono
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := Injective.factorThru (𝟙 X) f
        id := Injective.comp_factorThru (𝟙 X) f }
  obtain ⟨h, hh⟩ := hf.factors p hpnot
  let e : Y ⟶ Y := h ≫ i
  have he : f ≫ e = f := by
    dsimp only [e, i]
    rw [← Category.assoc, hh, Abelian.image.fac]
  haveI : IsIso e := hmin e he
  have hiSplit : IsSplitEpi i :=
    IsSplitEpi.mk'
      { section_ := inv e ≫ h
        id := by
          dsimp only [e]
          rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi i := hiSplit
  haveI : IsIso i := isIso_of_mono_of_isSplitEpi i
  rw [← Abelian.image.fac f]
  infer_instance

/-- A right-minimal right almost-split morphism with projective target is
monic. -/
theorem rightAlmostSplit_mono_of_projective_target
    {X Y : C} (f : X ⟶ Y) [Projective Y]
    (hf : IsRightAlmostSplit f) (hmin : IsRightMinimal f) :
    Mono f := by
  let q : X ⟶ Abelian.image f := Abelian.factorThruImage f
  let i : Abelian.image f ⟶ Y := Abelian.image.ι f
  have hinot : ¬ IsSplitEpi i := by
    intro hi
    letI : IsSplitEpi i := hi
    haveI : IsIso i := isIso_of_mono_of_isSplitEpi i
    have hfepi : Epi f := by
      rw [← Abelian.image.fac f]
      infer_instance
    letI : Epi f := hfepi
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := Projective.factorThru (𝟙 Y) f
        id := Projective.factorThru_comp (𝟙 Y) f }
  obtain ⟨h, hh⟩ := hf.factors i hinot
  let e : X ⟶ X := q ≫ h
  have he : e ≫ f = f := by
    dsimp only [e, q, i]
    rw [Category.assoc, hh, Abelian.image.fac]
  haveI : IsIso e := hmin e he
  have hqSplit : IsSplitMono q :=
    IsSplitMono.mk'
      { retraction := h ≫ inv e
        id := by
          dsimp only [e]
          rw [← Category.assoc, IsIso.hom_inv_id] }
  letI : IsSplitMono q := hqSplit
  haveI : IsIso q := isIso_of_epi_of_isSplitMono q
  rw [← Abelian.image.fac f]
  infer_instance

/-- The cokernel of a monic right almost-split morphism into a projective
object is simple.  This is the abstract projective-boundary case of an
almost-split sequence. -/
theorem simple_cokernel_of_mono_rightAlmostSplit_projective
    {R P : C} (r : R ⟶ P) [Mono r] [Projective P]
    (hr : IsRightAlmostSplit r) :
    Simple (cokernel r) := by
  let q := cokernel.π r
  have hq_ne : q ≠ 0 := by
    intro hq
    haveI : Epi r := Preadditive.epi_of_cokernel_zero hq
    haveI : IsIso r := isIso_of_mono_of_epi r
    exact hr.not_isSplitEpi inferInstance
  have hC_id_ne : (𝟙 (cokernel r) : cokernel r ⟶ cokernel r) ≠ 0 := by
    intro hzero
    apply hq_ne
    rw [← Category.comp_id q, hzero, comp_zero]
  constructor
  intro X f hf
  constructor
  · intro _ hfzero
    apply hC_id_ne
    apply (cancel_epi f).1
    rw [Category.comp_id, hfzero, zero_comp]
  · intro hfzero
    by_contra hfiso
    let E := pullback q f
    let p : E ⟶ P := pullback.fst q f
    let s : E ⟶ X := pullback.snd q f
    have hp_not_split : ¬ IsSplitEpi p := by
      intro hp
      letI : IsSplitEpi p := hp
      letI : IsIso p := isIso_of_mono_of_isSplitEpi p
      have hqfac : (inv p ≫ s) ≫ f = q := by
        rw [Category.assoc, ← pullback.condition]
        simp
      haveI : Epi f := epi_of_epi_fac hqfac
      exact hfiso (isIso_of_mono_of_epi f)
    obtain ⟨a, ha⟩ := hr.factors p hp_not_split
    have hszero : s = 0 := by
      apply (cancel_mono f).1
      rw [← pullback.condition]
      change p ≫ q = 0 ≫ f
      rw [← ha, Category.assoc, cokernel.condition, comp_zero, zero_comp]
    haveI : Epi s := by
      dsimp only [s, q]
      infer_instance
    apply hfzero
    rw [← Category.id_comp f]
    apply (cancel_epi s).1
    rw [hszero, zero_comp, comp_zero]

/-- Simplicity descends from an object of an opposite abelian category to
its underlying object. -/
theorem simple_unop_of_simple {X : Cᵒᵖ} [Simple X] : Simple X.unop := by
  apply simple_of_cosimple
  intro Z f hfepi
  letI : Simple (Opposite.op X.unop) :=
    Simple.of_iso (eqToIso (Opposite.op_unop X))
  haveI : Mono f.op := inferInstance
  have h := Simple.mono_isIso_iff_nonzero f.op
  constructor
  · intro hfiso
    haveI : IsIso f := hfiso
    haveI : IsIso f.op := (isIso_op_iff f).2 inferInstance
    have hfop : f.op ≠ 0 := h.mp inferInstance
    intro hfzero
    apply hfop
    rw [hfzero]
    rfl
  · intro hf
    have hfop : f.op ≠ 0 := by
      intro hfopzero
      apply hf
      apply Quiver.Hom.op_inj
      simpa using hfopzero
    haveI : IsIso f.op := h.mpr hfop
    exact (isIso_op_iff f).1 inferInstance

/-- The kernel of an epic left almost-split morphism out of an injective
object is simple.  This is the injective-boundary dual of
`simple_cokernel_of_mono_rightAlmostSplit_projective`. -/
theorem simple_kernel_of_epi_leftAlmostSplit_injective
    {I R : C} (r : I ⟶ R) [Epi r] [Injective I]
    (hr : IsLeftAlmostSplit r) :
    Simple (kernel r) := by
  haveI : Mono r.op := inferInstance
  haveI : Projective (Opposite.op I) := inferInstance
  have hsimpleOp : Simple (cokernel r.op) :=
    simple_cokernel_of_mono_rightAlmostSplit_projective
      r.op (leftAlmostSplit_op hr)
  letI : Simple (cokernel r.op) := hsimpleOp
  have hsimpleUnop : Simple (cokernel r.op).unop :=
    simple_unop_of_simple
  letI : Simple (cokernel r.op).unop := hsimpleUnop
  exact Simple.of_iso (cokernelOpUnop r).symm

/-- If the projective target of a monic right almost-split morphism has
local endomorphism ring, every nonzero morphism from it to a simple object
exhibits that simple as the cokernel. -/
noncomputable def cokernelIsoSimpleTarget_of_mono_rightAlmostSplit_projective
    {R P S : C} (r : R ⟶ P) [Mono r] [Projective P]
    [IsLocalRing (End P)] (hr : IsRightAlmostSplit r) [Simple S]
    (p : P ⟶ S) (hp : p ≠ 0) :
    cokernel r ≅ S := by
  letI : Simple (cokernel r) :=
    simple_cokernel_of_mono_rightAlmostSplit_projective r hr
  haveI : Epi p := epi_of_nonzero_to_simple hp
  have hrp : r ≫ p = 0 := by
    by_contra hrp
    letI : Epi (r ≫ p) := epi_of_nonzero_to_simple hrp
    let s := Projective.factorThru p (r ≫ p)
    have he : (s ≫ r) ≫ p = p := by
      rw [Category.assoc, Projective.factorThru_comp]
    have hone_sub_e_p : (𝟙 P - (s ≫ r)) ≫ p = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
    let e : End P := s ≫ r
    let e' : End P := 1 - e
    have he'p : e' ≫ p = 0 := by
      dsimp only [e', e]
      rw [End.one_def]
      exact hone_sub_e_p
    have hone_sub_e_not_unit : ¬ IsUnit (1 - e) := by
      intro hunit
      have hunit' : IsUnit e' := by simpa only [e'] using hunit
      letI : IsIso e' := (isUnit_iff_isIso e').1 hunit'
      apply hp
      rw [← IsIso.inv_hom_id_assoc e' p, he'p, comp_zero]
    have hsum : IsUnit (e + (1 - e)) := by
      rw [add_sub_cancel]
      exact isUnit_one
    have heunit : IsUnit e :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_right
        hone_sub_e_not_unit
    letI : IsIso (s ≫ r) := by
      simpa only [e] using (isUnit_iff_isIso e).1 heunit
    let sec : P ⟶ R := inv (s ≫ r) ≫ s
    have hsection : sec ≫ r = 𝟙 P := by
      dsimp only [sec]
      rw [Category.assoc, IsIso.inv_hom_id]
    apply hr.not_isSplitEpi
    exact IsSplitEpi.mk' { section_ := sec, id := hsection }
  let e : cokernel r ⟶ S := cokernel.desc r p hrp
  have heq : cokernel.π r ≫ e = p := cokernel.π_desc r p hrp
  haveI : Epi e := epi_of_epi_fac heq
  have he : e ≠ 0 := by
    intro hezero
    apply hp
    rw [← heq, hezero, comp_zero]
  letI : IsIso e := isIso_of_epi_of_nonzero he
  exact asIso e

/-- In an abelian category with enough projectives, a monic right
almost-split morphism has projective target. -/
theorem projective_of_mono_rightAlmostSplit
    [EnoughProjectives C]
    {X Y : C} (f : X ⟶ Y) [Mono f]
    (hf : IsRightAlmostSplit f) : Projective Y := by
  classical
  by_contra hY
  let P := Classical.choice (EnoughProjectives.presentation Y)
  have hPnot : ¬ IsSplitEpi P.f := by
    intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    apply hY
    exact MBDVendor.Magnitude.projective_of_retract
      (inferInstance : Projective P.p) s.section_ P.f s.id
  obtain ⟨h, hh⟩ := hf.factors P.f hPnot
  haveI : Epi f := epi_of_epi_fac hh
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact hf.not_isSplitEpi inferInstance

omit [Abelian C] in
/-- In a category with enough projectives, a right almost-split map ending at
a nonprojective object is epic. -/
theorem IsRightAlmostSplit.epi_of_not_projective
    [EnoughProjectives C]
    {X Y : C} (f : X ⟶ Y) (hf : IsRightAlmostSplit f)
    (hY : ¬ Projective Y) : Epi f := by
  classical
  let P := Classical.choice (EnoughProjectives.presentation Y)
  have hPnot : ¬ IsSplitEpi P.f := by
    intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    apply hY
    exact MBDVendor.Magnitude.projective_of_retract
      (inferInstance : Projective P.p) s.section_ P.f s.id
  obtain ⟨h, hh⟩ := hf.factors P.f hPnot
  exact epi_of_epi_fac hh

/-- The cokernel projection of a left-minimal left almost-split monomorphism
is right almost split. -/
theorem leftAlmostSplit_cokernel_π_isRightAlmostSplit
    {X Y : C} (f : X ⟶ Y) [Mono f]
    (hf : IsLeftAlmostSplit f) (hmin : IsLeftMinimal f) :
    IsRightAlmostSplit (cokernel.π f) := by
  let hfop : IsRightAlmostSplit f.op := leftAlmostSplit_op hf
  let hminop : IsRightMinimal f.op := leftMinimal_op hmin
  have hk : IsLeftAlmostSplit (kernel.ι f.op) :=
    hfop.kernel_ι_isLeftAlmostSplit f.op hminop
  have hku : IsRightAlmostSplit (kernel.ι f.op).unop :=
    leftAlmostSplit_unop hk
  have hpost : IsRightAlmostSplit
      ((kernel.ι f.op).unop ≫ (kernelOpUnop f).hom) :=
    IsRightAlmostSplit.postcomp_iso (kernelOpUnop f) hku
  let e : (Opposite.op Y).unop ≅ Y :=
    eqToIso (Opposite.unop_op Y)
  have hcomp : e.hom ≫ cokernel.π f =
      (kernel.ι f.op).unop ≫ (kernelOpUnop f).hom := by
    apply (cancel_mono (kernelOpUnop f).inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [e]
    change
      eqToHom (Opposite.unop_op Y) ≫ cokernel.π f ≫
          (kernelOpUnop f).inv =
        (kernel.ι f.op).unop
    exact (kernel.ι_op f).symm
  have he : IsRightAlmostSplit (e.hom ≫ cokernel.π f) := by
    rw [hcomp]
    exact hpost
  have htransport := rightAlmostSplit_precomp_iso e.symm he
  simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using htransport

end MBDVendor.Magnitude.CategoryTheory
