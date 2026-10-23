module

public import MBDVendor.Magnitude.Algebra.RightModuleAlmostSplit
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import MBDVendor.QSE.RepresentationTheory.IrreducibleRadicalQuotient

/-!
# The projective boundary almost-split morphism

For an indecomposable projective finitely generated module `P`, the inclusion
`rad P ⟶ P` is minimal right almost split.  The proof is a bounded adaptation
of the relevant arguments in the donor's `ProjectiveSimpleTop.lean`,
`ProjectiveSimpleRank.lean`, and `ProjectiveBoundaryAlmostSplit.lean` at commit
`d5ba0c48e7a851afd51247ff9cd81fc629e00ed2`.  Their unrelated simple-ranking
and standard-semantics layers are not imported.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open scoped ModuleCat.Algebra

namespace MBDVendor.Magnitude

universe u v w

/-- A categorical projective in `FGModuleCat` is projective as an unbundled
module. -/
theorem moduleProjective_of_fgProjective
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (X : FGModuleCat.{u} R) (hX : Projective X) :
    Module.Projective R X := by
  classical
  letI : Projective X := hX
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let F : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
  let q : F ⟶ X := FGModuleCat.ofHom p
  haveI : Epi q :=
    (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 X) q
  letI : Module.Projective R F :=
    Module.Projective.of_basis (Pi.basisFun R (Fin n))
  apply Module.Projective.of_split s.hom.hom q.hom.hom
  exact congrArg (fun f : X ⟶ X ↦ f.hom.hom) hs

/-- If a composite with a proper module quotient is surjective and the
intermediate target is projective with local endomorphism ring, then the
original map is surjective. -/
theorem surjective_of_quotient_comp_surjective
    {R : Type u} [Ring R]
    {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [IsLocalRing (Module.End R P)]
    {N : Submodule R P} (hN : N ≠ ⊤)
    {Z : Type w} [AddCommGroup Z] [Module R Z]
    (g : Z →ₗ[R] P)
    (hg : Function.Surjective (N.mkQ.comp g)) :
    Function.Surjective g := by
  obtain ⟨h, hh⟩ :=
    Module.projective_lifting_property (N.mkQ.comp g) N.mkQ hg
  let e : Module.End R P := g.comp h
  have heq : N.mkQ.comp e = N.mkQ := by
    simpa [e, LinearMap.comp_assoc] using hh
  let e' : Module.End R P := 1 - e
  have hsum : IsUnit (e + e') := by simp [e']
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with he | he'
  · have hesurj : Function.Surjective e :=
      ((Module.End.isUnit_iff e).mp he).2
    intro p
    obtain ⟨x, hx⟩ := hesurj p
    exact ⟨h x, by simpa [e] using hx⟩
  · have he'Surj : Function.Surjective e' :=
      ((Module.End.isUnit_iff e').mp he').2
    have hzero : N.mkQ.comp e' = 0 := by
      ext p
      have hp := DFunLike.congr_fun heq p
      simp only [LinearMap.comp_apply] at hp
      change N.mkQ p - N.mkQ (e p) = 0
      rw [hp]
      exact sub_self _
    have hqzero : N.mkQ = 0 := by
      ext p
      obtain ⟨x, hx⟩ := he'Surj p
      rw [← hx]
      exact DFunLike.congr_fun hzero x
    exfalso
    apply hN
    rw [← N.ker_mkQ, hqzero, LinearMap.ker_zero]

/-- A finite projective module with local endomorphism ring has a unique
maximal submodule, namely its module Jacobson radical. -/
theorem jacobson_isCoatom_of_projective_local_end
    {R : Type u} [Ring R]
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)] :
    IsCoatom (Module.jacobson R P) := by
  obtain ⟨N, hNcoatom, -⟩ :=
    (eq_top_or_exists_le_coatom
      (⊥ : Submodule R P)).resolve_left bot_ne_top
  have hUnique : ∀ M : Submodule R P, IsCoatom M → M = N := by
    intro M hMcoatom
    by_contra hMN
    have hsup : N ⊔ M = ⊤ :=
      hNcoatom.sup_eq_top_of_ne hMcoatom (Ne.symm hMN)
    have hcompSurj : Function.Surjective (N.mkQ.comp M.subtype) := by
      rw [← LinearMap.range_eq_top]
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact (N.map_mkQ_eq_top M).mpr hsup
    have hsubtypeSurj : Function.Surjective M.subtype :=
      surjective_of_quotient_comp_surjective
        hNcoatom.ne_top M.subtype hcompSurj
    apply hMcoatom.ne_top
    rw [← Submodule.range_subtype M, LinearMap.range_eq_top]
    exact hsubtypeSurj
  have hjac : Module.jacobson R P = N := by
    apply le_antisymm
    · exact sInf_le hNcoatom
    · rw [Module.jacobson, le_sInf_iff]
      intro M hM
      rw [hUnique M hM]
  rw [hjac]
  exact hNcoatom

/-- The module Jacobson radical of an arbitrary finitely generated module,
retained in the finitely generated module category. -/
def fgModuleRadical
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (P : FGModuleCat.{u} R) : FGModuleCat.{u} R := by
  letI : Module.Finite R (Module.jacobson R P) := inferInstance
  exact FGModuleCat.of R (Module.jacobson R P)

/-- The canonical inclusion of the module Jacobson radical into a finitely
generated module. -/
def fgModuleRadicalInclusion
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (P : FGModuleCat.{u} R) : fgModuleRadical P ⟶ P :=
  ConcreteCategory.ofHom (Module.jacobson R P).subtype

/-- For a nonzero projective with local module endomorphism ring, the
radical inclusion is right almost split. -/
theorem fgModuleRadicalInclusion_isRightAlmostSplit
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (P : FGModuleCat.{u} R) (hP : Projective P)
    [Nontrivial P] [IsLocalRing (Module.End R P)] :
    IsRightAlmostSplit (fgModuleRadicalInclusion P) := by
  classical
  letI : Projective P := hP
  letI : Module.Projective R P :=
    moduleProjective_of_fgProjective P hP
  have hradCoatom : IsCoatom (Module.jacobson R P) :=
    jacobson_isCoatom_of_projective_local_end
  constructor
  · intro hsplit
    letI : IsSplitEpi (fgModuleRadicalInclusion P) := hsplit
    have hsurjective : Function.Surjective
        (fgModuleRadicalInclusion P).hom.hom :=
      (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective
        (fgModuleRadicalInclusion P)).1 inferInstance
    apply hradCoatom.ne_top
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hsurjective x
    rw [← hy]
    exact y.2
  · intro X g hg
    have hrangeProper : LinearMap.range g.hom.hom ≠ ⊤ := by
      intro hrange
      have hsurjective : Function.Surjective g.hom.hom :=
        LinearMap.range_eq_top.mp hrange
      letI : Epi g :=
        (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective
          g).2 hsurjective
      apply hg
      obtain ⟨s, hs⟩ := Projective.factors (𝟙 P) g
      exact IsSplitEpi.mk' { section_ := s, id := hs }
    obtain ⟨M, hMCoatom, hrangeM⟩ :=
      (eq_top_or_exists_le_coatom
        (LinearMap.range g.hom.hom)).resolve_left hrangeProper
    have hradM : Module.jacobson R P ≤ M := by
      rw [Module.jacobson]
      exact sInf_le hMCoatom
    have hMrad : M = Module.jacobson R P :=
      (hradCoatom.le_iff_eq hMCoatom.ne_top).1 hradM
    have hrangeRadical :
        LinearMap.range g.hom.hom ≤ Module.jacobson R P := by
      simpa only [hMrad] using hrangeM
    let lift : X ⟶ fgModuleRadical P :=
      FGModuleCat.ofHom
        (LinearMap.codRestrict (Module.jacobson R P) g.hom.hom
          (fun x ↦ hrangeRadical
            (LinearMap.mem_range_self g.hom.hom x)))
    refine ⟨lift, ?_⟩
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- The radical inclusion of any finitely generated module is right
minimal. -/
theorem fgModuleRadicalInclusion_isRightMinimal
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (P : FGModuleCat.{u} R) :
    IsRightMinimal (fgModuleRadicalInclusion P) := by
  letI : Mono (fgModuleRadicalInclusion P) :=
    (MBDVendor.QSE.IndecomposableSkeleton.fg_mono_iff_injective
      (fgModuleRadicalInclusion P)).2
        (Module.jacobson R P).subtype_injective
  intro e he
  have heq : e = 𝟙 (fgModuleRadical P) :=
    (cancel_mono (fgModuleRadicalInclusion P)).1
      (by simpa only [Category.id_comp] using he)
  rw [heq]
  infer_instance

namespace RightModule.FiniteIndecomposableSkeleton

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The module Jacobson radical of a chosen right-module representative. -/
def projectiveBoundaryRadical (p : Fin S.n) :
    RightModule.FinitelyGeneratedCategory A :=
  letI : Module.Finite k (S.obj p) := S.obj_finite p
  letI : Module.Finite Aᵐᵒᵖ (S.obj p) :=
    Module.Finite.of_restrictScalars_finite k Aᵐᵒᵖ (S.obj p)
  FGModuleCat.of Aᵐᵒᵖ
    (Module.jacobson Aᵐᵒᵖ (S.fgObj p))

/-- The canonical inclusion `rad P ⟶ P`. -/
def projectiveBoundaryRadicalInclusion (p : Fin S.n) :
    S.projectiveBoundaryRadical p ⟶ S.fgObj p :=
  ConcreteCategory.ofHom
    (Module.jacobson Aᵐᵒᵖ (S.fgObj p)).subtype

/-- The Jacobson radical of a selected indecomposable projective is its
unique maximal submodule. -/
theorem projectiveBoundary_jacobson_isCoatom
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    IsCoatom (Module.jacobson Aᵐᵒᵖ (S.fgObj p)) := by
  letI : Projective (S.fgObj p) := hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Nontrivial (S.fgObj p) :=
    (S.fgObj_isIndecomposableModule p).nontrivial
  letI : IsLocalRing (Module.End Aᵐᵒᵖ (S.fgObj p)) :=
    MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
      (fgModule_isFiniteLength (k := k) (A := A) (S.fgObj p))
      (S.fgObj_isIndecomposableModule p)
  exact jacobson_isCoatom_of_projective_local_end

/-- The radical inclusion of an indecomposable projective is right almost
split. -/
theorem projectiveBoundaryRadicalInclusion_isRightAlmostSplit
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    IsRightAlmostSplit (S.projectiveBoundaryRadicalInclusion p) := by
  classical
  letI : Projective (S.fgObj p) := hp
  have hradCoatom := S.projectiveBoundary_jacobson_isCoatom p hp
  constructor
  · intro hsplit
    letI : IsSplitEpi (S.projectiveBoundaryRadicalInclusion p) := hsplit
    have hsurjective : Function.Surjective
        (S.projectiveBoundaryRadicalInclusion p).hom.hom :=
      (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective
        (S.projectiveBoundaryRadicalInclusion p)).1 inferInstance
    apply hradCoatom.ne_top
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hsurjective x
    rw [← hy]
    exact y.2
  · intro X g hg
    have hrangeProper : LinearMap.range g.hom.hom ≠ ⊤ := by
      intro hrange
      have hsurjective : Function.Surjective g.hom.hom :=
        LinearMap.range_eq_top.mp hrange
      letI : Epi g :=
        (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective g).2
          hsurjective
      apply hg
      obtain ⟨s, hs⟩ := Projective.factors (𝟙 (S.fgObj p)) g
      exact IsSplitEpi.mk' { section_ := s, id := hs }
    obtain ⟨M, hMCoatom, hrangeM⟩ :=
      (eq_top_or_exists_le_coatom
        (LinearMap.range g.hom.hom)).resolve_left hrangeProper
    have hradM : Module.jacobson Aᵐᵒᵖ (S.fgObj p) ≤ M := by
      rw [Module.jacobson]
      exact sInf_le hMCoatom
    have hMrad : M = Module.jacobson Aᵐᵒᵖ (S.fgObj p) :=
      (hradCoatom.le_iff_eq hMCoatom.ne_top).1 hradM
    have hrangeRadical :
        LinearMap.range g.hom.hom ≤
          Module.jacobson Aᵐᵒᵖ (S.fgObj p) := by
      simpa only [hMrad] using hrangeM
    let lift : X ⟶ S.projectiveBoundaryRadical p :=
      FGModuleCat.ofHom
        (LinearMap.codRestrict
          (Module.jacobson Aᵐᵒᵖ (S.fgObj p)) g.hom.hom
          (fun x ↦ hrangeRadical
            (LinearMap.mem_range_self g.hom.hom x)))
    refine ⟨lift, ?_⟩
    apply FGModuleCat.hom_ext
    ext x
    rfl

omit [FiniteDimensional k A] in
/-- The projective-boundary radical inclusion is right minimal. -/
theorem projectiveBoundaryRadicalInclusion_isRightMinimal (p : Fin S.n) :
    IsRightMinimal (S.projectiveBoundaryRadicalInclusion p) := by
  letI : Mono (S.projectiveBoundaryRadicalInclusion p) :=
    (IndecomposableSkeleton.fg_mono_iff_injective
      (S.projectiveBoundaryRadicalInclusion p)).2 (by
        change Function.Injective
          (Module.jacobson Aᵐᵒᵖ (S.fgObj p)).subtype
        exact (Module.jacobson Aᵐᵒᵖ (S.fgObj p)).subtype_injective)
  intro e he
  have heq : e = 𝟙 (S.projectiveBoundaryRadical p) :=
    (cancel_mono (S.projectiveBoundaryRadicalInclusion p)).1
      (by simpa only [Category.id_comp] using he)
  rw [heq]
  infer_instance

end RightModule.FiniteIndecomposableSkeleton

end MBDVendor.Magnitude
