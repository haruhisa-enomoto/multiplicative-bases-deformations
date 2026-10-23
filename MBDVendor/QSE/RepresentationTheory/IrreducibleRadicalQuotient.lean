module

public import MBDVendor.QSE.CategoryTheory.CategoricalRadical
public import MBDVendor.QSE.RepresentationTheory.FiniteTypeAlmostSplit

/-!
# Irreducible morphisms and the categorical radical quotient

This file formalizes the manuscript convention
`Irr(X,Y) = rad(X,Y) / rad²(X,Y)` for two representatives in a complete
indecomposable skeleton.  The construction uses additive Hom-groups and is
therefore independent of a ground field.

Between indecomposable finite-length objects, a radical map is equivalently
a nonsplit epimorphism, or equivalently a nonsplit monomorphism.  The square
is expressed by one factorization through an arbitrary finitely generated
module: finite sums of radical composites consolidate into such a
factorization through a finite biproduct.  Thus this is the square of the
categorical radical ideal, not the square of either endpoint endomorphism
ring.

No algebra presentation or classification of modules is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

private theorem isSplitEpi_of_isUnit_section_comp
    {x y : ι} (f : σ.obj x ⟶ σ.obj y)
    (s : σ.obj y ⟶ σ.obj x)
    (hu : IsUnit ((s ≫ f).hom.hom)) :
    IsSplitEpi f := by
  have hbij : Function.Bijective (s ≫ f).hom.hom :=
    (Module.End.isUnit_iff _).mp hu
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  haveI : IsIso (U.map (s ≫ f)) := by
    change IsIso ((s ≫ f).hom)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  letI : IsIso (s ≫ f) := isIso_of_reflects_iso (s ≫ f) U
  exact IsSplitEpi.mk'
    { section_ := inv (s ≫ f) ≫ s
      id := by simp }

omit [IsNoetherianRing R] in
private theorem isIso_of_isUnit_hom_hom
    {X : FGModuleCat.{w} R} (f : X ⟶ X)
    (hu : IsUnit f.hom.hom) : IsIso f := by
  have hbij : Function.Bijective f.hom.hom :=
    (Module.End.isUnit_iff _).mp hu
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  haveI : IsIso (U.map f) := by
    change IsIso f.hom
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  exact isIso_of_reflects_iso f U

/-- The field-free radical Hom-group between two chosen indecomposables,
realized as the morphisms which are not split epimorphisms. -/
def radicalHomAddSubgroup (x y : ι) :
    AddSubgroup (σ.obj x ⟶ σ.obj y) where
  carrier := {f | ¬ IsSplitEpi f}
  zero_mem' := by
    intro h
    letI : IsSplitEpi (0 : σ.obj x ⟶ σ.obj y) := h
    have hy : IsZero (σ.obj y) :=
      (IsZero.iff_isSplitEpi_eq_zero
        (0 : σ.obj x ⟶ σ.obj y)).2 rfl
    let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
    have hy' : IsZero (U.obj (σ.obj y)) := U.map_isZero hy
    have hs : Subsingleton (σ.obj y) :=
      ModuleCat.isZero_iff_subsingleton.mp hy'
    exact not_nontrivial_iff_subsingleton.mpr hs
      (σ.indecomposable y).nontrivial
  add_mem' := by
    intro f g hf hg hfg
    let H : σ.obj x ⟶ σ.obj y := f + g
    letI : IsSplitEpi H := hfg
    let s : σ.obj y ⟶ σ.obj x := section_ H
    let cf : Module.End R (σ.obj y) :=
      f.hom.hom.comp s.hom.hom
    let cg : Module.End R (σ.obj y) :=
      g.hom.hom.comp s.hom.hom
    have hcat : s ≫ H = 𝟙 _ := IsSplitEpi.id H
    have hlin := congrArg
      (fun q : σ.obj y ⟶ σ.obj y ↦ q.hom.hom) hcat
    change (f.hom.hom + g.hom.hom).comp s.hom.hom =
      LinearMap.id at hlin
    have hsum : cf + cg = 1 := by
      apply LinearMap.ext
      intro z
      have hz := LinearMap.congr_fun hlin z
      simpa [cf, cg, LinearMap.comp_apply, LinearMap.add_apply] using hz
    letI : IsLocalRing (Module.End R (σ.obj y)) :=
      MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
        (σ.finiteLength y) (σ.indecomposable y)
    have hu : IsUnit (cf + cg) := hsum.symm ▸ isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hcf | hcg
    · exact hf (isSplitEpi_of_isUnit_section_comp σ f s hcf)
    · exact hg (isSplitEpi_of_isUnit_section_comp σ g s hcg)
  neg_mem' := by
    intro f hf hneg
    obtain ⟨se⟩ := hneg.exists_splitEpi
    apply hf
    exact IsSplitEpi.mk'
      { section_ := -se.section_
        id := by
          simpa only [Preadditive.neg_comp, Preadditive.comp_neg]
            using se.id }

@[simp] theorem mem_radicalHomAddSubgroup_iff_not_isSplitEpi
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) :
    f ∈ σ.radicalHomAddSubgroup x y ↔ ¬ IsSplitEpi f :=
  Iff.rfl

/-- On the duplicate-free indecomposable skeleton, the same radical group
consists of the morphisms which are not split monomorphisms. -/
theorem mem_radicalHomAddSubgroup_iff_not_isSplitMono
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) :
    f ∈ σ.radicalHomAddSubgroup x y ↔ ¬ IsSplitMono f := by
  rw [mem_radicalHomAddSubgroup_iff_not_isSplitEpi]
  constructor
  · intro hEpi hMono
    letI : IsSplitMono f := hMono
    exact hEpi (σ.isSplitEpi_of_isSplitMono_between_obj f)
  · intro hMono hEpi
    letI : IsSplitEpi f := hEpi
    exact hMono (σ.isSplitMono_of_isSplitEpi_between_obj f)

/-- A morphism out of a chosen indecomposable is categorical-radical exactly
when it is not a split monomorphism, even when its target is an arbitrary
finitely generated module. -/
theorem isRadicalMorphism_iff_not_isSplitMono_from_obj
    {x : ι} {M : FGModuleCat.{w} R} (g : σ.obj x ⟶ M) :
    CategoricalRadical.IsRadicalMorphism g ↔ ¬ IsSplitMono g := by
  constructor
  · intro hg hsplit
    letI : IsSplitMono g := hsplit
    let r : M ⟶ σ.obj x := retraction g
    have hr : g ≫ r = 𝟙 (σ.obj x) := IsSplitMono.id g
    have hi : IsIso (𝟙 (σ.obj x) - g ≫ r) := hg r
    have hzero : 𝟙 (σ.obj x) - g ≫ r = 0 := by
      rw [hr, sub_self]
    haveI : IsIso (0 : σ.obj x ⟶ σ.obj x) := hzero ▸ hi
    have hx : IsZero (σ.obj x) :=
      (IsZero.iff_isSplitEpi_eq_zero
        (0 : σ.obj x ⟶ σ.obj x)).2 rfl
    let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
    have hx' : IsZero (U.obj (σ.obj x)) := U.map_isZero hx
    have hs : Subsingleton (σ.obj x) :=
      ModuleCat.isZero_iff_subsingleton.mp hx'
    exact not_nontrivial_iff_subsingleton.mpr hs
      (σ.indecomposable x).nontrivial
  · intro hg r
    let a : Module.End R (σ.obj x) := (g ≫ r).hom.hom
    have ha : ¬ IsUnit a := by
      intro hu
      letI : IsIso (g ≫ r) :=
        isIso_of_isUnit_hom_hom (g ≫ r) hu
      apply hg
      exact IsSplitMono.mk'
        { retraction := r ≫ inv (g ≫ r)
          id := by rw [← Category.assoc]; simp }
    letI : IsLocalRing (Module.End R (σ.obj x)) :=
      MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
        (σ.finiteLength x) (σ.indecomposable x)
    have hsum : IsUnit (a + (1 - a)) := by
      rw [show a + (1 - a) = 1 by abel]
      exact isUnit_one
    have hu : IsUnit (1 - a) :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left ha
    let q : σ.obj x ⟶ σ.obj x := 𝟙 (σ.obj x) - g ≫ r
    let underlying :
        (σ.obj x ⟶ σ.obj x) →+ Module.End R (σ.obj x) :=
      { toFun := fun t ↦ t.hom.hom
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    have hq : q.hom.hom = 1 - a := by
      change underlying (𝟙 (σ.obj x) - g ≫ r) =
        underlying (𝟙 (σ.obj x)) - underlying (g ≫ r)
      exact underlying.map_sub _ _
    apply isIso_of_isUnit_hom_hom q
    rw [hq]
    exact hu

/-- A morphism into a chosen indecomposable is categorical-radical exactly
when it is not a split epimorphism, even when its source is an arbitrary
finitely generated module. -/
theorem isRadicalMorphism_iff_not_isSplitEpi_to_obj
    {M : FGModuleCat.{w} R} {y : ι} (h : M ⟶ σ.obj y) :
    CategoricalRadical.IsRadicalMorphism h ↔ ¬ IsSplitEpi h := by
  constructor
  · intro hh hsplit
    letI : IsSplitEpi h := hsplit
    let s : σ.obj y ⟶ M := section_ h
    have hs : s ≫ h = 𝟙 (σ.obj y) := IsSplitEpi.id h
    have hi : IsIso (𝟙 M - h ≫ s) := hh s
    have hzero : s ≫ (𝟙 M - h ≫ s) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hs,
        Category.id_comp, sub_self]
    have hs0 : s = 0 := by
      rw [← cancel_mono (𝟙 M - h ≫ s)]
      simpa using hzero
    have hidzero : (𝟙 (σ.obj y) : σ.obj y ⟶ σ.obj y) = 0 := by
      rw [← hs, hs0, zero_comp]
    haveI : IsIso (0 : σ.obj y ⟶ σ.obj y) := hidzero ▸ inferInstance
    have hy : IsZero (σ.obj y) :=
      (IsZero.iff_isSplitEpi_eq_zero
        (0 : σ.obj y ⟶ σ.obj y)).2 rfl
    let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
    have hy' : IsZero (U.obj (σ.obj y)) := U.map_isZero hy
    have hsub : Subsingleton (σ.obj y) :=
      ModuleCat.isZero_iff_subsingleton.mp hy'
    exact not_nontrivial_iff_subsingleton.mpr hsub
      (σ.indecomposable y).nontrivial
  · intro hh s
    let a : Module.End R (σ.obj y) := (s ≫ h).hom.hom
    have ha : ¬ IsUnit a := by
      intro hu
      letI : IsIso (s ≫ h) :=
        isIso_of_isUnit_hom_hom (s ≫ h) hu
      apply hh
      exact IsSplitEpi.mk'
        { section_ := inv (s ≫ h) ≫ s
          id := by rw [Category.assoc]; simp }
    letI : IsLocalRing (Module.End R (σ.obj y)) :=
      MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
        (σ.finiteLength y) (σ.indecomposable y)
    have hsum : IsUnit (a + (1 - a)) := by
      rw [show a + (1 - a) = 1 by abel]
      exact isUnit_one
    have hu : IsUnit (1 - a) :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left ha
    let q : σ.obj y ⟶ σ.obj y := 𝟙 (σ.obj y) - s ≫ h
    let underlying :
        (σ.obj y ⟶ σ.obj y) →+ Module.End R (σ.obj y) :=
      { toFun := fun t ↦ t.hom.hom
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    have hq : q.hom.hom = 1 - a := by
      change underlying (𝟙 (σ.obj y) - s ≫ h) =
        underlying (𝟙 (σ.obj y)) - underlying (s ≫ h)
      exact underlying.map_sub _ _
    haveI : IsIso q := by
      apply isIso_of_isUnit_hom_hom q
      rw [hq]
      exact hu
    exact CategoricalRadical.isIso_one_sub_comp s h

/-- On chosen indecomposables, the nonsplit-epimorphism description agrees
with the intrinsic categorical Jacobson radical, in its source-object
convention. -/
theorem mem_radicalHomAddSubgroup_iff_isRadicalMorphism
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) :
    f ∈ σ.radicalHomAddSubgroup x y ↔
      CategoricalRadical.IsRadicalMorphism f := by
  rw [mem_radicalHomAddSubgroup_iff_not_isSplitMono]
  exact (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj f).symm

/-- A morphism between chosen indecomposables has a radical-square
factorization if it factors through an arbitrary finitely generated module,
with a nonsplit-monic first factor and a nonsplit-epic second factor. -/
def HasRadicalSquareFactorization {x y : ι}
    (f : σ.obj x ⟶ σ.obj y) : Prop :=
  ∃ (M : FGModuleCat.{w} R) (g : σ.obj x ⟶ M)
      (h : M ⟶ σ.obj y),
    ¬ IsSplitMono g ∧ ¬ IsSplitEpi h ∧ g ≫ h = f

/-- The arbitrary-middle predicate is literally one composite of two
categorical-radical morphisms. -/
theorem hasRadicalSquareFactorization_iff_categoricalRadical
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) :
    σ.HasRadicalSquareFactorization f ↔
      ∃ (M : FGModuleCat.{w} R) (g : σ.obj x ⟶ M)
          (h : M ⟶ σ.obj y),
        CategoricalRadical.IsRadicalMorphism g ∧
          CategoricalRadical.IsRadicalMorphism h ∧ g ≫ h = f := by
  constructor
  · rintro ⟨M, g, h, hg, hh, hcomp⟩
    exact ⟨M, g, h,
      (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj g).2 hg,
      (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj h).2 hh, hcomp⟩
  · rintro ⟨M, g, h, hg, hh, hcomp⟩
    exact ⟨M, g, h,
      (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj g).1 hg,
      (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj h).1 hh, hcomp⟩

/-- The field-free square of the categorical radical between two chosen
indecomposables.  Closure under addition consolidates two factorizations
through their biproduct. -/
def radicalSquareHomAddSubgroup (x y : ι) :
    AddSubgroup (σ.obj x ⟶ σ.obj y) where
  carrier := σ.HasRadicalSquareFactorization
  zero_mem' := by
    let F : Fin 0 → FGModuleCat.{w} R := fun j ↦ Fin.elim0 j
    let out : ∀ j, σ.obj x ⟶ F j := fun j ↦ Fin.elim0 j
    let inn : ∀ j, F j ⟶ σ.obj y := fun j ↦ Fin.elim0 j
    refine ⟨⨁ F, biproduct.lift out, biproduct.desc inn, ?_, ?_, ?_⟩
    · exact σ.biproductLift_not_isSplitMono F out
        (fun j ↦ Fin.elim0 j)
    · exact σ.biproductDesc_not_isSplitEpi F inn
        (fun j ↦ Fin.elim0 j)
    · rw [biproduct.lift_desc]
      simp
  add_mem' := by
    intro f₁ f₂ hf₁ hf₂
    obtain ⟨M₁, g₁, h₁, hg₁, hh₁, hcomp₁⟩ := hf₁
    obtain ⟨M₂, g₂, h₂, hg₂, hh₂, hcomp₂⟩ := hf₂
    let F : Fin 2 → FGModuleCat.{w} R :=
      Fin.cases M₁ (fun _ ↦ M₂)
    let out : ∀ j, σ.obj x ⟶ F j :=
      Fin.cases g₁ (fun _ ↦ g₂)
    let inn : ∀ j, F j ⟶ σ.obj y :=
      Fin.cases h₁ (fun _ ↦ h₂)
    have hout : ∀ j, ¬ IsSplitMono (out j) := by
      intro j
      fin_cases j
      · exact hg₁
      · exact hg₂
    have hinn : ∀ j, ¬ IsSplitEpi (inn j) := by
      intro j
      fin_cases j
      · exact hh₁
      · exact hh₂
    refine ⟨⨁ F, biproduct.lift out, biproduct.desc inn,
      σ.biproductLift_not_isSplitMono F out hout,
      σ.biproductDesc_not_isSplitEpi F inn hinn, ?_⟩
    rw [biproduct.lift_desc, Fin.sum_univ_two]
    have hcomp₀' : out 0 ≫ inn 0 = f₁ := by
      change g₁ ≫ h₁ = f₁
      exact hcomp₁
    have hcomp₁' : out 1 ≫ inn 1 = f₂ := by
      change g₂ ≫ h₂ = f₂
      exact hcomp₂
    rw [hcomp₀', hcomp₁']
  neg_mem' := by
    intro f hf
    obtain ⟨M, g, h, hg, hh, hcomp⟩ := hf
    refine ⟨M, g, -h, hg, ?_, ?_⟩
    · intro hneg
      obtain ⟨se⟩ := hneg.exists_splitEpi
      apply hh
      exact IsSplitEpi.mk'
        { section_ := -se.section_
          id := by
            simpa only [Preadditive.neg_comp, Preadditive.comp_neg]
              using se.id }
    · rw [Preadditive.comp_neg, hcomp]

@[simp] theorem mem_radicalSquareHomAddSubgroup_iff
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) :
    f ∈ σ.radicalSquareHomAddSubgroup x y ↔
      σ.HasRadicalSquareFactorization f :=
  Iff.rfl

/-- Every radical-square morphism is radical. -/
theorem radicalSquareHomAddSubgroup_le_radicalHomAddSubgroup
    (x y : ι) :
    σ.radicalSquareHomAddSubgroup x y ≤
      σ.radicalHomAddSubgroup x y := by
  intro f hf
  obtain ⟨M, g, h, _hg, hh, hcomp⟩ := hf
  intro hsplit
  obtain ⟨se⟩ := hsplit.exists_splitEpi
  apply hh
  exact IsSplitEpi.mk'
    { section_ := se.section_ ≫ g
      id := by
        simpa only [Category.assoc, hcomp] using se.id }

/-- The denominator `rad²(X,Y)` regarded as a subgroup of `rad(X,Y)`. -/
def radicalSquareInRadical (x y : ι) :
    AddSubgroup (σ.radicalHomAddSubgroup x y) :=
  (σ.radicalSquareHomAddSubgroup x y).comap
    (σ.radicalHomAddSubgroup x y).subtype

/-- The manuscript's field-free quotient
`Irr(X,Y) = rad(X,Y) / rad²(X,Y)`. -/
abbrev irreducibleHomQuotient (x y : ι) :=
  (σ.radicalHomAddSubgroup x y) ⧸ σ.radicalSquareInRadical x y

/-- Between chosen indecomposables, categorical irreducibility is exactly
membership in `rad` but not in `rad²`. -/
theorem isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) :
    IsIrreducibleMorphism f ↔
      f ∈ σ.radicalHomAddSubgroup x y ∧
        f ∉ σ.radicalSquareHomAddSubgroup x y := by
  constructor
  · intro hf
    refine ⟨hf.not_isSplitEpi, ?_⟩
    rintro ⟨M, g, h, hg, hh, hcomp⟩
    rcases hf.factorization g h hcomp with hgsplit | hhsplit
    · exact hg hgsplit
    · exact hh hhsplit
  · rintro ⟨hfrad, hfsquare⟩
    refine
      { not_isSplitMono := ?_
        not_isSplitEpi := hfrad
        factorization := ?_ }
    · intro hmono
      letI : IsSplitMono f := hmono
      exact hfrad (σ.isSplitEpi_of_isSplitMono_between_obj f)
    · intro M g h hcomp
      by_cases hg : IsSplitMono g
      · exact Or.inl hg
      by_cases hh : IsSplitEpi h
      · exact Or.inr hh
      exact (hfsquare ⟨M, g, h, hg, hh, hcomp⟩).elim

/-- The quotient `rad(X,Y) / rad²(X,Y)` is nontrivial exactly when there
is an irreducible morphism from `X` to `Y`. -/
theorem nontrivial_irreducibleHomQuotient_iff_hasIrreducibleMorphism
    (x y : ι) :
    Nontrivial (σ.irreducibleHomQuotient x y) ↔
      HasIrreducibleMorphism (σ.obj x) (σ.obj y) := by
  change
    Nontrivial
        ((σ.radicalHomAddSubgroup x y) ⧸
          σ.radicalSquareInRadical x y) ↔
      HasIrreducibleMorphism (σ.obj x) (σ.obj y)
  rw [QuotientAddGroup.nontrivial_iff]
  constructor
  · intro hproper
    obtain ⟨f, hf⟩ :=
      SetLike.exists_not_mem_of_ne_top
        (σ.radicalSquareInRadical x y) hproper
    refine ⟨f.1,
      (σ.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare
        f.1).2 ⟨f.2, ?_⟩⟩
    exact hf
  · rintro ⟨f, hf⟩ htop
    obtain ⟨hfrad, hfsquare⟩ :=
      (σ.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare
        f).1 hf
    have hmem :
        (⟨f, hfrad⟩ : σ.radicalHomAddSubgroup x y) ∈
          σ.radicalSquareInRadical x y := by
      rw [htop]
      exact Set.mem_univ _
    exact hfsquare hmem

/-- Manuscript-style orientation of the nonzero-quotient criterion. -/
theorem hasIrreducibleMorphism_iff_nontrivial_irreducibleHomQuotient
    (x y : ι) :
    HasIrreducibleMorphism (σ.obj x) (σ.obj y) ↔
      Nontrivial (σ.irreducibleHomQuotient x y) :=
  (σ.nontrivial_irreducibleHomQuotient_iff_hasIrreducibleMorphism x y).symm

end MBDVendor.QSE.IndecomposableSkeleton
