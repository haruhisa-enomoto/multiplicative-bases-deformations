import MBDVendor.QSE.RepresentationTheory.SubmoduleAntiExchange

/-!
# Extremality and relative split injectivity

This file gives the direct submodule-side bridge between extreme points and
relative split injectives.  The proof uses common kernels and the nilpotent
Jacobson radical; it does not invoke categorical duality or
Krull--Schmidt multiplicity uniqueness.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- An indecomposable is relatively split injective in `C` when every
monomorphism from it to an explicitly presented object of `add C`
admits a retraction. -/
def IsRelativeSplitInjective (C : Set ι) (x : ι) : Prop :=
  ∀ P : σ.SubPresentation C (σ.obj x),
    Nonempty (SplitMono P.map)

omit [IsNoetherianRing R] in
private theorem fg_hom_hom_sum {J : Type*} [Fintype J]
    {X Y : FGModuleCat.{w} R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by
  have h :
      (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h, ModuleCat.hom_sum]

omit [IsNoetherianRing R] in
private theorem biproduct_apply_eq_zero_of_components
    {J : Type*} [Fintype J]
    {X : FGModuleCat.{w} R} {Y : J → FGModuleCat.{w} R}
    (g : X ⟶ ⨁ Y) (x : X)
    (h : ∀ j, (g ≫ biproduct.π Y j).hom.hom x = 0) :
    g.hom.hom x = 0 := by
  classical
  let C : Submodule R X := R ∙ x
  letI : Module.Finite R C :=
    Module.Finite.of_fg (Submodule.fg_span_singleton x)
  let e : FGModuleCat.of R C ⟶ X :=
    FGModuleCat.ofHom C.subtype
  have he : e ≫ g = 0 := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, zero_comp]
    apply FGModuleCat.hom_ext
    ext z
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp z.2
    change (g ≫ biproduct.π Y j).hom.hom z.1 = 0
    rw [← hr, map_smul, h j, smul_zero]
  let z : C := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hz := congrArg
    (fun f : FGModuleCat.of R C ⟶ ⨁ Y ↦ f.hom.hom z) he
  change g.hom.hom (C.subtype z) = 0 at hz
  exact hz

/-- A split embedding of `X` into a sum of indecomposables all distinct
from `X` would put the identity in the endomorphism radical. -/
theorem not_splitMono_of_labels_ne
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (hne : ∀ t, x ≠ P.label t) :
    ¬ Nonempty (SplitMono P.map) := by
  classical
  rintro ⟨s⟩
  letI : Fintype P.index := FintypeCat.fintype
  let a (t : P.index) : σ.obj x ⟶ σ.obj (P.label t) :=
    P.map ≫
      biproduct.π
        (fun j : P.index ↦ σ.obj (P.label j)) t
  let b (t : P.index) : σ.obj (P.label t) ⟶ σ.obj x :=
    biproduct.ι
        (fun j : P.index ↦ σ.obj (P.label j)) t ≫
      s.retraction
  have hcat :
      (𝟙 (σ.obj x)) =
        ∑ t : P.index, a t ≫ b t := by
    rw [← s.id]
    calc
      P.map ≫ s.retraction =
          (P.map ≫ 𝟙 _) ≫ s.retraction := by simp
      _ =
          (P.map ≫
            (∑ t : P.index,
              biproduct.π
                  (fun j : P.index ↦ σ.obj (P.label j)) t ≫
                biproduct.ι
                  (fun j : P.index ↦ σ.obj (P.label j)) t)) ≫
            s.retraction := by rw [biproduct.total]
      _ = ∑ t : P.index, a t ≫ b t := by
        rw [Preadditive.comp_sum, Preadditive.sum_comp]
        simp only [a, b, Category.assoc]
  have hlinear := congrArg (fun q ↦ q.hom.hom) hcat
  simp only [FGModuleCat.hom_hom_id, fg_hom_hom_sum,
    FGModuleCat.hom_hom_comp] at hlinear
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hsum :
      (∑ t : P.index,
        (b t).hom.hom.comp (a t).hom.hom) ∈ J := by
    apply Ideal.sum_mem
    intro t _
    exact comp_mem_end_jacobson σ (hne t) (b t) (a t)
  have hone : (1 : Module.End R (σ.obj x)) ∈ J := by
    rw [Module.End.one_eq_id, hlinear]
    exact hsum
  have hnonunit :
      ¬ IsUnit (1 : Module.End R (σ.obj x)) :=
    (MBDVendor.QSE.mem_end_jacobson_iff_not_isUnit
      (σ.indecomposable x) (σ.finiteLength x) 1).1 hone
  exact hnonunit isUnit_one

/-- If a component of a presentation is an invertible endomorphism of
the source representative, then the whole presentation map splits. -/
theorem splitMono_of_isUnit_component
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (t : P.index) (ht : P.label t = x)
    (hunit :
      IsUnit
        ((P.map ≫
          biproduct.π
              (fun j : P.index ↦ σ.obj (P.label j)) t ≫
            eqToHom (congrArg σ.obj ht)).hom.hom)) :
    Nonempty (SplitMono P.map) := by
  let q : σ.obj (P.label t) ⟶ σ.obj x :=
    eqToHom (congrArg σ.obj ht)
  let a : σ.obj x ⟶ σ.obj x :=
    P.map ≫
      biproduct.π
          (fun j : P.index ↦ σ.obj (P.label j)) t ≫ q
  have hbijective : Function.Bijective a.hom.hom :=
    (Module.End.isUnit_iff a.hom.hom).mp hunit
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (F.map a) := by
    change IsIso a.hom
    exact
      (ConcreteCategory.isIso_iff_bijective a.hom).mpr
        hbijective
  letI : IsIso a :=
    isIso_of_reflects_iso a F
  refine ⟨{
    retraction :=
      biproduct.π
          (fun j : P.index ↦ σ.obj (P.label j)) t ≫
        q ≫ inv a
    id := ?_ }⟩
  change a ≫ inv a = 𝟙 _
  exact IsIso.hom_inv_id a

/-- If `x` is not generated by the other members of `C`, every
monomorphism from `obj x` to an object of `add C` splits.  Otherwise all
components landing in a copy of `obj x` would be radical, and the common
kernel argument would generate `x` from `C \ {x}`. -/
theorem splitMono_of_not_mem_sClosure_diff
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (hnot : x ∉ σ.sClosure (C \ {x}))
    (P : σ.SubPresentation C (σ.obj x)) :
    Nonempty (SplitMono P.map) := by
  classical
  by_contra hnosplit
  let D : Set ι := C \ {x}
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have component_mem_J
      (t : P.index) (ht : P.label t = x) :
      ((P.map ≫
        biproduct.π
            (fun j : P.index ↦ σ.obj (P.label j)) t ≫
          eqToHom (congrArg σ.obj ht)).hom.hom) ∈ J := by
    apply
      (MBDVendor.QSE.mem_end_jacobson_iff_not_isUnit
        (σ.indecomposable x) (σ.finiteLength x) _).2
    intro hunit
    exact hnosplit
      (splitMono_of_isUnit_component σ P t ht hunit)
  have hinf :
      σ.reject D (σ.obj x) ⊓
          MBDVendor.QSE.idealKernel J =
        ⊥ := by
    apply le_antisymm
    · intro z hz
      letI : Fintype P.index := FintypeCat.fintype
      have hmapzero : P.map.hom.hom z = 0 := by
        apply biproduct_apply_eq_zero_of_components P.map z
        intro t
        let ft : σ.obj x ⟶ σ.obj (P.label t) :=
          P.map ≫
            biproduct.π
              (fun j : P.index ↦ σ.obj (P.label j)) t
        by_cases ht : P.label t = x
        · let q : σ.obj (P.label t) ⟶ σ.obj x :=
            eqToHom (congrArg σ.obj ht)
          let a : Module.End R (σ.obj x) :=
            (ft ≫ q).hom.hom
          have haJ : a ∈ J := by
            exact component_mem_J t ht
          have hazero :=
            MBDVendor.QSE.idealKernel_le_ker a haJ hz.2
          rw [LinearMap.mem_ker] at hazero
          have hqinjective : Function.Injective q.hom.hom :=
            (fg_mono_iff_injective q).mp inferInstance
          apply hqinjective
          simpa only [a, q, ft, FGModuleCat.hom_hom_comp,
            LinearMap.comp_apply, map_zero] using hazero
        · have htD : P.label t ∈ D := by
            refine ⟨P.mem t, ?_⟩
            simpa only [Set.mem_singleton_iff] using ht
          exact LinearMap.mem_ker.mp
            (reject_le_ker_of_mem σ htD ft hz.1)
      letI : Mono P.map := P.mono
      have hzker :
          z ∈ LinearMap.ker P.map.hom.hom :=
        LinearMap.mem_ker.mpr hmapzero
      rw [ker_eq_bot_of_mono P.map] at hzker
      exact hzker
    · exact bot_le
  have hreject : σ.reject D (σ.obj x) = ⊥ := by
    apply MBDVendor.QSE.eq_bot_of_inf_idealKernel J
    · exact reject_fullyInvariant_linear σ (σ.obj x)
    · dsimp only [J]
      exact
        (Ideal.jacobson_bot (R :=
          Module.End R (σ.obj x))) ▸
            IsArtinianRing.isNilpotent_jacobson_bot
    · exact hinf
  apply hnot
  exact (mem_sClosure_iff_reject_eq_bot σ D x).2 hreject

/-- Relative split injectivity prevents `x` from embedding into a sum
of the other members of `C`. -/
theorem not_mem_sClosure_diff_of_relativeSplitInjective
    (C : Set ι) (x : ι)
    (hrel : σ.IsRelativeSplitInjective C x) :
    x ∉ σ.sClosure (C \ {x}) := by
  intro hxgen
  obtain ⟨P⟩ := hxgen
  let P' : σ.SubPresentation C (σ.obj x) :=
    SubPresentation.of_subset σ P Set.sdiff_subset
  have hne : ∀ t, x ≠ P.label t := by
    intro t hEq
    have hnotmem : P.label t ∉ ({x} : Set ι) :=
      (P.mem t).2
    exact hnotmem (by
      simpa only [Set.mem_singleton_iff] using hEq.symm)
  exact (not_splitMono_of_labels_ne σ P hne) (hrel P')

/-- The split-injective bridge, in a slightly stronger form not requiring
`C` itself to be closed. -/
theorem not_mem_sClosure_diff_iff_relativeSplitInjective
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))] :
    x ∉ σ.sClosure (C \ {x}) ↔
      σ.IsRelativeSplitInjective C x := by
  constructor
  · intro hnot P
    exact splitMono_of_not_mem_sClosure_diff σ C x hnot P
  · exact not_mem_sClosure_diff_of_relativeSplitInjective σ C x

/-- For an `s`-closed set and one of its members, deletion fails to
regenerate that member exactly when the member is relatively split
injective. -/
theorem extremal_iff_isRelativeSplitInjective_of_sClosed
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (_hC : σ.sClosure.IsClosed C) (_hxC : x ∈ C) :
    x ∉ σ.sClosure (C \ {x}) ↔
      σ.IsRelativeSplitInjective C x :=
  not_mem_sClosure_diff_iff_relativeSplitInjective σ C x

end MBDVendor.QSE.IndecomposableSkeleton
