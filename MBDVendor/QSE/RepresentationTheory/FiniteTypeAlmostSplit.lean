module

public import MBDVendor.QSE.RepresentationTheory.AlmostSplitCofinite
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Almost-split morphisms for a finite indecomposable skeleton

For a finite complete skeleton of finite-length indecomposable modules over a
finite-dimensional algebra, this file constructs right and left almost-split
morphisms by finite radical evaluation.  It then combines those morphisms with
the finite-length minimalization theorem in `AlmostSplitCofinite`.

The construction is intrinsic: it uses only the radical Hom-spaces between
the chosen indecomposables and their finite biproducts.  No presentation or
classification of the algebra or its modules enters.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

universe uK uR uι w

variable {K : Type uK} [Field K]
  {R : Type uR} [Ring R] [Algebra K R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

abbrev asHom {X Y : FGModuleCat.{w} R}
    (f : X →ₗ[R] Y) : X ⟶ Y :=
  ConcreteCategory.ofHom f

theorem zero_not_isSplitEpi (x z : ι) :
    ¬ IsSplitEpi (asHom (0 : σ.obj x →ₗ[R] σ.obj z)) := by
  intro h
  letI : IsSplitEpi (asHom (0 : σ.obj x →ₗ[R] σ.obj z)) := h
  have hz : IsZero (σ.obj z) :=
    (IsZero.iff_isSplitEpi_eq_zero
      (asHom (0 : σ.obj x →ₗ[R] σ.obj z))).2 rfl
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  have hz' : IsZero (U.obj (σ.obj z)) := U.map_isZero hz
  have hs : Subsingleton (σ.obj z) :=
    ModuleCat.isZero_iff_subsingleton.mp hz'
  exact not_nontrivial_iff_subsingleton.mpr hs
    (σ.indecomposable z).nontrivial

private theorem isSplitEpi_of_isUnit_section_comp
    {x z : ι} (f : σ.obj x →ₗ[R] σ.obj z)
    (s : σ.obj z ⟶ σ.obj x)
    (hu : IsUnit (f.comp s.hom.hom)) :
    IsSplitEpi (asHom f) := by
  let F : σ.obj x ⟶ σ.obj z := asHom f
  have hbij : Function.Bijective (f.comp s.hom.hom) :=
    (Module.End.isUnit_iff _).mp hu
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  haveI : IsIso (U.map (s ≫ F)) := by
    change IsIso ((s ≫ F).hom)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  letI : IsIso (s ≫ F) := isIso_of_reflects_iso (s ≫ F) U
  exact IsSplitEpi.mk'
    { section_ := inv (s ≫ F) ≫ s
      id := by simp [F] }

omit [IsNoetherianRing R] in
private theorem not_isUnit_comp_of_not_isSplitEpi
    {X Z : FGModuleCat.{w} R} (g : X ⟶ Z)
    (hg : ¬ IsSplitEpi g) (s : Z ⟶ X) :
    ¬ IsUnit ((s ≫ g).hom.hom) := by
  intro hunit
  have hbij : Function.Bijective (s ≫ g).hom.hom :=
    (Module.End.isUnit_iff _).mp hunit
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  haveI : IsIso (U.map (s ≫ g)) := by
    change IsIso ((s ≫ g).hom)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  letI : IsIso (s ≫ g) := isIso_of_reflects_iso (s ≫ g) U
  apply hg
  exact IsSplitEpi.mk'
    { section_ := inv (s ≫ g) ≫ s
      id := by simp }

omit [IsNoetherianRing R] in
private theorem not_isUnit_comp_of_not_isSplitMono
    {Z X : FGModuleCat.{w} R} (g : Z ⟶ X)
    (hg : ¬ IsSplitMono g) (r : X ⟶ Z) :
    ¬ IsUnit ((g ≫ r).hom.hom) := by
  intro hunit
  have hbij : Function.Bijective (g ≫ r).hom.hom :=
    (Module.End.isUnit_iff _).mp hunit
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  haveI : IsIso (U.map (g ≫ r)) := by
    change IsIso ((g ≫ r).hom)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  letI : IsIso (g ≫ r) := isIso_of_reflects_iso (g ≫ r) U
  apply hg
  exact IsSplitMono.mk'
    { retraction := r ≫ inv (g ≫ r)
      id := by
        rw [← Category.assoc]
        simp }

/-- The `K`-linear radical Hom-space between two chosen indecomposables,
realized as the maps which are not split epimorphisms. -/
def radicalHom (x z : ι) :
    Submodule K (σ.obj x →ₗ[R] σ.obj z) where
  carrier := {f | ¬ IsSplitEpi (asHom f)}
  zero_mem' := zero_not_isSplitEpi σ x z
  add_mem' := by
    intro f g hf hg hfg
    let H : σ.obj x ⟶ σ.obj z := asHom (f + g)
    letI : IsSplitEpi H := hfg
    let s : σ.obj z ⟶ σ.obj x := section_ H
    let cf : Module.End R (σ.obj z) := f.comp s.hom.hom
    let cg : Module.End R (σ.obj z) := g.comp s.hom.hom
    have hcat : s ≫ H = 𝟙 _ := IsSplitEpi.id H
    have hlin := congrArg
      (fun q : σ.obj z ⟶ σ.obj z => q.hom.hom) hcat
    change (f + g).comp s.hom.hom = LinearMap.id at hlin
    have hsum : cf + cg = 1 := by
      apply LinearMap.ext
      intro y
      have hy := LinearMap.congr_fun hlin y
      simpa [cf, cg, LinearMap.comp_apply, LinearMap.add_apply] using hy
    letI : IsLocalRing (Module.End R (σ.obj z)) :=
      MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
        (σ.finiteLength z) (σ.indecomposable z)
    have hu : IsUnit (cf + cg) := hsum.symm ▸ isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hcf | hcg
    · exact hf (isSplitEpi_of_isUnit_section_comp σ f s hcf)
    · exact hg (isSplitEpi_of_isUnit_section_comp σ g s hcg)
  smul_mem' := by
    intro c f hf hcf
    let CF : σ.obj x ⟶ σ.obj z := asHom (c • f)
    letI : IsSplitEpi CF := hcf
    let s : σ.obj z ⟶ σ.obj x := section_ CF
    apply hf
    refine IsSplitEpi.mk'
      { section_ := asHom (c • s.hom.hom)
        id := ?_ }
    apply FGModuleCat.hom_ext
    have hcat : s ≫ CF = 𝟙 _ := IsSplitEpi.id CF
    have hlin := congrArg
      (fun q : σ.obj z ⟶ σ.obj z => q.hom.hom) hcat
    change (c • f).comp s.hom.hom = LinearMap.id at hlin
    change f.comp (c • s.hom.hom) = LinearMap.id
    apply LinearMap.ext
    intro y
    have hy := LinearMap.congr_fun hlin y
    simpa [LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.map_smul_of_tower] using hy

@[simp] theorem mem_radicalHom_iff_not_isSplitEpi {x z : ι}
    (f : σ.obj x →ₗ[R] σ.obj z) :
    f ∈ σ.radicalHom (K := K) x z ↔
      ¬ IsSplitEpi
        (show σ.obj x ⟶ σ.obj z from ConcreteCategory.ofHom f) :=
  Iff.rfl

/-- On the duplicate-free indecomposable skeleton, the same radical
Hom-space consists of the maps which are not split monomorphisms. -/
theorem mem_radicalHom_iff_not_isSplitMono {x z : ι}
    (f : σ.obj x →ₗ[R] σ.obj z) :
    f ∈ σ.radicalHom (K := K) x z ↔
      ¬ IsSplitMono
        (show σ.obj x ⟶ σ.obj z from ConcreteCategory.ofHom f) := by
  rw [mem_radicalHom_iff_not_isSplitEpi]
  constructor
  · intro hEpi hMono
    letI : IsSplitMono (asHom f) := hMono
    exact hEpi (σ.isSplitEpi_of_isSplitMono_between_obj (asHom f))
  · intro hMono hEpi
    letI : IsSplitEpi (asHom f) := hEpi
    exact hMono (σ.isSplitMono_of_isSplitEpi_between_obj (asHom f))

private noncomputable def scalarId
    (M : FGModuleCat.{w} R)
    [Module K M] [IsScalarTower K R M]
    (c : K) : M ⟶ M :=
  ConcreteCategory.ofHom (c • LinearMap.id)

/-- A finite biproduct of finite-dimensional modules is finite-dimensional
over the same scalar field. -/
private theorem finiteDimensional_biproduct
    {J : Type} [Fintype J]
    (F : J → FGModuleCat.{w} R)
    [∀ j, Module K (F j)]
    [∀ j, IsScalarTower K R (F j)]
    [∀ j, FiniteDimensional K (F j)] :
    let B : FGModuleCat.{w} R := ⨁ F
    letI : Module K B := Module.restrictScalars K R B
    FiniteDimensional K B := by
  let B : FGModuleCat.{w} R := ⨁ F
  letI : Module K B := Module.restrictScalars K R B
  letI : IsScalarTower K R B :=
    IsScalarTower.restrictScalars K R B
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  letI : PreservesBiproduct F U :=
    preservesBiproduct_of_preservesProduct U
  let e : B ≅ FGModuleCat.of R (∀ j, F j) :=
    U.preimageIso
      (U.mapBiproduct F ≪≫
        ModuleCat.biproductIsoPi (fun j => U.obj (F j)))
  exact
    (Module.Finite.equiv_iff
      ((FGModuleCat.isoToLinearEquiv e).restrictScalars K)).mpr
      (inferInstance : Module.Finite K (∀ j, F j))

omit [IsNoetherianRing R] in
private theorem hom_hom_sum {J : Type} [Fintype J]
    {X Y : FGModuleCat.{w} R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by
  let underlying : (X ⟶ Y) →+ (X →ₗ[R] Y) :=
    { toFun := fun q => q.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change underlying (∑ j, f j) = ∑ j, underlying (f j)
  exact map_sum underlying f Finset.univ

/-- A finite biproduct map into a chosen indecomposable cannot split if none
of its components splits. -/
theorem biproductDesc_not_isSplitEpi
    {z : ι} {J : Type} [Fintype J]
    (F : J → FGModuleCat.{w} R)
    (component : ∀ j, F j ⟶ σ.obj z)
    (hnonsplit : ∀ j, ¬ IsSplitEpi (component j)) :
    ¬ IsSplitEpi (biproduct.desc component) := by
  classical
  intro hs
  obtain ⟨se⟩ := hs.exists_splitEpi
  let a (j : J) : σ.obj z ⟶ F j :=
    se.section_ ≫ biproduct.π F j
  have hcat :
      ∑ j : J, a j ≫ component j = 𝟙 (σ.obj z) := by
    have hsection : biproduct.lift a = se.section_ := by
      apply biproduct.hom_ext
      intro j
      rw [biproduct.lift_π]
    calc
      ∑ j : J, a j ≫ component j =
          biproduct.lift a ≫ biproduct.desc component :=
        biproduct.lift_desc.symm
      _ = se.section_ ≫ biproduct.desc component := by rw [hsection]
      _ = 𝟙 (σ.obj z) := se.id
  let c (j : J) : Module.End R (σ.obj z) :=
    (component j).hom.hom.comp (a j).hom.hom
  have hlinear := congrArg
    (fun q : σ.obj z ⟶ σ.obj z => q.hom.hom) hcat
  simp only [hom_hom_sum, FGModuleCat.hom_hom_comp,
    FGModuleCat.hom_hom_id] at hlinear
  have hsum : ∑ j : J, c j = 1 := by
    rw [Module.End.one_eq_id]
    exact hlinear
  letI : IsLocalRing (Module.End R (σ.obj z)) :=
    MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength z) (σ.indecomposable z)
  have hunit : IsUnit (∑ j : J, c j) := hsum.symm ▸ isUnit_one
  obtain ⟨j, _, hj⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := c) hunit
  exact
    (not_isUnit_comp_of_not_isSplitEpi
      (component j) (hnonsplit j) (a j)) hj

/-- Dually, a finite biproduct map out of a chosen indecomposable cannot
split if none of its component maps splits. -/
theorem biproductLift_not_isSplitMono
    {z : ι} {J : Type} [Fintype J]
    (F : J → FGModuleCat.{w} R)
    (component : ∀ j, σ.obj z ⟶ F j)
    (hnonsplit : ∀ j, ¬ IsSplitMono (component j)) :
    ¬ IsSplitMono (biproduct.lift component) := by
  classical
  intro hs
  obtain ⟨sm⟩ := hs.exists_splitMono
  let a (j : J) : F j ⟶ σ.obj z :=
    biproduct.ι F j ≫ sm.retraction
  have hcat :
      ∑ j : J, component j ≫ a j = 𝟙 (σ.obj z) := by
    have hretraction : biproduct.desc a = sm.retraction := by
      apply biproduct.hom_ext'
      intro j
      rw [biproduct.ι_desc]
    calc
      ∑ j : J, component j ≫ a j =
          biproduct.lift component ≫ biproduct.desc a :=
        biproduct.lift_desc.symm
      _ = biproduct.lift component ≫ sm.retraction := by
        rw [hretraction]
      _ = 𝟙 (σ.obj z) := sm.id
  let c (j : J) : Module.End R (σ.obj z) :=
    (a j).hom.hom.comp (component j).hom.hom
  have hlinear := congrArg
    (fun q : σ.obj z ⟶ σ.obj z => q.hom.hom) hcat
  simp only [hom_hom_sum, FGModuleCat.hom_hom_comp,
    FGModuleCat.hom_hom_id] at hlinear
  have hsum : ∑ j : J, c j = 1 := by
    rw [Module.End.one_eq_id]
    exact hlinear
  letI : IsLocalRing (Module.End R (σ.obj z)) :=
    MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength z) (σ.indecomposable z)
  have hunit : IsUnit (∑ j : J, c j) := hsum.symm ▸ isUnit_one
  obtain ⟨j, _, hj⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := c) hunit
  exact
    (not_isUnit_comp_of_not_isSplitMono
      (component j) (hnonsplit j) (a j)) hj

section FiniteSkeleton

variable [Finite ι]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

include K

/-- Finite radical evaluation gives a finite-length right almost-split map
into every representative of a finite indecomposable skeleton. -/
theorem exists_finiteLength_rightAlmostSplit (z : ι) :
    ∃ (E : FGModuleCat.{w} R) (f : E ⟶ σ.obj z),
      IsFiniteLength R E ∧ IsRightAlmostSplit f := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι
  let ε : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let label : Fin n → ι := ε
  let V (t : Fin n) := σ.radicalHom (K := K) (label t) z
  let d (t : Fin n) := Module.finrank K (V t)
  let B (t : Fin n) : FGModuleCat.{w} R :=
    ⨁ fun _ : Fin (d t) => σ.obj (label t)
  letI (t : Fin n) : Module K (B t) :=
    Module.restrictScalars K R (B t)
  letI (t : Fin n) : IsScalarTower K R (B t) :=
    IsScalarTower.restrictScalars K R (B t)
  letI (t : Fin n) : FiniteDimensional K (B t) :=
    finiteDimensional_biproduct (K := K)
      (fun _ : Fin (d t) => σ.obj (label t))
  let b (t : Fin n) := Module.finBasis K (V t)
  let e (t : Fin n) : B t ⟶ σ.obj z :=
    biproduct.desc fun j =>
      ConcreteCategory.ofHom ((b t j : V t).1)
  let E : FGModuleCat.{w} R := ⨁ B
  let f : E ⟶ σ.obj z := biproduct.desc e
  have factors_obj_aux
      (t : Fin n) (x : ι) (ht : label t = x)
      (g : σ.obj x ⟶ σ.obj z) (hg : ¬ IsSplitEpi g) :
      ∃ h : σ.obj x ⟶ E, h ≫ f = g := by
    subst x
    have hradical :
        g.hom.hom ∈ σ.radicalHom (K := K) (label t) z :=
      (σ.mem_radicalHom_iff_not_isSplitEpi
        (K := K) g.hom.hom).2 hg
    let u : V t := ⟨g.hom.hom, hradical⟩
    let q : σ.obj (label t) ⟶ B t :=
      biproduct.lift fun j =>
        scalarId (K := K) (σ.obj (label t)) ((b t).repr u j)
    refine ⟨q ≫ biproduct.ι B t, ?_⟩
    rw [Category.assoc, biproduct.ι_desc]
    dsimp only [q, e]
    rw [biproduct.lift_desc]
    apply FGModuleCat.hom_ext
    rw [hom_hom_sum]
    simp only [FGModuleCat.hom_hom_comp]
    change
      (∑ j : Fin (d t),
        (b t j : V t).1.comp
          (((b t).repr u j) • LinearMap.id)) = g.hom.hom
    calc
      (∑ j : Fin (d t),
          (b t j : V t).1.comp
            (((b t).repr u j) • LinearMap.id)) =
          ∑ j : Fin (d t),
            ((b t).repr u j) • (b t j : V t).1 := by
        apply Finset.sum_congr rfl
        intro j _
        ext y
        simp
      _ =
          ((∑ j : Fin (d t),
            ((b t).repr u j) • (b t j : V t) : V t) :
            σ.obj (label t) →ₗ[R] σ.obj z) := by
        symm
        exact map_sum (V t).subtype
          (fun j : Fin (d t) =>
            ((b t).repr u j) • (b t j : V t)) Finset.univ
      _ = (u : σ.obj (label t) →ₗ[R] σ.obj z) :=
        congrArg Subtype.val ((b t).sum_repr u)
      _ = g.hom.hom := rfl
  refine ⟨E, f, ?_, ?_⟩
  · letI : Module K E := Module.restrictScalars K R E
    letI : IsScalarTower K R E :=
      IsScalarTower.restrictScalars K R E
    letI : FiniteDimensional K E :=
      finiteDimensional_biproduct (K := K) B
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨isNoetherian_of_tower K inferInstance,
      isArtinian_of_tower K inferInstance⟩
  · apply σ.isRightAlmostSplit_of_factors_obj f
    · dsimp only [f]
      apply biproductDesc_not_isSplitEpi σ B e
      intro t
      dsimp only [e]
      apply biproductDesc_not_isSplitEpi σ
        (fun _ : Fin (d t) => σ.obj (label t))
      intro j
      exact
        (σ.mem_radicalHom_iff_not_isSplitEpi
          (K := K) (b t j : V t).1).1 (b t j : V t).2
    · intro x g hg
      let t : Fin n := ε.symm x
      have ht : label t = x := ε.apply_symm_apply x
      exact factors_obj_aux t x ht g hg

/-- Finite radical evaluation gives a finite-length left almost-split map
out of every representative of a finite indecomposable skeleton. -/
theorem exists_finiteLength_leftAlmostSplit (z : ι) :
    ∃ (E : FGModuleCat.{w} R) (f : σ.obj z ⟶ E),
      IsFiniteLength R E ∧ IsLeftAlmostSplit f := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι
  let ε : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let label : Fin n → ι := ε
  let V (t : Fin n) := σ.radicalHom (K := K) z (label t)
  let d (t : Fin n) := Module.finrank K (V t)
  let B (t : Fin n) : FGModuleCat.{w} R :=
    ⨁ fun _ : Fin (d t) => σ.obj (label t)
  letI (t : Fin n) : Module K (B t) :=
    Module.restrictScalars K R (B t)
  letI (t : Fin n) : IsScalarTower K R (B t) :=
    IsScalarTower.restrictScalars K R (B t)
  letI (t : Fin n) : FiniteDimensional K (B t) :=
    finiteDimensional_biproduct (K := K)
      (fun _ : Fin (d t) => σ.obj (label t))
  let b (t : Fin n) := Module.finBasis K (V t)
  let e (t : Fin n) : σ.obj z ⟶ B t :=
    biproduct.lift fun j =>
      ConcreteCategory.ofHom ((b t j : V t).1)
  let E : FGModuleCat.{w} R := ⨁ B
  let f : σ.obj z ⟶ E := biproduct.lift e
  refine ⟨E, f, ?_, ?_⟩
  · letI : Module K E := Module.restrictScalars K R E
    letI : IsScalarTower K R E :=
      IsScalarTower.restrictScalars K R E
    letI : FiniteDimensional K E :=
      finiteDimensional_biproduct (K := K) B
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨isNoetherian_of_tower K inferInstance,
      isArtinian_of_tower K inferInstance⟩
  · apply σ.isLeftAlmostSplit_of_factors_obj f
    · dsimp only [f]
      apply biproductLift_not_isSplitMono σ B e
      intro t
      dsimp only [e]
      apply biproductLift_not_isSplitMono σ
        (fun _ : Fin (d t) => σ.obj (label t))
      intro j
      exact
        (σ.mem_radicalHom_iff_not_isSplitMono
          (K := K) (b t j : V t).1).1 (b t j : V t).2
    · intro x g hg
      obtain ⟨t, rfl⟩ := ε.surjective x
      have hgmem : g.hom.hom ∈ V t :=
        (σ.mem_radicalHom_iff_not_isSplitMono
          (K := K) g.hom.hom).2 (by simpa using hg)
      let u : V t := ⟨g.hom.hom, hgmem⟩
      let q : B t ⟶ σ.obj (label t) :=
        biproduct.desc fun j =>
          scalarId (K := K) (σ.obj (label t))
            ((b t).repr u j)
      refine ⟨biproduct.π B t ≫ q, ?_⟩
      rw [← Category.assoc, biproduct.lift_π]
      change e t ≫ q = g
      dsimp only [e, q]
      rw [biproduct.lift_desc]
      apply FGModuleCat.hom_ext
      let underlying :
          (σ.obj z ⟶ σ.obj (label t)) →+
            (σ.obj z →ₗ[R] σ.obj (label t)) :=
        { toFun := fun h => h.hom.hom
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hmodule :
          (∑ j : Fin (d t),
            ConcreteCategory.ofHom ((b t j : V t).1) ≫
              scalarId (K := K) (σ.obj (label t))
                ((b t).repr u j)).hom.hom =
            ∑ j : Fin (d t),
              (ConcreteCategory.ofHom ((b t j : V t).1) ≫
                scalarId (K := K) (σ.obj (label t))
                  ((b t).repr u j)).hom.hom := by
        change underlying (∑ j : Fin (d t),
            ConcreteCategory.ofHom ((b t j : V t).1) ≫
              scalarId (K := K) (σ.obj (label t))
                ((b t).repr u j)) =
          ∑ j : Fin (d t), underlying
            (ConcreteCategory.ofHom ((b t j : V t).1) ≫
              scalarId (K := K) (σ.obj (label t))
                ((b t).repr u j))
        exact map_sum underlying _ Finset.univ
      rw [hmodule]
      simp only [FGModuleCat.hom_hom_comp]
      change
        (∑ j : Fin (d t),
          (((b t).repr u j) • LinearMap.id) ∘ₗ
            (b t j : V t).1 =
          (u : σ.obj z →ₗ[R] σ.obj (label t)))
      calc
        (∑ j : Fin (d t),
            (((b t).repr u j) • LinearMap.id) ∘ₗ
              (b t j : V t).1) =
            ∑ j : Fin (d t),
              ((b t).repr u j) • (b t j : V t).1 := by
          apply Finset.sum_congr rfl
          intro j _
          ext y
          simp
        _ =
            ((∑ j : Fin (d t),
              ((b t).repr u j) • (b t j : V t) : V t) :
              σ.obj z →ₗ[R] σ.obj (label t)) := by
          symm
          exact map_sum (V t).subtype
            (fun j : Fin (d t) =>
              ((b t).repr u j) • (b t j : V t)) Finset.univ
        _ = (u : σ.obj z →ₗ[R] σ.obj (label t)) :=
          congrArg Subtype.val ((b t).sum_repr u)

/-- Finite radical evaluation followed by finite-length minimalization gives
a minimal right almost-split decomposition at every skeleton vertex. -/
theorem minimalRightAlmostSplitDecomposition_nonempty (z : ι) :
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z) := by
  obtain ⟨E, f, hE, hf⟩ :=
    σ.exists_finiteLength_rightAlmostSplit (K := K) z
  exact
    MinimalRightAlmostSplitDecomposition.exists_of_rightAlmostSplit_of_finiteLength
      σ f hf hE

/-- The left-hand finite radical evaluation likewise has a minimal
finite-length representative. -/
theorem minimalLeftAlmostSplitDecomposition_nonempty (z : ι) :
    Nonempty (σ.MinimalLeftAlmostSplitDecomposition z) := by
  obtain ⟨E, f, hE, hf⟩ :=
    σ.exists_finiteLength_leftAlmostSplit (K := K) z
  exact
    MinimalLeftAlmostSplitDecomposition.exists_of_leftAlmostSplit_of_finiteLength
      σ f hf hE

/-- In the finite-skeleton setting, the quotient-side mixed criterion no
longer needs an almost-split existence hypothesis. -/
theorem qClosed_compl_pair_iff_hasIrreducible_of_finiteSkeleton
    {p z : ι} (hpz : p ≠ z)
    (hp : σ.IsRelativeSplitProjective Set.univ p)
    (hz : ¬ σ.IsRelativeSplitProjective Set.univ z) :
    σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ ↔
      HasIrreducibleMorphism (σ.obj p) (σ.obj z) :=
  σ.qClosed_compl_pair_iff_hasIrreducible_of_rightAR hpz hp hz
    (Classical.choice
      (σ.minimalRightAlmostSplitDecomposition_nonempty (K := K) z))

/-- The submodule-side mixed criterion is unconditionally available under
the same finite-skeleton hypotheses. -/
theorem sClosed_compl_pair_iff_hasIrreducible_of_finiteSkeleton
    {z i : ι} (hzi : z ≠ i)
    (hz : ¬ σ.IsRelativeSplitInjective Set.univ z)
    (hi : σ.IsRelativeSplitInjective Set.univ i) :
    σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ ↔
      HasIrreducibleMorphism (σ.obj z) (σ.obj i) :=
  σ.sClosed_compl_pair_iff_hasIrreducible_of_leftAR hzi hz hi
    (Classical.choice
      (σ.minimalLeftAlmostSplitDecomposition_nonempty (K := K) z))

end FiniteSkeleton

section FiniteDimensionalAlgebra

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- The usual finite-dimensional-algebra hypotheses supply all pointwise
scalar and finiteness instances required by right radical evaluation. -/
theorem exists_finiteLength_rightAlmostSplit_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    [Finite ι] (z : ι) :
    ∃ (E : FGModuleCat.{w} R) (f : E ⟶ σ.obj z),
      IsFiniteLength R E ∧ IsRightAlmostSplit f := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact σ.exists_finiteLength_rightAlmostSplit (K := K) z

/-- The corresponding finite-dimensional-algebra wrapper for left radical
evaluation. -/
theorem exists_finiteLength_leftAlmostSplit_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    [Finite ι] (z : ι) :
    ∃ (E : FGModuleCat.{w} R) (f : σ.obj z ⟶ E),
      IsFiniteLength R E ∧ IsLeftAlmostSplit f := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact σ.exists_finiteLength_leftAlmostSplit (K := K) z

/-- A finite-dimensional algebra with a finite complete indecomposable
skeleton has minimal right almost-split decompositions at every vertex. -/
theorem minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    [Finite ι] (z : ι) :
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z) := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact σ.minimalRightAlmostSplitDecomposition_nonempty (K := K) z

/-- The left-dual minimal decomposition exists under the same hypotheses. -/
theorem minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    [Finite ι] (z : ι) :
    Nonempty (σ.MinimalLeftAlmostSplitDecomposition z) := by
  letI (i : ι) : Module K (σ.obj i) :=
    Module.restrictScalars K R (σ.obj i)
  letI (i : ι) : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI (i : ι) : FiniteDimensional K (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  exact σ.minimalLeftAlmostSplitDecomposition_nonempty (K := K) z

/-- Paper-facing finite-dimensional-algebra form of the quotient-side mixed
criterion. -/
theorem qClosed_compl_pair_iff_hasIrreducible_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    [Finite ι] {p z : ι} (hpz : p ≠ z)
    (hp : σ.IsRelativeSplitProjective Set.univ p)
    (hz : ¬ σ.IsRelativeSplitProjective Set.univ z) :
    σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ ↔
      HasIrreducibleMorphism (σ.obj p) (σ.obj z) :=
  σ.qClosed_compl_pair_iff_hasIrreducible_of_rightAR hpz hp hz
    (Classical.choice
      (σ.minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional
        K z))

/-- Paper-facing finite-dimensional-algebra form of the dual mixed
criterion. -/
theorem sClosed_compl_pair_iff_hasIrreducible_of_finiteDimensional
    (K : Type uK) [Field K] [Algebra K R] [FiniteDimensional K R]
    [Finite ι] {z i : ι} (hzi : z ≠ i)
    (hz : ¬ σ.IsRelativeSplitInjective Set.univ z)
    (hi : σ.IsRelativeSplitInjective Set.univ i) :
    σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ ↔
      HasIrreducibleMorphism (σ.obj z) (σ.obj i) :=
  σ.sClosed_compl_pair_iff_hasIrreducible_of_leftAR hzi hz hi
    (Classical.choice
      (σ.minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional
        K z))

end FiniteDimensionalAlgebra

end MBDVendor.QSE.IndecomposableSkeleton
