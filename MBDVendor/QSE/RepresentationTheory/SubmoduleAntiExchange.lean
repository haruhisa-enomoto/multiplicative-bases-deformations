module

public import MBDVendor.QSE.RepresentationTheory.AntiExchange

/-!
# Anti-exchange for submodule closure

This file gives the direct reject-and-kernel dual of the trace proof in
`AntiExchange`.  In particular it does not assume an unformalized
duality equivalence: the common kernels of maps through a distinct
indecomposable are iterated through the nilpotent Jacobson radical.
-/

@[expose] public section

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The intersection of the kernels of all maps to one indecomposable
representative. -/
def pointReject (i : ι) (X : FGModuleCat.{w} R) :
    Submodule R X :=
  ⨅ f : X ⟶ σ.obj i, LinearMap.ker f.hom.hom

/-- Every map to a selected indecomposable occurs in the reject
intersection. -/
theorem reject_le_ker_of_mem {S : Set ι} {i : ι}
    (hi : i ∈ S) {X : FGModuleCat.{w} R}
    (f : X ⟶ σ.obj i) :
    σ.reject S X ≤ LinearMap.ker f.hom.hom := by
  let a : Fin 1 → ι := fun _ ↦ i
  let e :
      σ.sumOver (FintypeCat.of (Fin 1)) a ≅ σ.obj i :=
    biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)
  let g : σ.SelectedMapFrom S X :=
    { index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ hi
      map := f ≫ e.inv }
  have hreject := reject_le_ker σ g
  intro x hx
  have hxcomp := hreject hx
  rw [LinearMap.mem_ker] at hxcomp ⊢
  have hinj : Function.Injective e.inv.hom.hom :=
    (fg_mono_iff_injective e.inv).1 inferInstance
  apply hinj
  simpa only [map_zero, g, FGModuleCat.hom_hom_comp,
    LinearMap.comp_apply] using hxcomp

omit [IsNoetherianRing R] in
private theorem fg_hom_sum_apply {J : Type*} [Fintype J]
    {X Y : FGModuleCat.{w} R} (f : J → (X ⟶ Y)) (x : X) :
    ((∑ j, f j).hom.hom) x =
      ∑ j, (f j).hom.hom x := by
  have h₁ :
      (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h₁, ModuleCat.hom_sum]
  exact LinearMap.sum_apply _ _ x

/-- The reject against a singleton is the common kernel of all maps to
that indecomposable. -/
theorem reject_singleton_eq_pointReject (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.reject {i} X = σ.pointReject i X := by
  apply le_antisymm
  · apply le_iInf
    intro f
    exact reject_le_ker_of_mem σ (Set.mem_singleton i) f
  · apply le_iInf
    intro f
    letI : Fintype f.index := FintypeCat.fintype
    intro x hx
    rw [LinearMap.mem_ker]
    have hmap :
        f.map =
          ∑ t : f.index,
            (f.map ≫
              biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t) ≫
              biproduct.ι
                (fun t : f.index ↦ σ.obj (f.label t)) t := by
      calc
        f.map = f.map ≫ 𝟙 _ := (Category.comp_id _).symm
        _ =
            f.map ≫
              (∑ t : f.index,
                biproduct.π
                    (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                  biproduct.ι
                    (fun t : f.index ↦ σ.obj (f.label t)) t) := by
              rw [biproduct.total]
        _ = _ := by
          rw [Preadditive.comp_sum]
          simp only [Category.assoc]
    rw [hmap, fg_hom_sum_apply]
    apply Finset.sum_eq_zero
    intro t _
    have ht : f.label t = i := by
      simpa using f.mem t
    let ft : X ⟶ σ.obj (f.label t) :=
      f.map ≫
        biproduct.π (fun t : f.index ↦ σ.obj (f.label t)) t
    let ft' : X ⟶ σ.obj i :=
      ft ≫ eqToHom (congrArg σ.obj ht)
    have hft' : ft'.hom.hom x = 0 := by
      have hker :
          σ.pointReject i X ≤ LinearMap.ker ft'.hom.hom :=
        iInf_le
          (fun g : X ⟶ σ.obj i ↦ LinearMap.ker g.hom.hom) ft'
      exact LinearMap.mem_ker.mp (hker hx)
    have hcat :
        ft' ≫ eqToHom (congrArg σ.obj ht.symm) = ft := by
      dsimp only [ft']
      simp
    have hlinear := congrArg (fun q ↦ q.hom.hom) hcat
    simp only [FGModuleCat.hom_hom_comp] at hlinear
    have hft : ft.hom.hom x = 0 := by
      have heval := LinearMap.congr_fun hlinear x
      rw [← heval]
      simp only [LinearMap.comp_apply, hft', map_zero]
    change
      ((ft ≫
        biproduct.ι
          (fun t : f.index ↦ σ.obj (f.label t)) t).hom.hom) x = 0
    simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply,
      hft, map_zero]

/-- Reject converts unions of selected indecomposables to meets. -/
theorem reject_union (S T : Set ι) (X : FGModuleCat.{w} R) :
    σ.reject (S ∪ T) X = σ.reject S X ⊓ σ.reject T X := by
  apply le_antisymm
  · exact le_inf
      (reject_anti σ Set.subset_union_left X)
      (reject_anti σ Set.subset_union_right X)
  · apply le_iInf
    intro f
    letI : Fintype f.index := FintypeCat.fintype
    intro x hx
    rw [LinearMap.mem_ker]
    have hmap :
        f.map =
          ∑ t : f.index,
            (f.map ≫
              biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t) ≫
              biproduct.ι
                (fun t : f.index ↦ σ.obj (f.label t)) t := by
      calc
        f.map = f.map ≫ 𝟙 _ := (Category.comp_id _).symm
        _ =
            f.map ≫
              (∑ t : f.index,
                biproduct.π
                    (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                  biproduct.ι
                    (fun t : f.index ↦ σ.obj (f.label t)) t) := by
              rw [biproduct.total]
        _ = _ := by
          rw [Preadditive.comp_sum]
          simp only [Category.assoc]
    rw [hmap, fg_hom_sum_apply]
    apply Finset.sum_eq_zero
    intro t _
    let ft : X ⟶ σ.obj (f.label t) :=
      f.map ≫
        biproduct.π (fun t : f.index ↦ σ.obj (f.label t)) t
    have hft : ft.hom.hom x = 0 := by
      rcases f.mem t with ht | ht
      · exact LinearMap.mem_ker.mp
          ((reject_le_ker_of_mem σ ht ft) hx.1)
      · exact LinearMap.mem_ker.mp
          ((reject_le_ker_of_mem σ ht ft) hx.2)
    change
      ((ft ≫
        biproduct.ι
          (fun t : f.index ↦ σ.obj (f.label t)) t).hom.hom) x = 0
    simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply,
      hft, map_zero]

/-- Adjoining one indecomposable intersects with its point reject. -/
theorem reject_insert (S : Set ι) (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.reject (insert i S) X =
      σ.reject S X ⊓ σ.pointReject i X := by
  rw [show insert i S = S ∪ {i} by ext; simp]
  rw [reject_union, reject_singleton_eq_pointReject]

/-- The reject is invariant under every underlying endomorphism. -/
theorem reject_fullyInvariant_linear {S : Set ι}
    (X : FGModuleCat.{w} R) (f : Module.End R X) :
    Submodule.map f (σ.reject S X) ≤ σ.reject S X := by
  rw [Submodule.map_le_iff_le_comap]
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  let fc : X ⟶ X := F.preimage (ModuleCat.ofHom f)
  have hfc : fc.hom.hom = f := by
    have h := F.map_preimage (ModuleCat.ofHom f)
    exact congrArg ModuleCat.Hom.hom h
  rw [← hfc]
  exact reject_fullyInvariant σ X fc

/-- Mutual one-point submodule generation forces the reject of `C` in
`X` to meet the common Jacobson-radical kernel trivially. -/
theorem reject_inf_idealKernel_eq_bot
    (C : Set ι) {x y : ι} (hxy : x ≠ y)
    (hX :
      σ.reject C (σ.obj x) ⊓
        σ.pointReject y (σ.obj x) = ⊥)
    (hY :
      σ.reject C (σ.obj y) ⊓
        σ.pointReject x (σ.obj y) = ⊥) :
    σ.reject C (σ.obj x) ⊓
        MBDVendor.QSE.idealKernel
          (Ring.jacobson (Module.End R (σ.obj x))) = ⊥ := by
  apply le_antisymm
  · intro z hz
    have hzPoint : z ∈ σ.pointReject y (σ.obj x) := by
      rw [pointReject, Submodule.mem_iInf]
      intro f
      rw [LinearMap.mem_ker]
      have hfReject :
          f.hom.hom z ∈ σ.reject C (σ.obj y) := by
        exact (reject_le_comap_reject σ f) hz.1
      have hfPoint :
          f.hom.hom z ∈ σ.pointReject x (σ.obj y) := by
        rw [pointReject, Submodule.mem_iInf]
        intro g
        rw [LinearMap.mem_ker]
        have hrad :
            g.hom.hom.comp f.hom.hom ∈
              Ring.jacobson
                (Module.End R (σ.obj x)) :=
          comp_mem_end_jacobson σ hxy g f
        have hzero :=
          MBDVendor.QSE.idealKernel_le_ker
            (g.hom.hom.comp f.hom.hom) hrad hz.2
        rw [LinearMap.mem_ker, LinearMap.comp_apply] at hzero
        exact hzero
      have hfbot : f.hom.hom z ∈
          (⊥ : Submodule R (σ.obj y)) := by
        rw [← hY]
        exact ⟨hfReject, hfPoint⟩
      exact hfbot
    rw [← hX]
    exact ⟨hz.1, hzPoint⟩
  · exact bot_le

/-- Submodule closure satisfies anti-exchange whenever the relevant
endomorphism rings are Artinian. -/
theorem sClosure_isAntiExchange
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.sClosure.IsAntiExchange := by
  intro C x y hC hxC _hyC hxy hxgen hygen
  have hxreject :
      σ.reject C (σ.obj x) ⊓
        σ.pointReject y (σ.obj x) = ⊥ := by
    have h :=
      (mem_sClosure_iff_reject_eq_bot σ (insert y C) x).1 hxgen
    rw [reject_insert] at h
    exact h
  have hyreject :
      σ.reject C (σ.obj y) ⊓
        σ.pointReject x (σ.obj y) = ⊥ := by
    have h :=
      (mem_sClosure_iff_reject_eq_bot σ (insert x C) y).1 hygen
    rw [reject_insert] at h
    exact h
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hinf :
      σ.reject C (σ.obj x) ⊓
        MBDVendor.QSE.idealKernel J = ⊥ :=
    reject_inf_idealKernel_eq_bot σ C hxy hxreject hyreject
  have hrejectBot : σ.reject C (σ.obj x) = ⊥ := by
    apply MBDVendor.QSE.eq_bot_of_inf_idealKernel J
    · exact reject_fullyInvariant_linear σ (σ.obj x)
    · dsimp only [J]
      exact
        (Ideal.jacobson_bot (R :=
          Module.End R (σ.obj x))) ▸
            IsArtinianRing.isNilpotent_jacobson_bot
    · exact hinf
  apply hxC
  rw [← hC.closure_eq]
  exact (mem_sClosure_iff_reject_eq_bot σ C x).2 hrejectBot

/-- Under the Artinian endomorphism-ring hypothesis, submodule closure
is a convex geometry. -/
theorem sClosure_isConvexGeometry
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.sClosure.IsConvexGeometry :=
  ⟨sClosure_isClosed_empty σ, sClosure_isAntiExchange σ⟩

/-- The manuscript's finite-dimensional-over-a-field hypothesis supplies
submodule anti-exchange. -/
theorem sClosure_isAntiExchange_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.IsAntiExchange := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      MBDVendor.QSE.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  exact sClosure_isAntiExchange σ

/-- Submodule closure is a convex geometry for the finite-dimensional
module setup used in the manuscript. -/
theorem sClosure_isConvexGeometry_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.IsConvexGeometry :=
  ⟨sClosure_isClosed_empty σ,
    sClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩

/-- The exact combined content of the manuscript's anti-exchange
proposition: both closures are finitary and satisfy anti-exchange. -/
theorem quotientSubmodule_finitary_antiExchange_of_finiteDimensional
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    (σ.qClosure.IsFinitary ∧ σ.qClosure.IsAntiExchange) ∧
      (σ.sClosure.IsFinitary ∧ σ.sClosure.IsAntiExchange) :=
  ⟨⟨qClosure_isFinitary σ,
      qClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩,
    ⟨sClosure_isFinitary σ,
      sClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩⟩

/-- In finite representation type, quotient and submodule closure give
the two finite convex geometries asserted in the manuscript. -/
theorem twoConvexGeometries_of_finiteDimensional
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.IsConvexGeometry ∧
      σ.sClosure.IsConvexGeometry :=
  ⟨qClosure_isConvexGeometry_of_finiteDimensional (K := K) σ,
    sClosure_isConvexGeometry_of_finiteDimensional (K := K) σ⟩

end MBDVendor.QSE.IndecomposableSkeleton
