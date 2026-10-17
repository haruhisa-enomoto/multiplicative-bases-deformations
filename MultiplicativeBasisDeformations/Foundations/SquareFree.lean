import MultiplicativeBasisDeformations.Foundations.ARTranslationQuiver
import MBDVendor.Magnitude.CategoryTheory.FiniteTauIrreducible
import MBDVendor.Magnitude.CategoryTheory.IrreducibleAbelian
import MBDVendor.Magnitude.CategoryTheory.TauExactDimension
import MBDVendor.Magnitude.Algebra.RightModuleLeftTau

/-!
# Lemma 2.2: the Auslander--Reiten quiver is square-free

Lemma 2.2 (`lem:square-free`, `graded-category.tex:98–124`): for a basic
representation-finite algebra over an algebraically closed field, `Γ_A` has
no loops and at most one arrow between each ordered pair of vertices.

The manuscript's proof: an irreducible map is a monomorphism or an
epimorphism, so its source and target have different dimensions; this
excludes loops. If there are two arrows `X → Y` with `dim X > dim Y`, then `Y`
is nonprojective, the middle term of the almost split sequence ending at `Y`
contains `X²`, hence `dim τY ≥ 2 dim X − dim Y > dim X`, and the mates give two
arrows `τY → X`. Repeating gives indecomposables of strictly increasing
dimension, contrary to finite representation type. The case `dim X < dim Y`
is dual.

The formal proof is borrowed from `formalization/magnitude_conjecture`,
`Algebra/RightModuleRepresentationFiniteSquareFree.lean` (commit
`52fbbfa2b`), whose argument is the same: the dimension-growth step
`exists_multipleArrow_pair_of_multipleArrow`, and the finiteness argument
choosing a pair of maximal endpoint dimension (in place of an infinite chain).
Its helper declarations for parallel arrow occurrences are replaced by the
vendored middle-term inclusions and components (`FiniteTauIrreducible`), and
the exactness lemma `rightKernelMap_functionExact` is copied from
`Algebra/RightModuleHoshinoTorsion.lean`. The no-loop part is added here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Coefficient-field dimension of one selected indecomposable module. -/
def objectFinrank (x : Fin S.n) : ℕ :=
  Module.finrank k (S.fgObj x)

/-- Restrict a morphism of finitely generated right modules to a `k`-linear
map on the same underlying function. -/
def homRestrictScalars {X Y : RightModule.FinitelyGeneratedCategory A}
    (f : X ⟶ Y) : X →ₗ[k] Y :=
  f.hom.hom.restrictScalars k

@[simp]
theorem homRestrictScalars_apply
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y) (x : X) :
    homRestrictScalars (k := k) f x = f.hom.hom x :=
  rfl

/-- A monic irreducible map between selected indecomposables strictly raises
coefficient-field dimension. -/
theorem objectFinrank_lt_of_irreducible_mono
    {x y : Fin S.n} (f : S.fgObj x ⟶ S.fgObj y)
    (hf : IsIrreducibleMorphism f) [Mono f] :
    S.objectFinrank x < S.objectFinrank y := by
  letI : Module.Finite k (S.fgObj x) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj x)
  letI : Module.Finite k (S.fgObj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj y)
  let fₖ := homRestrictScalars (k := k) f
  have hinj : Function.Injective fₖ := by
    exact (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
  have hle : S.objectFinrank x ≤ S.objectFinrank y := by
    exact fₖ.finrank_le_finrank_of_injective hinj
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsurj : Function.Surjective fₖ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  have hsurj' : Function.Surjective f.hom.hom := hsurj
  letI : Epi f :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurj'
  letI : IsIso f := isIso_of_mono_of_epi f
  exact hf.not_isSplitMono inferInstance

/-- An epic irreducible map between selected indecomposables strictly lowers
coefficient-field dimension. -/
theorem objectFinrank_lt_of_irreducible_epi
    {x y : Fin S.n} (f : S.fgObj x ⟶ S.fgObj y)
    (hf : IsIrreducibleMorphism f) [Epi f] :
    S.objectFinrank y < S.objectFinrank x := by
  letI : Module.Finite k (S.fgObj x) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj x)
  letI : Module.Finite k (S.fgObj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj y)
  let fₖ := homRestrictScalars (k := k) f
  have hsurj : Function.Surjective fₖ := by
    exact (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
  have hle : S.objectFinrank y ≤ S.objectFinrank x := by
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hinj : Function.Injective fₖ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).2 hsurj
  have hinj' : Function.Injective f.hom.hom := hinj
  letI : Mono f :=
    (IndecomposableSkeleton.fg_mono_iff_injective f).2 hinj'
  letI : IsIso f := isIso_of_mono_of_epi f
  exact hf.not_isSplitEpi inferInstance

/-- Shorthand for the vendored right tau-category data. -/
abbrev tauData := S.finiteTauCategoryData

/-- An occurrence of `y` in the chosen middle decomposition of the right mesh
ending at `x`. -/
abbrev Occurrence (y x : Fin S.n) :=
  {i : Fin (FiniteTauMatrix.rightMiddleArity S.tauData.toFiniteRightTauCategoryData x) //
    FiniteTauMatrix.rightMiddleLabel S.tauData.toFiniteRightTauCategoryData x i = y}

/-- The arrow multiplicity counts occurrences. -/
theorem arrowMultiplicity_eq_card_occurrence (y x : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity S.tauData.toFiniteRightTauCategoryData y x =
      Fintype.card (S.Occurrence y x) := by
  classical
  rw [FiniteTauMatrix.arrowMultiplicity, Fintype.card_subtype, Finset.card_filter]
  congr 1
  funext i
  congr 1

/-- An occurrence gives an irreducible map from `y` to `x`. -/
def occurrenceMap {y x : Fin S.n} (i : S.Occurrence y x) : S.fgObj y ⟶ S.fgObj x :=
  eqToHom (congrArg S.fgObj i.2.symm) ≫
    FiniteTauMatrix.rightMiddleComponent S.tauData x i.1

theorem occurrenceMap_isIrreducible {y x : Fin S.n} (i : S.Occurrence y x) :
    IsIrreducibleMorphism (S.occurrenceMap i) := by
  obtain ⟨i, rfl⟩ := i
  simpa [occurrenceMap] using
    FiniteTauMatrix.rightMiddleComponent_isIrreducible S.tauData x i

/-- Inclusion of the occurrence `i` into the right-mesh middle term. -/
def occurrenceInclusion {y x : Fin S.n} (i : S.Occurrence y x) :
    S.fgObj y ⟶ (S.tauData.rightMesh (S.fgObj x)).X₂ :=
  eqToHom (congrArg S.fgObj i.2.symm) ≫
    FiniteTauMatrix.rightMiddleInclusion S.tauData x i.1

/-- Projection from the right-mesh middle term onto the occurrence `i`. -/
def occurrenceProjection {y x : Fin S.n} (i : S.Occurrence y x) :
    (S.tauData.rightMesh (S.fgObj x)).X₂ ⟶ S.fgObj y :=
  FiniteTauMatrix.rightMiddleProjection S.tauData x i.1 ≫
    eqToHom (congrArg S.fgObj i.2)

theorem occurrenceInclusion_projection {y x : Fin S.n} (i : S.Occurrence y x) :
    S.occurrenceInclusion i ≫ S.occurrenceProjection i = 𝟙 _ := by
  obtain ⟨i, rfl⟩ := i
  simp [occurrenceInclusion, occurrenceProjection]
  rfl

theorem occurrenceInclusion_projection_ne {y x : Fin S.n} {i j : S.Occurrence y x}
    (hij : i ≠ j) : S.occurrenceInclusion i ≫ S.occurrenceProjection j = 0 := by
  have hij' : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
  have hzero : FiniteTauMatrix.rightMiddleInclusion S.tauData x i.1 ≫
      FiniteTauMatrix.rightMiddleProjection S.tauData x j.1 = 0 := by
    unfold FiniteTauMatrix.rightMiddleInclusion FiniteTauMatrix.rightMiddleProjection
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [biproduct.ι_π_ne _ hij']
  simp only [occurrenceInclusion, occurrenceProjection, Category.assoc]
  rw [reassoc_of% hzero]
  simp

/-- Two distinct occurrences of `y` in the mesh ending at `x` bound twice the
dimension of `y` by the dimension of the middle term. -/
theorem two_mul_objectFinrank_le_rightMiddle (x y : Fin S.n)
    (hxy : 2 ≤ FiniteTauMatrix.arrowMultiplicity S.tauData.toFiniteRightTauCategoryData y x) :
    2 * S.objectFinrank y ≤
      Module.finrank k (S.tauData.rightMesh (S.fgObj x)).X₂ := by
  classical
  letI : Module.Finite k (S.fgObj y) :=
    RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj y)
  letI : Module.Finite k (S.tauData.rightMesh (S.fgObj x)).X₂ :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  rw [arrowMultiplicity_eq_card_occurrence] at hxy
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := S.Occurrence y x) (by omega)
  · let L : (S.fgObj y × S.fgObj y) →ₗ[k] (S.tauData.rightMesh (S.fgObj x)).X₂ :=
      (homRestrictScalars (k := k) (S.occurrenceInclusion a)).comp
          (LinearMap.fst k (S.fgObj y) (S.fgObj y)) +
        (homRestrictScalars (k := k) (S.occurrenceInclusion b)).comp
          (LinearMap.snd k (S.fgObj y) (S.fgObj y))
    have hinj : Function.Injective L := by
      intro p q hpq
      have hpa := congrArg (homRestrictScalars (k := k) (S.occurrenceProjection a)) hpq
      have hpb := congrArg (homRestrictScalars (k := k) (S.occurrenceProjection b)) hpq
      have e1 : ∀ v, (S.occurrenceProjection a).hom.hom ((S.occurrenceInclusion a).hom.hom v) = v :=
        fun v ↦ congrArg (fun g ↦ g.hom.hom v) (S.occurrenceInclusion_projection a)
      have e2 : ∀ v, (S.occurrenceProjection b).hom.hom ((S.occurrenceInclusion b).hom.hom v) = v :=
        fun v ↦ congrArg (fun g ↦ g.hom.hom v) (S.occurrenceInclusion_projection b)
      have e3 : ∀ v, (S.occurrenceProjection a).hom.hom ((S.occurrenceInclusion b).hom.hom v) = 0 :=
        fun v ↦ congrArg (fun g ↦ g.hom.hom v) (S.occurrenceInclusion_projection_ne hab.symm)
      have e4 : ∀ v, (S.occurrenceProjection b).hom.hom ((S.occurrenceInclusion a).hom.hom v) = 0 :=
        fun v ↦ congrArg (fun g ↦ g.hom.hom v) (S.occurrenceInclusion_projection_ne hab)
      simp only [L, LinearMap.add_apply, LinearMap.comp_apply, homRestrictScalars_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, map_add, e1, e2, e3, e4, add_zero,
        zero_add] at hpa hpb
      exact Prod.ext hpa hpb
    have hle := L.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_prod] at hle
    simpa [objectFinrank, two_mul] using hle

/-- The kernel map of the chosen almost split sequence is exact at the middle
term. Copied from `Algebra/RightModuleHoshinoTorsion.lean`. -/
theorem rightKernelMap_functionExact
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Function.Exact (S.rightKernelMap z).hom.hom
      (S.minimalRightAlmostSplitAt z.1).map.hom.hom := by
  let B := S.minimalRightAlmostSplitAt z.1
  let e := S.rightTranslationKernelIso z
  have hzero : S.rightKernelMap z ≫ B.map = 0 := by
    change ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map) ≫
      B.map = 0
    simp
  have hKernel : IsLimit
      (KernelFork.ofι (S.rightKernelMap z) hzero) :=
    IsLimit.ofIsoLimit (kernelIsKernel B.map)
      (Fork.ext e (by
        change e.hom ≫ ((S.rightTranslationKernelIso z).inv ≫
          kernel.ι B.map) = kernel.ι B.map
        simp [e]))
  let T : ShortComplex (FinitelyGeneratedCategory A) :=
    ShortComplex.mk (S.rightKernelMap z) B.map hzero
  have hT : T.Exact := T.exact_of_f_is_kernel hKernel
  let U := forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A)
  have hTU : (T.map U).Exact := hT.map U
  have hfun : Function.Exact (T.map U).f (T.map U).g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hTU
  change Function.Exact (S.rightKernelMap z).hom.hom B.map.hom.hom at hfun
  exact hfun

/-- Coefficient-field dimensions are additive across the selected
Auslander--Reiten sequence. -/
theorem rightMesh_finrank_eq_translation_add_endpoint
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Module.finrank k (S.tauData.rightMesh (S.fgObj z.1)).X₂ =
      S.objectFinrank (S.rightTranslationEquiv z).1 + S.objectFinrank z.1 := by
  let B := S.minimalRightAlmostSplitAt z.1
  letI : Module.Finite k (S.fgObj (S.rightTranslationEquiv z).1) :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  letI : Module.Finite k B.middle :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  letI : Module.Finite k (S.fgObj z.1) :=
    RightModule.finite_over_field_of_finitelyGenerated k A _
  let f := homRestrictScalars (k := k) (S.rightKernelMap z)
  let g := homRestrictScalars (k := k) B.map
  have hexact : Function.Exact f g := by
    change Function.Exact (S.rightKernelMap z).hom.hom B.map.hom.hom
    exact S.rightKernelMap_functionExact z
  have hinj : Function.Injective f := by
    haveI : Mono (S.rightKernelMap z) := by
      change Mono ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map)
      infer_instance
    exact (IndecomposableSkeleton.fg_mono_iff_injective
      (S.rightKernelMap z)).1 inferInstance
  have hsurj : Function.Surjective g := by
    haveI : Epi B.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
    exact (IndecomposableSkeleton.fg_epi_iff_surjective B.map).1
      inferInstance
  have hdim := MBDVendor.Magnitude.CategoryTheory.finrank_middle_eq_add_of_exact
    k f g hexact hinj hsurj
  rw [show S.tauData.rightMesh (S.fgObj z.1) = S.labelRightMesh z.1 by
    exact S.canonicalRightMesh_at_label z.1]
  rw [show S.labelRightMesh z.1 = S.nonprojectiveRightMesh z by
    simp [labelRightMesh, z.2]]
  exact hdim

/-- A pair carrying at least two parallel irreducible maps produces another
such pair with strictly larger maximal endpoint dimension: the
dimension-growth step of Lemma 2.2. -/
theorem exists_multipleArrow_pair_of_multipleArrow
    (x y : Fin S.n)
    (hxy : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.tauData.toFiniteRightTauCategoryData x y) :
    ∃ x' y' : Fin S.n,
      2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.tauData.toFiniteRightTauCategoryData x' y' ∧
      max (S.objectFinrank x) (S.objectFinrank y) <
        max (S.objectFinrank x') (S.objectFinrank y') := by
  classical
  have hcard := hxy
  rw [arrowMultiplicity_eq_card_occurrence] at hcard
  have hne : Nonempty (S.Occurrence x y) := Fintype.card_pos_iff.mp (by omega)
  let a : S.Occurrence x y := Classical.choice hne
  let f : S.fgObj x ⟶ S.fgObj y := S.occurrenceMap a
  have hf : IsIrreducibleMorphism f := S.occurrenceMap_isIrreducible a
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono f := hmono
    have hdim : S.objectFinrank x < S.objectFinrank y :=
      S.objectFinrank_lt_of_irreducible_mono f hf
    have hx : ¬ Injective (S.fgObj x) := by
      intro hxInjective
      letI : Injective (S.fgObj x) := hxInjective
      apply hf.not_isSplitMono
      exact IsSplitMono.mk'
        { retraction := Injective.factorThru (𝟙 (S.fgObj x)) f
          id := Injective.comp_factorThru (𝟙 (S.fgObj x)) f }
    let xni : {i : Fin S.n // ¬ Injective (S.fgObj i)} := ⟨x, hx⟩
    let z := (S.rightTranslationEquiv).symm xni
    have hz : (S.rightTranslationEquiv z).1 = x := by
      exact congrArg Subtype.val
        (S.rightTranslationEquiv.apply_symm_apply xni)
    have hmultiple : 2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.tauData.toFiniteRightTauCategoryData y z.1 := by
      rw [← S.arrowMultiplicity_eq_inverseTranslation xni y]
      exact hxy
    have htwo := S.two_mul_objectFinrank_le_rightMiddle z.1 y hmultiple
    have hmesh := S.rightMesh_finrank_eq_translation_add_endpoint z
    rw [hmesh, hz] at htwo
    have hgrowth : S.objectFinrank y < S.objectFinrank z.1 := by
      omega
    refine ⟨y, z.1, hmultiple, ?_⟩
    simp only [Nat.max_eq_right (Nat.le_of_lt hdim),
      Nat.max_eq_right (Nat.le_of_lt hgrowth)]
    exact hgrowth
  · letI : Epi f := hepi
    have hdim : S.objectFinrank y < S.objectFinrank x :=
      S.objectFinrank_lt_of_irreducible_epi f hf
    have hy : ¬ Projective (S.fgObj y) := by
      intro hyProjective
      letI : Projective (S.fgObj y) := hyProjective
      apply hf.not_isSplitEpi
      exact IsSplitEpi.mk'
        { section_ := Projective.factorThru (𝟙 (S.fgObj y)) f
          id := Projective.factorThru_comp (𝟙 (S.fgObj y)) f }
    let ynp : {i : Fin S.n // ¬ Projective (S.fgObj i)} := ⟨y, hy⟩
    let t := S.rightTranslationEquiv ynp
    have hback : ((S.rightTranslationEquiv).symm t).1 = y := by
      exact congrArg Subtype.val
        (S.rightTranslationEquiv.symm_apply_apply ynp)
    have hmultiple : 2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.tauData.toFiniteRightTauCategoryData t.1 x := by
      rw [S.arrowMultiplicity_eq_inverseTranslation t x, hback]
      exact hxy
    have htwo := S.two_mul_objectFinrank_le_rightMiddle y x hxy
    have hmesh := S.rightMesh_finrank_eq_translation_add_endpoint ynp
    have htwo' : 2 * S.objectFinrank x ≤
        S.objectFinrank t.1 + S.objectFinrank y := calc
      _ ≤ Module.finrank k
          (S.tauData.rightMesh (S.fgObj y)).X₂ := htwo
      _ = S.objectFinrank (S.rightTranslationEquiv ynp).1 +
          S.objectFinrank ynp.1 := hmesh
      _ = _ := rfl
    have hgrowth : S.objectFinrank x < S.objectFinrank t.1 := by
      omega
    refine ⟨t.1, x, hmultiple, ?_⟩
    simp only [Nat.max_eq_left (Nat.le_of_lt hdim),
      Nat.max_eq_left (Nat.le_of_lt hgrowth)]
    exact hgrowth

/-- At most one arrow between two selected indecomposables. -/
theorem arrowMultiplicity_le_one (x y : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity
      S.tauData.toFiniteRightTauCategoryData x y ≤ 1 := by
  classical
  by_contra hle
  have hxy : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.tauData.toFiniteRightTauCategoryData x y := by
    omega
  let pairs : Finset (Fin S.n × Fin S.n) :=
    Finset.univ.filter fun p ↦
      2 ≤ FiniteTauMatrix.arrowMultiplicity
        S.tauData.toFiniteRightTauCategoryData p.1 p.2
  have hxyMem : (x, y) ∈ pairs := by
    simp [pairs, hxy]
  obtain ⟨p, hp, hpMax⟩ := Finset.exists_max_image pairs
    (fun p ↦ max (S.objectFinrank p.1) (S.objectFinrank p.2))
    ⟨(x, y), hxyMem⟩
  have hpMultiple : 2 ≤ FiniteTauMatrix.arrowMultiplicity
      S.tauData.toFiniteRightTauCategoryData p.1 p.2 := by
    simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  obtain ⟨x', y', hmultiple, hgrowth⟩ :=
    S.exists_multipleArrow_pair_of_multipleArrow p.1 p.2 hpMultiple
  have hnewMem : (x', y') ∈ pairs := by
    simp [pairs, hmultiple]
  have hmax := hpMax (x', y') hnewMem
  exact (not_lt_of_ge hmax) hgrowth

/-- No loops: no occurrence of `x` in the mesh ending at `x`. -/
theorem arrowMultiplicity_self (x : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity S.tauData.toFiniteRightTauCategoryData x x = 0 := by
  classical
  rw [arrowMultiplicity_eq_card_occurrence, Fintype.card_eq_zero_iff]
  refine ⟨fun a ↦ ?_⟩
  have hf := S.occurrenceMap_isIrreducible a
  rcases hf.mono_or_epi with hmono | hepi
  · letI : Mono (S.occurrenceMap a) := hmono
    exact lt_irrefl _ (S.objectFinrank_lt_of_irreducible_mono _ hf)
  · letI : Epi (S.occurrenceMap a) := hepi
    exact lt_irrefl _ (S.objectFinrank_lt_of_irreducible_epi _ hf)

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- **Lemma 2.2** (`lem:square-free`). `Γ_A` has at most one arrow between each
ordered pair of vertices. -/
theorem finrank_irr_le_one (x y : Fin S.n) :
    Module.finrank k (S.Irr (S.ind x) (S.ind y)) ≤ 1 := by
  rw [S.finrank_irr_eq_arrowMultiplicity]
  exact S.toVendor.arrowMultiplicity_le_one x y

/-- **Lemma 2.2** (`lem:square-free`). `Γ_A` has no loops. -/
theorem finrank_irr_self (x : Fin S.n) :
    Module.finrank k (S.Irr (S.ind x) (S.ind x)) = 0 := by
  rw [S.finrank_irr_eq_arrowMultiplicity]
  exact S.toVendor.arrowMultiplicity_self x

/-- **Lemma 2.2** (`lem:square-free`), in the form of Definition 2.4: `Γ_A` has
at most one arrow between each ordered pair of vertices. -/
theorem hasAtMostOneArrow : HasAtMostOneArrow S.ARVertex := by
  intro x y
  constructor
  intro a b
  apply Fin.ext
  have := S.finrank_irr_le_one x y
  have ha := a.2
  have hb := b.2
  change _ < Module.finrank k (S.Irr (S.ind x) (S.ind y)) at ha hb
  omega

end MultiplicativeBasisDeformations.IndSkeleton
