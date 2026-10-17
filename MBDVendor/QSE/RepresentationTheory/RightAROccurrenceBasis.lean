import MBDVendor.QSE.RepresentationTheory.LinearIrreducibleHomSpace

/-!
# Occurrence bases for minimal right almost-split maps

For a chosen indecomposable decomposition of the middle term of a minimal
right almost-split map, this file constructs the coordinate map from copies
of one indecomposable to the linear irreducible-morphism space
`Irr = rad / rad²`.  Right minimality proves linear independence, while
scalar endomorphisms of the source prove spanning.  Thus the multiplicity of
an indecomposable middle summand is exactly the dimension of the corresponding
irreducible-morphism space.

The construction is abstract: it uses no quiver presentation or module
classification, and it applies to projective-boundary right almost-split maps
as well as to almost-split sequences.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {Iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)
  [∀ i : Iota, Module K (sigma.obj i)]
  [∀ i : Iota, IsScalarTower K R (sigma.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

attribute [local instance]
  FintypeCat.fintype

/-- The occurrences of one fixed indecomposable in a chosen right
almost-split middle decomposition. -/
abbrev RightAROccurrence {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :=
  {t : A.index // A.label t = x}

/-- The coordinate map from an occurring copy of `x` to the right
almost-split endpoint. -/
def rightAROccurrenceArrow {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (t : sigma.RightAROccurrence A x) : sigma.obj x ⟶ sigma.obj z := by
  classical
  exact eqToHom (congrArg sigma.obj t.2.symm) ≫
    biproduct.ι (fun j : A.index ↦ sigma.obj (A.label j)) t.1 ≫
    A.decomposition.inv ≫ A.map

/-- The same coordinate before composing with the right almost-split map. -/
def rightAROccurrenceMiddleArrow {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (t : sigma.RightAROccurrence A x) : sigma.obj x ⟶ A.middle := by
  classical
  exact eqToHom (congrArg sigma.obj t.2.symm) ≫
    biproduct.ι (fun j : A.index ↦ sigma.obj (A.label j)) t.1 ≫
    A.decomposition.inv

/-- The middle-term morphism represented by a coefficient vector. -/
def rightAROccurrenceMiddleCombination {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K) : sigma.obj x ⟶ A.middle := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  exact ∑ t, c t • sigma.rightAROccurrenceMiddleArrow A x t

/-- Projection back from the middle term to one specified occurrence. -/
def rightAROccurrenceMiddleProjection {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (t : sigma.RightAROccurrence A x) : A.middle ⟶ sigma.obj x := by
  classical
  exact A.decomposition.hom ≫
    biproduct.π (fun j : A.index ↦ sigma.obj (A.label j)) t.1 ≫
    eqToHom (congrArg sigma.obj t.2)

omit [FiniteDimensional K R]
  [∀ i : Iota, Module K (sigma.obj i)]
  [∀ i : Iota, IsScalarTower K R (sigma.obj i)] in
theorem rightAROccurrenceMiddleCombination_projection {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K)
    (t : sigma.RightAROccurrence A x) :
    sigma.rightAROccurrenceMiddleCombination A x c ≫
      sigma.rightAROccurrenceMiddleProjection A x t =
        c t • 𝟙 (sigma.obj x) := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  simp only [rightAROccurrenceMiddleCombination,
    Preadditive.sum_comp]
  rw [Finset.sum_eq_single t]
  · simp [rightAROccurrenceMiddleArrow,
      rightAROccurrenceMiddleProjection, Category.assoc]
  · intro s _ hst
    have hval : s.1 ≠ t.1 := by
      intro h
      exact hst (Subtype.ext h)
    simp [rightAROccurrenceMiddleArrow,
      rightAROccurrenceMiddleProjection, Category.assoc, hval]
  · simp

omit [FiniteDimensional K R]
  [∀ i : Iota, Module K (sigma.obj i)]
  [∀ i : Iota, IsScalarTower K R (sigma.obj i)] in
theorem rightAROccurrenceMiddleCombination_isSplitMono_of_ne_zero
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K) (hc : c ≠ 0) :
    IsSplitMono (sigma.rightAROccurrenceMiddleCombination A x c) := by
  classical
  have hex : ∃ t, c t ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext t
    exact h t
  obtain ⟨t, ht⟩ := hex
  exact IsSplitMono.mk'
    { retraction := (c t)⁻¹ •
        sigma.rightAROccurrenceMiddleProjection A x t
      id := by
        rw [Linear.comp_smul,
          sigma.rightAROccurrenceMiddleCombination_projection A x c t]
        simp [ht] }

/-- The same coordinate arrow as an `R`-linear map. -/
def rightAROccurrenceArrowLinear {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (t : sigma.RightAROccurrence A x) :
    sigma.obj x →ₗ[R] sigma.obj z :=
  (sigma.rightAROccurrenceArrow A x t).hom.hom

/-- A finite linear combination of occurrence-coordinate arrows. -/
def rightAROccurrenceCombination {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K) :
    sigma.obj x →ₗ[R] sigma.obj z := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  exact ∑ t, c t • sigma.rightAROccurrenceArrowLinear A x t

/-- Occurrence-coordinate combination is `K`-linear in its coefficients. -/
def rightAROccurrenceCombinationLinear {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :
    (sigma.RightAROccurrence A x → K) →ₗ[K]
      (sigma.obj x →ₗ[R] sigma.obj z) where
  toFun := sigma.rightAROccurrenceCombination A x
  map_add' := by
    classical
    letI : Fintype (sigma.RightAROccurrence A x) :=
      Fintype.ofFinite (sigma.RightAROccurrence A x)
    intro c d
    change (∑ t, (c t + d t) •
      sigma.rightAROccurrenceArrowLinear A x t) =
      (∑ t, c t • sigma.rightAROccurrenceArrowLinear A x t) +
      (∑ t, d t • sigma.rightAROccurrenceArrowLinear A x t)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [add_smul]
  map_smul' := by
    classical
    letI : Fintype (sigma.RightAROccurrence A x) :=
      Fintype.ofFinite (sigma.RightAROccurrence A x)
    intro a c
    change (∑ t, (a * c t) •
      sigma.rightAROccurrenceArrowLinear A x t) =
      a • (∑ t, c t • sigma.rightAROccurrenceArrowLinear A x t)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact mul_smul a (c t)
      (sigma.rightAROccurrenceArrowLinear A x t)

omit [FiniteDimensional K R] in
theorem rightAROccurrenceMiddleCombination_comp {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K) :
    sigma.rightAROccurrenceMiddleCombination A x c ≫ A.map =
      ConcreteCategory.ofHom
        (sigma.rightAROccurrenceCombination A x c) := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  have hcat :
      sigma.rightAROccurrenceMiddleCombination A x c ≫ A.map =
        ∑ t, c t • sigma.rightAROccurrenceArrow A x t := by
    simp only [rightAROccurrenceMiddleCombination,
      Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro t _
    rw [Linear.smul_comp]
    rfl
  rw [hcat]
  apply FGModuleCat.hom_ext
  let underlying :
      (sigma.obj x ⟶ sigma.obj z) →+ (sigma.obj x →ₗ[R] sigma.obj z) :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change underlying (∑ t, c t •
      sigma.rightAROccurrenceArrow A x t) =
    sigma.rightAROccurrenceCombination A x c
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  ext m
  change algebraMap K R (c t) •
      (sigma.rightAROccurrenceArrowLinear A x t) m =
    c t • (sigma.rightAROccurrenceArrowLinear A x t) m
  exact IsScalarTower.algebraMap_smul R (c t)
    ((sigma.rightAROccurrenceArrowLinear A x t) m)

/-- Every displayed occurrence-coordinate is radical: if that single
coordinate split epimorphically, then the whole right almost-split map would
split epimorphically. -/
theorem rightAROccurrenceArrow_not_isSplitEpi {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (t : sigma.RightAROccurrence A x) :
    ¬ IsSplitEpi (sigma.rightAROccurrenceArrow A x t) := by
  classical
  intro hsplit
  obtain ⟨se⟩ := hsplit.exists_splitEpi
  apply A.rightAlmostSplit.not_isSplitEpi
  exact IsSplitEpi.mk'
    { section_ := se.section_ ≫
        eqToHom (congrArg sigma.obj t.2.symm) ≫
        biproduct.ι (fun j : A.index ↦ sigma.obj (A.label j)) t.1 ≫
        A.decomposition.inv
      id := by
        simpa only [rightAROccurrenceArrow, Category.assoc] using se.id }

omit [FiniteDimensional K R] in
theorem rightAROccurrenceArrowLinear_mem_radical {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (t : sigma.RightAROccurrence A x) :
    sigma.rightAROccurrenceArrowLinear A x t ∈
      sigma.radicalHom (K := K) x z :=
  (sigma.mem_radicalHom_iff_not_isSplitEpi
    (K := K) (sigma.rightAROccurrenceArrowLinear A x t)).2
      (sigma.rightAROccurrenceArrow_not_isSplitEpi A x t)

omit [FiniteDimensional K R] in
theorem rightAROccurrenceCombination_mem_radical {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K) :
    sigma.rightAROccurrenceCombination A x c ∈
      sigma.radicalHom (K := K) x z := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  apply Submodule.sum_mem
  intro t _
  exact (sigma.radicalHom (K := K) x z).smul_mem
    (c t) (sigma.rightAROccurrenceArrowLinear_mem_radical A x t)

/-- The canonical linear map from occurrence coefficients to the linear
radical Hom-space. -/
def rightAROccurrenceToRadical {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :
    (sigma.RightAROccurrence A x → K) →ₗ[K]
      sigma.radicalHom (K := K) x z :=
  (sigma.rightAROccurrenceCombinationLinear A x).codRestrict
    (sigma.radicalHom (K := K) x z)
    (sigma.rightAROccurrenceCombination_mem_radical A x)

/-- The basis-candidate map from right-AR occurrences to
`rad(x,z) / rad²(x,z)`. -/
def rightAROccurrenceToIrr {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :
    (sigma.RightAROccurrence A x → K) →ₗ[K]
      sigma.irreducibleHomSpace (K := K) x z :=
  (sigma.radicalSquareInRadicalSubmodule (K := K) x z).mkQ.comp
    (sigma.rightAROccurrenceToRadical A x)

omit [FiniteDimensional K R] in
theorem rightAROccurrenceToIrr_eq_zero_iff {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K) :
    sigma.rightAROccurrenceToIrr A x c = 0 ↔
      (ConcreteCategory.ofHom
        (sigma.rightAROccurrenceCombination A x c) :
          sigma.obj x ⟶ sigma.obj z) ∈
        sigma.radicalSquareHomAddSubgroup x z := by
  rw [rightAROccurrenceToIrr, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

omit [FiniteDimensional K R] in
/-- Occurrence classes are linearly independent for every minimal right
almost-split decomposition.  Right minimality alone eliminates a hypothetical
radical-square relation, so this argument also covers projective boundary
maps and needs no AR kernel or translation data. -/
theorem rightAROccurrenceToIrr_eq_zero {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (c : sigma.RightAROccurrence A x → K)
    (hzero : sigma.rightAROccurrenceToIrr (K := K) A x c = 0) :
    c = 0 := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  by_contra hc
  have hsquare :=
    (sigma.rightAROccurrenceToIrr_eq_zero_iff A x c).1 hzero
  obtain ⟨M, g, h, hg, hh, hcomp⟩ := hsquare
  let q : sigma.obj x ⟶ A.middle :=
    sigma.rightAROccurrenceMiddleCombination A x c
  obtain ⟨k, hk⟩ := A.rightAlmostSplit.factors h hh
  let d : sigma.obj x ⟶ A.middle := q - g ≫ k
  have hqmap : q ≫ A.map =
      ConcreteCategory.ofHom
        (sigma.rightAROccurrenceCombination A x c) :=
    sigma.rightAROccurrenceMiddleCombination_comp A x c
  have hdmap : d ≫ A.map = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, hqmap, Category.assoc, hk, hcomp,
      sub_self]
  have hqsplit : IsSplitMono q :=
    sigma.rightAROccurrenceMiddleCombination_isSplitMono_of_ne_zero
      A x c hc
  letI : IsSplitMono q := hqsplit
  let rq : A.middle ⟶ sigma.obj x := retraction q
  have hqid : q ≫ rq = 𝟙 (sigma.obj x) := IsSplitMono.id q
  have hgrad : CategoricalRadical.IsRadicalMorphism g :=
    (sigma.isRadicalMorphism_iff_not_isSplitMono_from_obj g).2 hg
  let u : sigma.obj x ⟶ sigma.obj x :=
    𝟙 (sigma.obj x) - g ≫ (k ≫ rq)
  haveI : IsIso u := hgrad (k ≫ rq)
  have hdq : d ≫ rq = u := by
    dsimp only [d, u]
    rw [Preadditive.sub_comp, hqid, Category.assoc]
  letI : IsIso (d ≫ rq) := hdq.symm ▸ inferInstance
  have hdsplit : IsSplitMono d :=
    IsSplitMono.mk'
      { retraction := rq ≫ inv (d ≫ rq)
        id := by
          rw [← Category.assoc]
          simp }
  letI : IsSplitMono d := hdsplit
  let rd : A.middle ⟶ sigma.obj x := retraction d
  let e : A.middle ⟶ A.middle := 𝟙 A.middle - rd ≫ d
  have hemap : e ≫ A.map = A.map := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      hdmap, comp_zero, sub_zero]
  letI : IsIso e := A.rightMinimal e hemap
  have hde : d ≫ e = 0 := by
    dsimp only [e, rd]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      IsSplitMono.id, Category.id_comp, sub_self]
  have hd0 : d = 0 := by
    rw [← cancel_mono e]
    simp only [hde, zero_comp]
  have hdcomp : d ≫ retraction d = 0 ≫ retraction d :=
    congrArg (fun f ↦ f ≫ retraction d) hd0
  have hid0 : (𝟙 (sigma.obj x) : sigma.obj x ⟶ sigma.obj x) = 0 := by
    calc
      𝟙 (sigma.obj x) = d ≫ retraction d := (IsSplitMono.id d).symm
      _ = 0 := by simpa only [zero_comp] using hdcomp
  have hxzero : IsZero (sigma.obj x) :=
    IsZero.of_mono_eq_zero (𝟙 (sigma.obj x)) hid0
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have hxzero' : IsZero (U.obj (sigma.obj x)) := U.map_isZero hxzero
  have hsub : Subsingleton (sigma.obj x) :=
    ModuleCat.isZero_iff_subsingleton.mp hxzero'
  exact not_nontrivial_iff_subsingleton.mpr hsub
    (sigma.indecomposable x).nontrivial

omit [FiniteDimensional K R] in
theorem rightAROccurrenceToIrr_injective {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :
    Function.Injective
      (sigma.rightAROccurrenceToIrr (K := K) A x) := by
  intro c d hcd
  apply sub_eq_zero.mp
  apply sigma.rightAROccurrenceToIrr_eq_zero A x
  rw [map_sub, hcd, sub_self]

omit [FiniteDimensional K R] in
/-- The coordinate classes span `Irr` as soon as endomorphisms of the
source are scalar.  This is the right-minimal approximation half of the
standard occurrence--`Irr` basis theorem. -/
theorem rightAROccurrenceToIrr_surjective_of_scalar_endomorphisms
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (hscalar : ∀ f : sigma.obj x ⟶ sigma.obj x,
      ∃ a : K, a • 𝟙 (sigma.obj x) = f) :
    Function.Surjective (sigma.rightAROccurrenceToIrr (K := K) A x) := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  intro y
  obtain ⟨f, rfl⟩ :=
    (sigma.radicalSquareInRadicalSubmodule (K := K) x z).mkQ_surjective y
  let Fcat : sigma.obj x ⟶ sigma.obj z := ConcreteCategory.ofHom f.1
  have hFnonsplit : ¬ IsSplitEpi Fcat :=
    (sigma.mem_radicalHom_iff_not_isSplitEpi (K := K) f.1).1 f.2
  obtain ⟨h, hh⟩ := A.rightAlmostSplit.factors Fcat hFnonsplit
  let coeff (t : sigma.RightAROccurrence A x) : K :=
    Classical.choose
      (hscalar (h ≫ sigma.rightAROccurrenceMiddleProjection A x t))
  have coeff_spec (t : sigma.RightAROccurrence A x) :
      coeff t • 𝟙 (sigma.obj x) =
        h ≫ sigma.rightAROccurrenceMiddleProjection A x t :=
    Classical.choose_spec
      (hscalar (h ≫ sigma.rightAROccurrenceMiddleProjection A x t))
  let q : sigma.obj x ⟶ A.middle :=
    sigma.rightAROccurrenceMiddleCombination A x coeff
  let r : sigma.obj x ⟶ A.middle := h - q
  let family : A.index → FGModuleCat.{u} R :=
    fun j ↦ sigma.obj (A.label j)
  let component (j : A.index) : sigma.obj x ⟶ family j :=
    r ≫ A.decomposition.hom ≫ biproduct.π family j
  have hcomponent (j : A.index) : ¬ IsSplitMono (component j) := by
    by_cases hj : A.label j = x
    · let t : sigma.RightAROccurrence A x := ⟨j, hj⟩
      have hzero : component j = 0 := by
        have hrproj :
            r ≫ sigma.rightAROccurrenceMiddleProjection A x t = 0 := by
          dsimp only [r]
          rw [Preadditive.sub_comp, ← coeff_spec t,
            sigma.rightAROccurrenceMiddleCombination_projection A x coeff t,
            sub_self]
        rw [← cancel_mono (eqToHom (congrArg sigma.obj hj))]
        simpa only [component, family, t,
          rightAROccurrenceMiddleProjection, Category.assoc, zero_comp]
          using hrproj
      rw [hzero]
      intro hsplit
      letI : IsSplitMono (0 : sigma.obj x ⟶ family j) := hsplit
      have hxzero : IsZero (sigma.obj x) :=
        (IsZero.iff_isSplitMono_eq_zero
          (0 : sigma.obj x ⟶ family j)).2 rfl
      let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
      have hxzero' : IsZero (U.obj (sigma.obj x)) := U.map_isZero hxzero
      have hsub : Subsingleton (sigma.obj x) :=
        ModuleCat.isZero_iff_subsingleton.mp hxzero'
      exact not_nontrivial_iff_subsingleton.mpr hsub
        (sigma.indecomposable x).nontrivial
    · intro hsplit
      letI : IsSplitMono (component j) := hsplit
      letI : IsSplitEpi (component j) :=
        sigma.isSplitEpi_of_isSplitMono_between_obj (component j)
      letI : IsIso (component j) :=
        isIso_of_epi_of_isSplitMono (component j)
      exact hj (sigma.eq_of_iso ⟨asIso (component j)⟩).symm
  have hrnonsplit : ¬ IsSplitMono r := by
    have hlift : biproduct.lift component = r ≫ A.decomposition.hom := by
      apply biproduct.hom_ext
      intro j
      rw [biproduct.lift_π]
      rfl
    have hnonsplitLift : ¬ IsSplitMono (biproduct.lift component) :=
      sigma.biproductLift_not_isSplitMono family component hcomponent
    intro hrsplit
    letI : IsSplitMono r := hrsplit
    apply hnonsplitLift
    rw [hlift]
    infer_instance
  refine ⟨coeff, ?_⟩
  apply (Submodule.Quotient.eq
    (sigma.radicalSquareInRadicalSubmodule (K := K) x z)).2
  have hqmap : q ≫ A.map =
      ConcreteCategory.ofHom
        (sigma.rightAROccurrenceCombination A x coeff) :=
    sigma.rightAROccurrenceMiddleCombination_comp A x coeff
  have hsquare :
      (f - (sigma.rightAROccurrenceToRadical A x coeff)) ∈
        sigma.radicalSquareInRadicalSubmodule (K := K) x z := by
    change sigma.HasRadicalSquareFactorization
      (ConcreteCategory.ofHom
        (f.1 - sigma.rightAROccurrenceCombination A x coeff))
    refine ⟨A.middle, r, A.map, hrnonsplit,
      A.rightAlmostSplit.not_isSplitEpi, ?_⟩
    apply FGModuleCat.hom_ext
    change (r ≫ A.map).hom.hom =
      f.1 - sigma.rightAROccurrenceCombination A x coeff
    have hrmap : r ≫ A.map =
        Fcat - ConcreteCategory.ofHom
          (sigma.rightAROccurrenceCombination A x coeff) := by
      dsimp only [r, q]
      rw [Preadditive.sub_comp, hh, hqmap]
    rw [hrmap]
    rfl
  have hneg :=
    (sigma.radicalSquareInRadicalSubmodule (K := K) x z).neg_mem hsquare
  simpa [sub_eq_add_neg, add_comm] using hneg

/-- The general right-side occurrence--`Irr` equivalence, assuming only the
scalar-endomorphism conclusion needed for spanning. -/
def rightAROccurrenceLinearEquivOfScalarEndomorphisms
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (hscalar : ∀ f : sigma.obj x ⟶ sigma.obj x,
      ∃ a : K, a • 𝟙 (sigma.obj x) = f) :
    (sigma.RightAROccurrence A x → K) ≃ₗ[K]
      sigma.irreducibleHomSpace (K := K) x z :=
  LinearEquiv.ofBijective
    (sigma.rightAROccurrenceToIrr (K := K) A x)
    ⟨sigma.rightAROccurrenceToIrr_injective (K := K) A x,
      sigma.rightAROccurrenceToIrr_surjective_of_scalar_endomorphisms
        A x hscalar⟩

omit [FiniteDimensional K R] in
theorem finrank_irreducibleHomSpace_eq_card_rightAROccurrence
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (hscalar : ∀ f : sigma.obj x ⟶ sigma.obj x,
      ∃ a : K, a • 𝟙 (sigma.obj x) = f) :
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x z) =
      Nat.card (sigma.RightAROccurrence A x) := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  rw [← (sigma.rightAROccurrenceLinearEquivOfScalarEndomorphisms
    A x hscalar).finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

end MBDVendor.QSE.IndecomposableSkeleton
