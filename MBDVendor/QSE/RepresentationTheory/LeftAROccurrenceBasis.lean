import MBDVendor.QSE.RepresentationTheory.LinearIrreducibleHomSpace

/-!
# Occurrence bases for minimal left almost-split maps

This is the dual occurrence-coordinate construction for a chosen
indecomposable decomposition of the middle term of a minimal left
almost-split map.  Left minimality proves linear independence in
`Irr = rad / rad²`, while scalar endomorphisms of the target prove spanning.
Consequently, the multiplicity of a target indecomposable in the middle term
is exactly the dimension of the corresponding irreducible-morphism space.

The construction is abstract and uses no quiver presentation or module
classification.
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

/-- The occurrences of one fixed target indecomposable in a chosen minimal
left almost-split middle decomposition. -/
abbrev LeftAROccurrence {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :=
  {t : A.index // A.label t = y}

/-- Projection from the middle term to one occurring copy of `y`. -/
def leftAROccurrenceMiddleArrow {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (t : sigma.LeftAROccurrence A y) : A.middle ⟶ sigma.obj y := by
  classical
  exact A.decomposition.hom ≫
    biproduct.π (fun j : A.index ↦ sigma.obj (A.label j)) t.1 ≫
    eqToHom (congrArg sigma.obj t.2)

/-- The coordinate arrow from the left almost-split source to an occurring
copy of `y`. -/
def leftAROccurrenceArrow {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (t : sigma.LeftAROccurrence A y) : sigma.obj x ⟶ sigma.obj y :=
  A.map ≫ sigma.leftAROccurrenceMiddleArrow A y t

/-- Inclusion of one occurring copy of `y` back into the middle term. -/
def leftAROccurrenceMiddleInclusion {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (t : sigma.LeftAROccurrence A y) : sigma.obj y ⟶ A.middle := by
  classical
  exact eqToHom (congrArg sigma.obj t.2.symm) ≫
    biproduct.ι (fun j : A.index ↦ sigma.obj (A.label j)) t.1 ≫
    A.decomposition.inv

/-- The middle-term projection represented by a coefficient vector. -/
def leftAROccurrenceMiddleCombination {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K) : A.middle ⟶ sigma.obj y := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  exact ∑ t, c t • sigma.leftAROccurrenceMiddleArrow A y t

omit [FiniteDimensional K R]
    [∀ i : Iota, Module K (sigma.obj i)]
    [∀ i : Iota, IsScalarTower K R (sigma.obj i)] in
theorem leftAROccurrenceMiddleInclusion_combination {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K)
    (t : sigma.LeftAROccurrence A y) :
    sigma.leftAROccurrenceMiddleInclusion A y t ≫
      sigma.leftAROccurrenceMiddleCombination A y c =
        c t • 𝟙 (sigma.obj y) := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  simp only [leftAROccurrenceMiddleCombination,
    Preadditive.comp_sum]
  rw [Finset.sum_eq_single t]
  · simp [leftAROccurrenceMiddleInclusion,
      leftAROccurrenceMiddleArrow, Category.assoc]
  · intro s _ hst
    have hval : t.1 ≠ s.1 := by
      intro h
      exact hst (Subtype.ext h.symm)
    simp [leftAROccurrenceMiddleInclusion,
      leftAROccurrenceMiddleArrow, Category.assoc, hval]
  · simp

omit [FiniteDimensional K R]
    [∀ i : Iota, Module K (sigma.obj i)]
    [∀ i : Iota, IsScalarTower K R (sigma.obj i)] in
theorem leftAROccurrenceMiddleCombination_isSplitEpi_of_ne_zero
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K) (hc : c ≠ 0) :
    IsSplitEpi (sigma.leftAROccurrenceMiddleCombination A y c) := by
  classical
  have hex : ∃ t, c t ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext t
    exact h t
  obtain ⟨t, ht⟩ := hex
  exact IsSplitEpi.mk'
    { section_ := (c t)⁻¹ •
        sigma.leftAROccurrenceMiddleInclusion A y t
      id := by
        rw [Linear.smul_comp,
          sigma.leftAROccurrenceMiddleInclusion_combination A y c t]
        simp [ht] }

/-- The occurrence-coordinate arrow as an `R`-linear map. -/
def leftAROccurrenceArrowLinear {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (t : sigma.LeftAROccurrence A y) :
    sigma.obj x →ₗ[R] sigma.obj y :=
  (sigma.leftAROccurrenceArrow A y t).hom.hom

/-- A finite linear combination of occurrence-coordinate arrows. -/
def leftAROccurrenceCombination {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K) :
    sigma.obj x →ₗ[R] sigma.obj y := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  exact ∑ t, c t • sigma.leftAROccurrenceArrowLinear A y t

/-- Occurrence-coordinate combination is `K`-linear in its coefficients. -/
def leftAROccurrenceCombinationLinear {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :
    (sigma.LeftAROccurrence A y → K) →ₗ[K]
      (sigma.obj x →ₗ[R] sigma.obj y) where
  toFun := sigma.leftAROccurrenceCombination A y
  map_add' := by
    classical
    letI : Fintype (sigma.LeftAROccurrence A y) :=
      Fintype.ofFinite (sigma.LeftAROccurrence A y)
    intro c d
    change (∑ t, (c t + d t) •
      sigma.leftAROccurrenceArrowLinear A y t) =
      (∑ t, c t • sigma.leftAROccurrenceArrowLinear A y t) +
      (∑ t, d t • sigma.leftAROccurrenceArrowLinear A y t)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [add_smul]
  map_smul' := by
    classical
    letI : Fintype (sigma.LeftAROccurrence A y) :=
      Fintype.ofFinite (sigma.LeftAROccurrence A y)
    intro a c
    change (∑ t, (a * c t) •
      sigma.leftAROccurrenceArrowLinear A y t) =
      a • (∑ t, c t • sigma.leftAROccurrenceArrowLinear A y t)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact mul_smul a (c t)
      (sigma.leftAROccurrenceArrowLinear A y t)

omit [FiniteDimensional K R] in
theorem leftAROccurrenceCombination_eq_comp {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K) :
    A.map ≫ sigma.leftAROccurrenceMiddleCombination A y c =
      ConcreteCategory.ofHom
        (sigma.leftAROccurrenceCombination A y c) := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  have hcat :
      A.map ≫ sigma.leftAROccurrenceMiddleCombination A y c =
        ∑ t, c t • sigma.leftAROccurrenceArrow A y t := by
    simp only [leftAROccurrenceMiddleCombination,
      Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Linear.comp_smul]
    rfl
  rw [hcat]
  apply FGModuleCat.hom_ext
  let underlying :
      (sigma.obj x ⟶ sigma.obj y) →+ (sigma.obj x →ₗ[R] sigma.obj y) :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change underlying (∑ t, c t •
      sigma.leftAROccurrenceArrow A y t) =
    sigma.leftAROccurrenceCombination A y c
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  ext m
  change algebraMap K R (c t) •
      (sigma.leftAROccurrenceArrowLinear A y t) m =
    c t • (sigma.leftAROccurrenceArrowLinear A y t) m
  exact IsScalarTower.algebraMap_smul R (c t)
    ((sigma.leftAROccurrenceArrowLinear A y t) m)

/-- Every displayed left occurrence-coordinate is radical. -/
theorem leftAROccurrenceArrow_not_isSplitMono {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (t : sigma.LeftAROccurrence A y) :
    ¬ IsSplitMono (sigma.leftAROccurrenceArrow A y t) := by
  classical
  intro hsplit
  obtain ⟨sm⟩ := hsplit.exists_splitMono
  apply A.leftAlmostSplit.not_isSplitMono
  exact IsSplitMono.mk'
    { retraction :=
        sigma.leftAROccurrenceMiddleArrow A y t ≫ sm.retraction
      id := by
        simpa only [leftAROccurrenceArrow, Category.assoc] using sm.id }

omit [FiniteDimensional K R] in
theorem leftAROccurrenceArrowLinear_mem_radical {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (t : sigma.LeftAROccurrence A y) :
    sigma.leftAROccurrenceArrowLinear A y t ∈
      sigma.radicalHom (K := K) x y :=
  (sigma.mem_radicalHom_iff_not_isSplitMono
    (K := K) (sigma.leftAROccurrenceArrowLinear A y t)).2
      (sigma.leftAROccurrenceArrow_not_isSplitMono A y t)

omit [FiniteDimensional K R] in
theorem leftAROccurrenceCombination_mem_radical {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K) :
    sigma.leftAROccurrenceCombination A y c ∈
      sigma.radicalHom (K := K) x y := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  apply Submodule.sum_mem
  intro t _
  exact (sigma.radicalHom (K := K) x y).smul_mem
    (c t) (sigma.leftAROccurrenceArrowLinear_mem_radical A y t)

/-- The canonical linear map from left-occurrence coefficients to the
linear radical Hom-space. -/
def leftAROccurrenceToRadical {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :
    (sigma.LeftAROccurrence A y → K) →ₗ[K]
      sigma.radicalHom (K := K) x y :=
  (sigma.leftAROccurrenceCombinationLinear A y).codRestrict
    (sigma.radicalHom (K := K) x y)
    (sigma.leftAROccurrenceCombination_mem_radical A y)

/-- The basis-candidate map from left-AR occurrences to
`rad(x,y) / rad²(x,y)`. -/
def leftAROccurrenceToIrr {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :
    (sigma.LeftAROccurrence A y → K) →ₗ[K]
      sigma.irreducibleHomSpace (K := K) x y :=
  (sigma.radicalSquareInRadicalSubmodule (K := K) x y).mkQ.comp
    (sigma.leftAROccurrenceToRadical A y)

omit [FiniteDimensional K R] in
theorem leftAROccurrenceToIrr_eq_zero_iff {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K) :
    sigma.leftAROccurrenceToIrr A y c = 0 ↔
      (ConcreteCategory.ofHom
        (sigma.leftAROccurrenceCombination A y c) :
          sigma.obj x ⟶ sigma.obj y) ∈
        sigma.radicalSquareHomAddSubgroup x y := by
  rw [leftAROccurrenceToIrr, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

omit [FiniteDimensional K R] in
/-- Occurrence classes are linearly independent for every minimal left
almost-split decomposition.  This is the left-minimal dual of the standard
right occurrence argument. -/
theorem leftAROccurrenceToIrr_eq_zero {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (c : sigma.LeftAROccurrence A y → K)
    (hzero : sigma.leftAROccurrenceToIrr (K := K) A y c = 0) :
    c = 0 := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  by_contra hc
  have hsquare :=
    (sigma.leftAROccurrenceToIrr_eq_zero_iff A y c).1 hzero
  obtain ⟨M, g, h, hg, hh, hcomp⟩ := hsquare
  let q : A.middle ⟶ sigma.obj y :=
    sigma.leftAROccurrenceMiddleCombination A y c
  obtain ⟨k, hk⟩ := A.leftAlmostSplit.factors g hg
  let d : A.middle ⟶ sigma.obj y := q - k ≫ h
  have hmapq : A.map ≫ q =
      ConcreteCategory.ofHom
        (sigma.leftAROccurrenceCombination A y c) :=
    sigma.leftAROccurrenceCombination_eq_comp A y c
  have hmapd : A.map ≫ d = 0 := by
    dsimp only [d]
    rw [Preadditive.comp_sub, hmapq, ← Category.assoc, hk,
      hcomp, sub_self]
  have hqsplit : IsSplitEpi q :=
    sigma.leftAROccurrenceMiddleCombination_isSplitEpi_of_ne_zero
      A y c hc
  letI : IsSplitEpi q := hqsplit
  let sq : sigma.obj y ⟶ A.middle := section_ q
  have hqid : sq ≫ q = 𝟙 (sigma.obj y) := IsSplitEpi.id q
  have hhrad : CategoricalRadical.IsRadicalMorphism h :=
    (sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj h).2 hh
  let u : sigma.obj y ⟶ sigma.obj y :=
    𝟙 (sigma.obj y) - (sq ≫ k) ≫ h
  letI : IsIso (𝟙 M - h ≫ (sq ≫ k)) :=
    hhrad (sq ≫ k)
  haveI : IsIso u := by
    dsimp only [u]
    exact CategoricalRadical.isIso_one_sub_comp h (sq ≫ k)
  have hsqd : sq ≫ d = u := by
    dsimp only [d, u]
    rw [Preadditive.comp_sub, hqid, Category.assoc]
  letI : IsIso (sq ≫ d) := hsqd.symm ▸ inferInstance
  have hdsplit : IsSplitEpi d :=
    IsSplitEpi.mk'
      { section_ := inv (sq ≫ d) ≫ sq
        id := by
          rw [Category.assoc]
          simp }
  letI : IsSplitEpi d := hdsplit
  let sd : sigma.obj y ⟶ A.middle := section_ d
  let e : A.middle ⟶ A.middle := 𝟙 A.middle - d ≫ sd
  have hmape : A.map ≫ e = A.map := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      hmapd, zero_comp, sub_zero]
  letI : IsIso e := A.leftMinimal e hmape
  have hed : e ≫ d = 0 := by
    dsimp only [e, sd]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      IsSplitEpi.id, Category.comp_id, sub_self]
  have hd0 : d = 0 := by
    rw [← cancel_epi e]
    simp only [hed, comp_zero]
  have hcomp0 : section_ d ≫ d = section_ d ≫ 0 :=
    congrArg (fun f ↦ section_ d ≫ f) hd0
  have hid0 : (𝟙 (sigma.obj y) : sigma.obj y ⟶ sigma.obj y) = 0 := by
    calc
      𝟙 (sigma.obj y) = section_ d ≫ d := (IsSplitEpi.id d).symm
      _ = 0 := by simpa only [comp_zero] using hcomp0
  have hyzero : IsZero (sigma.obj y) :=
    IsZero.of_mono_eq_zero (𝟙 (sigma.obj y)) hid0
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have hyzero' : IsZero (U.obj (sigma.obj y)) := U.map_isZero hyzero
  have hsub : Subsingleton (sigma.obj y) :=
    ModuleCat.isZero_iff_subsingleton.mp hyzero'
  exact not_nontrivial_iff_subsingleton.mpr hsub
    (sigma.indecomposable y).nontrivial

omit [FiniteDimensional K R] in
theorem leftAROccurrenceToIrr_injective {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :
    Function.Injective
      (sigma.leftAROccurrenceToIrr (K := K) A y) := by
  intro c d hcd
  apply sub_eq_zero.mp
  apply sigma.leftAROccurrenceToIrr_eq_zero A y
  rw [map_sub, hcd, sub_self]

omit [FiniteDimensional K R] in
/-- The coordinate classes span `Irr` as soon as endomorphisms of the
target are scalar.  This is the left-minimal approximation half of the
standard occurrence--`Irr` basis theorem. -/
theorem leftAROccurrenceToIrr_surjective_of_scalar_endomorphisms
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (hscalar : ∀ f : sigma.obj y ⟶ sigma.obj y,
      ∃ a : K, a • 𝟙 (sigma.obj y) = f) :
    Function.Surjective (sigma.leftAROccurrenceToIrr (K := K) A y) := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  intro z
  obtain ⟨f, rfl⟩ :=
    (sigma.radicalSquareInRadicalSubmodule (K := K) x y).mkQ_surjective z
  let Fcat : sigma.obj x ⟶ sigma.obj y := ConcreteCategory.ofHom f.1
  have hFnonsplit : ¬ IsSplitMono Fcat :=
    (sigma.mem_radicalHom_iff_not_isSplitMono (K := K) f.1).1 f.2
  obtain ⟨h, hh⟩ := A.leftAlmostSplit.factors Fcat hFnonsplit
  let coeff (t : sigma.LeftAROccurrence A y) : K :=
    Classical.choose
      (hscalar (sigma.leftAROccurrenceMiddleInclusion A y t ≫ h))
  have coeff_spec (t : sigma.LeftAROccurrence A y) :
      coeff t • 𝟙 (sigma.obj y) =
        sigma.leftAROccurrenceMiddleInclusion A y t ≫ h :=
    Classical.choose_spec
      (hscalar (sigma.leftAROccurrenceMiddleInclusion A y t ≫ h))
  let q : A.middle ⟶ sigma.obj y :=
    sigma.leftAROccurrenceMiddleCombination A y coeff
  let r : A.middle ⟶ sigma.obj y := h - q
  let family : A.index → FGModuleCat.{u} R :=
    fun j ↦ sigma.obj (A.label j)
  let component (j : A.index) : family j ⟶ sigma.obj y :=
    biproduct.ι family j ≫ A.decomposition.inv ≫ r
  have hcomponent (j : A.index) : ¬ IsSplitEpi (component j) := by
    by_cases hj : A.label j = y
    · let t : sigma.LeftAROccurrence A y := ⟨j, hj⟩
      have hzero : component j = 0 := by
        have hinclr :
            sigma.leftAROccurrenceMiddleInclusion A y t ≫ r = 0 := by
          dsimp only [r]
          rw [Preadditive.comp_sub, ← coeff_spec t,
            sigma.leftAROccurrenceMiddleInclusion_combination
              A y coeff t,
            sub_self]
        rw [← cancel_epi (eqToHom (congrArg sigma.obj hj.symm))]
        simpa only [component, family, t,
          leftAROccurrenceMiddleInclusion, Category.assoc, comp_zero]
          using hinclr
      rw [hzero]
      intro hsplit
      letI : IsSplitEpi (0 : family j ⟶ sigma.obj y) := hsplit
      have hyzero : IsZero (sigma.obj y) :=
        (IsZero.iff_isSplitEpi_eq_zero
          (0 : family j ⟶ sigma.obj y)).2 rfl
      let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
      have hyzero' : IsZero (U.obj (sigma.obj y)) := U.map_isZero hyzero
      have hsub : Subsingleton (sigma.obj y) :=
        ModuleCat.isZero_iff_subsingleton.mp hyzero'
      exact not_nontrivial_iff_subsingleton.mpr hsub
        (sigma.indecomposable y).nontrivial
    · intro hsplit
      letI : IsSplitEpi (component j) := hsplit
      letI : IsSplitMono (component j) :=
        sigma.isSplitMono_of_isSplitEpi_between_obj (component j)
      letI : IsIso (component j) :=
        isIso_of_mono_of_isSplitEpi (component j)
      exact hj (sigma.eq_of_iso ⟨asIso (component j)⟩)
  have hrnonsplit : ¬ IsSplitEpi r := by
    have hdesc : biproduct.desc component = A.decomposition.inv ≫ r := by
      apply biproduct.hom_ext'
      intro j
      rw [biproduct.ι_desc]
    have hnonsplitDesc : ¬ IsSplitEpi (biproduct.desc component) :=
      sigma.biproductDesc_not_isSplitEpi family component hcomponent
    intro hrsplit
    letI : IsSplitEpi r := hrsplit
    apply hnonsplitDesc
    rw [hdesc]
    infer_instance
  refine ⟨coeff, ?_⟩
  apply (Submodule.Quotient.eq
    (sigma.radicalSquareInRadicalSubmodule (K := K) x y)).2
  have hmapq : A.map ≫ q =
      ConcreteCategory.ofHom
        (sigma.leftAROccurrenceCombination A y coeff) :=
    sigma.leftAROccurrenceCombination_eq_comp A y coeff
  have hsquare :
      (f - (sigma.leftAROccurrenceToRadical A y coeff)) ∈
        sigma.radicalSquareInRadicalSubmodule (K := K) x y := by
    change sigma.HasRadicalSquareFactorization
      (ConcreteCategory.ofHom
        (f.1 - sigma.leftAROccurrenceCombination A y coeff))
    refine ⟨A.middle, A.map, r,
      A.leftAlmostSplit.not_isSplitMono, hrnonsplit, ?_⟩
    apply FGModuleCat.hom_ext
    change (A.map ≫ r).hom.hom =
      f.1 - sigma.leftAROccurrenceCombination A y coeff
    have hmapr : A.map ≫ r =
        Fcat - ConcreteCategory.ofHom
          (sigma.leftAROccurrenceCombination A y coeff) := by
      dsimp only [r, q]
      rw [Preadditive.comp_sub, hh, hmapq]
    rw [hmapr]
    rfl
  have hneg :=
    (sigma.radicalSquareInRadicalSubmodule (K := K) x y).neg_mem hsquare
  simpa [sub_eq_add_neg, add_comm] using hneg

/-- The general left-side occurrence--`Irr` equivalence, assuming only the
scalar-endomorphism conclusion needed for spanning. -/
def leftAROccurrenceLinearEquivOfScalarEndomorphisms
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (hscalar : ∀ f : sigma.obj y ⟶ sigma.obj y,
      ∃ a : K, a • 𝟙 (sigma.obj y) = f) :
    (sigma.LeftAROccurrence A y → K) ≃ₗ[K]
      sigma.irreducibleHomSpace (K := K) x y :=
  LinearEquiv.ofBijective
    (sigma.leftAROccurrenceToIrr (K := K) A y)
    ⟨sigma.leftAROccurrenceToIrr_injective (K := K) A y,
      sigma.leftAROccurrenceToIrr_surjective_of_scalar_endomorphisms
        A y hscalar⟩

omit [FiniteDimensional K R] in
theorem finrank_irreducibleHomSpace_eq_card_leftAROccurrence
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (hscalar : ∀ f : sigma.obj y ⟶ sigma.obj y,
      ∃ a : K, a • 𝟙 (sigma.obj y) = f) :
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x y) =
      Nat.card (sigma.LeftAROccurrence A y) := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  rw [← (sigma.leftAROccurrenceLinearEquivOfScalarEndomorphisms
    A y hscalar).finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

end MBDVendor.QSE.IndecomposableSkeleton
