import MBDVendor.QSE.RepresentationTheory.RightAROccurrenceBasis
import MBDVendor.QSE.RepresentationTheory.LeftAROccurrenceBasis
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Occurrence bases over an algebraically closed field

For an indecomposable finite-dimensional module over an algebraically closed
field, every endomorphism is scalar modulo the categorical radical.  This is
the precise form of Schur's lemma needed to identify repeated summands in an
almost-split middle term with the dimension of the corresponding irreducible
morphism space; the endomorphism itself need not be scalar.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {Iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

local instance restrictedModule (i : Iota) : Module K (sigma.obj i) :=
  Module.restrictScalars K R (sigma.obj i)

local instance restrictedScalarTower (i : Iota) :
    IsScalarTower K R (sigma.obj i) :=
  IsScalarTower.restrictScalars K R (sigma.obj i)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

attribute [local instance]
  FintypeCat.fintype

/-- Over an algebraically closed field, an endomorphism of an indecomposable
finite-dimensional module differs from a scalar by a radical endomorphism. -/
theorem exists_scalar_sub_mem_radicalHom (x : Iota)
    (f : sigma.obj x ⟶ sigma.obj x) :
    ∃ a : K,
      f.hom.hom - a • LinearMap.id ∈
        sigma.radicalHom (K := K) x x := by
  letI : FiniteDimensional K (sigma.obj x) :=
    Module.Finite.trans R (sigma.obj x)
  letI : Nontrivial (sigma.obj x) :=
    (sigma.indecomposable x).nontrivial
  let fK : Module.End K (sigma.obj x) :=
    f.hom.hom.restrictScalars K
  obtain ⟨a, ha⟩ := fK.exists_eigenvalue
  obtain ⟨w, hw⟩ := ha.exists_hasEigenvector
  refine ⟨a, (sigma.mem_radicalHom_iff_not_isSplitMono
    (K := K) (f.hom.hom - a • LinearMap.id)).2 ?_⟩
  intro hsplit
  let d : sigma.obj x ⟶ sigma.obj x :=
    ConcreteCategory.ofHom (f.hom.hom - a • LinearMap.id)
  letI : IsSplitMono d := hsplit
  have hdw : d.hom.hom w = 0 := by
    change f.hom.hom w - a • w = 0
    exact sub_eq_zero.mpr hw.apply_eq_smul
  have hcat : d ≫ retraction d = 𝟙 (sigma.obj x) :=
    IsSplitMono.id d
  have hlin := congrArg
    (fun q : sigma.obj x ⟶ sigma.obj x ↦ q.hom.hom) hcat
  have hwzero : w = 0 := by
    have hwlin := LinearMap.congr_fun hlin w
    change (retraction d).hom.hom (d.hom.hom w) = w at hwlin
    rw [hdw, map_zero] at hwlin
    exact hwlin.symm
  exact hw.2 hwzero

omit [IsAlgClosed K] [FiniteDimensional K R] in
private theorem hom_hom_sub_smul_id (x : Iota)
    (f : sigma.obj x ⟶ sigma.obj x) (a : K) :
    (f - a • 𝟙 (sigma.obj x)).hom.hom =
      f.hom.hom - a • LinearMap.id := by
  have hsubhom :
      (f - a • 𝟙 (sigma.obj x)).hom =
        f.hom - (a • 𝟙 (sigma.obj x)).hom := by
    have h := map_sub
      (CategoryTheory.InducedCategory.homLinearEquiv (R := K))
      f (a • 𝟙 (sigma.obj x))
    change (f - a • 𝟙 (sigma.obj x)).hom =
      f.hom - (a • 𝟙 (sigma.obj x)).hom at h
    exact h
  have hsmulhom :
      (a • 𝟙 (sigma.obj x)).hom =
        a • (𝟙 (sigma.obj x) : sigma.obj x ⟶ sigma.obj x).hom := by
    have h := map_smul
      (CategoryTheory.InducedCategory.homLinearEquiv (R := K))
      a (𝟙 (sigma.obj x) : sigma.obj x ⟶ sigma.obj x)
    change (a • 𝟙 (sigma.obj x)).hom =
      a • (𝟙 (sigma.obj x) : sigma.obj x ⟶ sigma.obj x).hom at h
    exact h
  rw [hsubhom, ModuleCat.hom_sub, hsmulhom, ModuleCat.hom_smul,
    CategoryTheory.ObjectProperty.FullSubcategory.id_hom,
    ModuleCat.hom_id]

/-- Over an algebraically closed field, an endomorphism of a chosen
indecomposable differs from a scalar identity by a categorical-radical
morphism. -/
theorem exists_scalar_sub_isRadicalMorphism (x : Iota)
    (f : sigma.obj x ⟶ sigma.obj x) :
    ∃ a : K, CategoricalRadical.IsRadicalMorphism
      (f - a • 𝟙 (sigma.obj x)) := by
  obtain ⟨a, ha⟩ := sigma.exists_scalar_sub_mem_radicalHom (K := K) x f
  refine ⟨a, (sigma.isRadicalMorphism_iff_not_isSplitEpi_to_obj _).2 ?_⟩
  have hmem : (f - a • 𝟙 (sigma.obj x)).hom.hom ∈
      sigma.radicalHom (K := K) x x := by
    rw [hom_hom_sub_smul_id]
    exact ha
  have hnot :=
    (sigma.mem_radicalHom_iff_not_isSplitEpi
      ((f - a • 𝟙 (sigma.obj x)).hom.hom)).1 hmem
  change ¬ IsSplitEpi
    (show sigma.obj x ⟶ sigma.obj x from
      ConcreteCategory.ofHom
        ((f - a • 𝟙 (sigma.obj x)).hom.hom)) at hnot
  simpa using hnot

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- The right almost-split occurrence coordinates span `Irr` when source
endomorphisms are scalar modulo the radical. -/
theorem rightAROccurrenceToIrr_surjective_of_scalar_mod_radical
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota)
    (hscalar : ∀ f : sigma.obj x ⟶ sigma.obj x,
      ∃ a : K, f.hom.hom - a • LinearMap.id ∈
        sigma.radicalHom (K := K) x x) :
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
      (h ≫ sigma.rightAROccurrenceMiddleProjection A x t).hom.hom -
          coeff t • LinearMap.id ∈
        sigma.radicalHom (K := K) x x :=
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
      have hrproj :
          (r ≫ sigma.rightAROccurrenceMiddleProjection A x t).hom.hom ∈
            sigma.radicalHom (K := K) x x := by
        have hsub : r ≫ sigma.rightAROccurrenceMiddleProjection A x t =
            h ≫ sigma.rightAROccurrenceMiddleProjection A x t -
              coeff t • 𝟙 (sigma.obj x) := by
          dsimp only [r, q]
          rw [Preadditive.sub_comp,
            sigma.rightAROccurrenceMiddleCombination_projection
              A x coeff t]
        rw [hsub]
        rw [sigma.hom_hom_sub_smul_id (K := K)]
        exact coeff_spec t
      intro hsplit
      letI : IsSplitMono (component j) := hsplit
      have hcomp :
          component j ≫ eqToHom (congrArg sigma.obj hj) =
            r ≫ sigma.rightAROccurrenceMiddleProjection A x t := by
        simp only [component, family, t,
          rightAROccurrenceMiddleProjection, Category.assoc]
      have hscomp : IsSplitMono
          (component j ≫ eqToHom (congrArg sigma.obj hj)) := by
        infer_instance
      have hsproj : IsSplitMono
          (r ≫ sigma.rightAROccurrenceMiddleProjection A x t) :=
        hcomp ▸ hscomp
      exact (sigma.mem_radicalHom_iff_not_isSplitMono
        (K := K)
        (r ≫ sigma.rightAROccurrenceMiddleProjection A x t).hom.hom).1
          hrproj hsproj
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

/-- Over an algebraically closed field, right almost-split occurrences form
a basis of the corresponding irreducible-morphism space. -/
def rightAROccurrenceLinearEquivOfIsAlgClosed
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :
    (sigma.RightAROccurrence A x → K) ≃ₗ[K]
      sigma.irreducibleHomSpace (K := K) x z :=
  LinearEquiv.ofBijective
    (sigma.rightAROccurrenceToIrr (K := K) A x)
    ⟨sigma.rightAROccurrenceToIrr_injective (K := K) A x,
      sigma.rightAROccurrenceToIrr_surjective_of_scalar_mod_radical
        A x (sigma.exists_scalar_sub_mem_radicalHom (K := K) x)⟩

/-- The dimension of `Irr(x,z)` is the number of occurrences of `x` in a
minimal right almost-split middle term over an algebraically closed field. -/
theorem finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
    {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) (x : Iota) :
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x z) =
      Nat.card (sigma.RightAROccurrence A x) := by
  classical
  letI : Fintype (sigma.RightAROccurrence A x) :=
    Fintype.ofFinite (sigma.RightAROccurrence A x)
  rw [← (sigma.rightAROccurrenceLinearEquivOfIsAlgClosed A x).finrank_eq,
    Module.finrank_pi, Nat.card_eq_fintype_card]

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- The left almost-split occurrence coordinates span `Irr` when target
endomorphisms are scalar modulo the radical. -/
theorem leftAROccurrenceToIrr_surjective_of_scalar_mod_radical
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota)
    (hscalar : ∀ f : sigma.obj y ⟶ sigma.obj y,
      ∃ a : K, f.hom.hom - a • LinearMap.id ∈
        sigma.radicalHom (K := K) y y) :
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
      (sigma.leftAROccurrenceMiddleInclusion A y t ≫ h).hom.hom -
          coeff t • LinearMap.id ∈
        sigma.radicalHom (K := K) y y :=
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
      have hinclr :
          (sigma.leftAROccurrenceMiddleInclusion A y t ≫ r).hom.hom ∈
            sigma.radicalHom (K := K) y y := by
        have hsub :
            sigma.leftAROccurrenceMiddleInclusion A y t ≫ r =
              sigma.leftAROccurrenceMiddleInclusion A y t ≫ h -
                coeff t • 𝟙 (sigma.obj y) := by
          dsimp only [r, q]
          rw [Preadditive.comp_sub,
            sigma.leftAROccurrenceMiddleInclusion_combination
              A y coeff t]
        rw [hsub, sigma.hom_hom_sub_smul_id (K := K)]
        exact coeff_spec t
      intro hsplit
      letI : IsSplitEpi (component j) := hsplit
      have hcomp :
          eqToHom (congrArg sigma.obj hj.symm) ≫ component j =
            sigma.leftAROccurrenceMiddleInclusion A y t ≫ r := by
        simp only [component, family, t,
          leftAROccurrenceMiddleInclusion, Category.assoc]
      have hsecomp : IsSplitEpi
          (eqToHom (congrArg sigma.obj hj.symm) ≫ component j) := by
        infer_instance
      have hseproj : IsSplitEpi
          (sigma.leftAROccurrenceMiddleInclusion A y t ≫ r) :=
        hcomp ▸ hsecomp
      exact (sigma.mem_radicalHom_iff_not_isSplitEpi
        (K := K)
        (sigma.leftAROccurrenceMiddleInclusion A y t ≫ r).hom.hom).1
          hinclr hseproj
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

/-- Over an algebraically closed field, left almost-split occurrences form
a basis of the corresponding irreducible-morphism space. -/
def leftAROccurrenceLinearEquivOfIsAlgClosed
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :
    (sigma.LeftAROccurrence A y → K) ≃ₗ[K]
      sigma.irreducibleHomSpace (K := K) x y :=
  LinearEquiv.ofBijective
    (sigma.leftAROccurrenceToIrr (K := K) A y)
    ⟨sigma.leftAROccurrenceToIrr_injective (K := K) A y,
      sigma.leftAROccurrenceToIrr_surjective_of_scalar_mod_radical
        A y (sigma.exists_scalar_sub_mem_radicalHom (K := K) y)⟩

/-- The dimension of `Irr(x,y)` is the number of occurrences of `y` in a
minimal left almost-split middle term over an algebraically closed field. -/
theorem finrank_irreducibleHomSpace_eq_card_leftAROccurrence_of_isAlgClosed
    {x : Iota}
    (A : sigma.MinimalLeftAlmostSplitDecomposition x) (y : Iota) :
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x y) =
      Nat.card (sigma.LeftAROccurrence A y) := by
  classical
  letI : Fintype (sigma.LeftAROccurrence A y) :=
    Fintype.ofFinite (sigma.LeftAROccurrence A y)
  rw [← (sigma.leftAROccurrenceLinearEquivOfIsAlgClosed A y).finrank_eq,
    Module.finrank_pi, Nat.card_eq_fintype_card]

end MBDVendor.QSE.IndecomposableSkeleton
