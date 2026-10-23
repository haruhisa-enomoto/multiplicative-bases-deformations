module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Basic
public import MBDVendor.Magnitude.CategoryTheory.RadicalMinimality
public import MBDVendor.QSE.CategoryTheory.SplitMorphismComplement

/-!
# Finite Krull--Schmidt matrices

An endomorphism of a finite biproduct of pairwise nonisomorphic
indecomposables with local endomorphism rings is invertible as soon as every
diagonal component is invertible.  This is the finite-support matrix lemma in
the Krull--Schmidt--Warfield argument used by Gabriel's Lemma 3.5.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.Magnitude.CategoryTheory

open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable [IsIdempotentComplete C]

omit [HasFiniteBiproducts C] in
/-- A split subobject of an indecomposable object is the whole object when
its source is nonzero. -/
theorem isIso_of_isSplitMono_to_indecomposable
    {X Y : C} (hY : Indecomposable Y)
    (j : X ⟶ Y) [IsSplitMono j] (hX : ¬ IsZero X) :
    IsIso j := by
  let d := splitMonoComplement j
  let e : Y ≅ X ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hcomp : IsZero d.complement :=
    (hY.2 X d.complement e).resolve_left hX
  apply IsIso.mk
  refine ⟨retraction j, IsSplitMono.id j, ?_⟩
  rw [← d.total]
  have hp : d.projection = 0 := hcomp.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hcomp.eq_of_src _ _
  rw [hp, hi, zero_comp, add_zero]

omit [HasFiniteBiproducts C] in
/-- A split quotient of an indecomposable object is the whole object when
its target is nonzero. -/
theorem isIso_of_isSplitEpi_from_indecomposable
    {X Y : C} (hX : Indecomposable X)
    (p : X ⟶ Y) [IsSplitEpi p] (hY : ¬ IsZero Y) :
    IsIso p := by
  let d := splitEpiComplement p
  let e : X ≅ d.complement ⊞ Y :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hcomp : IsZero d.complement :=
    (hX.2 d.complement Y e).resolve_right hY
  apply IsIso.mk
  refine ⟨section_ p, ?_, IsSplitEpi.id p⟩
  rw [← d.total]
  have hp : d.projection = 0 := hcomp.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hcomp.eq_of_src _ _
  rw [hp, hi, zero_comp, zero_add]

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- A unit for the preadditive-ring structure on an endomorphism is a
categorical isomorphism.  This bridges Mathlib's two monoid instances on
categorical endomorphisms. -/
theorem isIso_of_isUnit_preadditiveEnd
    {X : C} (f : X ⟶ X)
    (hf : @IsUnit (End X) Preadditive.instSemiringEnd.toMonoid
      (End.of f)) : IsIso f := by
  obtain ⟨u, hu⟩ := hf
  have huHom : End.asHom (u : End X) = f := hu
  have huInv :
      End.asHom (u : End X) ≫ End.asHom u.inv = 𝟙 X := by
    exact congrArg End.asHom <| by
      simpa only [End.mul_def, End.one_def] using u.inv_val
  have hInvu :
      End.asHom u.inv ≫ End.asHom (u : End X) = 𝟙 X := by
    exact congrArg End.asHom <| by
      simpa only [End.mul_def, End.one_def] using u.val_inv
  apply IsIso.mk
  refine ⟨End.asHom u.inv, ?_, ?_⟩
  · rw [← huHom]
    exact huInv
  · rw [← huHom]
    exact hInvu

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- In a local categorical endomorphism ring, one of two endomorphisms whose
sum is the identity is an isomorphism. -/
theorem isIso_or_isIso_of_add_eq_id
    {X : C} [IsLocalRing (End X)] (f g : X ⟶ X)
    (hfg : f + g = 𝟙 X) : IsIso f ∨ IsIso g := by
  have hunit : IsUnit (End.of f + End.of g) := by
    have hfg' : End.of f + End.of g = (1 : End X) := hfg
    rw [hfg']
    exact isUnit_one
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit).imp
    (isIso_of_isUnit_preadditiveEnd f)
    (isIso_of_isUnit_preadditiveEnd g)

omit [HasFiniteBiproducts C] in
/-- Every morphism between nonisomorphic indecomposables is radical when the
source has local endomorphism ring. -/
theorem isRadicalMorphism_of_indecomposable_of_not_iso
    {X Y : C} (hX : Indecomposable X) (hY : Indecomposable Y)
    [IsLocalRing (End X)] (hXY : ¬ Nonempty (X ≅ Y))
    (f : X ⟶ Y) : IsRadicalMorphism f := by
  intro g
  have hnunit : ¬ IsUnit (End.of (f ≫ g)) := by
    intro hunit
    haveI hfg : IsIso (f ≫ g) :=
      (isUnit_iff_isIso (f ≫ g)).mp hunit
    haveI hfSplit : IsSplitMono f := by
      apply IsSplitMono.mk'
      exact
        { retraction := g ≫ inv (f ≫ g)
          id := by
            rw [← Category.assoc, IsIso.hom_inv_id] }
    haveI hfIso : IsIso f :=
      isIso_of_isSplitMono_to_indecomposable hY f hX.1
    exact hXY ⟨asIso f⟩
  have hone : IsUnit
      ((1 - End.of (f ≫ g)) + End.of (f ≫ g)) := by
    simpa using (isUnit_one : IsUnit (1 : End X))
  have hunit : IsUnit (1 - End.of (f ≫ g)) :=
    (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hone).resolve_right hnunit
  exact isIso_of_isUnit_preadditiveEnd _ hunit

/-- A finite Krull--Schmidt matrix is invertible whenever all its diagonal
entries are invertible. -/
theorem isIso_of_finBiproduct_diagonal_isIso
    {J : Type w} [Fintype J]
    (X : J → C)
    (hX : ∀ i, Indecomposable (X i))
    (hlocal : ∀ i, IsLocalRing (End (X i)))
    (hpair : ∀ i j, i ≠ j → ¬ Nonempty (X i ≅ X j))
    (f : (⨁ X) ⟶ (⨁ X))
    (hdiag : ∀ i, IsIso
      (biproduct.ι X i ≫ f ≫ biproduct.π X i)) :
    IsIso f := by
  classical
  letI localEnd (i : J) : IsLocalRing (End (X i)) := hlocal i
  letI diagonalIso (i : J) : IsIso
      (biproduct.ι X i ≫ f ≫ biproduct.π X i) := hdiag i
  let d : (⨁ X) ≅ (⨁ X) :=
    biproduct.mapIso fun i ↦
      asIso (biproduct.ι X i ≫ f ≫ biproduct.π X i)
  let r : (⨁ X) ⟶ (⨁ X) := d.hom - f
  have hmatrix :
      r = ∑ i : J, ∑ j : J,
        biproduct.π X i ≫
          (biproduct.ι X i ≫ r ≫ biproduct.π X j) ≫
          biproduct.ι X j := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hlj
        simp [hlj]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro l _ hli
      simp [Ne.symm hli]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hcomponent (i j : J) :
      IsRadicalMorphism
        (biproduct.ι X i ≫ r ≫ biproduct.π X j) := by
    by_cases hij : i = j
    · subst j
      have hz :
          biproduct.ι X i ≫ r ≫ biproduct.π X i = 0 := by
        simp [r, d]
      rw [hz]
      exact isRadicalMorphism_zero
    · have hc :
          biproduct.ι X i ≫ r ≫ biproduct.π X j =
            -(biproduct.ι X i ≫ f ≫ biproduct.π X j) := by
        simp [r, d, hij]
      rw [hc]
      apply isRadicalMorphism_neg
      exact isRadicalMorphism_of_indecomposable_of_not_iso
        (hX i) (hX j) (hpair i j hij)
          (biproduct.ι X i ≫ f ≫ biproduct.π X j)
  have hr : IsRadicalMorphism r := by
    rw [hmatrix]
    apply isRadicalMorphism_finset_sum
    intro i hi
    apply isRadicalMorphism_finset_sum
    intro j hj
    simpa only [Category.assoc] using
      isRadicalMorphism_postcomp (biproduct.ι X j)
        (isRadicalMorphism_precomp (biproduct.π X i)
          (hcomponent i j))
  haveI hnormalized : IsIso (𝟙 (⨁ X) - r ≫ d.inv) := hr d.inv
  have hfactor :
      (𝟙 (⨁ X) - r ≫ d.inv) ≫ d.hom = f := by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inv_hom_id, Category.comp_id]
    dsimp only [r]
    abel
  rw [← hfactor]
  infer_instance

end MBDVendor.Magnitude.CategoryTheory
