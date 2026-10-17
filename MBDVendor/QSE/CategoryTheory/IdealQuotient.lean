import Mathlib.CategoryTheory.Quotient.Preadditive
import MBDVendor.QSE.CategoryTheory.CategoricalRadical
import MBDVendor.QSE.CategoryTheory.HomIdeal

/-!
# Ideal quotients of preadditive categories

Mathlib supplies quotients by a categorical congruence. This file packages
a two-sided additive Hom ideal as such a congruence, equips the quotient with
its induced preadditive structure, and proves that the quotient functor kills
exactly the ideal.
-/

noncomputable section

open CategoryTheory

namespace MBDVendor.QSE.CategoricalIdeal

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

namespace HomIdeal

variable {C} (I : HomIdeal C)

/-- Congruence modulo the given Hom ideal. -/
def rel : HomRel C :=
  fun {X Y} f g ↦ f - g ∈ I.hom X Y

instance : Congruence I.rel where
  equivalence := {
    refl := fun f ↦ by simp [rel]
    symm := by
      intro f g h
      have h' := (I.hom _ _).neg_mem h
      simpa [rel, neg_sub] using h'
    trans := by
      intro f g h hfg hgh
      have h' := (I.hom _ _).add_mem hfg hgh
      simpa [rel] using h' }
  comp_left := by
    intro X Y Z f g g' h
    simpa [rel] using I.precomp f h
  comp_right := by
    intro X Y Z f f' g h
    simpa [rel] using I.postcomp g h

theorem add_compatible
    {X Y : C} (f₁ f₂ g₁ g₂ : X ⟶ Y)
    (hf : I.rel f₁ f₂) (hg : I.rel g₁ g₂) :
    I.rel (f₁ + g₁) (f₂ + g₂) := by
  have h := (I.hom X Y).add_mem hf hg
  change (f₁ + g₁) - (f₂ + g₂) ∈ I.hom X Y
  convert h using 1
  all_goals abel

/-- The induced preadditive structure on the category quotient. -/
abbrev quotientPreadditive :
    Preadditive (CategoryTheory.Quotient I.rel) :=
  CategoryTheory.Quotient.preadditive I.rel
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
      I.add_compatible f₁ f₂ g₁ g₂ hf hg)

/-- The quotient functor kills exactly the given Hom ideal. -/
theorem map_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    (CategoryTheory.Quotient.functor I.rel).map f = 0 ↔
      f ∈ I.hom X Y := by
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  rw [← (CategoryTheory.Quotient.functor I.rel).map_zero X Y,
    CategoryTheory.Quotient.functor_map_eq_iff]
  simp [rel]

/-- The quotient functor sends categorical radical morphisms to
categorical radical morphisms. -/
theorem map_isRadicalMorphism
    {X Y : C} (f : X ⟶ Y)
    (hf : CategoricalRadical.IsRadicalMorphism f) :
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    CategoricalRadical.IsRadicalMorphism
      ((CategoryTheory.Quotient.functor I.rel).map f) := by
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  intro g
  obtain ⟨g', rfl⟩ :=
    (CategoryTheory.Quotient.functor I.rel).map_surjective g
  haveI : IsIso (𝟙 X - f ≫ g') := hf g'
  rw [← (CategoryTheory.Quotient.functor I.rel).map_id,
    ← (CategoryTheory.Quotient.functor I.rel).map_comp,
    ← (CategoryTheory.Quotient.functor I.rel).map_sub]
  infer_instance

/-- If the quotient has zero categorical radical, every radical morphism
upstairs belongs to the defining Hom ideal. -/
theorem mem_of_isRadicalMorphism_of_quotient_hasZeroRadical
    {X Y : C} (f : X ⟶ Y)
    (hzero :
      letI : Preadditive (CategoryTheory.Quotient I.rel) :=
        I.quotientPreadditive
      CategoricalRadical.HasZeroRadical
        (CategoryTheory.Quotient I.rel))
    (hf : CategoricalRadical.IsRadicalMorphism f) :
    f ∈ I.hom X Y := by
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  apply (I.map_eq_zero_iff f).1
  exact hzero _
    (I.map_isRadicalMorphism f hf)

end HomIdeal

end MBDVendor.QSE.CategoricalIdeal
