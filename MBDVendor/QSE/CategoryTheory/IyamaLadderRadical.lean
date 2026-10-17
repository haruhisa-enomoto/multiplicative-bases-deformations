import MBDVendor.QSE.CategoryTheory.FiniteTauCategory

/-!
# Radical and nonmonicity foundations for Iyama ladders

This file supplies the elementwise starting point of Iyama's ladder
extraction.  Failure of monicity gives a literal nonzero left annihilator;
nilpotence lets that annihilator escape some radical power; and, on a chosen
indecomposable with local endomorphism ring, categorical-radical membership
is equivalent to failure of split monicity.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

open CategoricalRadical

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- In a preadditive category, failure of monicity has a literal nonzero
left annihilator. -/
theorem exists_nonzero_comp_eq_zero_of_not_mono
    {X Y : C} {f : X ⟶ Y} (hf : ¬ Mono f) :
    ∃ (W : C) (s : W ⟶ X), s ≠ 0 ∧ s ≫ f = 0 := by
  rw [Preadditive.mono_iff_cancel_zero] at hf
  push Not at hf
  obtain ⟨W, s, hs, hs0⟩ := hf
  exact ⟨W, s, hs0, hs⟩

/-- A nonzero morphism escapes some power of a nilpotent categorical
radical. -/
theorem exists_power_not_mem_of_ne_zero
    (R : NilpotentRadicalData C)
    {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) :
    ∃ n : ℕ, f ∉ (R.ideal.pow n).hom X Y := by
  by_contra h
  push Not at h
  exact hf (R.eq_zero_of_mem_every_power h)

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- For a chosen indecomposable with local endomorphism ring, the intrinsic
categorical radical consists exactly of the morphisms which are not split
monomorphisms.  No module-category realization is used. -/
theorem FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
    (T : FiniteRightTauCategoryData C Ind)
    {x : Ind} {Y : C} (f : T.obj x ⟶ Y) :
    IsRadicalMorphism f ↔ ¬ IsSplitMono f := by
  constructor
  · intro hf hsplit
    letI : IsSplitMono f := hsplit
    let r : Y ⟶ T.obj x := retraction f
    have hr : f ≫ r = 𝟙 (T.obj x) := IsSplitMono.id f
    have hi : IsIso (𝟙 (T.obj x) - f ≫ r) := hf r
    have hzero : 𝟙 (T.obj x) - f ≫ r = 0 := by
      rw [hr, sub_self]
    haveI : IsIso (0 : T.obj x ⟶ T.obj x) := hzero ▸ hi
    have hx : IsZero (T.obj x) :=
      (IsZero.iff_isSplitEpi_eq_zero
        (0 : T.obj x ⟶ T.obj x)).2 rfl
    exact (T.obj_indec x).1 hx
  · intro hf r
    let a : End (T.obj x) := f ≫ r
    have ha : ¬ IsUnit a := by
      intro hu
      haveI : IsIso (f ≫ r) :=
        (isUnit_iff_isIso (f ≫ r)).1 hu
      apply hf
      exact IsSplitMono.mk'
        { retraction := r ≫ inv (f ≫ r)
          id := by rw [← Category.assoc]; simp }
    letI : IsLocalRing (End (T.obj x)) := T.obj_end_local x
    have hsum : IsUnit (a + (1 - a)) := by
      rw [add_sub_cancel]
      exact isUnit_one
    have hu : IsUnit (1 - a) :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left ha
    exact (isUnit_iff_isIso (𝟙 (T.obj x) - f ≫ r)).1 hu

/-- Dually, a morphism into a chosen indecomposable is radical exactly when
it is not a split epimorphism.  This uses only the finite Krull--Schmidt
skeleton, not any chosen left tau-sequences. -/
theorem FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
    (T : FiniteRightTauCategoryData C Ind)
    {x : Ind} {M : C} (f : M ⟶ T.obj x) :
    IsRadicalMorphism f ↔ ¬ IsSplitEpi f := by
  constructor
  · intro hf hsplit
    letI : IsSplitEpi f := hsplit
    have hidRad : IsRadicalMorphism (𝟙 (T.obj x)) := by
      simpa using isRadicalMorphism_precomp (section_ f) hf
    have hzeroIso : IsIso (0 : T.obj x ⟶ T.obj x) := by
      have hi := hidRad (𝟙 (T.obj x))
      simpa using hi
    letI : IsIso (0 : T.obj x ⟶ T.obj x) := hzeroIso
    have hx : IsZero (T.obj x) :=
      (IsZero.iff_isSplitEpi_eq_zero
        (0 : T.obj x ⟶ T.obj x)).2 rfl
    exact (T.obj_indec x).1 hx
  · intro hf g
    let a : End (T.obj x) := g ≫ f
    have ha : ¬ IsUnit a := by
      intro hu
      haveI : IsIso (g ≫ f) :=
        (isUnit_iff_isIso (g ≫ f)).1 hu
      apply hf
      exact IsSplitEpi.mk'
        { section_ := inv (g ≫ f) ≫ g
          id := by rw [Category.assoc]; simp }
    letI : IsLocalRing (End (T.obj x)) := T.obj_end_local x
    have hsum : IsUnit (a + (1 - a)) := by
      rw [add_sub_cancel]
      exact isUnit_one
    have hu : IsUnit (1 - a) :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left ha
    haveI : IsIso (𝟙 (T.obj x) - g ≫ f) :=
      (isUnit_iff_isIso (𝟙 (T.obj x) - g ≫ f)).1 hu
    exact isIso_one_sub_comp g f

end MBDVendor.QSE.Iyama
