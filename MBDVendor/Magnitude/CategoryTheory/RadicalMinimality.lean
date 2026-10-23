module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import MBDVendor.QSE.CategoryTheory.CategoricalRadicalIdeal
public import MBDVendor.QSE.CategoryTheory.MinimalMorphism

/-!
# Radical morphisms and minimal projective presentations

This file records the generic radical calculus needed to recognize a minimal
projective presentation after applying an exact additive functor.  It also
packages the componentwise criterion for radical maps between finite
biproducts.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical

namespace MBDVendor.Magnitude.CategoryTheory

universe u v w uD vD

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

/-- A morphism with nonzero local source is radical exactly when it is not
split monic. -/
theorem isRadicalMorphism_iff_not_isSplitMono_of_local_end
    {X Y : C} [IsLocalRing (End X)] (hX : ¬ IsZero X)
    (f : X ⟶ Y) :
    IsRadicalMorphism f ↔ ¬ IsSplitMono f := by
  constructor
  · intro hf hsplit
    letI : IsSplitMono f := hsplit
    let r : Y ⟶ X := retraction f
    have hr : f ≫ r = 𝟙 X := IsSplitMono.id f
    have hi : IsIso (𝟙 X - f ≫ r) := hf r
    have hzero : 𝟙 X - f ≫ r = 0 := by
      rw [hr, sub_self]
    haveI : IsIso (0 : X ⟶ X) := hzero ▸ hi
    exact hX ((IsZero.iff_isSplitEpi_eq_zero (0 : X ⟶ X)).2 rfl)
  · intro hf r
    let a : End X := f ≫ r
    have ha : ¬ IsUnit a := by
      intro hu
      haveI : IsIso (f ≫ r) :=
        (isUnit_iff_isIso (f ≫ r)).1 hu
      apply hf
      exact IsSplitMono.mk'
        { retraction := r ≫ inv (f ≫ r)
          id := by rw [← Category.assoc]; simp }
    have hsum : IsUnit (a + (1 - a)) := by
      rw [add_sub_cancel]
      exact isUnit_one
    have hu : IsUnit (1 - a) :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left ha
    exact (isUnit_iff_isIso (𝟙 X - f ≫ r)).1 hu

/-- A morphism into a nonzero object with local endomorphism ring is radical
exactly when it is not split epic. -/
theorem isRadicalMorphism_iff_not_isSplitEpi_of_local_end
    {X Y : C} [IsLocalRing (End Y)] (hY : ¬ IsZero Y)
    (f : X ⟶ Y) :
    IsRadicalMorphism f ↔ ¬ IsSplitEpi f := by
  constructor
  · intro hf hsplit
    letI : IsSplitEpi f := hsplit
    have hidRad : IsRadicalMorphism (𝟙 Y) := by
      simpa using isRadicalMorphism_precomp (section_ f) hf
    have hzeroIso : IsIso (0 : Y ⟶ Y) := by
      have hi := hidRad (𝟙 Y)
      simpa using hi
    letI : IsIso (0 : Y ⟶ Y) := hzeroIso
    exact hY ((IsZero.iff_isSplitEpi_eq_zero (0 : Y ⟶ Y)).2 rfl)
  · intro hf g
    let a : End Y := g ≫ f
    have ha : ¬ IsUnit a := by
      intro hu
      haveI : IsIso (g ≫ f) :=
        (isUnit_iff_isIso (g ≫ f)).1 hu
      apply hf
      exact IsSplitEpi.mk'
        { section_ := inv (g ≫ f) ≫ g
          id := by rw [Category.assoc]; simp }
    have hsum : IsUnit (a + (1 - a)) := by
      rw [add_sub_cancel]
      exact isUnit_one
    have hu : IsUnit (1 - a) :=
      (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left ha
    haveI : IsIso (𝟙 Y - g ≫ f) :=
      (isUnit_iff_isIso (𝟙 Y - g ≫ f)).1 hu
    exact isIso_one_sub_comp g f

/-- A radical morphism with nonzero source cannot be split monic. -/
theorem not_isSplitMono_of_isRadicalMorphism
    {X Y : C} (hX : ¬ IsZero X) {f : X ⟶ Y}
    (hf : IsRadicalMorphism f) : ¬ IsSplitMono f := by
  intro hsplit
  letI : IsSplitMono f := hsplit
  let r : Y ⟶ X := retraction f
  have hi : IsIso (𝟙 X - f ≫ r) := hf r
  have hzero : 𝟙 X - f ≫ r = 0 := by
    rw [IsSplitMono.id f, sub_self]
  haveI : IsIso (0 : X ⟶ X) := hzero ▸ hi
  exact hX ((IsZero.iff_isSplitEpi_eq_zero (0 : X ⟶ X)).2 rfl)

/-- A finite sum of radical morphisms is radical. -/
theorem isRadicalMorphism_finset_sum
    {ι : Type w} {X Y : C} (s : Finset ι) (f : ι → (X ⟶ Y))
    (hf : ∀ i ∈ s, IsRadicalMorphism (f i)) :
    IsRadicalMorphism (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isRadicalMorphism_zero :
        IsRadicalMorphism (0 : X ⟶ Y))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply isRadicalMorphism_add
      · exact hf i (Finset.mem_insert_self i s)
      · exact ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)

end Preadditive

section Abelian

variable [Abelian C]

/-- In an exact complex, a radical first differential makes the second
differential right minimal when its source is projective. -/
theorem ShortComplex.Exact.isRightMinimal_g_of_isRadicalMorphism_f
    {S : ShortComplex C} [Projective S.X₂] (hS : S.Exact)
    (hf : IsRadicalMorphism S.f) : IsRightMinimal S.g := by
  intro e he
  have heZero : (e - 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
  let q : S.X₁ ⟶ kernel S.g :=
    kernel.lift S.g S.f S.zero
  letI : Epi q := hS.epi_kernelLift
  let t : S.X₂ ⟶ kernel S.g :=
    kernel.lift S.g (e - 𝟙 S.X₂) heZero
  let l : S.X₂ ⟶ S.X₁ := Projective.factorThru t q
  have hl : l ≫ S.f = e - 𝟙 S.X₂ := by
    calc
      l ≫ S.f = (l ≫ q) ≫ kernel.ι S.g := by
        simp [q, Category.assoc]
      _ = t ≫ kernel.ι S.g := by
        rw [Projective.factorThru_comp]
      _ = e - 𝟙 S.X₂ := by simp [t]
  have hlrad : IsRadicalMorphism (l ≫ S.f) :=
    isRadicalMorphism_precomp l hf
  have hi : IsIso (𝟙 S.X₂ - (l ≫ S.f) ≫ (-𝟙 S.X₂)) :=
    hlrad (-𝟙 S.X₂)
  have hid : 𝟙 S.X₂ - (l ≫ S.f) ≫ (-𝟙 S.X₂) = e := by
    rw [hl]
    simp
  exact hid ▸ hi

/-- The kernel inclusion of a right-minimal morphism is radical. -/
theorem isRadicalMorphism_kernel_ι_of_isRightMinimal
    {X Y : C} (f : X ⟶ Y)
    (hf : IsRightMinimal f) :
    IsRadicalMorphism (kernel.ι f) := by
  intro g
  have hfix : (𝟙 X - g ≫ kernel.ι f) ≫ f = f := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      kernel.condition, comp_zero, sub_zero]
  letI : IsIso (𝟙 X - g ≫ kernel.ι f) := hf _ hfix
  exact isIso_one_sub_comp g (kernel.ι f)

/-- A morphism from a projective object is right minimal exactly when its
kernel inclusion is radical. -/
theorem isRightMinimal_iff_kernel_ι_isRadicalMorphism
    {X Y : C} [Projective X] (f : X ⟶ Y) :
    IsRightMinimal f ↔ IsRadicalMorphism (kernel.ι f) := by
  constructor
  · exact isRadicalMorphism_kernel_ι_of_isRightMinimal f
  · intro hrad
    exact ShortComplex.Exact.isRightMinimal_g_of_isRadicalMorphism_f
      (ShortComplex.exact_kernel f) hrad

end Abelian

section FiniteBiproducts

variable [Preadditive C] [HasFiniteBiproducts C]

/-- A map between finite biproducts is the finite sum of its matrix
components inserted into the corresponding source and target summands. -/
theorem finBiproduct_eq_sum_components
    {I J : Type w} [Fintype I] [Fintype J]
    (X : I → C) (Y : J → C)
    (f : (⨁ X) ⟶ (⨁ Y)) :
    f = ∑ i : I, ∑ j : J,
      biproduct.π X i ≫
        (biproduct.ι X i ≫ f ≫ biproduct.π Y j) ≫
        biproduct.ι Y j := by
  classical
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

/-- Every matrix component of a radical finite-biproduct map is radical. -/
theorem isRadicalMorphism_finBiproduct_component
    {I J : Type w} [Fintype I] [Fintype J]
    (X : I → C) (Y : J → C)
    (f : (⨁ X) ⟶ (⨁ Y)) (hf : IsRadicalMorphism f)
    (i : I) (j : J) :
    IsRadicalMorphism
      (biproduct.ι X i ≫ f ≫ biproduct.π Y j) := by
  simpa only [Category.assoc] using
    isRadicalMorphism_postcomp (biproduct.π Y j)
      (isRadicalMorphism_precomp (biproduct.ι X i) hf)

/-- A map of finite biproducts is radical when all of its matrix components
are radical. -/
theorem isRadicalMorphism_finBiproduct_of_components
    {I J : Type w} [Fintype I] [Fintype J]
    (X : I → C) (Y : J → C)
    (f : (⨁ X) ⟶ (⨁ Y))
    (hf : ∀ i j,
      IsRadicalMorphism
        (biproduct.ι X i ≫ f ≫ biproduct.π Y j)) :
    IsRadicalMorphism f := by
  classical
  rw [finBiproduct_eq_sum_components X Y f]
  apply isRadicalMorphism_finset_sum
  intro i _
  apply isRadicalMorphism_finset_sum
  intro j _
  simpa only [Category.assoc] using
    isRadicalMorphism_postcomp (biproduct.ι Y j)
      (isRadicalMorphism_precomp (biproduct.π X i) (hf i j))

end FiniteBiproducts

/-- An additive functor maps a finite-biproduct morphism to a radical
morphism when it maps every matrix component to a radical morphism. -/
theorem map_finBiproduct_isRadicalMorphism
    [Preadditive C] [HasFiniteBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {I J : Type} [Fintype I] [Fintype J]
    (X : I → C) (Y : J → C) (f : (⨁ X) ⟶ (⨁ Y))
    (hf : ∀ i j, IsRadicalMorphism
      (F.map (biproduct.ι X i ≫ f ≫ biproduct.π Y j))) :
    IsRadicalMorphism (F.map f) := by
  classical
  rw [finBiproduct_eq_sum_components X Y f, F.map_sum]
  apply isRadicalMorphism_finset_sum
  intro i _
  rw [F.map_sum]
  apply isRadicalMorphism_finset_sum
  intro j _
  have hsparse : IsRadicalMorphism
      (F.map (biproduct.π X i) ≫
        F.map (biproduct.ι X i ≫ f ≫ biproduct.π Y j) ≫
        F.map (biproduct.ι Y j)) := by
    simpa only [Category.assoc] using
      isRadicalMorphism_postcomp (F.map (biproduct.ι Y j))
        (isRadicalMorphism_precomp (F.map (biproduct.π X i)) (hf i j))
  simpa only [F.map_comp, Category.assoc] using hsparse

end MBDVendor.Magnitude.CategoryTheory
