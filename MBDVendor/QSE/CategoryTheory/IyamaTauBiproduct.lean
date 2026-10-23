module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import MBDVendor.QSE.CategoryTheory.IyamaTauSequence
public import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Finite biproducts of Iyama tau-approximation complexes

This file constructs the explicit componentwise finite biproduct of short
complexes.  Weak kernels, weak cokernels, and Iyama's radical approximation
conditions are preserved.  When the categorical radical is represented by a
two-sided additive Hom ideal, minimality is also preserved, so both right and
left tau-sequences are closed under finite biproducts.  The current interface
supplies that ideal through `NilpotentRadicalData`; its nilpotence field is not
used by the results in this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

open CategoricalIdeal CategoricalRadical

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- The componentwise finite biproduct of short complexes. -/
def shortComplexBiproduct {J : Type w} [Fintype J]
    (S : J → ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (biproduct.map fun j ↦ (S j).f)
    (biproduct.map fun j ↦ (S j).g)
    (by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp)

@[simp]
theorem shortComplexBiproduct_f {J : Type w} [Fintype J]
    (S : J → ShortComplex C) :
    (shortComplexBiproduct S).f = biproduct.map fun j ↦ (S j).f :=
  rfl

@[simp]
theorem shortComplexBiproduct_g {J : Type w} [Fintype J]
    (S : J → ShortComplex C) :
    (shortComplexBiproduct S).g = biproduct.map fun j ↦ (S j).g :=
  rfl

/-- Finite componentwise biproducts preserve weak kernels. -/
theorem isWeakKernel_shortComplexBiproduct
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, ShortComplex.IsWeakKernel (S j)) :
    ShortComplex.IsWeakKernel (shortComplexBiproduct S) := by
  rw [ShortComplex.isWeakKernel_iff]
  intro W k hk
  change W ⟶ (⨁ fun j ↦ (S j).X₂) at k
  change k ≫ (biproduct.map fun j ↦ (S j).g) = 0 at hk
  have hk_component (j : J) :
      (k ≫ biproduct.π (fun j ↦ (S j).X₂) j) ≫ (S j).g = 0 := by
    have h := congrArg
      (fun q ↦ q ≫ biproduct.π (fun j ↦ (S j).X₃) j) hk
    rw [Category.assoc] at h
    rw [biproduct.map_π] at h
    simpa [Category.assoc] using h
  choose l hl using fun j ↦
    (ShortComplex.isWeakKernel_iff (S j)).mp
      (hS j) (k ≫ biproduct.π (fun j ↦ (S j).X₂) j)
        (hk_component j)
  refine ⟨biproduct.lift l, ?_⟩
  change biproduct.lift l ≫
      (biproduct.map fun j ↦ (S j).f) = k
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, biproduct.map_π,
    biproduct.lift_π_assoc, hl j]

/-- Finite componentwise biproducts preserve weak cokernels. -/
theorem isWeakCokernel_shortComplexBiproduct
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, ShortComplex.IsWeakCokernel (S j)) :
    ShortComplex.IsWeakCokernel (shortComplexBiproduct S) := by
  rw [ShortComplex.isWeakCokernel_iff]
  intro W k hk
  change (⨁ fun j ↦ (S j).X₂) ⟶ W at k
  change (biproduct.map fun j ↦ (S j).f) ≫ k = 0 at hk
  have hk_component (j : J) :
      (S j).f ≫
        (biproduct.ι (fun j ↦ (S j).X₂) j ≫ k) = 0 := by
    have h := congrArg
      (fun q ↦ biproduct.ι (fun j ↦ (S j).X₁) j ≫ q) hk
    simpa [Category.assoc, biproduct.ι_map] using h
  choose l hl using fun j ↦
    (ShortComplex.isWeakCokernel_iff (S j)).mp
      (hS j) (biproduct.ι (fun j ↦ (S j).X₂) j ≫ k)
        (hk_component j)
  refine ⟨biproduct.desc l, ?_⟩
  change (biproduct.map fun j ↦ (S j).g) ≫
      biproduct.desc l = k
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, biproduct.ι_map,
    Category.assoc, biproduct.ι_desc, hl j]

/-- A componentwise finite biproduct of radical morphisms is radical once
the categorical radical is available as a two-sided additive Hom ideal. -/
theorem isRadicalMorphism_biproduct_map
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, IsRadicalMorphism (f j)) :
    IsRadicalMorphism (biproduct.map f) := by
  classical
  rw [← R.mem_ideal_iff]
  have hmap :
      biproduct.map f =
        ∑ j : J,
          biproduct.π X j ≫ f j ≫ biproduct.ι Y j := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    · intro k _ hki
      simp [Ne.symm hki]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hmap]
  apply (R.ideal.hom (⨁ X) (⨁ Y)).sum_mem
  intro j hj
  change
    biproduct.π X j ≫ f j ≫ biproduct.ι Y j ∈
      R.ideal.hom (⨁ X) (⨁ Y)
  simpa only [Category.assoc] using
    R.ideal.postcomp (biproduct.ι Y j)
      (R.ideal.precomp (biproduct.π X j)
        ((R.mem_ideal_iff (f j)).2 (hf j)))

/-- Tau-approximation conditions are preserved by finite componentwise
biproducts.  Minimality is deliberately not part of this statement. -/
theorem tauApproximation_shortComplexBiproduct
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, TauApproximation (S j)) :
    TauApproximation (shortComplexBiproduct S) where
  f_radical :=
    isRadicalMorphism_biproduct_map R (fun j ↦ (S j).f)
      (fun j ↦ (hS j).f_radical)
  g_radical :=
    isRadicalMorphism_biproduct_map R (fun j ↦ (S j).g)
      (fun j ↦ (hS j).g_radical)
  factors_from_left := by
    intro W a ha
    change (⨁ fun j ↦ (S j).X₁) ⟶ W at a
    have ha_component (j : J) :
        IsRadicalMorphism
          (biproduct.ι (fun j ↦ (S j).X₁) j ≫ a) :=
      (R.mem_ideal_iff _).1
        (R.ideal.precomp (biproduct.ι (fun j ↦ (S j).X₁) j)
          ((R.mem_ideal_iff a).2 ha))
    choose b hb using fun j ↦
      (hS j).factors_from_left
        (biproduct.ι (fun j ↦ (S j).X₁) j ≫ a)
        (ha_component j)
    refine ⟨biproduct.desc b, ?_⟩
    change (biproduct.map fun j ↦ (S j).f) ≫
        biproduct.desc b = a
    apply biproduct.hom_ext'
    intro j
    rw [← Category.assoc, biproduct.ι_map,
      Category.assoc, biproduct.ι_desc, hb j]
  factors_into_right := by
    intro W a ha
    change W ⟶ (⨁ fun j ↦ (S j).X₃) at a
    have ha_component (j : J) :
        IsRadicalMorphism
          (a ≫ biproduct.π (fun j ↦ (S j).X₃) j) :=
      (R.mem_ideal_iff _).1
        (R.ideal.postcomp (biproduct.π (fun j ↦ (S j).X₃) j)
          ((R.mem_ideal_iff a).2 ha))
    choose b hb using fun j ↦
      (hS j).factors_into_right
        (a ≫ biproduct.π (fun j ↦ (S j).X₃) j)
        (ha_component j)
    refine ⟨biproduct.lift b, ?_⟩
    change biproduct.lift b ≫
        (biproduct.map fun j ↦ (S j).g) = a
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.map_π,
      biproduct.lift_π_assoc, hb j]

omit [HasFiniteBiproducts C] in
/-- Any morphism annihilated on the right by a right-minimal morphism is
categorically radical. -/
theorem isRadicalMorphism_of_comp_eq_zero_of_isRightMinimal
    {W X Y : C} {a : W ⟶ X} {f : X ⟶ Y}
    (hf : IsRightMinimal f) (ha : a ≫ f = 0) :
    IsRadicalMorphism a := by
  intro b
  have hfix : (𝟙 X - b ≫ a) ≫ f = f := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      ha, comp_zero, sub_zero]
  letI : IsIso (𝟙 X - b ≫ a) := hf _ hfix
  exact isIso_one_sub_comp b a

omit [HasFiniteBiproducts C] in
/-- Any morphism annihilated on the left by a left-minimal morphism is
categorically radical. -/
theorem isRadicalMorphism_of_comp_eq_zero_of_isLeftMinimal
    {X Y W : C} {f : X ⟶ Y} {a : Y ⟶ W}
    (hf : IsLeftMinimal f) (ha : f ≫ a = 0) :
    IsRadicalMorphism a := by
  intro b
  apply hf
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    ha, zero_comp, sub_zero]

/-- A matrix whose every component belongs to the chosen radical Hom ideal
belongs to that ideal. -/
theorem mem_radicalIdeal_of_biproduct_components
    (R : NilpotentRadicalData C)
    {J K : Type w} [Fintype J] [Fintype K]
    {X : J → C} {Y : K → C}
    (q : (⨁ X) ⟶ (⨁ Y))
    (hq : ∀ i j,
      (biproduct.ι X i ≫ q ≫ biproduct.π Y j) ∈
        R.ideal.hom (X i) (Y j)) :
    q ∈ R.ideal.hom (⨁ X) (⨁ Y) := by
  classical
  have hmatrix :
      q = ∑ i : J, ∑ j : K,
        biproduct.π X i ≫
          (biproduct.ι X i ≫ q ≫ biproduct.π Y j) ≫
          biproduct.ι Y j := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [hkj]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro k _ hki
      simp [Ne.symm hki]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hmatrix]
  apply (R.ideal.hom (⨁ X) (⨁ Y)).sum_mem
  intro i hi
  apply (R.ideal.hom (⨁ X) (⨁ Y)).sum_mem
  intro j hj
  change
    biproduct.π X i ≫
        (biproduct.ι X i ≫ q ≫ biproduct.π Y j) ≫
        biproduct.ι Y j ∈
      R.ideal.hom (⨁ X) (⨁ Y)
  simpa only [Category.assoc] using
    R.ideal.postcomp (biproduct.ι Y j)
      (R.ideal.precomp (biproduct.π X i) (hq i j))

/-- A morphism out of a finite biproduct belongs to the radical ideal when
each restriction to a summand does. -/
theorem mem_radicalIdeal_of_biproduct_source_components
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X : J → C} {Y : C}
    (q : (⨁ X) ⟶ Y)
    (hq : ∀ i,
      biproduct.ι X i ≫ q ∈ R.ideal.hom (X i) Y) :
    q ∈ R.ideal.hom (⨁ X) Y := by
  classical
  have hsum :
      q = ∑ i : J,
        biproduct.π X i ≫ (biproduct.ι X i ≫ q) := by
    apply biproduct.hom_ext'
    intro i
    simp only [Preadditive.comp_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsum]
  apply (R.ideal.hom (⨁ X) Y).sum_mem
  intro i hi
  exact R.ideal.precomp (biproduct.π X i) (hq i)

/-- Finite componentwise biproducts preserve right-minimal morphisms whenever
the categorical radical is realized by a two-sided additive Hom ideal. -/
theorem isRightMinimal_biproduct_map
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, IsRightMinimal (f j)) :
    IsRightMinimal (biproduct.map f) := by
  classical
  intro e he
  have hdiag (i : J) :
      (biproduct.ι X i ≫ e ≫ biproduct.π X i) ≫ f i = f i := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y i) he
    simpa [Category.assoc] using h
  have hoffdiag (i j : J) (hij : i ≠ j) :
      (biproduct.ι X i ≫ e ≫ biproduct.π X j) ≫ f j = 0 := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y j) he
    simpa [Category.assoc, hij] using h
  letI componentIso (i : J) :
      IsIso (biproduct.ι X i ≫ e ≫ biproduct.π X i) :=
    hf i _ (hdiag i)
  let d : (⨁ X) ≅ (⨁ X) :=
    biproduct.mapIso fun i ↦
      asIso (biproduct.ι X i ≫ e ≫ biproduct.π X i)
  have hrad : IsRadicalMorphism (d.hom - e) := by
    rw [← R.mem_ideal_iff]
    apply mem_radicalIdeal_of_biproduct_components R
    intro i j
    by_cases hij : i = j
    · subst j
      have hz :
          biproduct.ι X i ≫ (d.hom - e) ≫ biproduct.π X i = 0 := by
        simp [d]
      rw [hz]
      exact zero_mem _
    · have hc :
          biproduct.ι X i ≫ (d.hom - e) ≫ biproduct.π X j =
            -(biproduct.ι X i ≫ e ≫ biproduct.π X j) := by
        simp [d, hij]
      rw [hc]
      apply neg_mem
      rw [R.mem_ideal_iff]
      exact isRadicalMorphism_of_comp_eq_zero_of_isRightMinimal
        (hf j) (hoffdiag i j hij)
  haveI : IsIso (𝟙 (⨁ X) - (d.hom - e) ≫ d.inv) :=
    hrad d.inv
  have hfactor :
      (𝟙 (⨁ X) - (d.hom - e) ≫ d.inv) ≫ d.hom = e := by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inv_hom_id, Category.comp_id]
    abel
  rw [← hfactor]
  infer_instance

/-- Finite componentwise biproducts preserve left-minimal morphisms whenever
the categorical radical is realized by a two-sided additive Hom ideal. -/
theorem isLeftMinimal_biproduct_map
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, IsLeftMinimal (f j)) :
    IsLeftMinimal (biproduct.map f) := by
  classical
  intro e he
  have hdiag (i : J) :
      f i ≫ (biproduct.ι Y i ≫ e ≫ biproduct.π Y i) = f i := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y i) he
    simpa [Category.assoc] using h
  have hoffdiag (i j : J) (hij : i ≠ j) :
      f i ≫ (biproduct.ι Y i ≫ e ≫ biproduct.π Y j) = 0 := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y j) he
    simpa [Category.assoc, hij] using h
  letI componentIso (i : J) :
      IsIso (biproduct.ι Y i ≫ e ≫ biproduct.π Y i) :=
    hf i _ (hdiag i)
  let d : (⨁ Y) ≅ (⨁ Y) :=
    biproduct.mapIso fun i ↦
      asIso (biproduct.ι Y i ≫ e ≫ biproduct.π Y i)
  have hrad : IsRadicalMorphism (d.hom - e) := by
    rw [← R.mem_ideal_iff]
    apply mem_radicalIdeal_of_biproduct_components R
    intro i j
    by_cases hij : i = j
    · subst j
      have hz :
          biproduct.ι Y i ≫ (d.hom - e) ≫ biproduct.π Y i = 0 := by
        simp [d]
      rw [hz]
      exact zero_mem _
    · have hc :
          biproduct.ι Y i ≫ (d.hom - e) ≫ biproduct.π Y j =
            -(biproduct.ι Y i ≫ e ≫ biproduct.π Y j) := by
        simp [d, hij]
      rw [hc]
      apply neg_mem
      rw [R.mem_ideal_iff]
      exact isRadicalMorphism_of_comp_eq_zero_of_isLeftMinimal
        (hf i) (hoffdiag i j hij)
  haveI : IsIso (𝟙 (⨁ Y) - (d.hom - e) ≫ d.inv) :=
    hrad d.inv
  have hfactor :
      (𝟙 (⨁ Y) - (d.hom - e) ≫ d.inv) ≫ d.hom = e := by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inv_hom_id, Category.comp_id]
    abel
  rw [← hfactor]
  infer_instance

/-- Right tau-sequences are closed under finite componentwise biproducts. -/
theorem rightTauSequence_shortComplexBiproduct
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, RightTauSequence (S j)) :
    RightTauSequence (shortComplexBiproduct S) where
  toTauApproximation :=
    tauApproximation_shortComplexBiproduct R S
      (fun j ↦ (hS j).toTauApproximation)
  minimalWeakKernel := ⟨
    isWeakKernel_shortComplexBiproduct S
      (fun j ↦ (hS j).minimalWeakKernel.1),
    isRightMinimal_biproduct_map R (fun j ↦ (S j).f)
      (fun j ↦ (hS j).minimalWeakKernel.2)⟩

/-- Left tau-sequences are closed under finite componentwise biproducts. -/
theorem leftTauSequence_shortComplexBiproduct
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, LeftTauSequence (S j)) :
    LeftTauSequence (shortComplexBiproduct S) where
  toTauApproximation :=
    tauApproximation_shortComplexBiproduct R S
      (fun j ↦ (hS j).toTauApproximation)
  minimalWeakCokernel := ⟨
    isWeakCokernel_shortComplexBiproduct S
      (fun j ↦ (hS j).minimalWeakCokernel.1),
    isLeftMinimal_biproduct_map R (fun j ↦ (S j).g)
      (fun j ↦ (hS j).minimalWeakCokernel.2)⟩

end MBDVendor.QSE.Iyama
