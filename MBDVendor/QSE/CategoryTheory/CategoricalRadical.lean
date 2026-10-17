import Mathlib.Algebra.Field.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The radical of a preadditive category

This file defines the standard Jacobson-radical condition for a morphism in
a preadditive category and proves a one-generator cosemisimplicity criterion.
If every object is a finite biproduct of one object `P` and every nonzero
endomorphism of `P` is invertible, then the categorical radical is zero.
-/

noncomputable section

namespace MBDVendor.QSE.CategoricalRadical

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- The Jacobson-radical condition for a morphism in a preadditive
category, using the source-object convention. -/
def IsRadicalMorphism {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ g : Y ⟶ X, IsIso (𝟙 X - f ≫ g)

omit [HasFiniteBiproducts C] in
/-- The categorical Jacobson identity: invertibility of `1 - a b` implies
invertibility of `1 - b a`. -/
theorem isIso_one_sub_comp
    {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    [IsIso (𝟙 X - a ≫ b)] :
    IsIso (𝟙 Y - b ≫ a) := by
  let h : X ⟶ X := 𝟙 X - a ≫ b
  let k : Y ⟶ Y :=
    𝟙 Y + b ≫ inv h ≫ a
  apply IsIso.mk
  refine ⟨k, ?_, ?_⟩
  · dsimp only [k]
    simp only [Preadditive.sub_comp, Preadditive.comp_add,
      Category.id_comp, Category.comp_id, Category.assoc]
    have hh : h ≫ inv h = 𝟙 X :=
      IsIso.hom_inv_id h
    dsimp only [h] at hh
    have hh' :
        inv h - a ≫ b ≫ inv h = 𝟙 X := by
      simpa only [Preadditive.sub_comp, Category.id_comp,
        Category.assoc] using hh
    have hmid :
        b ≫ inv h ≫ a -
            b ≫ a ≫ b ≫ inv h ≫ a =
          b ≫ a := by
      calc
        b ≫ inv h ≫ a -
              b ≫ a ≫ b ≫ inv h ≫ a =
            b ≫ (inv h - a ≫ b ≫ inv h) ≫ a := by
              simp only [Preadditive.comp_sub,
                Preadditive.sub_comp, Category.assoc]
        _ = b ≫ a := by rw [hh']; simp
    rw [hmid]
    abel

  · dsimp only [k]
    simp only [Preadditive.add_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id, Category.assoc]
    have hh : inv h ≫ h = 𝟙 X :=
      IsIso.inv_hom_id h
    dsimp only [h] at hh
    have hh' :
        inv h - inv h ≫ a ≫ b = 𝟙 X := by
      simpa only [Preadditive.comp_sub, Category.comp_id,
        Category.assoc] using hh
    have hmid :
        b ≫ inv h ≫ a -
            b ≫ inv h ≫ a ≫ b ≫ a =
          b ≫ a := by
      calc
        b ≫ inv h ≫ a -
              b ≫ inv h ≫ a ≫ b ≫ a =
            b ≫ (inv h - inv h ≫ a ≫ b) ≫ a := by
              simp only [Preadditive.comp_sub,
                Preadditive.sub_comp, Category.assoc]
        _ = b ≫ a := by rw [hh']; simp
    rw [show
      𝟙 Y + b ≫ inv h ≫ a -
            (b ≫ a + b ≫ inv h ≫ a ≫ b ≫ a) =
          𝟙 Y - b ≫ a +
            (b ≫ inv h ≫ a -
              b ≫ inv h ≫ a ≫ b ≫ a) by
        abel,
      hmid]
    abel

omit [HasFiniteBiproducts C] in
/-- The categorical radical is closed under precomposition. -/
theorem isRadicalMorphism_precomp
    {W X Y : C} (a : W ⟶ X) {f : X ⟶ Y}
    (hf : IsRadicalMorphism f) :
    IsRadicalMorphism (a ≫ f) := by
  intro g
  haveI : IsIso (𝟙 X - (f ≫ g) ≫ a) := by
    simpa only [Category.assoc] using hf (g ≫ a)
  simpa only [Category.assoc] using
    (isIso_one_sub_comp (f ≫ g) a)

omit [HasFiniteBiproducts C] in
/-- The categorical radical is closed under postcomposition. -/
theorem isRadicalMorphism_postcomp
    {X Y Z : C} {f : X ⟶ Y} (b : Y ⟶ Z)
    (hf : IsRadicalMorphism f) :
    IsRadicalMorphism (f ≫ b) := by
  intro g
  simpa only [Category.assoc] using hf (b ≫ g)

omit [HasFiniteBiproducts C] in
/-- Adding a radical morphism to a split monomorphism preserves split
monicity. -/
theorem isSplitMono_add_of_isRadicalMorphism
    {X Y : C} (j : X ⟶ Y) [IsSplitMono j]
    {r : X ⟶ Y} (hr : IsRadicalMorphism r) :
    IsSplitMono (j + r) := by
  let a : X ⟶ X := (j + r) ≫ retraction j
  have hr' : IsRadicalMorphism (r ≫ retraction j) :=
    isRadicalMorphism_postcomp (retraction j) hr
  haveI : IsIso a := by
    have hi : IsIso (𝟙 X - (r ≫ retraction j) ≫ (-𝟙 X)) :=
      hr' (-𝟙 X)
    simpa [a, Preadditive.add_comp] using hi
  exact IsSplitMono.mk'
    { retraction := retraction j ≫ inv a
      id := by
        rw [← Category.assoc]
        change a ≫ inv a = 𝟙 X
        simp }

omit [HasFiniteBiproducts C] in
/-- Adding a radical morphism to a split epimorphism preserves split
epicity. -/
theorem isSplitEpi_add_of_isRadicalMorphism
    {X Y : C} (p : X ⟶ Y) [IsSplitEpi p]
    {r : X ⟶ Y} (hr : IsRadicalMorphism r) :
    IsSplitEpi (p + r) := by
  let a : Y ⟶ Y := section_ p ≫ (p + r)
  have hr' : IsRadicalMorphism (section_ p ≫ r) :=
    isRadicalMorphism_precomp (section_ p) hr
  haveI : IsIso a := by
    have hi : IsIso (𝟙 Y - (section_ p ≫ r) ≫ (-𝟙 Y)) :=
      hr' (-𝟙 Y)
    simpa [a, Preadditive.comp_add] using hi
  exact IsSplitEpi.mk'
    { section_ := inv a ≫ section_ p
      id := by
        rw [Category.assoc]
        change inv a ≫ a = 𝟙 Y
        simp }

/-- A preadditive category has zero radical if its only radical morphisms
are zero. -/
def HasZeroRadical (C : Type u) [Category.{v} C]
    [Preadditive C] : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    IsRadicalMorphism f → f = 0

omit [HasFiniteBiproducts C] in
/-- A morphism is radical if every return composite is nilpotent. -/
theorem isRadicalMorphism_of_forall_comp_isNilpotent
    {X Y : C} (f : X ⟶ Y)
    (h : ∀ g : Y ⟶ X,
      IsNilpotent (End.of (f ≫ g))) :
    IsRadicalMorphism f := by
  intro g
  rw [← isUnit_iff_isIso]
  exact (h g).isUnit_one_sub

private theorem exists_biproduct_component_ne_zero
    {P : C} {J K : Type} [Fintype J] [Fintype K]
    (f :
      (⨁ fun _ : J ↦ P) ⟶
        ⨁ fun _ : K ↦ P)
    (hf : f ≠ 0) :
    ∃ j k, biproduct.components f j k ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  rw [← biproduct.components_matrix f]
  simp only [h]
  ext
  simp

private theorem sparse_reverse_contracts_row
    {P : C} {J K : Type} [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K]
    (row : K → End P)
    (j : J) (k : K)
    (ha : IsIso (row k)) :
    let g :
        (⨁ fun _ : K ↦ P) ⟶
          ⨁ fun _ : J ↦ P :=
      biproduct.matrix fun k' j' ↦
        if k' = k ∧ j' = j then inv (row k) else 0
    biproduct.lift row ≫ g =
      biproduct.ι (fun _ : J ↦ P) j := by
  classical
  letI : IsIso (row k) := ha
  dsimp only
  ext l
  simp only [Category.assoc, biproduct.matrix_π,
    biproduct.lift_desc]
  rw [Finset.sum_eq_single k]
  · by_cases hl : l = j
    · subst l
      simp
    · simp [hl, Ne.symm hl]
  · intro k' _ hk'
    simp [hk']
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- If every nonzero endomorphism of `P` is invertible, then the
categorical radical between any two finite biproducts of `P` is zero. -/
theorem radicalMorphism_eq_zero_between_biproducts
    {P : C}
    (hP : ∀ a : End P, a ≠ 0 → IsIso a)
    {J K : Type} [Fintype J] [Fintype K]
    (f :
      (⨁ fun _ : J ↦ P) ⟶
        ⨁ fun _ : K ↦ P)
    (hf : IsRadicalMorphism f) :
    f = 0 := by
  classical
  by_contra hf0
  obtain ⟨j, k, hjk⟩ :=
    exists_biproduct_component_ne_zero f hf0
  let a : End P := biproduct.components f j k
  letI : IsIso a := hP a hjk
  let g :
      (⨁ fun _ : K ↦ P) ⟶
        ⨁ fun _ : J ↦ P :=
    biproduct.matrix fun k' j' ↦
      if k' = k ∧ j' = j then inv a else 0
  have hrow :
      biproduct.ι (fun _ : J ↦ P) j ≫ f =
        biproduct.lift fun k' ↦
          biproduct.components f j k' := by
    rw [← biproduct.components_matrix f,
      biproduct.ι_matrix]
    simp
  have hcontract :
      biproduct.ι (fun _ : J ↦ P) j ≫ f ≫ g =
        biproduct.ι (fun _ : J ↦ P) j := by
    rw [← Category.assoc, hrow]
    exact
      sparse_reverse_contracts_row
        (fun k' ↦ biproduct.components f j k')
        j k inferInstance
  have hzero :
      biproduct.ι (fun _ : J ↦ P) j ≫
          (𝟙 _ - f ≫ g) =
        0 := by
    rw [Preadditive.comp_sub, Category.comp_id,
      hcontract, sub_self]
  haveI : IsIso (𝟙 _ - f ≫ g) := hf g
  have hi_zero :
      biproduct.ι (fun _ : J ↦ P) j = 0 := by
    rw [← cancel_mono (𝟙 _ - f ≫ g)]
    simpa using hzero
  have hid_zero : (𝟙 P : P ⟶ P) = 0 := by
    rw [← biproduct.ι_π_self (fun _ : J ↦ P) j,
      hi_zero, zero_comp]
  have hid_nonzero : (𝟙 P : P ⟶ P) ≠ 0 :=
    fun h ↦ hjk (by
      rw [← Category.id_comp
        (biproduct.components f j k), h, zero_comp])
  exact hid_nonzero hid_zero

/-- A category is additively generated by one object when every object is
isomorphic to a finite biproduct of copies of it. -/
def IsAdditivelyGeneratedBy (P : C) : Prop :=
  ∀ X : C,
    ∃ (J : FintypeCat.{0}),
      Nonempty (X ≅ ⨁ fun _ : J ↦ P)

/-- Every radical morphism is zero in an additive category generated by
one object whose nonzero endomorphisms are all invertible. -/
theorem radicalMorphism_eq_zero_of_isAdditivelyGeneratedBy
    {P : C}
    (hP : ∀ a : End P, a ≠ 0 → IsIso a)
    (hgen : IsAdditivelyGeneratedBy P)
    {X Y : C} (f : X ⟶ Y)
    (hf : IsRadicalMorphism f) :
    f = 0 := by
  classical
  obtain ⟨J, ⟨eX⟩⟩ := hgen X
  obtain ⟨K, ⟨eY⟩⟩ := hgen Y
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype K := Fintype.ofFinite K
  let f' :
      (⨁ fun _ : J ↦ P) ⟶
        ⨁ fun _ : K ↦ P :=
    eX.inv ≫ f ≫ eY.hom
  have hf' : IsRadicalMorphism f' := by
    intro g'
    let g : Y ⟶ X :=
      eY.hom ≫ g' ≫ eX.inv
    let h : X ⟶ X := 𝟙 X - f ≫ g
    letI : IsIso h := hf g
    have heq :
        𝟙 (⨁ fun _ : J ↦ P) - f' ≫ g' =
          eX.inv ≫ h ≫ eX.hom := by
      simp [f', g, h, Preadditive.comp_sub,
        Preadditive.sub_comp, Category.assoc]
    rw [heq]
    infer_instance
  have hfzero :
      f' = 0 :=
    radicalMorphism_eq_zero_between_biproducts
      hP f' hf'
  calc
    f = eX.hom ≫ f' ≫ eY.inv := by
      simp [f', Category.assoc]
    _ = 0 := by rw [hfzero]; simp

/-- One-generator Schur data imply that the whole categorical radical is
zero. -/
theorem hasZeroRadical_of_isAdditivelyGeneratedBy
    {P : C}
    (hP : ∀ a : End P, a ≠ 0 → IsIso a)
    (hgen : IsAdditivelyGeneratedBy P) :
    HasZeroRadical C :=
  fun {_ _} f hf ↦
    radicalMorphism_eq_zero_of_isAdditivelyGeneratedBy
      hP hgen f hf

end MBDVendor.QSE.CategoricalRadical
