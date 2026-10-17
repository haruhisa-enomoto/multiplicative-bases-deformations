import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MBDVendor.QSE.CategoryTheory.CategoricalRadicalIdeal
import MBDVendor.QSE.CategoryTheory.IyamaTauSequence

/-!
# Dimension recurrence from a strict right tau-sequence

For a strict right tau-sequence `X₁ ⟶ X₂ ⟶ X₃`, evaluation at a source
object `W` gives a short exact sequence

`0 ⟶ Hom(W,X₁) ⟶ Hom(W,X₂) ⟶ rad(W,X₃) ⟶ 0`.

This file constructs the radical as a linear subspace and proves the resulting
finite-dimensional equality.  It is the linear-algebraic heart of the mesh/
Hom inverse recurrence.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MBDVendor.Magnitude.CategoryTheory

open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama

universe s v u

variable (k : Type s) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The categorical radical between two objects, as a linear subspace of the
Hom space. -/
def radicalSubmodule (X Y : C) : Submodule k (X ⟶ Y) where
  carrier := {f | IsRadicalMorphism f}
  zero_mem' := isRadicalMorphism_zero
  add_mem' hf hg := isRadicalMorphism_add hf hg
  smul_mem' r f hf := by
    have h := isRadicalMorphism_precomp (r • 𝟙 X) hf
    simpa using h

/-- Postcomposition by a radical morphism, with codomain restricted to the
radical subspace. -/
def rightCompToRadical (W : C) {Y Z : C} (g : Y ⟶ Z)
    (hg : IsRadicalMorphism g) :
    (W ⟶ Y) →ₗ[k] radicalSubmodule k W Z where
  toFun f := ⟨f ≫ g, isRadicalMorphism_precomp f hg⟩
  map_add' f f' := by
    apply Subtype.ext
    simp
  map_smul' r f := by
    apply Subtype.ext
    simp

/-- Postcomposition by an isomorphism transports the radical subspace. -/
def radicalTargetLinearEquiv (X : C) {Y Z : C} (e : Y ≅ Z) :
    radicalSubmodule k X Y ≃ₗ[k] radicalSubmodule k X Z where
  toFun f :=
    ⟨f.1 ≫ e.hom, isRadicalMorphism_postcomp e.hom f.2⟩
  invFun f :=
    ⟨f.1 ≫ e.inv, isRadicalMorphism_postcomp e.inv f.2⟩
  left_inv f := by
    apply Subtype.ext
    simp
  right_inv f := by
    apply Subtype.ext
    simp
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' r f := by
    apply Subtype.ext
    simp

/-- Precomposition by an isomorphism transports the radical subspace. -/
def radicalSourceLinearEquiv (Y : C) {X Z : C} (e : X ≅ Z) :
    radicalSubmodule k X Y ≃ₗ[k] radicalSubmodule k Z Y where
  toFun f :=
    ⟨e.inv ≫ f.1, isRadicalMorphism_precomp e.inv f.2⟩
  invFun f :=
    ⟨e.hom ≫ f.1, isRadicalMorphism_precomp e.hom f.2⟩
  left_inv f := by
    apply Subtype.ext
    simp
  right_inv f := by
    apply Subtype.ext
    simp
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' r f := by
    apply Subtype.ext
    simp

/-- Precomposition by a radical morphism, with codomain restricted to the
radical subspace. -/
def leftCompToRadical (W : C) {X Y : C} (f : X ⟶ Y)
    (hf : IsRadicalMorphism f) :
    (Y ⟶ W) →ₗ[k] radicalSubmodule k X W where
  toFun g := ⟨f ≫ g, isRadicalMorphism_postcomp g hf⟩
  map_add' g g' := by
    apply Subtype.ext
    simp
  map_smul' r g := by
    apply Subtype.ext
    simp

/-- Rank-nullity form of a finite-dimensional short exact sequence of linear
maps. -/
theorem finrank_middle_eq_add_of_exact
    {U V W : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module k U] [Module k V] [Module k W]
    [FiniteDimensional k V]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hExact : Function.Exact f g)
    (f_injective : Function.Injective f)
    (g_surjective : Function.Surjective g) :
    Module.finrank k V = Module.finrank k U + Module.finrank k W := by
  have hRangeF :
      Module.finrank k f.range = Module.finrank k U :=
    (LinearEquiv.ofInjective f f_injective).finrank_eq.symm
  have hRankNullity := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr g_surjective, finrank_top,
    hExact.linearMap_ker_eq, hRangeF] at hRankNullity
  omega

/-- Hom-dimension recurrence supplied by a strict right tau-sequence. -/
theorem rightTauSequence_finrank
    (S : ShortComplex C) (hS : RightTauSequence S) [Mono S.f]
    (W : C)
    [FiniteDimensional k (W ⟶ S.X₂)] :
    Module.finrank k (W ⟶ S.X₂) =
      Module.finrank k (W ⟶ S.X₁) +
        Module.finrank k (radicalSubmodule k W S.X₃) := by
  let f : (W ⟶ S.X₁) →ₗ[k] (W ⟶ S.X₂) :=
    CategoryTheory.Linear.rightComp k W S.f
  let g : (W ⟶ S.X₂) →ₗ[k] radicalSubmodule k W S.X₃ :=
    rightCompToRadical k W S.g hS.g_radical
  have f_injective : Function.Injective f := by
    intro a b hab
    change a ≫ S.f = b ≫ S.f at hab
    exact (cancel_mono S.f).mp hab
  have g_surjective : Function.Surjective g := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hS.factors_into_right a ha
    refine ⟨b, ?_⟩
    apply Subtype.ext
    exact hb
  have hExact : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : b ≫ S.g = 0 := by
        have := congrArg Subtype.val hb
        exact this
      exact (hS.minimalWeakKernel.1.exact_postcomp W b).mp hb'
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      simp [f, g, rightCompToRadical, Category.assoc, S.zero]
  exact finrank_middle_eq_add_of_exact k f g hExact f_injective g_surjective

/-- Dual Hom-dimension recurrence supplied by a strict left tau-sequence. -/
theorem leftTauSequence_finrank
    (S : ShortComplex C) (hS : LeftTauSequence S) [Epi S.g]
    (W : C)
    [FiniteDimensional k (S.X₂ ⟶ W)] :
    Module.finrank k (S.X₂ ⟶ W) =
      Module.finrank k (S.X₃ ⟶ W) +
        Module.finrank k (radicalSubmodule k S.X₁ W) := by
  let f : (S.X₃ ⟶ W) →ₗ[k] (S.X₂ ⟶ W) :=
    CategoryTheory.Linear.leftComp k W S.g
  let g : (S.X₂ ⟶ W) →ₗ[k] radicalSubmodule k S.X₁ W :=
    leftCompToRadical k W S.f hS.f_radical
  have f_injective : Function.Injective f := by
    intro a b hab
    change S.g ≫ a = S.g ≫ b at hab
    exact (cancel_epi S.g).mp hab
  have g_surjective : Function.Surjective g := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hS.factors_from_left a ha
    refine ⟨b, ?_⟩
    apply Subtype.ext
    exact hb
  have hExact : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hb' : S.f ≫ b = 0 := by
        have := congrArg Subtype.val hb
        exact this
      exact (hS.minimalWeakCokernel.1.exact_precomp W b).mp hb'
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      simp [f, g, leftCompToRadical, ← Category.assoc, S.zero]
  exact finrank_middle_eq_add_of_exact k f g hExact f_injective g_surjective

end MBDVendor.Magnitude.CategoryTheory
