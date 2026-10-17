import MBDVendor.QSE.CategoryTheory.CategoricalRadical
import MBDVendor.QSE.CategoryTheory.HomIdealPowers

/-!
# A nilpotent categorical radical as Hom-ideal data

The current categorical-radical predicate is morphismwise.  Iyama's ladder
argument also needs powers of that radical.  This file gives the exact bridge:
a two-sided additive Hom ideal whose membership predicate is the categorical
radical, together with a nilpotence exponent.

Nilpotence is stronger than Iyama's general `J^∞ = 0` hypothesis, but is the
appropriate finite condition for the acyclic word mesh categories used in the
manuscript.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MBDVendor.QSE.CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

open CategoricalIdeal

/-- A realization of the categorical radical as a nilpotent two-sided
additive Hom ideal. -/
structure NilpotentRadicalData (C : Type u) [Category.{v} C]
    [Preadditive C] where
  ideal : HomIdeal C
  mem_iff :
    ∀ {X Y : C} (f : X ⟶ Y),
      f ∈ ideal.hom X Y ↔ IsRadicalMorphism f
  nilpotent : ideal.IsNilpotent

namespace NilpotentRadicalData

variable (R : NilpotentRadicalData C)

/-- Radical membership may be converted to membership in the chosen Hom
ideal. -/
theorem mem_ideal_iff {X Y : C} (f : X ⟶ Y) :
    f ∈ R.ideal.hom X Y ↔ IsRadicalMorphism f :=
  R.mem_iff f

/-- A morphism lying in every power of a nilpotent categorical radical is
zero. -/
theorem eq_zero_of_mem_every_power
    {X Y : C} {f : X ⟶ Y}
    (hf : ∀ n, f ∈ (R.ideal.pow n).hom X Y) :
    f = 0 :=
  HomIdeal.eq_zero_of_mem_every_power R.nilpotent hf

/-- A radical endomorphism is nilpotent when the categorical radical Hom
ideal is nilpotent. -/
theorem isNilpotent_end_of_mem_ideal
    {X : C} {f : X ⟶ X}
    (hf : f ∈ R.ideal.hom X X) :
    IsNilpotent (CategoryTheory.End.of f) := by
  obtain ⟨N, hN⟩ := R.nilpotent
  have hpow : ∀ n : ℕ,
      (CategoryTheory.End.of f) ^ n ∈
        (R.ideal.pow n).hom X X := by
    intro n
    induction n with
    | zero =>
        change (𝟙 X) ∈ (⊤ : HomIdeal C).hom X X
        change True
        trivial
    | succ n ih =>
        rw [pow_succ, CategoryTheory.End.mul_def]
        rw [HomIdeal.pow_succ_eq_mul_pow]
        exact HomIdeal.comp_mem_mul hf ih
  refine ⟨N, ?_⟩
  have h := hpow N
  rw [hN] at h
  change (CategoryTheory.End.of f) ^ N = 0 at h
  exact h

end NilpotentRadicalData

end MBDVendor.QSE.CategoricalRadical
