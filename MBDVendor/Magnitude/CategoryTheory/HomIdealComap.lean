import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.Submodule.Basic
import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Pullback of categorical Hom ideals

An additive functor pulls a two-sided additive Hom ideal back along its Hom
maps.  Ideal powers in the pullback map into the corresponding powers
downstairs.  For a fully faithful additive functor, categorical-radical
membership is equivalent before and after applying the functor.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MBDVendor.QSE.CategoricalIdeal.HomIdeal

universe u v w

variable {C : Type u} {D : Type v}
variable [Category.{w} C] [Category.{w} D] [Preadditive C] [Preadditive D]

/-- Pull a Hom ideal back along an additive functor. -/
def comap (F : C ⥤ D) [F.Additive] (I : HomIdeal D) : HomIdeal C where
  hom X Y :=
    { carrier := {f | F.map f ∈ I.hom (F.obj X) (F.obj Y)}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        simpa using (I.hom (F.obj X) (F.obj Y)).add_mem hf hg
      neg_mem' := by
        intro f hf
        simpa using (I.hom (F.obj X) (F.obj Y)).neg_mem hf }
  precomp := by
    intro X Y Z f g hg
    show F.map (f ≫ g) ∈ I.hom (F.obj X) (F.obj Z)
    simpa only [F.map_comp] using I.precomp (F.map f) hg
  postcomp := by
    intro X Y Z f g hf
    show F.map (f ≫ g) ∈ I.hom (F.obj X) (F.obj Z)
    simpa only [F.map_comp] using I.postcomp (F.map g) hf

@[simp]
theorem mem_comap_iff (F : C ⥤ D) [F.Additive] (I : HomIdeal D)
    {X Y : C} (f : X ⟶ Y) :
    f ∈ (comap F I).hom X Y ↔
      F.map f ∈ I.hom (F.obj X) (F.obj Y) :=
  Iff.rfl

/-- A morphism in a power of a pulled-back ideal maps into the same power of
the original ideal. -/
theorem map_mem_pow_of_mem_comap_pow
    (F : C ⥤ D) [F.Additive] (I : HomIdeal D) :
    ∀ (n : ℕ) {X Y : C} {f : X ⟶ Y},
      f ∈ ((comap F I).pow n).hom X Y →
        F.map f ∈ (I.pow n).hom (F.obj X) (F.obj Y) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro X Z f hf
      rw [pow_succ] at hf ⊢
      induction hf using AddSubgroup.closure_induction with
      | mem f hf =>
          obtain ⟨Y, a, b, ha, hb, rfl⟩ := hf
          rw [F.map_comp]
          exact comp_mem_mul (ih ha) hb
      | zero => simp
      | add f g _ _ hf hg =>
          simpa using add_mem hf hg
      | neg f _ hf =>
          simpa using neg_mem hf

/-- Powers of a Hom ideal add their exponents under ideal multiplication. -/
theorem pow_add (I : HomIdeal C) (m n : ℕ) :
    I.pow (m + n) = I.pow m ⋆ᵢ I.pow n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, pow_succ, ih, pow_succ, mul_assoc]

variable {k : Type*} [Semiring k] [Linear k C]

/-- A Hom ideal in a linear category, regarded pointwise as a linear
submodule. -/
def homSubmodule (I : HomIdeal C) (X Y : C) : Submodule k (X ⟶ Y) where
  carrier := {f | f ∈ I.hom X Y}
  zero_mem' := (I.hom X Y).zero_mem
  add_mem' := (I.hom X Y).add_mem
  smul_mem' := by
    intro c f hf
    have h := I.precomp (c • 𝟙 X) hf
    change c • f ∈ I.hom X Y
    simpa only [CategoryTheory.Linear.smul_comp, Category.id_comp] using h

@[simp]
theorem mem_homSubmodule_iff (I : HomIdeal C) (X Y : C) (f : X ⟶ Y) :
    f ∈ homSubmodule (k := k) I X Y ↔ f ∈ I.hom X Y :=
  Iff.rfl

end MBDVendor.QSE.CategoricalIdeal.HomIdeal

namespace MBDVendor.Magnitude

universe u v w

variable {C : Type u} {D : Type v}
variable [Category.{w} C] [Category.{w} D] [Preadditive C] [Preadditive D]

/-- A fully faithful additive functor preserves and reflects categorical
radical morphisms between objects in its image. -/
theorem isRadicalMorphism_iff_map_of_fullyFaithful
    (F : C ⥤ D) [F.Additive] (hF : F.FullyFaithful)
    {X Y : C} (f : X ⟶ Y) :
    MBDVendor.QSE.CategoricalRadical.IsRadicalMorphism f ↔
      MBDVendor.QSE.CategoricalRadical.IsRadicalMorphism
        (F.map f) := by
  letI : F.Full := hF.full
  letI : F.Faithful := hF.faithful
  constructor
  · intro hf g
    obtain ⟨g, rfl⟩ := F.map_surjective g
    haveI : IsIso (𝟙 X - f ≫ g) := hf g
    rw [← F.map_id, ← F.map_comp, ← F.map_sub]
    infer_instance
  · intro hf g
    haveI : IsIso (F.map (𝟙 X - f ≫ g)) := by
      rw [F.map_sub, F.map_id, F.map_comp]
      exact hf (F.map g)
    exact isIso_of_reflects_iso (𝟙 X - f ≫ g) F

end MBDVendor.Magnitude
