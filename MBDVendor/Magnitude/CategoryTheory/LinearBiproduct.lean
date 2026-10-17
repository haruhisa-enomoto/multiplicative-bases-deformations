import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear Hom spaces and finite biproducts

Small reusable linear-algebra interfaces for passing between morphisms into a
finite biproduct and the family of their components.  They are used to turn a
chosen Krull--Schmidt middle-term decomposition into the corresponding Hom-
dimension sum.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace MBDVendor.Magnitude.CategoryTheory

universe s v u w

variable (k : Type s) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasFiniteBiproducts C]
variable {J : Type w} [Fintype J]

/-- A morphism into a finite biproduct is linearly equivalent to its family of
components. -/
def homBiproductLinearEquiv (X : C) (F : J → C) :
    (X ⟶ ⨁ F) ≃ₗ[k] (∀ j, X ⟶ F j) where
  toFun f j := f ≫ biproduct.π F j
  invFun f := biproduct.lift f
  left_inv f := by
    apply biproduct.hom_ext
    intro j
    simp
  right_inv f := by
    funext j
    simp
  map_add' f g := by
    funext j
    simp
  map_smul' r f := by
    funext j
    simp

/-- Transport the component equivalence across an isomorphism with a finite
biproduct. -/
def homBiproductLinearEquivOfIso (X Y : C) (F : J → C)
    (e : Y ≅ ⨁ F) :
    (X ⟶ Y) ≃ₗ[k] (∀ j, X ⟶ F j) :=
  (CategoryTheory.Linear.homCongr k (Iso.refl X) e).trans
    (homBiproductLinearEquiv k X F)

/-- A morphism from a finite biproduct is linearly equivalent to its family
of restrictions to the summands. -/
def biproductHomLinearEquiv (Y : C) (F : J → C) :
    ((⨁ F) ⟶ Y) ≃ₗ[k] (∀ j, F j ⟶ Y) where
  toFun f j := biproduct.ι F j ≫ f
  invFun f := biproduct.desc f
  left_inv f := by
    apply biproduct.hom_ext'
    intro j
    simp
  right_inv f := by
    funext j
    simp
  map_add' f g := by
    funext j
    simp
  map_smul' r f := by
    funext j
    simp

/-- Transport the summand-restriction equivalence across an isomorphism with
a finite biproduct. -/
def biproductHomLinearEquivOfIso (X Y : C) (F : J → C)
    (e : X ≅ ⨁ F) :
    (X ⟶ Y) ≃ₗ[k] (∀ j, F j ⟶ Y) :=
  (CategoryTheory.Linear.homCongr k e (Iso.refl Y)).trans
    (biproductHomLinearEquiv k Y F)

/-- Hom dimension into a displayed finite biproduct is the sum of the Hom
dimensions into its summands. -/
theorem finrank_hom_eq_sum_of_iso_biproduct
    (X Y : C) (F : J → C) (e : Y ≅ ⨁ F)
    [FiniteDimensional k (X ⟶ Y)]
    [∀ j, FiniteDimensional k (X ⟶ F j)] :
    Module.finrank k (X ⟶ Y) =
      ∑ j, Module.finrank k (X ⟶ F j) := by
  calc
    Module.finrank k (X ⟶ Y) =
        Module.finrank k (∀ j, X ⟶ F j) :=
      (homBiproductLinearEquivOfIso k X Y F e).finrank_eq
    _ = ∑ j, Module.finrank k (X ⟶ F j) :=
      Module.finrank_pi_fintype k

/-- Hom dimension from a displayed finite biproduct is the sum of the Hom
dimensions from its summands. -/
theorem finrank_hom_eq_sum_of_biproduct_iso
    (X Y : C) (F : J → C) (e : X ≅ ⨁ F)
    [FiniteDimensional k (X ⟶ Y)]
    [∀ j, FiniteDimensional k (F j ⟶ Y)] :
    Module.finrank k (X ⟶ Y) =
      ∑ j, Module.finrank k (F j ⟶ Y) := by
  calc
    Module.finrank k (X ⟶ Y) =
      Module.finrank k (∀ j, F j ⟶ Y) :=
      (biproductHomLinearEquivOfIso k X Y F e).finrank_eq
    _ = ∑ j, Module.finrank k (F j ⟶ Y) :=
      Module.finrank_pi_fintype k

/-- Split a selected summand out of a finite biproduct, retaining the
remaining summands as a biproduct over the complementary subtype. -/
def biproductSplitAtIso (F : J → C) (i : J) :
    (⨁ F) ≅
      (⨁ Subtype.restrict (fun j ↦ j ≠ i) F) ⊞ F i where
  hom := biprod.lift
    (biproduct.toSubtype F (fun j ↦ j ≠ i))
    (biproduct.π F i)
  inv := biprod.desc
    (biproduct.fromSubtype F (fun j ↦ j ≠ i))
    (biproduct.ι F i)
  hom_inv_id := by
    classical
    apply biproduct.hom_ext
    intro j
    rw [biprod.lift_desc, Preadditive.add_comp,
      biproduct.toSubtype_fromSubtype, biproduct.map_π]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, Ne.symm hj]
  inv_hom_id := by
    classical
    apply biprod.hom_ext
    · apply biprod.hom_ext' <;> simp
    · apply biprod.hom_ext' <;> simp

end MBDVendor.Magnitude.CategoryTheory
