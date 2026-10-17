import MBDVendor.Magnitude.CategoryTheory.HomIdealComap
import MBDVendor.QSE.CategoryTheory.CategoricalRadicalIdeal
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The intrinsic linear space of irreducible morphisms -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.CategoricalRadical
namespace MBDVendor.Magnitude.CategoricalIrreducible
universe u v w
variable (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The intrinsic categorical radical as a linear subspace. -/
def radical (X Y : C) : Submodule k (X ⟶ Y) := HomIdeal.homSubmodule homIdeal X Y

/-- The square of the intrinsic radical as a linear subspace. -/
def radicalSquare (X Y : C) : Submodule k (X ⟶ Y) :=
  HomIdeal.homSubmodule (homIdeal ⋆ᵢ homIdeal) X Y

/-- The radical-square denominator inside the radical numerator. -/
def denominator (X Y : C) : Submodule k (radical k X Y) :=
  (radicalSquare k X Y).comap (radical k X Y).subtype

/-- The standard quotient `rad(X,Y) / rad²(X,Y)` in a linear category. -/
abbrev Space (X Y : C) := (radical k X Y) ⧸ denominator k X Y

/-- The irreducible quotient cannot have dimension larger than its Hom space. -/
theorem finrank_le_hom (X Y : C) [FiniteDimensional k (X ⟶ Y)] :
    Module.finrank k (Space k X Y) ≤ Module.finrank k (X ⟶ Y) :=
  (Submodule.finrank_quotient_le (denominator k X Y)).trans (Submodule.finrank_le _)

end MBDVendor.Magnitude.CategoricalIrreducible
