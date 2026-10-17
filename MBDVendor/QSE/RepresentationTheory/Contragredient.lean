import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The contragredient action on a vector-space dual

This is the concrete algebraic core used to instantiate `AlignedBiduality`
with `D = Hom_k(-, k)`.
-/

noncomputable section

namespace MBDVendor.QSE.Contragredient

universe uK uR uX

variable (K : Type uK) (R : Type uR) (X : Type uX)
  [Field K] [Ring R] [Algebra K R]
  [AddCommGroup X] [Module K X] [Module R X]
  [IsScalarTower K R X]

/-- The action of `Rᵐᵒᵖ` on the `K`-linear dual, encoded as a ring
homomorphism into the `K`-linear endomorphism ring. -/
def dualActionHom :
    Rᵐᵒᵖ →+* Module.End K (Module.Dual K X) where
  toFun r :=
    (Algebra.lsmul K K X r.unop).dualMap
  map_one' := by
    ext f x
    simp
  map_mul' r s := by
    ext f x
    simp [Algebra.lsmul_apply, smul_smul]
  map_zero' := by
    ext f x
    simp
  map_add' r s := by
    ext f x
    simp [Algebra.lsmul_apply]

@[simp]
theorem dualActionHom_apply
    (r : Rᵐᵒᵖ) (f : Module.Dual K X) (x : X) :
    dualActionHom K R X r f x = f (r.unop • x) :=
  rfl

/-- The resulting left `Rᵐᵒᵖ`-module structure on the dual. -/
@[reducible]
def dualModule : Module Rᵐᵒᵖ (Module.Dual K X) :=
  Module.compHom (Module.Dual K X) (dualActionHom K R X)

attribute [local instance] dualModule

/-- The contragredient action restricts to the original `K`-vector-space
structure. -/
theorem dualIsScalarTower :
    IsScalarTower K Rᵐᵒᵖ (Module.Dual K X) :=
  IsScalarTower.of_algebraMap_smul fun k f ↦ by
    ext x
    change f ((algebraMap K R k) • x) = k * f x
    rw [IsScalarTower.algebraMap_smul R k x, map_smul]
    rfl

attribute [local instance] dualIsScalarTower

/-- A finite-dimensional vector-space dual is finitely generated over the
opposite algebra. -/
theorem dual_finite_of_finiteDimensional
    [FiniteDimensional K X] :
    Module.Finite Rᵐᵒᵖ (Module.Dual K X) :=
  Module.Finite.of_restrictScalars_finite K Rᵐᵒᵖ
    (Module.Dual K X)

variable {K R X}
  {Y : Type*} [AddCommGroup Y] [Module K Y] [Module R Y]
  [IsScalarTower K R Y]

/-- The ordinary `K`-linear dual map is linear for the contragredient
`Rᵐᵒᵖ`-actions. -/
def dualMap (g : X →ₗ[R] Y) :
    Module.Dual K Y →ₗ[Rᵐᵒᵖ] Module.Dual K X where
  toFun := (g.restrictScalars K).dualMap
  map_add' := by
    intro f₁ f₂
    rfl
  map_smul' := by
    intro r f
    ext x
    change f (r.unop • g x) = f (g (r.unop • x))
    rw [g.map_smul]

@[simp]
theorem dualMap_apply (g : X →ₗ[R] Y)
    (f : Module.Dual K Y) (x : X) :
    dualMap g f x = f (g x) :=
  rfl

variable (K R) [FiniteDimensional K R]

/-- On a finite-dimensional algebra, the contragredient dual of every
finitely generated module is again a finitely generated module over the
opposite algebra. -/
def dualFGObj (M : FGModuleCat.{uX} R) :
    FGModuleCat.{max uK uX} Rᵐᵒᵖ := by
  letI : Module K M := Module.restrictScalars K R M
  letI : IsScalarTower K R M :=
    IsScalarTower.restrictScalars K R M
  letI : FiniteDimensional K M :=
    Module.Finite.trans R M
  letI : Module Rᵐᵒᵖ (Module.Dual K M) :=
    dualModule K R M
  letI : IsScalarTower K Rᵐᵒᵖ (Module.Dual K M) :=
    dualIsScalarTower K R M
  letI : Module.Finite Rᵐᵒᵖ (Module.Dual K M) :=
    dual_finite_of_finiteDimensional K R M
  exact FGModuleCat.of Rᵐᵒᵖ (Module.Dual K M)

end MBDVendor.QSE.Contragredient
