module

public import MBDVendor.QSE.RepresentationTheory.Contragredient

/-!
# Linearity of finite-dimensional bidual evaluation

This verifies the load-bearing algebraic fact needed to turn the concrete
contragredient functor into an equivalence: after identifying `Rᵐᵒᵖᵐᵒᵖ`
with `R`, evaluation into the double dual is `R`-linear.
-/

@[expose] public section

noncomputable section

namespace MBDVendor.QSE.Contragredient

universe uK uR uX

variable (K : Type uK) (R : Type uR) (X : Type uX)
  [Field K] [Ring R] [Algebra K R]
  [AddCommGroup X] [Module K X] [Module R X]
  [IsScalarTower K R X]

attribute [local instance] dualModule dualIsScalarTower

/-- Regard the double contragredient dual as an `R`-module through the
canonical ring equivalence `R ≃+* Rᵐᵒᵖᵐᵒᵖ`. -/
@[reducible]
def bidualModule :
    Module R (Module.Dual K (Module.Dual K X)) :=
  Module.compHom (Module.Dual K (Module.Dual K X))
    (RingEquiv.opOp R).toRingHom

attribute [local instance] bidualModule

/-- Evaluation into the double contragredient dual is `R`-linear. -/
def bidualEval :
    X →ₗ[R] Module.Dual K (Module.Dual K X) where
  toFun := Module.Dual.eval K X
  map_add' := by
    intro x y
    exact map_add (Module.Dual.eval K X) x y
  map_smul' := by
    intro r x
    ext f
    rfl

@[simp]
theorem bidualEval_apply (x : X) (f : Module.Dual K X) :
    bidualEval K R X x f = f x :=
  rfl

/-- Finite-dimensional biduality, now bundled over the algebra rather than
only over the base field. -/
def bidualLinearEquiv [FiniteDimensional K X] :
    X ≃ₗ[R] Module.Dual K (Module.Dual K X) :=
  LinearEquiv.ofBijective (bidualEval K R X)
    (Module.bijective_dual_eval K X)

end MBDVendor.QSE.Contragredient
