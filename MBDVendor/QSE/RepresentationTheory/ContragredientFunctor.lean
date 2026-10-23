module

public import MBDVendor.QSE.RepresentationTheory.Contragredient

/-!
# Categorical packaging of the contragredient dual
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace MBDVendor.QSE.Contragredient

universe uK uR uM

variable (K : Type uK) (R : Type uR)
  [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]

/-- The `K`-linear dual as a contravariant functor from finitely generated
`R`-modules to finitely generated `Rᵐᵒᵖ`-modules. -/
def dualFunctor :
    (FGModuleCat.{uM} R)ᵒᵖ ⥤
      FGModuleCat.{max uK uM} Rᵐᵒᵖ where
  obj M := dualFGObj K R M.unop
  map {M N} f := by
    letI : Module K M.unop :=
      Module.restrictScalars K R M.unop
    letI : IsScalarTower K R M.unop :=
      IsScalarTower.restrictScalars K R M.unop
    letI : FiniteDimensional K M.unop :=
      Module.Finite.trans R M.unop
    letI : Module K N.unop :=
      Module.restrictScalars K R N.unop
    letI : IsScalarTower K R N.unop :=
      IsScalarTower.restrictScalars K R N.unop
    letI : FiniteDimensional K N.unop :=
      Module.Finite.trans R N.unop
    letI : Module Rᵐᵒᵖ (Module.Dual K M.unop) :=
      dualModule K R M.unop
    letI : IsScalarTower K Rᵐᵒᵖ (Module.Dual K M.unop) :=
      dualIsScalarTower K R M.unop
    letI : Module.Finite Rᵐᵒᵖ (Module.Dual K M.unop) :=
      dual_finite_of_finiteDimensional K R M.unop
    letI : Module Rᵐᵒᵖ (Module.Dual K N.unop) :=
      dualModule K R N.unop
    letI : IsScalarTower K Rᵐᵒᵖ (Module.Dual K N.unop) :=
      dualIsScalarTower K R N.unop
    letI : Module.Finite Rᵐᵒᵖ (Module.Dual K N.unop) :=
      dual_finite_of_finiteDimensional K R N.unop
    exact FGModuleCat.ofHom
      (dualMap f.unop.hom.hom)
  map_id M := by
    apply FGModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    rfl

end MBDVendor.QSE.Contragredient
