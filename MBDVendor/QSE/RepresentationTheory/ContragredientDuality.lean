import MBDVendor.QSE.RepresentationTheory.ContragredientFunctor
import MBDVendor.QSE.RepresentationTheory.Biduality
import MBDVendor.QSE.RepresentationTheory.ContravariantTransport
import MBDVendor.QSE.RepresentationTheory.DualityConsequences

noncomputable section

open CategoryTheory

namespace MBDVendor.QSE.Contragredient

universe u v w

variable (K R : Type u)
  [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]

/-- Every bundled finitely generated module is canonically isomorphic to
the `FGModuleCat.of` object built from its carrier.  The two objects have
the same elements and action, but are not definitionally equal because an
arbitrary object retains its original `ModuleCat` wrapper. -/
def ofCarrierIso (M : FGModuleCat.{u} R) :
    M ≅ FGModuleCat.of R M where
  hom := ConcreteCategory.ofHom (LinearMap.id : M →ₗ[R] M)
  inv := ConcreteCategory.ofHom (LinearMap.id : M →ₗ[R] M)
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    rfl
  inv_hom_id := by
    apply FGModuleCat.hom_ext
    rfl

/-- The dual of an `Rᵐᵒᵖ`-module, regarded directly as an `R`-module. -/
@[reducible]
def dualOpModule
    (X : Type u) [AddCommGroup X] [Module K X] [Module Rᵐᵒᵖ X]
    [IsScalarTower K Rᵐᵒᵖ X] :
    Module R (Module.Dual K X) := by
  letI : Module (Rᵐᵒᵖ)ᵐᵒᵖ (Module.Dual K X) :=
    dualModule K Rᵐᵒᵖ X
  exact
    Module.compHom (Module.Dual K X)
      (RingEquiv.opOp R).toRingHom

attribute [local instance] dualOpModule

omit [FiniteDimensional K R] in
theorem dualOpIsScalarTower
    (X : Type u) [AddCommGroup X] [Module K X] [Module Rᵐᵒᵖ X]
    [IsScalarTower K Rᵐᵒᵖ X] :
    IsScalarTower K R (Module.Dual K X) :=
  IsScalarTower.of_algebraMap_smul fun k f ↦ by
    ext x
    change f ((algebraMap K Rᵐᵒᵖ k) • x) = k * f x
    rw [IsScalarTower.algebraMap_smul Rᵐᵒᵖ k x, map_smul]
    rfl

attribute [local instance] dualOpIsScalarTower

/-- The reverse contragredient object, with the canonical identification
`R ≃ Rᵐᵒᵖᵐᵒᵖ` built into its action. -/
def dualOpFGObj (M : FGModuleCat.{u} Rᵐᵒᵖ) :
    FGModuleCat.{u} R := by
  letI : Module K M := Module.restrictScalars K Rᵐᵒᵖ M
  letI : IsScalarTower K Rᵐᵒᵖ M :=
    IsScalarTower.restrictScalars K Rᵐᵒᵖ M
  letI : FiniteDimensional K M := Module.Finite.trans Rᵐᵒᵖ M
  letI : Module R (Module.Dual K M) := dualOpModule K R M
  letI : IsScalarTower K R (Module.Dual K M) :=
    dualOpIsScalarTower K R M
  letI : Module.Finite R (Module.Dual K M) :=
    Module.Finite.of_restrictScalars_finite K R (Module.Dual K M)
  exact FGModuleCat.of R (Module.Dual K M)

variable {K R}
  {X Y : Type u}
  [AddCommGroup X] [Module K X] [Module Rᵐᵒᵖ X]
  [IsScalarTower K Rᵐᵒᵖ X]
  [AddCommGroup Y] [Module K Y] [Module Rᵐᵒᵖ Y]
  [IsScalarTower K Rᵐᵒᵖ Y]

/-- The dual map, with source and target regarded as `R`-modules. -/
def dualOpMap (g : X →ₗ[Rᵐᵒᵖ] Y) :
    Module.Dual K Y →ₗ[R] Module.Dual K X where
  toFun := (g.restrictScalars K).dualMap
  map_add' := by
    intro f₁ f₂
    rfl
  map_smul' := by
    intro r f
    ext x
    change f ((MulOpposite.op r) • g x) =
      f (g ((MulOpposite.op r) • x))
    rw [g.map_smul]

variable (K R)

/-- The reverse contragredient functor. -/
def reverseDualFunctor :
    (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ⥤ FGModuleCat.{u} R where
  obj M := dualOpFGObj K R M.unop
  map {M N} f := by
    letI : Module K M.unop :=
      Module.restrictScalars K Rᵐᵒᵖ M.unop
    letI : IsScalarTower K Rᵐᵒᵖ M.unop :=
      IsScalarTower.restrictScalars K Rᵐᵒᵖ M.unop
    letI : FiniteDimensional K M.unop :=
      Module.Finite.trans Rᵐᵒᵖ M.unop
    letI : Module K N.unop :=
      Module.restrictScalars K Rᵐᵒᵖ N.unop
    letI : IsScalarTower K Rᵐᵒᵖ N.unop :=
      IsScalarTower.restrictScalars K Rᵐᵒᵖ N.unop
    letI : FiniteDimensional K N.unop :=
      Module.Finite.trans Rᵐᵒᵖ N.unop
    letI : Module R (Module.Dual K M.unop) :=
      dualOpModule K R M.unop
    letI : IsScalarTower K R (Module.Dual K M.unop) :=
      dualOpIsScalarTower K R M.unop
    letI : Module.Finite R (Module.Dual K M.unop) :=
      Module.Finite.of_restrictScalars_finite K R
        (Module.Dual K M.unop)
    letI : Module R (Module.Dual K N.unop) :=
      dualOpModule K R N.unop
    letI : IsScalarTower K R (Module.Dual K N.unop) :=
      dualOpIsScalarTower K R N.unop
    letI : Module.Finite R (Module.Dual K N.unop) :=
      Module.Finite.of_restrictScalars_finite K R
        (Module.Dual K N.unop)
    exact FGModuleCat.ofHom (dualOpMap f.unop.hom.hom)
  map_id M := by
    apply FGModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    rfl

local instance moduleKOfFGModule
    (M : FGModuleCat.{u} R) : Module K M :=
  Module.restrictScalars K R M

local instance moduleKOfFGModuleOp
    (M : FGModuleCat.{u} Rᵐᵒᵖ) : Module K M :=
  Module.restrictScalars K Rᵐᵒᵖ M

local instance towerKROfFGModule
    (M : FGModuleCat.{u} R) : IsScalarTower K R M :=
  IsScalarTower.restrictScalars K R M

local instance towerKROfFGModuleOp
    (M : FGModuleCat.{u} Rᵐᵒᵖ) :
    IsScalarTower K Rᵐᵒᵖ M :=
  IsScalarTower.restrictScalars K Rᵐᵒᵖ M

/-- The `K`-module on the forward contragredient object, obtained by
restricting its `Rᵐᵒᵖ`-action, is canonically the ordinary `K`-linear
dual.  The underlying function is the identity; the proof records the
non-definitional scalar-action comparison. -/
def forwardInnerDualEquiv (M : FGModuleCat.{u} R) :
    ((dualFunctor K R).obj (Opposite.op M) : Type u) ≃ₗ[K]
      Module.Dual K M where
  toFun := fun f ↦ f
  invFun := fun f ↦ f
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro k f
    change Module.Dual K M at f
    ext x
    change f ((algebraMap K Rᵐᵒᵖ k).unop • x) = k * f x
    rw [show (algebraMap K Rᵐᵒᵖ k).unop =
      algebraMap K R k by rfl]
    rw [IsScalarTower.algebraMap_smul R k x, map_smul]
    rfl
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- As plain types, the concrete forward-then-reverse object is the usual
double dual after correcting the inner restricted-scalar structure. -/
def forwardCanonicalToCompositeEquiv
    (M : FGModuleCat.{u} R) :
    Module.Dual K (Module.Dual K M) ≃
      (reverseDualFunctor K R).obj
        (Opposite.op
          ((dualFunctor K R).obj (Opposite.op M))) :=
  (forwardInnerDualEquiv K R M).dualMap.toEquiv

/-- Evaluation into the actual forward-then-reverse object, linear over
`R`. -/
def forwardBidualMap (M : FGModuleCat.{u} R) :
    M →ₗ[R]
      (reverseDualFunctor K R).obj
        (Opposite.op
          ((dualFunctor K R).obj (Opposite.op M))) where
  toFun x := by
    change
      Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M))
    exact
      (Module.Dual.eval K M x).comp
        (forwardInnerDualEquiv K R M).toLinearMap
  map_add' := by
    intro x y
    change
      (show Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M)) from
          (Module.Dual.eval K M (x + y)).comp
            (forwardInnerDualEquiv K R M).toLinearMap) =
      (show Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M)) from
          (Module.Dual.eval K M x).comp
              (forwardInnerDualEquiv K R M).toLinearMap +
            (Module.Dual.eval K M y).comp
              (forwardInnerDualEquiv K R M).toLinearMap)
    ext f
    simp
  map_smul' := by
    intro r x
    change
      (show Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M)) from
          (Module.Dual.eval K M (r • x)).comp
            (forwardInnerDualEquiv K R M).toLinearMap) =
      (show Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M)) from
          r •
            (Module.Dual.eval K M x).comp
              (forwardInnerDualEquiv K R M).toLinearMap)
    ext f
    rfl

/-- The concrete evaluation map is bijective.  The proof factors its
underlying function through ordinary finite-dimensional biduality and the
restricted-scalar correction above. -/
theorem forwardBidualMap_bijective (M : FGModuleCat.{u} R) :
    Function.Bijective (forwardBidualMap K R M) := by
  letI : FiniteDimensional K M := Module.Finite.trans R M
  let e := forwardCanonicalToCompositeEquiv K R M
  have hcomp :
      (e : Module.Dual K (Module.Dual K M) →
        (reverseDualFunctor K R).obj
          (Opposite.op
            ((dualFunctor K R).obj (Opposite.op M)))) ∘
          (bidualEval K R M : M →
            Module.Dual K (Module.Dual K M)) =
        (forwardBidualMap K R M : M →
          (reverseDualFunctor K R).obj
            (Opposite.op
              ((dualFunctor K R).obj (Opposite.op M)))) := by
    funext x
    change
      (show Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M)) from
          e (bidualEval K R M x)) =
      (show Module.Dual K
        ((dualFunctor K R).obj (Opposite.op M)) from
          (Module.Dual.eval K M x).comp
            (forwardInnerDualEquiv K R M).toLinearMap)
    ext f
    rfl
  rw [← hcomp]
  exact e.bijective.comp (Module.bijective_dual_eval K M)

/-- Evaluation as an `R`-linear equivalence with the actual composite
object. -/
def forwardBidualLinearEquiv (M : FGModuleCat.{u} R) :
    M ≃ₗ[R]
      (reverseDualFunctor K R).obj
        (Opposite.op
          ((dualFunctor K R).obj (Opposite.op M))) :=
  LinearEquiv.ofBijective (forwardBidualMap K R M)
    (forwardBidualMap_bijective K R M)

/-- Turn a linear equivalence between the carriers of two arbitrary
`FGModuleCat` objects into a categorical isomorphism, without replacing
either object by an `FGModuleCat.of` wrapper. -/
def fgModuleIsoOfLinearEquiv
    {M N : FGModuleCat.{u} R} (e : M ≃ₗ[R] N) :
    M ≅ N where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    ext x
    exact e.left_inv x
  inv_hom_id := by
    apply FGModuleCat.hom_ext
    ext x
    exact e.right_inv x

/-- Objectwise biduality for the forward-then-reverse composite. -/
def forwardBidualIso (M : FGModuleCat.{u} R) :
    M ≅
      (reverseDualFunctor K R).obj
        (Opposite.op ((dualFunctor K R).obj (Opposite.op M))) := by
  exact fgModuleIsoOfLinearEquiv R
    (forwardBidualLinearEquiv K R M)

/-- The covariant forward-then-reverse double-dual functor. -/
def forwardDoubleDualFunctor :
    FGModuleCat.{u} R ⥤ FGModuleCat.{u} R :=
  (dualFunctor K R).rightOp ⋙ reverseDualFunctor K R

/-- Finite-dimensional bidual evaluation is natural for the concrete
forward-then-reverse functor. -/
def forwardBidualNatIso :
    𝟭 (FGModuleCat.{u} R) ≅
      forwardDoubleDualFunctor K R :=
  NatIso.ofComponents
    (forwardBidualIso K R)
    (fun {M N} f ↦ by
      apply FGModuleCat.hom_ext
      rfl)

/-- The reverse contragredient object has the ordinary `K`-linear dual as
its underlying `K`-module after comparing its `K`-action restricted from
`R` with the canonical action. -/
def reverseInnerDualEquiv (N : FGModuleCat.{u} Rᵐᵒᵖ) :
    ((reverseDualFunctor K R).obj (Opposite.op N) : Type u) ≃ₗ[K]
      Module.Dual K N where
  toFun := fun f ↦ f
  invFun := fun f ↦ f
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro k f
    change Module.Dual K N at f
    ext x
    change
      f (MulOpposite.op (algebraMap K R k) • x) =
        k * f x
    rw [show MulOpposite.op (algebraMap K R k) =
      algebraMap K Rᵐᵒᵖ k by rfl]
    rw [IsScalarTower.algebraMap_smul Rᵐᵒᵖ k x, map_smul]
    rfl
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- As plain types, the reverse-then-forward object is the usual double
dual after correcting the inner restricted-scalar structure. -/
def reverseCanonicalToCompositeEquiv
    (N : FGModuleCat.{u} Rᵐᵒᵖ) :
    Module.Dual K (Module.Dual K N) ≃
      (dualFunctor K R).obj
        (Opposite.op
          ((reverseDualFunctor K R).obj (Opposite.op N))) :=
  (reverseInnerDualEquiv K R N).dualMap.toEquiv

/-- Evaluation into the actual reverse-then-forward object, linear over
`Rᵐᵒᵖ`. -/
def reverseBidualMap (N : FGModuleCat.{u} Rᵐᵒᵖ) :
    N →ₗ[Rᵐᵒᵖ]
      (dualFunctor K R).obj
        (Opposite.op
          ((reverseDualFunctor K R).obj (Opposite.op N))) where
  toFun x := by
    change
      Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N))
    exact
      (Module.Dual.eval K N x).comp
        (reverseInnerDualEquiv K R N).toLinearMap
  map_add' := by
    intro x y
    change
      (show Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N)) from
          (Module.Dual.eval K N (x + y)).comp
            (reverseInnerDualEquiv K R N).toLinearMap) =
      (show Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N)) from
          (Module.Dual.eval K N x).comp
              (reverseInnerDualEquiv K R N).toLinearMap +
            (Module.Dual.eval K N y).comp
              (reverseInnerDualEquiv K R N).toLinearMap)
    ext f
    simp
  map_smul' := by
    intro r x
    letI : Module Rᵐᵒᵖ
        (Module.Dual K
          ((reverseDualFunctor K R).obj (Opposite.op N))) :=
      dualModule K R
        ((reverseDualFunctor K R).obj (Opposite.op N))
    change
      (show Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N)) from
          (Module.Dual.eval K N (r • x)).comp
            (reverseInnerDualEquiv K R N).toLinearMap) =
      (show Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N)) from
          r •
            ((Module.Dual.eval K N x).comp
              (reverseInnerDualEquiv K R N).toLinearMap :
                Module.Dual K
                  ((reverseDualFunctor K R).obj
                    (Opposite.op N))))
    ext f
    rfl

/-- The reverse concrete evaluation map is bijective. -/
theorem reverseBidualMap_bijective
    (N : FGModuleCat.{u} Rᵐᵒᵖ) :
    Function.Bijective (reverseBidualMap K R N) := by
  letI : FiniteDimensional K N := Module.Finite.trans Rᵐᵒᵖ N
  let e := reverseCanonicalToCompositeEquiv K R N
  have hcomp :
      (e : Module.Dual K (Module.Dual K N) →
        (dualFunctor K R).obj
          (Opposite.op
            ((reverseDualFunctor K R).obj (Opposite.op N)))) ∘
          (Module.Dual.eval K N : N →
            Module.Dual K (Module.Dual K N)) =
        (reverseBidualMap K R N : N →
          (dualFunctor K R).obj
            (Opposite.op
              ((reverseDualFunctor K R).obj
                (Opposite.op N)))) := by
    funext x
    change
      (show Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N)) from
          e (Module.Dual.eval K N x)) =
      (show Module.Dual K
        ((reverseDualFunctor K R).obj (Opposite.op N)) from
          (Module.Dual.eval K N x).comp
            (reverseInnerDualEquiv K R N).toLinearMap)
    ext f
    rfl
  rw [← hcomp]
  exact e.bijective.comp (Module.bijective_dual_eval K N)

/-- Reverse evaluation as an `Rᵐᵒᵖ`-linear equivalence. -/
def reverseBidualLinearEquiv
    (N : FGModuleCat.{u} Rᵐᵒᵖ) :
    N ≃ₗ[Rᵐᵒᵖ]
      (dualFunctor K R).obj
        (Opposite.op
          ((reverseDualFunctor K R).obj (Opposite.op N))) :=
  LinearEquiv.ofBijective (reverseBidualMap K R N)
    (reverseBidualMap_bijective K R N)

/-- Objectwise biduality for the reverse-then-forward composite. -/
def reverseBidualIso (N : FGModuleCat.{u} Rᵐᵒᵖ) :
    N ≅
      (dualFunctor K R).obj
        (Opposite.op
          ((reverseDualFunctor K R).obj (Opposite.op N))) :=
  fgModuleIsoOfLinearEquiv Rᵐᵒᵖ
    (reverseBidualLinearEquiv K R N)

/-- The covariant reverse-then-forward double-dual functor. -/
def reverseDoubleDualFunctor :
    FGModuleCat.{u} Rᵐᵒᵖ ⥤ FGModuleCat.{u} Rᵐᵒᵖ :=
  (reverseDualFunctor K R).rightOp ⋙ dualFunctor K R

/-- Reverse bidual evaluation is natural. -/
def reverseBidualNatIso :
    𝟭 (FGModuleCat.{u} Rᵐᵒᵖ) ≅
      reverseDoubleDualFunctor K R :=
  NatIso.ofComponents
    (reverseBidualIso K R)
    (fun {M N} f ↦ by
      apply FGModuleCat.hom_ext
      rfl)

/-- The forward bidual natural isomorphism, viewed on the opposite
category in the orientation required for a categorical equivalence. -/
def oppositeForwardBidualNatIso :
    𝟭 ((FGModuleCat.{u} R)ᵒᵖ) ≅
      dualFunctor K R ⋙ (reverseDualFunctor K R).rightOp :=
  (NatIso.op (forwardBidualNatIso K R)).symm

/-- Same-universe contragredient duality between the opposite category of
finitely generated `R`-modules and finitely generated
`Rᵐᵒᵖ`-modules.  `Equivalence.mk` adjointifies the supplied unit, so no
additional choice-dependent triangle calculation is needed. -/
noncomputable def dualityEquivalence :
    (FGModuleCat.{u} R)ᵒᵖ ≌ FGModuleCat.{u} Rᵐᵒᵖ :=
  CategoryTheory.Equivalence.mk
    (dualFunctor K R)
    (reverseDualFunctor K R).rightOp
    (oppositeForwardBidualNatIso K R)
    (reverseBidualNatIso K R).symm

/-- The reverse same-universe equivalence, with the concrete reverse dual
as its forward functor. -/
noncomputable def reverseDualityEquivalence :
    (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R :=
  CategoryTheory.Equivalence.mk
    (reverseDualFunctor K R)
    (dualFunctor K R).rightOp
    (NatIso.op (reverseBidualNatIso K R)).symm
    (forwardBidualNatIso K R).symm

/-- An anti-equivalence of finitely generated module categories preserves
the project foundation's module-level indecomposability predicate. -/
theorem indecomposable_map_anti
    {S : Type u} [Ring S]
    (E : (FGModuleCat.{u} R)ᵒᵖ ≌ FGModuleCat.{u} S)
    {M : FGModuleCat.{u} R}
    (hM : MBDVendor.QSE.Foundation.IsIndecomposableModule R M) :
    MBDVendor.QSE.Foundation.IsIndecomposableModule S
      (E.functor.obj (Opposite.op M)) := by
  rw [MBDVendor.QSE.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · by_contra h
    letI : Subsingleton (E.functor.obj (Opposite.op M)) :=
      not_nontrivial_iff_subsingleton.mp h
    have htarget :
        (𝟙 (E.functor.obj (Opposite.op M)) :
          E.functor.obj (Opposite.op M) ⟶
            E.functor.obj (Opposite.op M)) = 0 := by
      apply FGModuleCat.hom_ext
      ext x
      exact Subsingleton.elim _ _
    have hsourceOp :
        (𝟙 (Opposite.op M) :
          Opposite.op M ⟶ Opposite.op M) = 0 := by
      apply E.functor.map_injective
      simpa using htarget
    have hsource : (𝟙 M : M ⟶ M) = 0 := by
      apply Quiver.Hom.op_inj
      simpa using hsourceOp
    letI : Nontrivial M := hM.nontrivial
    have hend : (1 : Module.End R M) = 0 := by
      have hlinear :=
        congrArg (fun f : M ⟶ M ↦ f.hom.hom) hsource
      simpa [Module.End.one_eq_id] using hlinear
    exact one_ne_zero hend
  · intro f hf
    let fcat :
        E.functor.obj (Opposite.op M) ⟶
          E.functor.obj (Opposite.op M) :=
      FGModuleCat.ofHom f
    have fcat_apply (x : E.functor.obj (Opposite.op M)) :
        fcat.hom.hom x = f x :=
      rfl
    let gop : Opposite.op M ⟶ Opposite.op M :=
      E.functor.preimage fcat
    let g : Module.End R M :=
      gop.unop.hom.hom
    have hcat : gop ≫ gop = gop := by
      apply E.functor.map_injective
      rw [E.functor.map_comp]
      change
        E.functor.map (E.functor.preimage fcat) ≫
            E.functor.map (E.functor.preimage fcat) =
          E.functor.map (E.functor.preimage fcat)
      rw [E.functor.map_preimage fcat]
      apply FGModuleCat.hom_ext
      change f.comp f = f
      change f * f = f at hf
      simpa [Module.End.mul_eq_comp] using hf
    have hg : IsIdempotentElem g := by
      change g * g = g
      have hlinear :=
        congrArg
          (fun q : Opposite.op M ⟶ Opposite.op M ↦
            q.unop.hom.hom) hcat
      simpa [g, Module.End.mul_eq_comp] using hlinear
    rcases
        hM.eq_zero_or_eq_one_of_isIdempotentElem hg with
      hg | hg
    · left
      have hgcat : gop = 0 := by
        apply Quiver.Hom.unop_inj
        apply FGModuleCat.hom_ext
        exact hg
      have hfcat : fcat = 0 := by
        calc
          fcat = E.functor.map gop :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map 0 :=
            congrArg E.functor.map hgcat
          _ = 0 :=
            E.functor.map_zero (Opposite.op M) (Opposite.op M)
      ext x
      have hx :=
        congrArg
          (fun q :
            E.functor.obj (Opposite.op M) ⟶
              E.functor.obj (Opposite.op M) ↦ q.hom.hom x)
          hfcat
      rw [fcat_apply] at hx
      simpa using hx
    · right
      have hgcat : gop = 𝟙 (Opposite.op M) := by
        apply Quiver.Hom.unop_inj
        apply FGModuleCat.hom_ext
        simpa [g, Module.End.one_eq_id] using hg
      have hfcat :
          fcat = 𝟙 (E.functor.obj (Opposite.op M)) := by
        calc
          fcat = E.functor.map gop :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map (𝟙 (Opposite.op M)) :=
            congrArg E.functor.map hgcat
          _ = 𝟙 (E.functor.obj (Opposite.op M)) :=
            E.functor.map_id (Opposite.op M)
      ext x
      have hx :=
        congrArg
          (fun q :
            E.functor.obj (Opposite.op M) ⟶
              E.functor.obj (Opposite.op M) ↦ q.hom.hom x)
          hfcat
      rw [fcat_apply] at hx
      simpa [Module.End.one_eq_id] using hx

/-- Contragredient duality preserves indecomposability in the forward
direction. -/
theorem dualFunctor_indec
    {M : FGModuleCat.{u} R}
    (hM : MBDVendor.QSE.Foundation.IsIndecomposableModule R M) :
    MBDVendor.QSE.Foundation.IsIndecomposableModule Rᵐᵒᵖ
      ((dualFunctor K R).obj (Opposite.op M)) :=
  indecomposable_map_anti R (dualityEquivalence K R) hM

/-- Contragredient duality preserves indecomposability in the reverse
direction. -/
theorem reverseDualFunctor_indec
    {N : FGModuleCat.{u} Rᵐᵒᵖ}
    (hN : MBDVendor.QSE.Foundation.IsIndecomposableModule Rᵐᵒᵖ N) :
    MBDVendor.QSE.Foundation.IsIndecomposableModule R
      ((reverseDualFunctor K R).obj (Opposite.op N)) :=
  indecomposable_map_anti Rᵐᵒᵖ
    (reverseDualityEquivalence K R) hN

section SkeletonAlignment

variable [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} {κ : Type w}
  (σ : MBDVendor.QSE.IndecomposableSkeleton.{u, v, u} R ι)
  (τ : MBDVendor.QSE.IndecomposableSkeleton.{u, w, u} Rᵐᵒᵖ κ)

/-- The target label selected for the dual of a source representative. -/
def dualMapLabel (i : ι) : κ :=
  Classical.choose
    (τ.complete
      ((dualFunctor K R).obj (Opposite.op (σ.obj i)))
      (dualFunctor_indec K R (σ.indecomposable i)))

/-- The chosen target representative is isomorphic to the forward dual. -/
def dualMapObjIso (i : ι) :
    (dualFunctor K R).obj (Opposite.op (σ.obj i)) ≅
      τ.obj (dualMapLabel K R σ τ i) :=
  Classical.choice
    (Classical.choose_spec
      (τ.complete
        ((dualFunctor K R).obj (Opposite.op (σ.obj i)))
        (dualFunctor_indec K R (σ.indecomposable i))))

/-- The source label selected for the reverse dual of a target
representative. -/
def reverseMapLabel (j : κ) : ι :=
  Classical.choose
    (σ.complete
      ((reverseDualFunctor K R).obj (Opposite.op (τ.obj j)))
      (reverseDualFunctor_indec K R (τ.indecomposable j)))

/-- The chosen source representative is isomorphic to the reverse dual. -/
def reverseMapObjIso (j : κ) :
    (reverseDualFunctor K R).obj (Opposite.op (τ.obj j)) ≅
      σ.obj (reverseMapLabel K R σ τ j) :=
  Classical.choice
    (Classical.choose_spec
      (σ.complete
        ((reverseDualFunctor K R).obj (Opposite.op (τ.obj j)))
        (reverseDualFunctor_indec K R (τ.indecomposable j))))

/-- Forward and reverse label selection compose to the identity on the
source skeleton. -/
theorem reverseMapLabel_dualMapLabel (i : ι) :
    reverseMapLabel K R σ τ (dualMapLabel K R σ τ i) = i := by
  apply σ.eq_of_iso
  exact ⟨
    (reverseMapObjIso K R σ τ
        (dualMapLabel K R σ τ i)).symm ≪≫
      (reverseDualFunctor K R).mapIso
        (dualMapObjIso K R σ τ i).op ≪≫
      (forwardBidualIso K R (σ.obj i)).symm⟩

/-- Forward and reverse label selection compose to the identity on the
target skeleton. -/
theorem dualMapLabel_reverseMapLabel (j : κ) :
    dualMapLabel K R σ τ (reverseMapLabel K R σ τ j) = j := by
  apply τ.eq_of_iso
  exact ⟨
    (dualMapObjIso K R σ τ
        (reverseMapLabel K R σ τ j)).symm ≪≫
      (dualFunctor K R).mapIso
        (reverseMapObjIso K R σ τ j).op ≪≫
      (reverseBidualIso K R (τ.obj j)).symm⟩

/-- The induced equivalence of arbitrary complete duplicate-free chosen
indecomposable skeletons. -/
def dualLabelEquiv : ι ≃ κ where
  toFun := dualMapLabel K R σ τ
  invFun := reverseMapLabel K R σ τ
  left_inv := reverseMapLabel_dualMapLabel K R σ τ
  right_inv := dualMapLabel_reverseMapLabel K R σ τ

/-- The concrete duality aligned with the two chosen skeletons. -/
noncomputable def alignedBiduality :
    MBDVendor.QSE.IndecomposableSkeleton.AlignedBiduality σ τ where
  forward :=
    { categoryEquiv := dualityEquivalence K R
      labelEquiv := dualLabelEquiv K R σ τ
      objIso := dualMapObjIso K R σ τ }
  backward :=
    { categoryEquiv := reverseDualityEquivalence K R
      labelEquiv := (dualLabelEquiv K R σ τ).symm
      objIso := reverseMapObjIso K R σ τ }
  backward_label := rfl

end SkeletonAlignment

end MBDVendor.QSE.Contragredient
