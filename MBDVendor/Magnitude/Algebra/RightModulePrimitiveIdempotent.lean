import MBDVendor.Magnitude.Algebra.RightModuleFactorStrict
import MBDVendor.QSE.RepresentationTheory.Trace
import Mathlib.LinearAlgebra.Projection

/-!
# The primitive-idempotent multiplicity package

(Extracted glue file: lines 1–1245 of the magnitude file of the same name;
see `MBDVendor/README.md`. The skeleton-specific remainder is not copied.)

For a primitive idempotent `e : A`, this file constructs the projective
right ideal `eA`, the injective right module `D(Ae)`, and the common
coordinate `Xe`.  Evaluation identifies `Hom_A(eA, X)` with `Xe`, while
duality identifies `Hom_A(X, D(Ae))` with `D(Xe)`.  On a finite
indecomposable skeleton these literal modules give the source, sink, and
weight satisfying both factor mesh unit equations used in the frozen
manuscript.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.Contragredient
open scoped ModuleCat.Algebra ZeroObject

namespace MBDVendor.Magnitude.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The right regular module is linearly equivalent to the regular module
over the opposite ring. -/
def rightRegularLinearEquiv : Aᵐᵒᵖ ≃ₗ[Aᵐᵒᵖ] A where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op

/-- Left multiplication by `e`, regarded as an endomorphism of the right
regular module. -/
def rightRegularLeftMul (e : A) : A →ₗ[Aᵐᵒᵖ] A where
  toFun a := e * a
  map_add' := mul_add e
  map_smul' := by
    intro r a
    change e * (a * r.unop) = (e * a) * r.unop
    exact (mul_assoc e a r.unop).symm

@[simp]
theorem rightRegularLeftMul_apply (e a : A) :
    rightRegularLeftMul e a = e * a :=
  rfl

/-- The literal right ideal `eA`. -/
def rightIdeal (e : A) : Submodule Aᵐᵒᵖ A :=
  LinearMap.range (rightRegularLeftMul e)

/-- The canonical generator `e` of `eA`. -/
def rightIdealGenerator (e : A) : rightIdeal e :=
  ⟨e, ⟨1, by
    change e * 1 = e
    simp⟩⟩

/-- Every element of `eA` is fixed by left multiplication by `e`. -/
theorem rightIdeal_fixed {e : A} (he : IsIdempotentElem e)
    (y : rightIdeal e) : e * y.1 = y.1 := by
  obtain ⟨a, ha⟩ := y.2
  change e * a = y.1 at ha
  rw [← ha, ← mul_assoc, he.eq]

/-- The right ideal `eA` as a literal finitely generated right module. -/
def rightIdealFGObj (e : A) : FinitelyGeneratedCategory A := by
  letI : Module.Finite Aᵐᵒᵖ A :=
    Module.Finite.equiv rightRegularLinearEquiv
  letI : IsNoetherian Aᵐᵒᵖ A := inferInstance
  letI : Module.Finite Aᵐᵒᵖ (rightIdeal e) := inferInstance
  exact FGModuleCat.of Aᵐᵒᵖ (rightIdeal e)

/-- The regular right module is projective. -/
theorem rightRegular_projective : Module.Projective Aᵐᵒᵖ A := by
  letI : Module.Projective Aᵐᵒᵖ Aᵐᵒᵖ := inferInstance
  exact Module.Projective.of_equiv' rightRegularLinearEquiv

/-- The idempotent right ideal `eA` is projective. -/
theorem rightIdeal_moduleProjective {e : A} (he : IsIdempotentElem e) :
    Module.Projective Aᵐᵒᵖ (rightIdeal e) := by
  letI : Module.Projective Aᵐᵒᵖ A := rightRegular_projective
  let inclusion : rightIdeal e →ₗ[Aᵐᵒᵖ] A := (rightIdeal e).subtype
  let retraction : A →ₗ[Aᵐᵒᵖ] rightIdeal e :=
    (rightRegularLeftMul e).codRestrict (rightIdeal e) fun a ↦
      ⟨a, rfl⟩
  apply Module.Projective.of_split inclusion retraction
  ext x
  obtain ⟨a, ha⟩ := x.2
  change e * x.1 = x.1
  rw [← ha]
  change e * (e * a) = e * a
  rw [← mul_assoc, he.eq]

/-- The idempotent right ideal is categorically projective in the literal
finitely generated module category. -/
theorem rightIdealFGObj_projective {e : A} (he : IsIdempotentElem e) :
    Projective (rightIdealFGObj e) := by
  apply fgProjective_of_moduleProjective
  exact rightIdeal_moduleProjective he

/-- The `e`-coordinate `Xe`, realized as the range of right multiplication
by `e` on a right module `X`. -/
def idempotentCoordinate (e : A) (X : FinitelyGeneratedCategory A) :
    Submodule k X :=
  LinearMap.range (Algebra.lsmul k k X (MulOpposite.op e))

/-- An element of `Xe` is fixed by right multiplication by `e`. -/
theorem idempotentCoordinate_fixed {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A)
    (x : idempotentCoordinate (k := k) e X) :
    (MulOpposite.op e) • (x.1 : X) = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  rw [← hy]
  change (MulOpposite.op e) • ((MulOpposite.op e) • y) =
    (MulOpposite.op e) • y
  rw [← mul_smul]
  have hop : (MulOpposite.op e) * (MulOpposite.op e) =
      MulOpposite.op e := by
    simpa using congrArg MulOpposite.op he.eq
  rw [hop]

/-- Evaluation at the generator identifies right-ideal maps with the
idempotent coordinate. -/
def rightIdealLinearMapCoordinateEquiv {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    ((rightIdeal e) →ₗ[Aᵐᵒᵖ] X) ≃ₗ[k]
      idempotentCoordinate (k := k) e X where
  toFun f := by
    refine ⟨f (rightIdealGenerator e), ?_⟩
    refine ⟨f (rightIdealGenerator e), ?_⟩
    change (MulOpposite.op e) • f (rightIdealGenerator e) =
      f (rightIdealGenerator e)
    rw [← f.map_smul]
    congr 1
    apply Subtype.ext
    exact he.eq
  invFun x :=
    { toFun := fun a ↦ (MulOpposite.op a.1) • (x.1 : X)
      map_add' := by
        intro a b
        change ((MulOpposite.op a.1) + (MulOpposite.op b.1)) •
            (x.1 : X) =
          (MulOpposite.op a.1) • (x.1 : X) +
            (MulOpposite.op b.1) • (x.1 : X)
        rw [add_smul]
      map_smul' := by
        intro r a
        change (MulOpposite.op (a.1 * r.unop)) • (x.1 : X) =
          r • ((MulOpposite.op a.1) • (x.1 : X))
        rw [← mul_smul]
        rfl }
  map_add' := by
    intro f g
    apply Subtype.ext
    rfl
  map_smul' := by
    intro r f
    apply Subtype.ext
    rfl
  left_inv := by
    intro f
    ext a
    obtain ⟨b, hb⟩ := a.2
    change e * b = a.1 at hb
    have hgen : (MulOpposite.op e) • rightIdealGenerator e =
        rightIdealGenerator e := by
      apply Subtype.ext
      exact he.eq
    have ha : (MulOpposite.op b) • rightIdealGenerator e = a := by
      apply Subtype.ext
      exact hb
    change (MulOpposite.op a.1) • f (rightIdealGenerator e) = f a
    calc
      (MulOpposite.op a.1) • f (rightIdealGenerator e) =
          (MulOpposite.op (e * b)) • f (rightIdealGenerator e) := by
            rw [hb]
      _ = (MulOpposite.op b) •
          ((MulOpposite.op e) • f (rightIdealGenerator e)) := by
            rw [← mul_smul]
            rfl
      _ = (MulOpposite.op b) •
          f ((MulOpposite.op e) • rightIdealGenerator e) := by
            rw [f.map_smul]
      _ = (MulOpposite.op b) • f (rightIdealGenerator e) := by
            rw [hgen]
      _ = f ((MulOpposite.op b) • rightIdealGenerator e) := by
            rw [f.map_smul]
      _ = f a := by rw [ha]
  right_inv := by
    intro x
    apply Subtype.ext
    change (MulOpposite.op e) • (x.1 : X) = x.1
    exact idempotentCoordinate_fixed he X x

/-- The categorical Hom space from `eA` is linearly equivalent to `Xe`. -/
def rightIdealHomCoordinateEquiv {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    (rightIdealFGObj e ⟶ X) ≃ₗ[k]
      idempotentCoordinate (k := k) e X :=
  ((InducedCategory.homLinearEquiv (R := k)).trans
    (ModuleCat.homLinearEquiv (S := k))).trans
      (rightIdealLinearMapCoordinateEquiv he X)

/-- The map `eA → X` associated to an element `x ∈ X`, namely
`y ↦ x y`. -/
def rightIdealActionHom (e : A)
    (X : FinitelyGeneratedCategory A) (x : X) :
    rightIdealFGObj e ⟶ X := by
  letI : Module.Finite Aᵐᵒᵖ A :=
    Module.Finite.equiv rightRegularLinearEquiv
  letI : IsNoetherian Aᵐᵒᵖ A := inferInstance
  letI : Module.Finite Aᵐᵒᵖ (rightIdeal e) := inferInstance
  exact FGModuleCat.ofHom
    { toFun := fun y ↦ (MulOpposite.op y.1) • x
      map_add' := by
        intro y z
        change ((MulOpposite.op y.1) + (MulOpposite.op z.1)) • x = _
        rw [add_smul]
      map_smul' := by
        intro r y
        change (MulOpposite.op (y.1 * r.unop)) • x =
          r • ((MulOpposite.op y.1) • x)
        rw [← mul_smul]
        rfl }

@[simp]
theorem rightIdealActionHom_apply (e : A)
    (X : FinitelyGeneratedCategory A) (x : X) (y : rightIdealFGObj e) :
    (rightIdealActionHom e X x).hom.hom y =
      (MulOpposite.op y.1) • x :=
  by
    rfl

/-- The idempotent coordinate has dimension zero exactly when `e` acts by
zero on the whole module. -/
theorem finrank_idempotentCoordinate_eq_zero_iff
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    Module.finrank k (idempotentCoordinate (k := k) e X) = 0 ↔
      ∀ x : X, (MulOpposite.op e) • x = 0 := by
  letI : FiniteDimensional k X :=
    finite_over_field_of_finitelyGenerated k A X
  rw [finrank_zero_iff_forall_zero]
  constructor
  · intro h x
    let y : idempotentCoordinate (k := k) e X :=
      ⟨(MulOpposite.op e) • x, ⟨x, rfl⟩⟩
    exact congrArg Subtype.val (h y)
  · intro h x
    apply Subtype.ext
    change x.1 = 0
    rw [← idempotentCoordinate_fixed he X x]
    exact h x.1

/-- The Hom dimension from `eA` is exactly the dimension of the
`e`-coordinate. -/
theorem finrank_hom_rightIdeal_eq_coordinate
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    Module.finrank k (rightIdealFGObj e ⟶ X) =
      Module.finrank k (idempotentCoordinate (k := k) e X) :=
  (rightIdealHomCoordinateEquiv he X).finrank_eq

/-- Right multiplication by `e`, regarded as an endomorphism of the left
regular module. -/
def leftRegularRightMul (e : A) : A →ₗ[A] A where
  toFun a := a * e
  map_add' := fun a b ↦ add_mul a b e
  map_smul' := by
    intro r a
    exact mul_assoc r a e

/-- The literal left ideal `Ae`. -/
def leftIdeal (e : A) : Submodule A A :=
  LinearMap.range (leftRegularRightMul e)

/-- The canonical generator `e` of `Ae`. -/
def leftIdealGenerator (e : A) : leftIdeal e :=
  ⟨e, ⟨1, by
    change 1 * e = e
    simp⟩⟩

/-- The left ideal `Ae` as a literal finitely generated left module. -/
abbrev leftIdealFGObj (e : A) : FGModuleCat.{u} A := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  letI : IsNoetherian A A := inferInstance
  letI : Module.Finite A (leftIdeal e) := inferInstance
  exact FGModuleCat.of A (leftIdeal e)

/-- The idempotent left ideal `Ae` is projective. -/
theorem leftIdeal_moduleProjective {e : A} (he : IsIdempotentElem e) :
    Module.Projective A (leftIdeal e) := by
  let inclusion : leftIdeal e →ₗ[A] A := (leftIdeal e).subtype
  let retraction : A →ₗ[A] leftIdeal e :=
    (leftRegularRightMul e).codRestrict (leftIdeal e) fun a ↦
      ⟨a, rfl⟩
  apply Module.Projective.of_split inclusion retraction
  ext x
  obtain ⟨a, ha⟩ := x.2
  change x.1 * e = x.1
  change a * e = x.1 at ha
  rw [← ha]
  rw [mul_assoc, he.eq]

/-- The idempotent left ideal is categorically projective. -/
theorem leftIdealFGObj_projective {e : A} (he : IsIdempotentElem e) :
    Projective (leftIdealFGObj (k := k) e) := by
  apply fgProjective_of_moduleProjective
  exact leftIdeal_moduleProjective he

/-- The manuscript's injective `I(e)=D(Ae)` as a literal finitely generated
right module. -/
abbrev primitiveInjectiveFGObj (e : A) : FinitelyGeneratedCategory A :=
  (dualFunctor k A).obj (Opposite.op (leftIdealFGObj (k := k) e))

/-- The principal right ideal generated by `op e` over the opposite algebra,
viewed as the original left ideal `Ae`. -/
def oppositeRightIdealToLeftIdeal (e : A) :
    rightIdeal (MulOpposite.op e) → leftIdeal e := fun x => by
  refine ⟨x.1.unop, ?_⟩
  obtain ⟨b, hb⟩ := x.2
  refine ⟨b.unop, ?_⟩
  change b.unop * e = x.1.unop
  exact congrArg MulOpposite.unop hb

/-- The inverse identification of `Ae` with the principal right ideal
generated by `op e` over the opposite algebra. -/
def leftIdealToOppositeRightIdeal (e : A) :
    leftIdeal e → rightIdeal (MulOpposite.op e) := fun y => by
  refine ⟨MulOpposite.op y.1, ?_⟩
  obtain ⟨a, ha⟩ := y.2
  refine ⟨MulOpposite.op a, ?_⟩
  change MulOpposite.op (a * e) = MulOpposite.op y.1
  exact congrArg MulOpposite.op ha

/-- Evaluation identifies the opposite principal projective `(op e)Aᵒᵖ`
with the contragredient dual of the original primitive injective `D(Ae)`.
The scalar calculation is exactly the reversal of multiplication under
`MulOpposite`. -/
def oppositeRightIdealBidualMap (e : A) :
    rightIdeal (MulOpposite.op e) →ₗ[(Aᵐᵒᵖ)ᵐᵒᵖ]
      ((dualFunctor k Aᵐᵒᵖ).obj
        (Opposite.op (primitiveInjectiveFGObj (k := k) e))) := by
  letI : Module k (primitiveInjectiveFGObj (k := k) e) :=
    Module.restrictScalars k Aᵐᵒᵖ _
  letI : IsScalarTower k Aᵐᵒᵖ
      (primitiveInjectiveFGObj (k := k) e) :=
    IsScalarTower.restrictScalars k Aᵐᵒᵖ _
  exact {
    toFun := fun x => by
      change Module.Dual k (primitiveInjectiveFGObj (k := k) e)
      exact forwardBidualMap k A (leftIdealFGObj (k := k) e)
        (oppositeRightIdealToLeftIdeal e x)
    map_add' := by
      intro x y
      change id (forwardBidualMap k A (leftIdealFGObj (k := k) e)
          (oppositeRightIdealToLeftIdeal e (x + y))) =
        id (forwardBidualMap k A (leftIdealFGObj (k := k) e)
            (oppositeRightIdealToLeftIdeal e x)) +
          id (forwardBidualMap k A (leftIdealFGObj (k := k) e)
            (oppositeRightIdealToLeftIdeal e y))
      rw [show oppositeRightIdealToLeftIdeal e (x + y) =
          oppositeRightIdealToLeftIdeal e x +
            oppositeRightIdealToLeftIdeal e y by
        apply Subtype.ext
        rfl]
      exact map_add _ _ _
    map_smul' := by
      intro r x
      apply LinearMap.ext
      intro f
      rfl }

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The evaluation map from the opposite principal projective to the dual
of the primitive injective is bijective. -/
theorem oppositeRightIdealBidualMap_bijective (e : A) :
    Function.Bijective (oppositeRightIdealBidualMap (k := k) e) := by
  letI : Module k (primitiveInjectiveFGObj (k := k) e) :=
    Module.restrictScalars k Aᵐᵒᵖ _
  letI : IsScalarTower k Aᵐᵒᵖ
      (primitiveInjectiveFGObj (k := k) e) :=
    IsScalarTower.restrictScalars k Aᵐᵒᵖ _
  let J : rightIdeal (MulOpposite.op e) ≃ leftIdeal e := {
    toFun := oppositeRightIdealToLeftIdeal e
    invFun := leftIdealToOppositeRightIdeal e
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro y; apply Subtype.ext; rfl }
  have hcomp :
      (forwardBidualMap k A (leftIdealFGObj (k := k) e) :
        leftIdeal e →
          (reverseDualFunctor k A).obj
            (Opposite.op (primitiveInjectiveFGObj (k := k) e))) ∘
        (J : rightIdeal (MulOpposite.op e) → leftIdeal e) =
      (oppositeRightIdealBidualMap (k := k) e :
        rightIdeal (MulOpposite.op e) →
          (dualFunctor k Aᵐᵒᵖ).obj
            (Opposite.op (primitiveInjectiveFGObj (k := k) e))) := by
    funext x
    apply LinearMap.ext
    intro f
    rfl
  rw [← hcomp]
  exact (forwardBidualMap_bijective k A
    (leftIdealFGObj (k := k) e)).comp J.bijective

/-- The opposite principal projective is linearly equivalent to the
contragredient dual of the original primitive injective. -/
def oppositeRightIdealBidualLinearEquiv (e : A) :
    rightIdeal (MulOpposite.op e) ≃ₗ[(Aᵐᵒᵖ)ᵐᵒᵖ]
      ((dualFunctor k Aᵐᵒᵖ).obj
        (Opposite.op (primitiveInjectiveFGObj (k := k) e))) :=
  LinearEquiv.ofBijective (oppositeRightIdealBidualMap (k := k) e)
    (oppositeRightIdealBidualMap_bijective (k := k) e)

/-- Categorical form of the identification
`(op e)Aᵒᵖ ≅ D(D(Ae))`. -/
def oppositeRightIdealDualPrimitiveInjectiveIso
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ] (e : A) :
    rightIdealFGObj (MulOpposite.op e) ≅
      (dualFunctor k Aᵐᵒᵖ).obj
        (Opposite.op (primitiveInjectiveFGObj (k := k) e)) :=
  fgModuleIsoOfLinearEquiv (Aᵐᵒᵖ)ᵐᵒᵖ
    (oppositeRightIdealBidualLinearEquiv (k := k) e)

/-- Contragredient duality sends the projective left ideal `Ae` to the
injective right module `D(Ae)`. -/
theorem primitiveInjectiveFGObj_injective {e : A}
    (he : IsIdempotentElem e) :
    Injective (primitiveInjectiveFGObj (k := k) e) := by
  have hP : Projective (leftIdealFGObj (k := k) e) :=
    leftIdealFGObj_projective he
  have hop : Injective (Opposite.op (leftIdealFGObj (k := k) e)) :=
    Injective.projective_iff_injective_op.mp hP
  exact ((dualityEquivalence k A).map_injective_iff
    (Opposite.op (leftIdealFGObj (k := k) e))).2 hop

/-- Every element of `Ae` is fixed by right multiplication by `e`. -/
theorem leftIdeal_fixed {e : A} (he : IsIdempotentElem e)
    (y : leftIdeal e) : y.1 * e = y.1 := by
  obtain ⟨a, ha⟩ := y.2
  change a * e = y.1 at ha
  rw [← ha, mul_assoc, he.eq]

/-- Multiplication of `x : X` by an element of `Ae` lands in `Xe`. -/
def coordinateProduct {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) (x : X)
    (y : leftIdealFGObj (k := k) e) :
    idempotentCoordinate (k := k) e X := by
  refine ⟨(MulOpposite.op y.1) • x, ?_⟩
  refine ⟨(MulOpposite.op y.1) • x, ?_⟩
  change (MulOpposite.op e) • ((MulOpposite.op y.1) • x) =
    (MulOpposite.op y.1) • x
  rw [← mul_smul]
  have hop : (MulOpposite.op e) * (MulOpposite.op y.1) =
      MulOpposite.op y.1 := by
    simpa using congrArg MulOpposite.op (leftIdeal_fixed he y)
  rw [hop]

@[simp]
theorem coordinateProduct_add_leftIdeal {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) (x : X)
    (y z : leftIdealFGObj (k := k) e) :
    coordinateProduct he X x (y + z) =
      coordinateProduct he X x y + coordinateProduct he X x z := by
  apply Subtype.ext
  change (MulOpposite.op (y.1 + z.1)) • x =
    (MulOpposite.op y.1) • x + (MulOpposite.op z.1) • x
  rw [MulOpposite.op_add, add_smul]

@[simp]
theorem coordinateProduct_add_source {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) (x z : X)
    (y : leftIdealFGObj (k := k) e) :
    coordinateProduct he X (x + z) y =
      coordinateProduct he X x y + coordinateProduct he X z y := by
  apply Subtype.ext
  change (MulOpposite.op y.1) • (x + z) =
    (MulOpposite.op y.1) • x + (MulOpposite.op y.1) • z
  rw [smul_add]

/-- The inherited `k`-action on the literal left ideal agrees with the
action obtained by restricting its `A`-module structure. -/
theorem leftIdeal_module_eq_restrictScalars (e : A) :
    (inferInstance : Module k (leftIdeal e)) =
      Module.restrictScalars k A (leftIdealFGObj (k := k) e) := by
  apply Module.ext'
  intro r y
  apply Subtype.ext
  change r • y.1 = (algebraMap k A r) * y.1
  rw [Algebra.smul_def]

@[simp]
theorem coe_smul_leftIdeal (e : A) (r : k) (x : leftIdeal e) :
    ((r • x : leftIdeal e) : A) = r • (x : A) :=
  Submodule.coe_smul_of_tower r x

@[simp]
theorem coe_smul_rightIdeal (e : A) (r : k) (x : rightIdeal e) :
    ((r • x : rightIdeal e) : A) = r • (x : A) :=
  Submodule.coe_smul_of_tower r x

@[simp]
theorem coe_restrictScalars_smul_leftIdeal (e : A) (r : k)
    (x : leftIdealFGObj (k := k) e) :
    (@SMul.smul k _
        (Module.restrictScalars k A
          (leftIdealFGObj (k := k) e)).toSMul r x).1 =
      r • x.1 := by
  change (algebraMap k A r) * x.1 = r • x.1
  rw [Algebra.smul_def]

@[simp]
theorem coe_restrictScalars_smul_rightIdeal (e : A) (r : k)
    (x : rightIdealFGObj e) :
    (@SMul.smul k _
        (Module.restrictScalars k Aᵐᵒᵖ
          (rightIdealFGObj e)).toSMul r x).1 =
      r • x.1 := by
  change x.1 * (algebraMap k Aᵐᵒᵖ r).unop = r • x.1
  rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  rw [Algebra.smul_def, Algebra.commutes]

/-- Evaluation of a left-ideal map at the generator, bundled in the common
corner coordinate. -/
def leftIdealToRightCoordinate
    {e f : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : (leftIdeal f) →ₗ[A] (leftIdeal e)) :
    idempotentCoordinate (k := k) e (rightIdealFGObj f) := by
  let y := h (leftIdealGenerator f)
  have hfy : f * y.1 = y.1 := by
    have hgen : f • leftIdealGenerator f = leftIdealGenerator f := by
      apply Subtype.ext
      exact hf.eq
    have hh := congrArg Subtype.val
      (h.map_smul f (leftIdealGenerator f))
    rw [hgen] at hh
    exact hh.symm
  let yr : rightIdeal f := ⟨y.1, ⟨y.1, hfy⟩⟩
  refine ⟨yr, ⟨yr, ?_⟩⟩
  apply Subtype.ext
  change y.1 * e = y.1
  exact leftIdeal_fixed he y

/-- A common corner coordinate acts by right multiplication to produce a
map `Af → Ae`. -/
def rightCoordinateToLeftIdeal
    {e f : A} (he : IsIdempotentElem e)
    (x : idempotentCoordinate (k := k) e (rightIdealFGObj f)) :
    (leftIdeal f) →ₗ[A] (leftIdeal e) := by
  have hxe : x.1.1 * e = x.1.1 := by
    exact congrArg Subtype.val
      (idempotentCoordinate_fixed he (rightIdealFGObj f) x)
  exact
    { toFun := fun z ↦ by
        refine ⟨z.1 * x.1.1, ⟨z.1 * x.1.1, ?_⟩⟩
        change (z.1 * x.1.1) * e = z.1 * x.1.1
        rw [mul_assoc, hxe]
      map_add' := by
        intro z w
        apply Subtype.ext
        exact add_mul z.1 w.1 x.1.1
      map_smul' := by
        intro a z
        apply Subtype.ext
        exact mul_assoc a z.1 x.1.1 }

/-- Evaluation at the generator of `Af` identifies maps `Af → Ae` with
the same corner coordinate that represents maps `eA → fA`. -/
def leftIdealLinearMapRightCoordinateEquiv
    {e f : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    ((leftIdeal f) →ₗ[A] (leftIdeal e)) ≃ₗ[k]
      idempotentCoordinate (k := k) e (rightIdealFGObj f) where
  toFun := leftIdealToRightCoordinate (k := k) he hf
  invFun := rightCoordinateToLeftIdeal (k := k) he
  map_add' := by
    intro h l
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' := by
    intro r h
    apply Subtype.ext
    apply Subtype.ext
    change (leftIdealToRightCoordinate (k := k) he hf (r • h)).1.1 =
      ((r • leftIdealToRightCoordinate (k := k) he hf h).1).1
    calc
      _ = ((r • h) (leftIdealGenerator f)).1 := rfl
      _ = r • (h (leftIdealGenerator f)).1 :=
        coe_smul_leftIdeal e r _
      _ = r • (leftIdealToRightCoordinate (k := k) he hf h).1.1 := rfl
      _ = (@SMul.smul k _
          (Module.restrictScalars k Aᵐᵒᵖ
            (rightIdealFGObj f)).toSMul r
            (leftIdealToRightCoordinate (k := k) he hf h).1).1 :=
        (coe_restrictScalars_smul_rightIdeal f r _).symm
      _ = ((r • leftIdealToRightCoordinate (k := k) he hf h).1).1 := by
        exact congrArg Subtype.val
          (Submodule.coe_smul r
            (leftIdealToRightCoordinate (k := k) he hf h)).symm
  left_inv := by
    intro h
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    have hz : z.1 • leftIdealGenerator f = z := by
      apply Subtype.ext
      exact leftIdeal_fixed hf z
    calc
      z.1 * (h (leftIdealGenerator f)).1 =
          (z.1 • h (leftIdealGenerator f)).1 := rfl
      _ = (h (z.1 • leftIdealGenerator f)).1 := by
        rw [h.map_smul]
      _ = (h z).1 := by rw [hz]
  right_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change f * x.1.1 = x.1.1
    exact rightIdeal_fixed hf x.1

/-- Categorical left-ideal Hom and right-ideal Hom have the same corner
coordinate. -/
def leftIdealHomRightCoordinateEquiv
    {e f : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (leftIdealFGObj (k := k) f ⟶ leftIdealFGObj (k := k) e) ≃ₗ[k]
      idempotentCoordinate (k := k) e (rightIdealFGObj f) := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  letI : Module.Finite A (leftIdeal e) := inferInstance
  letI : Module.Finite A (leftIdeal f) := inferInstance
  exact {
  toFun h := leftIdealToRightCoordinate (k := k) he hf h.hom.hom
  invFun x := FGModuleCat.ofHom
    (rightCoordinateToLeftIdeal (k := k) he x)
  map_add' := by
    intro h l
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' := by
    intro r h
    apply Subtype.ext
    apply Subtype.ext
    change (leftIdealToRightCoordinate (k := k) he hf
        (r • h).hom.hom).1.1 =
      ((r • leftIdealToRightCoordinate (k := k) he hf h.hom.hom).1).1
    calc
      _ = ((r • h).hom.hom (leftIdealGenerator f)).1 := rfl
      _ = (@SMul.smul k _
          (Module.restrictScalars k A
            (leftIdealFGObj (k := k) e)).toSMul r
            (h.hom.hom (leftIdealGenerator f))).1 := rfl
      _ = r • (h.hom.hom (leftIdealGenerator f)).1 :=
        coe_restrictScalars_smul_leftIdeal e r _
      _ = r •
          (leftIdealToRightCoordinate (k := k) he hf h.hom.hom).1.1 := rfl
      _ = (@SMul.smul k _
          (Module.restrictScalars k Aᵐᵒᵖ
            (rightIdealFGObj f)).toSMul r
            (leftIdealToRightCoordinate (k := k) he hf h.hom.hom).1).1 :=
        (coe_restrictScalars_smul_rightIdeal f r _).symm
      _ = ((r •
          leftIdealToRightCoordinate (k := k) he hf h.hom.hom).1).1 := by
        exact congrArg Subtype.val
          (Submodule.coe_smul r
            (leftIdealToRightCoordinate (k := k) he hf h.hom.hom)).symm
  left_inv := by
    intro h
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    have hz : z.1 • leftIdealGenerator f = z := by
      apply Subtype.ext
      exact leftIdeal_fixed hf z
    calc
      z.1 * (h.hom.hom (leftIdealGenerator f)).1 =
          (z.1 • h.hom.hom (leftIdealGenerator f)).1 := rfl
      _ = (h.hom.hom (z.1 • leftIdealGenerator f)).1 := by
        rw [h.hom.hom.map_smul]
      _ = (h.hom.hom z).1 := by rw [hz]
  right_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change f * x.1.1 = x.1.1
    exact rightIdeal_fixed hf x.1 }

private theorem primitiveInjectiveMap_apply
    (e f : A)
    (h : leftIdealFGObj (k := k) f ⟶ leftIdealFGObj (k := k) e)
    (φ : primitiveInjectiveFGObj (k := k) e)
    (x : leftIdealFGObj (k := k) f) :
    forwardInnerDualEquiv k A (leftIdealFGObj (k := k) f)
        (((dualFunctor k A).map h.op).hom.hom φ) x =
      forwardInnerDualEquiv k A (leftIdealFGObj (k := k) e) φ
        (h.hom.hom x) :=
  rfl

private theorem primitiveInjective_restrictScalars_smul_apply
    (f : A) (r : k)
    (ψ : primitiveInjectiveFGObj (k := k) f)
    (x : leftIdealFGObj (k := k) f) :
    forwardInnerDualEquiv k A (leftIdealFGObj (k := k) f)
        (@SMul.smul k _
          (Module.restrictScalars k Aᵐᵒᵖ
            (primitiveInjectiveFGObj (k := k) f)).toSMul r ψ) x =
      r * forwardInnerDualEquiv k A
        (leftIdealFGObj (k := k) f) ψ x := by
  let E := forwardInnerDualEquiv k A (leftIdealFGObj (k := k) f)
  have hs := E.map_smul r ψ
  have hsx := congrArg (fun θ ↦ θ x) hs
  change
    forwardInnerDualEquiv k A (leftIdealFGObj (k := k) f)
        (@SMul.smul k _
          (Module.restrictScalars k Aᵐᵒᵖ
            (primitiveInjectiveFGObj (k := k) f)).toSMul r ψ) x =
      r * forwardInnerDualEquiv k A
        (leftIdealFGObj (k := k) f) ψ x at hsx
  exact hsx

private theorem leftIdealDual_restrictScalars_smul_apply
    (e : A) (r : k)
    (φ : primitiveInjectiveFGObj (k := k) e)
    (x : leftIdealFGObj (k := k) e) :
    forwardInnerDualEquiv k A (leftIdealFGObj (k := k) e) φ
        (@SMul.smul k _
          (Module.restrictScalars k A
            (leftIdealFGObj (k := k) e)).toSMul r x) =
      r * forwardInnerDualEquiv k A
        (leftIdealFGObj (k := k) e) φ x := by
  letI : Module k (leftIdealFGObj (k := k) e) :=
    Module.restrictScalars k A (leftIdealFGObj (k := k) e)
  let φ' := forwardInnerDualEquiv k A
    (leftIdealFGObj (k := k) e) φ
  exact φ'.map_smul r x

/-- Contragredient duality sends a map `Af → Ae` to the reversed map
`D(Ae) → D(Af)`, linearly over the coefficient field. -/
def leftIdealHomPrimitiveInjectiveHomLinearMap (e f : A) :
    (leftIdealFGObj (k := k) f ⟶ leftIdealFGObj (k := k) e) →ₗ[k]
      (primitiveInjectiveFGObj (k := k) e ⟶
        primitiveInjectiveFGObj (k := k) f) where
  toFun h := (dualFunctor k A).map h.op
  map_add' := by
    intro h l
    letI : Module k (leftIdealFGObj (k := k) f) :=
      Module.restrictScalars k A (leftIdealFGObj (k := k) f)
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply (forwardInnerDualEquiv k A
      (leftIdealFGObj (k := k) f)).injective
    apply LinearMap.coe_injective
    funext x
    change
      (forwardInnerDualEquiv k A (leftIdealFGObj (k := k) e) φ)
          (h.hom.hom x + l.hom.hom x) =
        (forwardInnerDualEquiv k A (leftIdealFGObj (k := k) e) φ)
            (h.hom.hom x) +
          (forwardInnerDualEquiv k A (leftIdealFGObj (k := k) e) φ)
            (l.hom.hom x)
    rw [map_add]
  map_smul' := by
    intro r h
    letI : Module k (leftIdealFGObj (k := k) f) :=
      Module.restrictScalars k A (leftIdealFGObj (k := k) f)
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    let E := forwardInnerDualEquiv k A (leftIdealFGObj (k := k) f)
    apply E.injective
    have hout :
        ((r • (dualFunctor k A).map h.op).hom.hom φ) =
          @SMul.smul k _
            (Module.restrictScalars k Aᵐᵒᵖ
              (primitiveInjectiveFGObj (k := k) f)).toSMul r
              (((dualFunctor k A).map h.op).hom.hom φ) := rfl
    have hout' :
        (((RingHom.id k) r • (dualFunctor k A).map h.op).hom.hom φ) =
          @SMul.smul k _
            (Module.restrictScalars k Aᵐᵒᵖ
              (primitiveInjectiveFGObj (k := k) f)).toSMul r
              (((dualFunctor k A).map h.op).hom.hom φ) := by
      simpa only [RingHom.id_apply] using hout
    rw [hout']
    apply LinearMap.coe_injective
    funext x
    have hin :
        (r • h).hom.hom x =
          @SMul.smul k _
            (Module.restrictScalars k A
              (leftIdealFGObj (k := k) e)).toSMul r
              (h.hom.hom x) := rfl
    rw [primitiveInjectiveMap_apply,
      primitiveInjective_restrictScalars_smul_apply, hin,
      leftIdealDual_restrictScalars_smul_apply,
      primitiveInjectiveMap_apply]

private theorem leftIdealHomPrimitiveInjectiveHomLinearMap_bijective
    (e f : A) :
    Function.Bijective
      (leftIdealHomPrimitiveInjectiveHomLinearMap (k := k) e f) := by
  constructor
  · intro h l hhl
    have hop : h.op = l.op := by
      apply (dualityEquivalence k A).functor.map_injective
      exact hhl
    exact Quiver.Hom.op_inj hop
  · intro a
    letI : (dualFunctor k A).Full :=
      (dualityEquivalence k A).fullyFaithfulFunctor.full
    refine ⟨((dualFunctor k A).preimage a).unop, ?_⟩
    change (dualFunctor k A).map
        (((dualFunctor k A).preimage a).unop).op = a
    rw [Quiver.Hom.op_unop, (dualFunctor k A).map_preimage]

/-- The Hom space between primitive injectives is the reversed Hom space
between their defining left ideals. -/
def leftIdealHomPrimitiveInjectiveHomEquiv (e f : A) :
    (leftIdealFGObj (k := k) f ⟶ leftIdealFGObj (k := k) e) ≃ₗ[k]
      (primitiveInjectiveFGObj (k := k) e ⟶
        primitiveInjectiveFGObj (k := k) f) :=
  LinearEquiv.ofBijective
    (leftIdealHomPrimitiveInjectiveHomLinearMap (k := k) e f)
    (leftIdealHomPrimitiveInjectiveHomLinearMap_bijective (k := k) e f)

/-- Maps between primitive injectives and maps between the corresponding
primitive projectives have the same corner coordinate. -/
def primitiveInjectiveHomRightIdealHomEquiv
    {e f : A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (primitiveInjectiveFGObj (k := k) e ⟶
        primitiveInjectiveFGObj (k := k) f) ≃ₗ[k]
      (rightIdealFGObj e ⟶ rightIdealFGObj f) :=
  (leftIdealHomPrimitiveInjectiveHomEquiv (k := k) e f).symm |>.trans <|
    (leftIdealHomRightCoordinateEquiv (k := k) he hf) |>.trans <|
      (rightIdealHomCoordinateEquiv (k := k) he (rightIdealFGObj f)).symm

/-- The coordinate product is `k`-linear when the left ideal is equipped
with the restricted scalar action used by contragredient duality. -/
@[simp]
theorem coordinateProduct_restrictScalars_smul {e : A}
    (he : IsIdempotentElem e) (X : FinitelyGeneratedCategory A)
    (x : X) (r : k) (y : leftIdealFGObj (k := k) e) :
    coordinateProduct he X x
        (@SMul.smul k _
          (Module.restrictScalars k A
            (leftIdealFGObj (k := k) e)).toSMul r y) =
      r • coordinateProduct he X x y := by
  apply Subtype.ext
  change (MulOpposite.op ((algebraMap k A r) * y.1)) • x =
    r • ((MulOpposite.op y.1) • x)
  change (MulOpposite.op ((algebraMap k A r) * y.1)) • x =
    (algebraMap k Aᵐᵒᵖ r) • ((MulOpposite.op y.1) • x)
  rw [← mul_smul]
  congr 1
  rw [MulOpposite.algebraMap_apply, ← MulOpposite.op_mul]
  exact congrArg MulOpposite.op (Algebra.commutes r y.1)

/-- The concrete contragredient object has the ordinary vector-space dual
as its underlying `k`-module. -/
def primitiveInjectiveInnerDualEquiv (e : A) :=
  forwardInnerDualEquiv k A (leftIdealFGObj (k := k) e)

/-- The elementary dual-coordinate form of the standard isomorphism
`Hom_A(X,D(Ae)) ≅ D(Xe)`. -/
def homPrimitiveInjectiveCoordinateDualEquiv
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    (X →ₗ[Aᵐᵒᵖ] primitiveInjectiveFGObj (k := k) e) ≃ₗ[k]
      Module.Dual k (idempotentCoordinate (k := k) e X) := by
  letI hmod : Module k (leftIdealFGObj (k := k) e) :=
    Module.restrictScalars k A (leftIdealFGObj (k := k) e)
  exact {
  toFun f :=
    { toFun := fun x ↦
        primitiveInjectiveInnerDualEquiv (k := k) e (f x.1)
          (leftIdealGenerator e)
      map_add' := by
        intro x y
        change primitiveInjectiveInnerDualEquiv (k := k) e
            (f (x.1 + y.1)) (leftIdealGenerator e) = _
        rw [f.map_add, map_add, LinearMap.add_apply]
      map_smul' := by
        intro r x
        change primitiveInjectiveInnerDualEquiv (k := k) e
            (f (r • x.1)) (leftIdealGenerator e) = _
        rw [f.map_smul_of_tower, map_smul]
        rfl }
  invFun φ :=
    { toFun := fun x ↦
        (primitiveInjectiveInnerDualEquiv (k := k) e).symm
          { toFun := fun y ↦ φ (coordinateProduct he X x y)
            map_add' := by
              intro y z
              rw [coordinateProduct_add_leftIdeal, φ.map_add]
            map_smul' := by
              intro r y
              change φ (coordinateProduct he X x
                (@SMul.smul k _ hmod.toSMul r y)) = _
              rw [coordinateProduct_restrictScalars_smul, φ.map_smul]
              rfl }
      map_add' := by
        intro x y
        rw [← map_add]
        congr 1
        apply LinearMap.ext
        intro z
        change φ (coordinateProduct he X (x + y) z) =
          φ (coordinateProduct he X x z) +
            φ (coordinateProduct he X y z)
        rw [coordinateProduct_add_source, φ.map_add]
      map_smul' := by
        intro r x
        rw [LinearEquiv.symm_apply_eq]
        apply LinearMap.ext
        intro y
        change φ (coordinateProduct he X (r • x) y) =
          φ (coordinateProduct he X x (r.unop • y))
        congr 1
        apply Subtype.ext
        change (MulOpposite.op y.1) • (r • x) =
          (MulOpposite.op (r.unop * y.1)) • x
        rw [← mul_smul]
        rfl }
  map_add' := by
    intro f g
    ext x
    change primitiveInjectiveInnerDualEquiv (k := k) e
        ((f + g) x.1) (leftIdealGenerator e) = _
    rw [LinearMap.add_apply, map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    intro r f
    ext x
    change primitiveInjectiveInnerDualEquiv (k := k) e
        ((r • f) x.1) (leftIdealGenerator e) = _
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
    rfl
  left_inv := by
    intro f
    apply LinearMap.ext
    intro x
    change (primitiveInjectiveInnerDualEquiv (k := k) e).symm
        { toFun := fun y ↦ primitiveInjectiveInnerDualEquiv (k := k) e
            (f ((MulOpposite.op y.1) • x)) (leftIdealGenerator e)
          map_add' := _
          map_smul' := _ } = f x
    rw [LinearEquiv.symm_apply_eq]
    apply LinearMap.ext
    intro y
    have hy : y.1 * e = y.1 := leftIdeal_fixed he y
    change primitiveInjectiveInnerDualEquiv (k := k) e
        (f ((MulOpposite.op y.1) • x)) (leftIdealGenerator e) =
      primitiveInjectiveInnerDualEquiv (k := k) e (f x) y
    rw [f.map_smul]
    change primitiveInjectiveInnerDualEquiv (k := k) e (f x)
        ⟨y.1 * e, _⟩ =
      primitiveInjectiveInnerDualEquiv (k := k) e (f x) y
    congr 2
  right_inv := by
    intro φ
    ext x
    change φ (coordinateProduct he X x.1 (leftIdealGenerator e)) = φ x
    congr 1
    apply Subtype.ext
    change (MulOpposite.op e) • (x.1 : X) = x.1
    exact idempotentCoordinate_fixed he X x }

/-- The categorical sink Hom space is linearly equivalent to the dual of
the primitive coordinate. -/
def primitiveInjectiveHomCoordinateDualEquiv
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    (X ⟶ primitiveInjectiveFGObj (k := k) e) ≃ₗ[k]
      Module.Dual k (idempotentCoordinate (k := k) e X) :=
  ((InducedCategory.homLinearEquiv (R := k)).trans
    (ModuleCat.homLinearEquiv (S := k))).trans
      (homPrimitiveInjectiveCoordinateDualEquiv he X)

@[simp]
theorem primitiveInjectiveHomCoordinateDualEquiv_apply
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A)
    (f : X ⟶ primitiveInjectiveFGObj (k := k) e)
    (x : idempotentCoordinate (k := k) e X) :
    primitiveInjectiveHomCoordinateDualEquiv (k := k) he X f x =
      primitiveInjectiveInnerDualEquiv (k := k) e (f.hom.hom x.1)
        (leftIdealGenerator e) :=
  rfl

theorem primitiveInjectiveHomCoordinateDualEquiv_apply_eq_zero
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A)
    (f : X ⟶ primitiveInjectiveFGObj (k := k) e)
    (x : idempotentCoordinate (k := k) e X)
    (hfx : f.hom.hom x.1 = 0) :
    primitiveInjectiveHomCoordinateDualEquiv (k := k) he X f x = 0 := by
  letI hmod : Module k (leftIdealFGObj (k := k) e) :=
    Module.restrictScalars k A (leftIdealFGObj (k := k) e)
  rw [primitiveInjectiveHomCoordinateDualEquiv_apply, hfx, map_zero,
    LinearMap.zero_apply]

/-- The Hom dimension into `D(Ae)` is the dimension of `Xe`. -/
theorem finrank_hom_primitiveInjective_eq_coordinate
    {e : A} (he : IsIdempotentElem e)
    (X : FinitelyGeneratedCategory A) :
    Module.finrank k (X ⟶ primitiveInjectiveFGObj (k := k) e) =
      Module.finrank k (idempotentCoordinate (k := k) e X) := by
  rw [(primitiveInjectiveHomCoordinateDualEquiv he X).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- Module-theoretic indecomposability implies categorical
indecomposability in the finitely generated module category. -/
theorem fgIndecomposable_of_isIndecomposableModule
    {R : Type u} [Ring R] [IsNoetherianRing R] (M : FGModuleCat.{u} R)
    (hM : Foundation.IsIndecomposableModule R M) :
    Indecomposable M := by
  refine ⟨?_, ?_⟩
  · intro hzero
    let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    have hzeroObj : IsZero M.obj := U.map_isZero hzero
    have hsub : Subsingleton M := ModuleCat.subsingleton_of_isZero hzeroObj
    letI : Nontrivial M := hM.nontrivial
    exact not_subsingleton M hsub
  · intro Y Z e
    let iY : Y ⟶ M := biprod.inl ≫ e.inv
    let qY : M ⟶ Y := e.hom ≫ biprod.fst
    let p : M ⟶ M := qY ≫ iY
    have hp : p ≫ p = p := by
      simp [p, iY, qY, Category.assoc]
    have hpLinear : IsIdempotentElem p.hom.hom := by
      change p.hom.hom.comp p.hom.hom = p.hom.hom
      exact congrArg (fun q : M ⟶ M ↦ q.hom.hom) hp
    rcases hM.eq_zero_or_eq_one_of_isIdempotentElem hpLinear with hp0 | hp1
    · left
      have hpZero : p = 0 := by
        apply FGModuleCat.hom_ext
        simpa using hp0
      apply (IsZero.iff_id_eq_zero Y).2
      calc
        𝟙 Y = iY ≫ p ≫ qY := by
          simp [p, iY, qY, Category.assoc]
        _ = 0 := by rw [hpZero]; simp
    · right
      have hpOne : p = 𝟙 M := by
        apply FGModuleCat.hom_ext
        simpa [Module.End.one_eq_id] using hp1
      let iZ : Z ⟶ M := biprod.inr ≫ e.inv
      let qZ : M ⟶ Z := e.hom ≫ biprod.snd
      have hiZ : iZ = 0 := by
        calc
          iZ = iZ ≫ p := by rw [hpOne]; simp
          _ = 0 := by simp [p, iY, qY, iZ, Category.assoc]
      apply (IsZero.iff_id_eq_zero Z).2
      calc
        𝟙 Z = iZ ≫ qZ := by simp [iZ, qZ, Category.assoc]
        _ = 0 := by rw [hiZ]; simp

/-- A primitive idempotent, expressed by the absence of nontrivial
idempotents in its corner `eAe`. -/
structure PrimitiveIdempotentData (e : A) where
  idempotent : IsIdempotentElem e
  nonzero : e ≠ 0
  corner_idempotent : ∀ b : A, IsIdempotentElem b →
    e * b = b → b * e = b → b = 0 ∨ b = e

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- A primitive idempotent remains primitive in the opposite algebra. -/
theorem PrimitiveIdempotentData.opposite {e : A}
    (D : PrimitiveIdempotentData e) :
    PrimitiveIdempotentData (MulOpposite.op e) where
  idempotent := by
    apply MulOpposite.unop_injective
    exact D.idempotent.eq
  nonzero := by
    intro hzero
    apply D.nonzero
    have h := congrArg MulOpposite.unop hzero
    simpa using h
  corner_idempotent := by
    intro b hb hleft hright
    have hb' : IsIdempotentElem b.unop := by
      apply MulOpposite.op_injective
      exact hb.eq
    have hleft' : e * b.unop = b.unop := by
      have h := congrArg MulOpposite.unop hright
      simpa using h
    have hright' : b.unop * e = b.unop := by
      have h := congrArg MulOpposite.unop hleft
      simpa using h
    rcases D.corner_idempotent b.unop hb' hleft' hright' with h | h
    · left
      apply MulOpposite.unop_injective
      simpa using h
    · right
      apply MulOpposite.unop_injective
      exact h

/-- The right ideal of a primitive idempotent is indecomposable in the
module-theoretic sense. -/
theorem rightIdeal_isIndecomposableModule {e : A}
    (D : PrimitiveIdempotentData e) :
    Foundation.IsIndecomposableModule Aᵐᵒᵖ (rightIdealFGObj e) := by
  rw [Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  let gen : rightIdealFGObj e := rightIdealGenerator e
  constructor
  · refine ⟨⟨gen, 0, ?_⟩⟩
    intro h
    apply D.nonzero
    exact congrArg Subtype.val h
  · intro f hf
    let b : A := (f gen).1
    have hb_left : e * b = b :=
      rightIdeal_fixed D.idempotent (f gen)
    have hgen_fixed : (MulOpposite.op e) • gen = gen := by
      apply Subtype.ext
      exact D.idempotent.eq
    have hb_right_subtype :
        (MulOpposite.op e) • f gen = f gen := by
      rw [← f.map_smul, hgen_fixed]
    have hb_right : b * e = b := congrArg Subtype.val hb_right_subtype
    have hb_gen : (MulOpposite.op b) • gen = f gen := by
      apply Subtype.ext
      exact hb_left
    have hff : f (f gen) = f gen :=
      DFunLike.congr_fun hf gen
    have hb_idem_subtype :
        (MulOpposite.op b) • f gen = f gen := by
      rw [← f.map_smul, hb_gen, hff]
    have hb_idem : IsIdempotentElem b :=
      congrArg Subtype.val hb_idem_subtype
    rcases D.corner_idempotent b hb_idem hb_left hb_right with hb | hb
    · left
      apply LinearMap.ext
      intro y
      obtain ⟨a, ha⟩ := y.2
      change e * a = y.1 at ha
      have hy : (MulOpposite.op a) • gen = y := by
        apply Subtype.ext
        exact ha
      rw [← hy, f.map_smul]
      apply Subtype.ext
      change b * a = 0
      rw [hb, zero_mul]
    · right
      apply LinearMap.ext
      intro y
      obtain ⟨a, ha⟩ := y.2
      change e * a = y.1 at ha
      have hy : (MulOpposite.op a) • gen = y := by
        apply Subtype.ext
        exact ha
      rw [← hy, f.map_smul]
      change (MulOpposite.op a) • f gen = (MulOpposite.op a) • gen
      apply Subtype.ext
      change b * a = e * a
      rw [hb]

/-- The literal right ideal of a primitive idempotent is categorically
indecomposable. -/
theorem rightIdealFGObj_indecomposable {e : A}
    (D : PrimitiveIdempotentData e) :
    Indecomposable (rightIdealFGObj e) :=
  fgIndecomposable_of_isIndecomposableModule
    (rightIdealFGObj e) (rightIdeal_isIndecomposableModule D)

/-- The left ideal of a primitive idempotent is indecomposable in the
module-theoretic sense used by contragredient duality. -/
theorem leftIdeal_isIndecomposableModule {e : A}
    (D : PrimitiveIdempotentData e) :
    Foundation.IsIndecomposableModule A (leftIdealFGObj (k := k) e) := by
  rw [Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · refine ⟨⟨leftIdealGenerator e, 0, ?_⟩⟩
    intro h
    apply D.nonzero
    exact congrArg Subtype.val h
  · intro f hf
    let b : A := (f (leftIdealGenerator e)).1
    have hb_right : b * e = b :=
      leftIdeal_fixed D.idempotent (f (leftIdealGenerator e))
    have hgen_fixed : e • leftIdealGenerator e = leftIdealGenerator e := by
      apply Subtype.ext
      exact D.idempotent.eq
    have hb_left_subtype :
        e • f (leftIdealGenerator e) = f (leftIdealGenerator e) := by
      rw [← f.map_smul, hgen_fixed]
    have hb_left : e * b = b := congrArg Subtype.val hb_left_subtype
    have hb_gen : b • leftIdealGenerator e = f (leftIdealGenerator e) := by
      apply Subtype.ext
      exact hb_right
    have hff : f (f (leftIdealGenerator e)) =
        f (leftIdealGenerator e) :=
      DFunLike.congr_fun hf (leftIdealGenerator e)
    have hb_idem_subtype :
        b • f (leftIdealGenerator e) = f (leftIdealGenerator e) := by
      rw [← f.map_smul, hb_gen, hff]
    have hb_idem : IsIdempotentElem b :=
      congrArg Subtype.val hb_idem_subtype
    rcases D.corner_idempotent b hb_idem hb_left hb_right with hb | hb
    · left
      apply LinearMap.ext
      intro y
      obtain ⟨a, ha⟩ := y.2
      change a * e = y.1 at ha
      have hy : a • leftIdealGenerator e = y := by
        apply Subtype.ext
        exact ha
      rw [← hy, f.map_smul]
      apply Subtype.ext
      change a * b = 0
      rw [hb, mul_zero]
    · right
      apply LinearMap.ext
      intro y
      obtain ⟨a, ha⟩ := y.2
      change a * e = y.1 at ha
      have hy : a • leftIdealGenerator e = y := by
        apply Subtype.ext
        exact ha
      rw [← hy, f.map_smul]
      change a • f (leftIdealGenerator e) = a • leftIdealGenerator e
      apply Subtype.ext
      change a * b = a * e
      rw [hb]

/-- Contragredient duality sends the primitive left ideal to an
indecomposable right injective. -/
theorem primitiveInjectiveFGObj_indecomposable {e : A}
    (D : PrimitiveIdempotentData e) :
    Indecomposable (primitiveInjectiveFGObj (k := k) e) :=
  fgIndecomposable_of_isIndecomposableModule
    (primitiveInjectiveFGObj (k := k) e)
    (dualFunctor_indec k A (leftIdeal_isIndecomposableModule D))

end MBDVendor.Magnitude.RightModule
