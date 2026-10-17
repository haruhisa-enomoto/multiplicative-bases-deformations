import MultiplicativeBasisDeformations.Foundations.RepFinite
import MultiplicativeBasisDeformations.Foundations.CornerAlgebra
import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd
import MBDVendor.Magnitude.Algebra.IndecomposableLocalEnd

/-!
# Idempotent corners of representation-finite algebras

Lemma 3.1(1), second part (`projective-rays.tex:38–45`): for `C = eAe`, the
extension of `C`-modules to `A`-modules is fully faithful and preserves finite
dimension, indecomposability and isomorphism classes; hence `C` is
representation-finite. The source uses induction `V ↦ V ⊗_C eA`, whose unit
`V → (V ⊗_C eA)e` is an isomorphism. We use the adjoint form, coinduction
`V ↦ Hom_C(Ae, V)`, whose counit `Hom_C(Ae, V)e → V` is an isomorphism; this
avoids tensor products over the noncommutative ring `C`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] {e : A} (he : IsIdempotentElem e)

namespace Coind

/-- The left ideal `Ae`. -/
def leftIdeal : AddSubgroup A where
  carrier := {x | x * e = x}
  add_mem' {x y} hx hy := by
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  zero_mem' := zero_mul e
  neg_mem' {x} hx := by
    change -x * e = -x
    rw [neg_mul, hx]

variable {he}

theorem mem_leftIdeal {x : A} : x ∈ leftIdeal (e := e) ↔ x * e = x := Iff.rfl

/-- `Ae` is a right `C`-module. -/
instance : SMul he.Cornerᵐᵒᵖ (leftIdeal (e := e)) where
  smul c x := ⟨x.1 * cornerVal he c.unop, by
    change x.1 * cornerVal he c.unop * e = _
    rw [mul_assoc, corner_mul_right]⟩

@[simp] theorem smul_val (c : he.Cornerᵐᵒᵖ) (x : leftIdeal (e := e)) :
    ((c • x : leftIdeal (e := e)) : A) = x.1 * cornerVal he c.unop := rfl

instance : Module he.Cornerᵐᵒᵖ (leftIdeal (e := e)) where
  one_smul x := Subtype.ext (by
    rw [smul_val, MulOpposite.unop_one, corner_one_val]; exact x.2)
  mul_smul c d x := Subtype.ext (by
    simp only [smul_val, MulOpposite.unop_mul, corner_mul_val, mul_assoc])
  smul_zero c := Subtype.ext (by simp)
  smul_add c x y := Subtype.ext (by simp [add_mul])
  add_smul c d x := Subtype.ext (by simp [mul_add])
  zero_smul x := Subtype.ext (by simp)

/-- Left multiplication by `a` on `Ae`. -/
def lmul (a : A) : leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] leftIdeal (e := e) where
  toFun x := ⟨a * x.1, by change a * x.1 * e = a * x.1; rw [mul_assoc, x.2]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (by simp [mul_assoc])

@[simp] theorem lmul_val (a : A) (x : leftIdeal (e := e)) : (lmul (he := he) a x : A) = a * x.1 := rfl

variable (he) in
/-- The carrier `Hom_C(Ae, V)` of the coinduced module. -/
def Obj (V : RightModuleCat he.Corner) := leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V

instance (V : RightModuleCat he.Corner) : AddCommGroup (Obj he V) :=
  inferInstanceAs (AddCommGroup (leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V))

instance (V : RightModuleCat he.Corner) : FunLike (Obj he V) (leftIdeal (e := e)) V :=
  inferInstanceAs (FunLike (leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V) _ _)

instance (V : RightModuleCat he.Corner) :
    LinearMapClass (Obj he V) he.Cornerᵐᵒᵖ (leftIdeal (e := e)) V :=
  inferInstanceAs (LinearMapClass (leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V) _ _ _)

instance (V : RightModuleCat he.Corner) : SMul Aᵐᵒᵖ (Obj he V) where
  smul a φ := LinearMap.comp (show leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V from φ) (lmul a.unop)

theorem smul_apply' {V : RightModuleCat he.Corner} (a : Aᵐᵒᵖ) (φ : Obj he V) (y : leftIdeal (e := e)) :
    (a • φ) y = φ (lmul (he := he) a.unop y) := rfl

@[ext] theorem Obj.ext {V : RightModuleCat he.Corner} {φ ψ : Obj he V} (h : ∀ y, φ y = ψ y) : φ = ψ :=
  LinearMap.ext h

theorem add_apply' {V : RightModuleCat he.Corner} (φ ψ : Obj he V) (y : leftIdeal (e := e)) :
    (φ + ψ) y = φ y + ψ y := rfl

theorem zero_apply' {V : RightModuleCat he.Corner} (y : leftIdeal (e := e)) :
    (0 : Obj he V) y = 0 := rfl

instance (V : RightModuleCat he.Corner) : Module Aᵐᵒᵖ (Obj he V) where
  one_smul φ := Obj.ext fun y ↦ by
    rw [smul_apply']; congr 1; exact Subtype.ext (by simp)
  mul_smul a b φ := Obj.ext fun y ↦ by
    rw [smul_apply', smul_apply', smul_apply']; congr 1
    exact Subtype.ext (by simp [mul_assoc])
  smul_zero a := Obj.ext fun y ↦ rfl
  smul_add a φ ψ := Obj.ext fun y ↦ rfl
  add_smul a b φ := Obj.ext fun y ↦ by
    rw [smul_apply', add_apply', smul_apply', smul_apply', ← map_add]; congr 1
    exact Subtype.ext (by simp [add_mul])
  zero_smul φ := Obj.ext fun y ↦ by
    rw [smul_apply', zero_apply', ← map_zero (show leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V from φ)]
    congr 1; exact Subtype.ext (by simp)

variable (he) in
/-- The coinduced right `A`-module `Hom_C(Ae, V)`. -/
def coind (V : RightModuleCat he.Corner) : RightModuleCat A := ModuleCat.of Aᵐᵒᵖ (Obj he V)

/-- Postcomposition with a map of `C`-modules. -/
def mapObj {V W : RightModuleCat he.Corner} (f : V ⟶ W) : Obj he V →ₗ[Aᵐᵒᵖ] Obj he W where
  toFun φ := (f.hom : V →ₗ[he.Cornerᵐᵒᵖ] W).comp (show leftIdeal (e := e) →ₗ[he.Cornerᵐᵒᵖ] V from φ)
  map_add' φ ψ := Obj.ext fun y ↦ map_add f.hom (φ y) (ψ y)
  map_smul' a φ := Obj.ext fun y ↦ rfl

theorem mapObj_apply {V W : RightModuleCat he.Corner} (f : V ⟶ W) (φ : Obj he V)
    (y : leftIdeal (e := e)) : mapObj f φ y = f.hom (φ y) := rfl

variable (he) in
/-- **Coinduction** `V ↦ Hom_C(Ae, V)`. -/
def functor : RightModuleCat he.Corner ⥤ RightModuleCat A where
  obj := coind he
  map f := ModuleCat.ofHom (mapObj f)
  map_id V := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro φ; exact Obj.ext fun y ↦ rfl
  map_comp f g := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro φ; exact Obj.ext fun y ↦ rfl

instance (V : RightModuleCat he.Corner) :
    FunLike ((functor he).obj V) (leftIdeal (e := e)) V :=
  inferInstanceAs (FunLike (Obj he V) _ _)

instance (V : RightModuleCat he.Corner) :
    LinearMapClass ((functor he).obj V) he.Cornerᵐᵒᵖ (leftIdeal (e := e)) V :=
  inferInstanceAs (LinearMapClass (Obj he V) _ _ _)

/-- The generator `e ∈ Ae`. -/
def eL : leftIdeal (e := e) := ⟨e, by change e * e = e; exact he.eq⟩

theorem ey_mem (y : leftIdeal (e := e)) : e * y.1 ∈ Subsemigroup.corner e :=
  ⟨y.1, by change e * y.1 * e = e * y.1; rw [mul_assoc, y.2]⟩

variable (he) in
/-- `ey ∈ eAe` for `y ∈ Ae`. -/
def ey (y : leftIdeal (e := e)) : he.Corner := cornerMk he (e * y.1) (ey_mem y)

theorem ey_add (y z : leftIdeal (e := e)) : ey he (y + z) = ey he y + ey he z :=
  corner_ext he (by simp [ey, mul_add])

theorem ey_smul (c : he.Cornerᵐᵒᵖ) (y : leftIdeal (e := e)) :
    ey he (c • y) = ey he y * c.unop :=
  corner_ext he (by simp [ey, mul_assoc])

theorem ey_eL : ey he (eL (he := he)) = 1 := corner_ext he (by simp [ey, eL, he.eq])

variable (he) in
/-- `ψ_v : y ↦ v · (ey)`. -/
def psi {V : RightModuleCat he.Corner} (v : V) : Obj he V where
  toFun y := MulOpposite.op (ey he y) • v
  map_add' y z := by rw [ey_add, MulOpposite.op_add, add_smul]
  map_smul' c y := by
    rw [ey_smul, MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]; rfl

theorem psi_apply {V : RightModuleCat he.Corner} (v : V) (y : leftIdeal (e := e)) :
    psi he v y = MulOpposite.op (ey he y) • v := rfl

theorem psi_eL {V : RightModuleCat he.Corner} (v : V) : psi he v (eL (he := he)) = v := by
  rw [psi_apply, ey_eL, MulOpposite.op_one, one_smul]

/-- `y · (ex) = yx` in `Ae`. -/
theorem smul_ey (y x : leftIdeal (e := e)) :
    (MulOpposite.op (ey he x)) • y = lmul (he := he) y.1 x :=
  Subtype.ext (by
    simp only [smul_val, MulOpposite.unop_op, lmul_val, ey, cornerVal_mk]
    rw [← mul_assoc, y.2])

/-- `y · φ = ψ_{φ(y)}`. -/
theorem smul_eq_psi {V : RightModuleCat he.Corner} (φ : Obj he V) (y : leftIdeal (e := e)) :
    MulOpposite.op y.1 • φ = psi he (φ y) := Obj.ext fun x ↦ by
  rw [smul_apply', psi_apply, MulOpposite.unop_op, ← smul_ey, map_smul]

instance faithful : (functor he).Faithful where
  map_injective {V W} f g h := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro v
    have := congrArg (fun F ↦ (F.hom (psi he v)) (eL (he := he))) h
    change f.hom (psi he v eL) = g.hom (psi he v eL) at this
    rwa [psi_eL] at this

theorem psi_add {V : RightModuleCat he.Corner} (v w : V) : psi he (v + w) = psi he v + psi he w :=
  Obj.ext fun y ↦ by rw [add_apply', psi_apply, psi_apply, psi_apply, smul_add]

theorem psi_smul {V : RightModuleCat he.Corner} (c : he.Cornerᵐᵒᵖ) (v : V) :
    psi he (c • v) = MulOpposite.op (cornerVal he c.unop) • psi he v := Obj.ext fun y ↦ by
  rw [smul_apply', psi_apply, psi_apply, smul_smul]
  congr 1
  apply MulOpposite.unop_injective
  apply corner_ext he
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op, corner_mul_val, ey, cornerVal_mk,
    lmul_val]
  rw [← mul_assoc, corner_mul_right, ← mul_assoc, corner_mul_left]

theorem lmul_eL (y : leftIdeal (e := e)) : lmul (he := he) y.1 (eL (he := he)) = y :=
  Subtype.ext (by change y.1 * e = y.1; exact y.2)

theorem lmul_corner_eL (c : he.Cornerᵐᵒᵖ) :
    lmul (he := he) (cornerVal he c.unop) (eL (he := he)) = c • eL (he := he) :=
  Subtype.ext (by
    change cornerVal he c.unop * e = e * cornerVal he c.unop
    rw [corner_mul_right, corner_mul_left])

instance full : (functor he).Full where
  map_surjective {V W} F := by
    let Fh : Obj he V →ₗ[Aᵐᵒᵖ] Obj he W := F.hom
    let f0 : V →ₗ[he.Cornerᵐᵒᵖ] W :=
      { toFun v := Fh (psi he v) eL
        map_add' v w := by
          change Fh (psi he (v + w)) eL = _
          rw [psi_add, map_add]; rfl
        map_smul' c v := by
          change Fh (psi he (c • v)) eL = _
          rw [psi_smul, map_smul]
          change Fh (psi he v) (lmul (he := he) (cornerVal he c.unop) eL) = _
          rw [lmul_corner_eL, map_smul]; rfl }
    refine ⟨ModuleCat.ofHom f0, ?_⟩
    apply ModuleCat.hom_ext; apply LinearMap.ext
    change ∀ φ : Obj he V, mapObj (V := V) (W := W) (ModuleCat.ofHom f0) φ = Fh φ
    intro φ
    refine Obj.ext fun y ↦ ?_
    change Fh (psi he (φ y)) eL = Fh φ y
    rw [← smul_eq_psi, map_smul]
    change Fh φ (lmul (he := he) y.1 eL) = _
    rw [lmul_eL]

instance : (functor he).Additive where
  map_add := by
    intro V W f g
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro φ
    exact Obj.ext fun y ↦ rfl

/-- `xe ∈ Ae`. -/
def xe (x : A) : leftIdeal (e := e) := ⟨x * e, by change x * e * e = x * e; rw [mul_assoc, he.eq]⟩

theorem xe_smul (c : k) (x : A) :
    xe (he := he) (c • x) = (MulOpposite.op (algebraMap k he.Corner c)) • xe (he := he) x :=
  Subtype.ext (by
    change c • x * e = x * e * cornerVal he (algebraMap k he.Corner c)
    rw [show cornerVal he (algebraMap k he.Corner c) = c • e from by
      change cornerVal he (c • (1 : he.Corner)) = c • e
      rw [corner_smul_val, corner_one_val]]
    rw [mul_smul_comm, mul_assoc, he.eq, smul_mul_assoc])

/-- Evaluation of `Hom_C(Ae, V)` on the elements `xe`, a `k`-linear injection
into `Hom_k(A, V)`. -/
def evalK (V : RightModuleCat he.Corner) : coind he V →ₗ[k] (A →ₗ[k] V) where
  toFun φ :=
    { toFun x := (show Obj he V from φ) (xe (he := he) x)
      map_add' x y := by
        rw [← map_add]; congr 1; exact Subtype.ext (add_mul _ _ _)
      map_smul' c x := by
        rw [xe_smul, map_smul]; rfl }
  map_add' φ ψ := LinearMap.ext fun x ↦ rfl
  map_smul' c φ := LinearMap.ext fun x ↦ by
    change (show Obj he V from φ) (lmul (he := he) (algebraMap k A c) (xe (he := he) x)) =
      c • (show Obj he V from φ) (xe (he := he) x)
    rw [show lmul (he := he) (algebraMap k A c) (xe (he := he) x) = xe (he := he) (c • x) from
      Subtype.ext (by
        change algebraMap k A c * (x * e) = c • x * e
        rw [← mul_assoc, ← Algebra.smul_def]), xe_smul, map_smul]
    rfl

theorem evalK_injective (V : RightModuleCat he.Corner) : Function.Injective (evalK (k := k) V) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ
  rw [Submodule.mem_bot]
  change (show Obj he V from φ) = 0
  refine Obj.ext fun y ↦ ?_
  have := LinearMap.congr_fun hφ y.1
  change (show Obj he V from φ) (xe (he := he) y.1) = 0 at this
  rwa [show xe (he := he) y.1 = y from Subtype.ext y.2] at this

theorem coind_finite [FiniteDimensional k A] (V : RightModuleCat he.Corner) [Module.Finite k V] :
    Module.Finite k (coind he V) :=
  Module.Finite.of_injective (evalK V) (evalK_injective V)

end Coind

/-- The corner is finite-dimensional. -/
theorem corner_finite [FiniteDimensional k A] : Module.Finite k he.Corner := by
  let f : he.Corner →ₗ[k] A :=
    { toFun := cornerVal he
      map_add' := corner_add_val he
      map_smul' := corner_smul_val he }
  exact Module.Finite.of_injective f fun x y h ↦ corner_ext he h

open Coind in
/-- **Lemma 3.1(1)**, second part: every idempotent corner of a
representation-finite algebra is representation-finite. -/
theorem corner_isRepresentationFinite_of [FiniteDimensional k A] (hA : IsRepresentationFinite k A) :
    IsRepresentationFinite k he.Corner := by
  classical
  obtain ⟨N, X, hX, hcomp⟩ := hA
  haveI : Module.Finite k he.Corner := corner_finite he
  let P : Fin N → Prop := fun i ↦ ∃ V : RightModuleCat he.Corner,
    IsFiniteIndecomposable k he.Corner V ∧ Nonempty ((functor he).obj V ≅ X i)
  let T := {i // P i}
  let eT := Fintype.equivFin T
  refine ⟨Fintype.card T, fun j ↦ (eT.symm j).2.choose, fun j ↦ (eT.symm j).2.choose_spec.1, ?_⟩
  intro V hV
  haveI := hV.1
  have hfin : Module.Finite k ((functor he).obj V) := coind_finite V
  haveI : Module.Finite k he.Cornerᵐᵒᵖ := inferInstance
  haveI : IsLocalRing (End V) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := he.Cornerᵐᵒᵖ) V hV.2
  haveI : IsLocalRing (End ((functor he).obj V)) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm
      (MBDVendor.Magnitude.CategoryTheory.Functor.endRingEquivOfFullyFaithful (functor he) V)
  have hind : Indecomposable ((functor he).obj V) :=
    MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _
  obtain ⟨i, ⟨e1⟩⟩ := hcomp _ ⟨hfin, hind⟩
  let t : T := ⟨i, V, hV, ⟨e1⟩⟩
  refine ⟨eT t, ?_⟩
  have ht : eT.symm (eT t) = t := eT.symm_apply_apply t
  show Nonempty (V ≅ (eT.symm (eT t)).2.choose)
  rw [ht]
  exact ⟨((functor he).preimageIso (e1 ≪≫ t.2.choose_spec.2.some.symm))⟩

end MultiplicativeBasisDeformations
