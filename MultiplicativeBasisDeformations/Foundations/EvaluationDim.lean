import MultiplicativeBasisDeformations.Foundations.GradedHomDimension
import MultiplicativeBasisDeformations.Foundations.StandardForm

/-!
# Proposition 2.10(3): dimensions of evaluated modules

`graded-category.tex:497–507` (`prop:projective-evaluation`(3)): "If `X₀` is the evaluation of
the object labelled by an indecomposable `A`-module `X`, then `dim_k X₀e_x = dim_k Xe_x` […]
`dim X₀e_x = dim C(P_x, X) = dim Xe_x`."

The evaluation at the projective label `P_x` is `C(P_x, X)`, of dimension `dim Hom_A(P_x, X)`
(`finrank_meshHom`, eq. graded-hom-dimensions); for `P_x ≅ e_xA`, `Hom_A(e_xA, X) ≅ Xe_x` by
evaluation at `e_x` (`homIdealEquiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra
open MBDVendor.Magnitude.RightModule

namespace MultiplicativeBasisDeformations

universe u

section Yoneda

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {e : A} (he : IsIdempotentElem e)
  (M : RightModuleCat A)

/-- The subspace `Me = {m | m e = m}`. -/
def fixSub : Submodule k M where
  carrier := {m | MulOpposite.op e • m = m}
  add_mem' {a b} ha hb := by
    change MulOpposite.op e • (a + b) = a + b
    rw [smul_add, ha, hb]
  zero_mem' := smul_zero _
  smul_mem' c m hm := by
    change MulOpposite.op e • (c • m) = c • m
    rw [smul_comm, hm]

include he in
theorem gen_smul (x : rightIdeal e) : MulOpposite.op x.1 • rightIdealGenerator e = x := by
  apply Subtype.ext
  change e * x.1 = x.1
  obtain ⟨a, ha⟩ := x.2
  change e * a = x.1 at ha
  rw [← ha, ← mul_assoc, he.eq]

include he in
/-- **`Hom_A(eA, M) ≅ Me`**, by evaluation at `e`. -/
def homIdealEquiv : (idealMod e ⟶ M) ≃ₗ[k] fixSub (k := k) (e := e) M where
  toFun f := ⟨f.hom (rightIdealGenerator e), by
    change MulOpposite.op e • f.hom (rightIdealGenerator e) = _
    rw [← f.hom.map_smul]
    congr 1
    apply Subtype.ext
    change e * e = e
    exact he.eq⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun m := ModuleCat.ofHom
    { toFun := fun x ↦ MulOpposite.op x.1 • m.1
      map_add' := fun x y ↦ by rw [Submodule.coe_add, MulOpposite.op_add, add_smul]
      map_smul' := fun r x ↦ by
        change MulOpposite.op ((x : A) * r.unop) • _ = r • (MulOpposite.op (x : A) • _)
        rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul] }
  left_inv f := by
    ext x
    change MulOpposite.op x.1 • f.hom (rightIdealGenerator e) = f.hom x
    rw [← f.hom.map_smul, gen_smul he]
  right_inv m := by
    apply Subtype.ext
    change MulOpposite.op e • m.1 = m.1
    exact m.2

end Yoneda

namespace IndSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- `Hom` in `ind(mod A)` is `Hom` of right modules. -/
def inclHomEquiv (X Y : S.Ind) : (X ⟶ Y) ≃ₗ[k] (S.incl.obj X ⟶ S.incl.obj Y) :=
  haveI : S.incl.Linear k := ⟨fun _ _ ↦ rfl⟩
  LinearEquiv.ofBijective (S.incl.mapLinearMap k)
    ⟨S.incl.map_injective, S.incl.map_surjective⟩

/-- **Proposition 2.10(3)** (`prop:projective-evaluation`(3)): for a projective label
`P_x ≅ eA`, the evaluation `X₀e_x = C(P_x, X)` of the object labelled by `X` has the dimension
of `Xe`. -/
theorem finrank_evaluation (p y : S.ARVertex) {e : A} (he : IsIdempotentElem e)
    (i : S.obj p ≅ idealMod e) :
    Module.finrank k (S.meshObj b p ⟶ S.meshObj b y) =
      Module.finrank k (fixSub (k := k) (e := e) (S.obj y)) := by
  rw [S.finrank_meshHom b p y, ((S.inclHomEquiv (S.label p) (S.label y)).trans
    ((Linear.homCongr k i (Iso.refl _)).trans (homIdealEquiv he (S.obj y)))).finrank_eq]

end IndSkeleton

end MultiplicativeBasisDeformations
