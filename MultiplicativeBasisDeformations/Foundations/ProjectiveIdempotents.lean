module

public import MultiplicativeBasisDeformations.Foundations.SimpleTops
public import MBDVendor.Magnitude.Algebra.RightModulePrimitiveIdempotent

/-!
# Indecomposable projectives are principal right ideals `eA`

Construction 2.8 keeps "the original labels `P_x = e_xA`"
(`graded-category.tex`). Every indecomposable projective label is
isomorphic to `eA` for a primitive idempotent `e`: a finite dual basis writes
`1_P` as a sum of composites `P → A → P`, one of them is invertible because
`End(P)` is local, so `P` is a retract of `A_A`, and the corresponding
idempotent endomorphism of `A_A` is left multiplication by `e`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u

section LocalRing

variable {R : Type*} [Ring R] [IsLocalRing R]

theorem exists_isUnit_of_sum {ι : Type*} (s : Finset ι) (f : ι → R)
    (h : IsUnit (∑ i ∈ s, f i)) : ∃ i ∈ s, IsUnit (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert a s ha ih =>
      rw [Finset.sum_insert ha] at h
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h1 | h1
      · exact ⟨a, Finset.mem_insert_self _ _, h1⟩
      · obtain ⟨i, hi, h2⟩ := ih h1
        exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

theorem idem_eq_zero_or_one {p : R} (hp : IsIdempotentElem p) : p = 0 ∨ p = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (add_sub_cancel p 1) with h | h
  · right
    obtain ⟨w, rfl⟩ := h
    have h1 : ((w⁻¹ : Rˣ) : R) * (w * w) = ((w⁻¹ : Rˣ) : R) * w := by rw [hp.eq]
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h1
  · left
    obtain ⟨w, hw⟩ := h
    have h1 : (w : R) * p = 0 := by rw [hw, sub_mul, one_mul, hp.eq, sub_self]
    have h2 := congrArg (((w⁻¹ : Rˣ) : R) * ·) h1
    simpa [← mul_assoc] using h2

end LocalRing

section Retract

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M] [IsLocalRing (Module.End R M)]

/-- A finitely generated projective module with local endomorphism ring is a
retract of the regular module. -/
theorem exists_retract_regular :
    ∃ (u : M →ₗ[R] R) (v : R →ₗ[R] M), v ∘ₗ u = LinearMap.id := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g LinearMap.id hg
  have hsum : (1 : Module.End R M) =
      ∑ i : Fin n, (g ∘ₗ LinearMap.single R (fun _ ↦ R) i) ∘ₗ (LinearMap.proj i ∘ₗ h) := by
    refine LinearMap.ext fun m ↦ ?_
    rw [LinearMap.sum_apply, Module.End.one_apply]
    have := congrArg (· m) hh
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    conv_lhs => rw [← this, ← Finset.univ_sum_single (h m), map_sum]
    rfl
  obtain ⟨i, -, hi⟩ := exists_isUnit_of_sum (R := Module.End R M) Finset.univ _
    (hsum ▸ isUnit_one)
  refine ⟨LinearMap.proj i ∘ₗ h, (hi.unit⁻¹ : (Module.End R M)ˣ).1 ∘ₗ
    (g ∘ₗ LinearMap.single R (fun _ ↦ R) i), ?_⟩
  have := hi.unit.inv_mul
  rw [IsUnit.unit_spec, Module.End.mul_eq_comp, Module.End.one_eq_id] at this
  rw [LinearMap.comp_assoc]
  exact this

end Retract

section Idempotent

open MBDVendor.Magnitude.RightModule

variable {A : Type u} [Ring A] [IsNoetherianRing Aᵐᵒᵖ] {M : Type*} [AddCommGroup M]
  [Module Aᵐᵒᵖ M]

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- An endomorphism of the regular module is right multiplication by its
value at `1`. -/
theorem regular_end_apply (E : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) (r : Aᵐᵒᵖ) : E r = r * E 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

variable (u : M →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) (v : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] M) (huv : v ∘ₗ u = LinearMap.id)

/-- The idempotent of a retract of the regular module. -/
def retractIdem : A := ((u ∘ₗ v) 1).unop

include huv in
omit [IsNoetherianRing Aᵐᵒᵖ] in
theorem u_eq_mul (m : M) : u m = u m * (u ∘ₗ v) 1 := by
  rw [← regular_end_apply]
  change u m = u (v (u m))
  rw [show v (u m) = m from congrArg (· m) huv]

include huv in
omit [IsNoetherianRing Aᵐᵒᵖ] in
theorem unop_u_eq (m : M) : retractIdem u v * (u m).unop = (u m).unop := by
  conv_rhs => rw [u_eq_mul u v huv m]
  rfl

include huv in
omit [IsNoetherianRing Aᵐᵒᵖ] in
theorem retractIdem_idem : IsIdempotentElem (retractIdem u v) := by
  have h := u_eq_mul u v huv (v 1)
  change retractIdem u v * retractIdem u v = retractIdem u v
  have : (u ∘ₗ v) 1 * (u ∘ₗ v) 1 = (u ∘ₗ v) 1 := h.symm
  exact congrArg MulOpposite.unop this

/-- `eA ≅ M` for a retract of the regular module. -/
def retractEquiv : rightIdeal (retractIdem u v) ≃ₗ[Aᵐᵒᵖ] M where
  toFun y := v (MulOpposite.op y.1)
  invFun m := ⟨(u m).unop, ⟨(u m).unop, unop_u_eq u v huv m⟩⟩
  map_add' y z := by
    change v (MulOpposite.op (y.1 + z.1)) = _
    rw [MulOpposite.op_add, map_add]
  map_smul' r y := by
    change v (MulOpposite.op (y.1 * r.unop)) = r • v (MulOpposite.op y.1)
    rw [MulOpposite.op_mul, MulOpposite.op_unop, ← smul_eq_mul, map_smul]
  left_inv y := by
    apply Subtype.ext
    change (u (v (MulOpposite.op y.1))).unop = y.1
    have h := regular_end_apply (u ∘ₗ v) (MulOpposite.op y.1)
    change u (v (MulOpposite.op y.1)) = _ at h
    rw [h, MulOpposite.unop_mul, MulOpposite.unop_op]
    exact rightIdeal_fixed (retractIdem_idem u v huv) y
  right_inv m := by
    change v (MulOpposite.op (u m).unop) = m
    rw [MulOpposite.op_unop]
    exact congrArg (· m) huv

include huv in
omit [IsNoetherianRing Aᵐᵒᵖ] in
theorem uv_apply (r : Aᵐᵒᵖ) : u (v r) = r * MulOpposite.op (retractIdem u v) := by
  rw [retractIdem, MulOpposite.op_unop]
  exact regular_end_apply (u ∘ₗ v) r

include huv in
/-- The idempotent of a retract with local endomorphism ring is primitive. -/
theorem retractIdem_primitive [IsLocalRing (Module.End Aᵐᵒᵖ M)] :
    PrimitiveIdempotentData (retractIdem u v) where
  idempotent := retractIdem_idem u v huv
  nonzero := by
    intro h0
    have hsub : ∀ m : M, m = 0 := by
      intro m
      have h1 : u m = 0 := by
        rw [u_eq_mul u v huv m]
        change u m * MulOpposite.op (retractIdem u v) = 0
        rw [h0, MulOpposite.op_zero, mul_zero]
      rw [← show v (u m) = m from congrArg (· m) huv, h1, map_zero]
    have : (1 : Module.End Aᵐᵒᵖ M) = 0 := LinearMap.ext fun m ↦ hsub _
    exact one_ne_zero this
  corner_idempotent := by
    intro b hb hleft hright
    let ρ : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := LinearMap.toSpanSingleton Aᵐᵒᵖ Aᵐᵒᵖ (MulOpposite.op b)
    have hρ : ∀ r, ρ r = r * MulOpposite.op b := fun r ↦ rfl
    have hbe : MulOpposite.op b * MulOpposite.op (retractIdem u v) = MulOpposite.op b := by
      rw [← MulOpposite.op_mul, hleft]
    have heb : MulOpposite.op (retractIdem u v) * MulOpposite.op b = MulOpposite.op b := by
      rw [← MulOpposite.op_mul, hright]
    have hbb : MulOpposite.op b * MulOpposite.op b = MulOpposite.op b := by
      rw [← MulOpposite.op_mul, hb.eq]
    let g : Module.End Aᵐᵒᵖ M := v ∘ₗ ρ ∘ₗ u
    have hg : IsIdempotentElem g := by
      change g ∘ₗ g = g
      refine LinearMap.ext fun m ↦ ?_
      change v (ρ (u (v (ρ (u m))))) = v (ρ (u m))
      rw [uv_apply u v huv]
      simp only [hρ]
      rw [mul_assoc, mul_assoc, heb, hbb]
    have hugv : u (g (v 1)) = MulOpposite.op b := by
      change u (v (ρ (u (v 1)))) = _
      rw [uv_apply u v huv, hρ, uv_apply u v huv, one_mul, heb, hbe]
    rcases idem_eq_zero_or_one hg with h | h
    · left
      rw [h, LinearMap.zero_apply, map_zero] at hugv
      exact MulOpposite.op_injective hugv.symm
    · right
      rw [h, Module.End.one_apply, uv_apply u v huv, one_mul] at hugv
      exact MulOpposite.op_injective hugv.symm

end Idempotent

namespace IndSkeleton

open MBDVendor.Magnitude.RightModule

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- **Each indecomposable projective label is `eA` for a primitive idempotent.** -/
theorem exists_primitive (x : Fin S.n) (hx : Projective (S.fg x)) :
    ∃ e : A, PrimitiveIdempotentData e ∧ Nonempty (rightIdealFGObj e ≅ S.fg x) := by
  haveI : Module.Projective Aᵐᵒᵖ (S.fg x) :=
    MBDVendor.Magnitude.moduleProjective_of_fgProjective (S.fg x) hx
  haveI : Module.Finite k Aᵐᵒᵖ := inferInstance
  haveI : Module.Finite k (S.obj x) := (S.isFiniteIndecomposable x).1
  haveI : IsLocalRing (End (S.obj x)) :=
    MBDVendor.Magnitude.moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖ) (S.obj x)
      (S.isFiniteIndecomposable x).2
  haveI : IsLocalRing (Module.End Aᵐᵒᵖ (S.fg x)) :=
    MBDVendor.Magnitude.RingEquiv.isLocalRing_noncomm (ModuleCat.endRingEquiv (S.obj x))
  obtain ⟨u, v, huv⟩ := exists_retract_regular (R := Aᵐᵒᵖ) (M := S.fg x)
  exact ⟨retractIdem u v, retractIdem_primitive u v huv,
    ⟨MBDVendor.QSE.Contragredient.fgModuleIsoOfLinearEquiv Aᵐᵒᵖ (retractEquiv u v huv)⟩⟩

/-- **The injective label of a projective label**: for each indecomposable
projective `P_x = e_xA` the indecomposable injective `I_x = D(Ae_x)` is a label
with `dim Hom_A(M, I_x) = dim Hom_A(P_x, M)` (both are `dim Me_x`). -/
theorem exists_injective_label (x : Fin S.n) (hx : Projective (S.fg x)) :
    ∃ I : Fin S.n, ∀ M : ModCat A,
      Module.finrank k (M ⟶ S.fg I) = Module.finrank k (S.fg x ⟶ M) := by
  obtain ⟨e, D, ⟨eP⟩⟩ := S.exists_primitive x hx
  obtain ⟨I, ⟨eI⟩⟩ := S.toVendor.fgObj_complete (primitiveInjectiveFGObj (k := k) e)
    (primitiveInjectiveFGObj_indecomposable D)
  refine ⟨I, fun M ↦ ?_⟩
  rw [← (Linear.homCongr k (Iso.refl M) eI).finrank_eq,
    finrank_hom_primitiveInjective_eq_coordinate D.idempotent,
    ← finrank_hom_rightIdeal_eq_coordinate D.idempotent,
    (Linear.homCongr k eP (Iso.refl M)).finrank_eq]

end IndSkeleton

end MultiplicativeBasisDeformations
