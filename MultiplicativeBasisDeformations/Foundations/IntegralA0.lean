import MultiplicativeBasisDeformations.Foundations.IntegralTable
import MultiplicativeBasisDeformations.Foundations.HomBasis
import MultiplicativeBasisDeformations.Foundations.A0Graded
import MultiplicativeBasisDeformations.Foundations.PsiInjective
import MultiplicativeBasisDeformations.Foundations.ZModFour
import MultiplicativeBasisDeformations.Foundations.GradedBasis

/-!
# `A⁽⁴⁾ = 𝒪P` and its reduction to `A⁽²⁾` (Proposition 10.1, the algebra)

`integral-deformations.tex:29–31, 45–60`: "Its projective corner is `A⁽²⁾` […]. Put
`A⁽⁴⁾ = 𝒪P`, graded by length."

Setting (`TabIso`): a scalar mesh category over `𝔽₂` with mesh data `D` and a ray table `P`
with a ray degree `d` and an isomorphism `Θ : 𝔽₂P ≅ A⁽²⁾` taking every ray to a homogeneous
element of its degree and the vertex rays to the vertex idempotents (for `C⁽²⁾` this is
`IndSkeleton.Θ₂`). Then `A⁽⁴⁾ = 𝒪P` is graded by the degrees of the rays (`galgO`), and the
reduction `π : 𝒪P → 𝔽₂P ≅ A⁽²⁾` is a reduction of graded algebras (`isRed_πO`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]

theorem hfin2 : ∀ x y : V, FiniteDimensional 𝔽₂ (obj c x ⟶ obj c y) := fun x y ↦ hfd x y

variable {R : Type} [Fintype R] [DecidableEq R]

/-- **A ray table of `A⁽²⁾`**: ray degrees and `Θ : 𝔽₂P ≅ A⁽²⁾`, homogeneous on the rays and
matching the vertex idempotents. -/
structure TabIso (P : RaySys.Mult D.PV R) where
  d : R → ℤ
  d_mul : ∀ r s t, P.mul r s = some t → d t = d r + d s
  d_e : ∀ x, d (P.e x) = 0
  d_nonneg : ∀ r, 0 ≤ d r
  Θ : P.Lin 𝔽₂ ≃ₐ[𝔽₂] (Alg D.F0)ᵐᵒᵖ
  Θ_hom : ∀ r, (lenA0 D (hfin2 (c := c))).IsHom (d r).toNat (Θ (P.b 𝔽₂ r))
  Θ_e : ∀ x, Θ (P.b 𝔽₂ (P.e x)) = eP D x

variable {D} {P : RaySys.Mult D.PV R} (T : TabIso D P)

/-- **`𝒪P` as a graded algebra.** -/
abbrev galgO : GAlg (R := ZMod 4) (P.Lin (ZMod 4)) :=
  P.galgLin T.d T.d_mul (ZMod 4) T.d_e

/-- **The reduction `𝒪P → A⁽²⁾`.** -/
abbrev πO : P.Lin (ZMod 4) →+* (Alg D.F0)ᵐᵒᵖ :=
  T.Θ.toRingHom.comp (P.redLin Z4.red)

theorem πO_b (r : R) : πO T (P.b (ZMod 4) r) = T.Θ (P.b 𝔽₂ r) := by
  simp only [πO, RingHom.comp_apply]
  rw [RaySys.Mult.redLin_b]; rfl

theorem πO_smul (a : ZMod 4) (x : P.Lin (ZMod 4)) : πO T (a • x) = Z4.red a • πO T x := by
  simp only [πO, RingHom.comp_apply, RaySys.Mult.redLin_smul]
  exact map_smul T.Θ _ _

theorem πO_eq_zero {x : P.Lin (ZMod 4)} (h : πO T x = 0) :
    ∀ r, Z4.red ((P.basis (ZMod 4)).repr x r) = 0 := by
  intro r
  have h' : P.redLin Z4.red x = 0 := T.Θ.injective (by rw [map_zero]; exact h)
  rw [← RaySys.Mult.repr_redLin, h', map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem galgA0_isHom_len' (d : ℕ) (a : (Alg D.F0)ᵐᵒᵖ) :
    (galgA0 D (hfin2 (c := c))).gr.IsHom d a ↔ (lenA0 D (hfin2 (c := c))).IsHom d a :=
  ZGr.ofLen_isHom (lenA0 D (hfin2 (c := c))) d a

theorem repr_Θ_symm_eq_zero (p' : ℕ) (a : (Alg D.F0)ᵐᵒᵖ)
    (ha' : (lenA0 D (hfin2 (c := c))).IsHom p' a) (r : R) (hr : T.d r ≠ p') :
    (P.basis 𝔽₂).repr (T.Θ.symm a) r = 0 := by
  have e : ((P.basis 𝔽₂).map T.Θ.toLinearEquiv).repr a r = (P.basis 𝔽₂).repr (T.Θ.symm a) r := by
    rw [Module.Basis.map_repr]; rfl
  rw [← e]
  refine LenGrading.repr_eq_zero_of_isHom (lenA0 D (hfin2 (c := c)))
    ((P.basis 𝔽₂).map T.Θ.toLinearEquiv) (fun r ↦ (T.d r).toNat) (fun r ↦ by
      rw [Module.Basis.map_apply, RaySys.Mult.basis_apply]; exact T.Θ_hom r) ha' ?_
  have := T.d_nonneg r
  omega

/-- A lift of an element of `A⁽²⁾` to `𝒪P`. -/
def liftO (a : (Alg D.F0)ᵐᵒᵖ) : P.Lin (ZMod 4) :=
  ∑ r, Z4.lift ((P.basis 𝔽₂).repr (T.Θ.symm a) r) • P.b (ZMod 4) r

theorem πO_liftO (a : (Alg D.F0)ᵐᵒᵖ) : πO T (liftO T a) = a := by
  rw [liftO, map_sum]
  simp only [πO_smul, πO_b, Z4.red_lift, ← map_smul T.Θ]
  rw [← map_sum]
  conv_rhs => rw [← T.Θ.apply_symm_apply a, ← (P.basis 𝔽₂).sum_repr (T.Θ.symm a)]
  simp only [RaySys.Mult.basis_apply]

theorem liftO_isHom (p' : ℕ) (a : (Alg D.F0)ᵐᵒᵖ) (ha' : (lenA0 D (hfin2 (c := c))).IsHom p' a) :
    (galgO T).gr.IsHom p' (liftO T a) := by
  refine (galgO T).gr.isHom_sum _ _ fun r _ ↦ ?_
  by_cases hr : T.d r = p'
  · rw [← hr]
    exact (galgO T).gr.isHom_smul _ (P.grLin_b T.d (ZMod 4) r)
  · rw [repr_Θ_symm_eq_zero T p' a ha' r hr, Z4.lift_zero, zero_smul]
    exact (galgO T).gr.isHom_zero _

theorem πO_lift (p : ℤ) (a : (Alg D.F0)ᵐᵒᵖ) (ha : (galgA0 D (hfin2 (c := c))).gr.IsHom p a) :
    ∃ x', (galgO T).gr.IsHom p x' ∧ πO T x' = a := by
  rcases lt_or_ge p 0 with hp | hp
  · refine ⟨0, (galgO T).gr.isHom_zero _, ?_⟩
    rw [map_zero]
    exact ((galgA0_isHom_neg D (hfin2 (c := c)) hp a).1 ha).symm
  obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
  exact ⟨liftO T a, liftO_isHom T p' a ((galgA0_isHom_len' p' a).1 ha), πO_liftO T a⟩

theorem πO_deg (p : ℤ) (x : P.Lin (ZMod 4)) (hx : (galgO T).gr.IsHom p x) :
    (galgA0 D (hfin2 (c := c))).gr.IsHom p (πO T x) := by
  have e := (P.basis (ZMod 4)).sum_repr x
  rw [← e, map_sum]
  refine (galgA0 D (hfin2 (c := c))).gr.isHom_sum _ _ fun r _ ↦ ?_
  rw [πO_smul, RaySys.Mult.basis_apply, πO_b]
  by_cases hr : T.d r = p
  · refine (galgA0 D (hfin2 (c := c))).gr.isHom_smul _ ?_
    rw [← hr]
    rw [show T.d r = ((T.d r).toNat : ℤ) from (Int.toNat_of_nonneg (T.d_nonneg r)).symm,
      galgA0_isHom_len']
    exact T.Θ_hom r
  · rw [P.repr_eq_zero_of_isHom T.d (ZMod 4) hx hr, map_zero, zero_smul]
    exact (galgA0 D (hfin2 (c := c))).gr.isHom_zero _

theorem πO_ker (x : P.Lin (ZMod 4)) (hx : πO T x = 0) : ∃ y, x = (2 : ZMod 4) • y := by
  choose y hy using fun r ↦ Z4.exists_two_mul_of_red (πO_eq_zero T hx r)
  refine ⟨∑ r, y r • P.b (ZMod 4) r, ?_⟩
  conv_lhs => rw [← (P.basis (ZMod 4)).sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [hy r, smul_smul, RaySys.Mult.basis_apply]

theorem πO_ann (x : P.Lin (ZMod 4)) (hx : (2 : ZMod 4) • x = 0) : πO T x = 0 := by
  have hr : ∀ r, Z4.red ((P.basis (ZMod 4)).repr x r) = 0 := fun r ↦ by
    have := congrArg (fun z ↦ (P.basis (ZMod 4)).repr z r) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    exact (Z4.two_mul_eq_zero_iff _).1 this
  have h' : P.redLin Z4.red x = 0 := by
    refine (P.basis 𝔽₂).ext_elem fun r ↦ ?_
    rw [RaySys.Mult.repr_redLin, hr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  simp only [πO, RingHom.comp_apply, h', map_zero]

/-- **`π` is a reduction of graded algebras.** -/
theorem isRed_πO : IsRed (galgO T) (galgA0 D (hfin2 (c := c))) (πO T) :=
  ⟨πO_smul T, πO_deg T, πO_lift T, πO_ker T, πO_ann T⟩

end MeshWalk

end MultiplicativeBasisDeformations
