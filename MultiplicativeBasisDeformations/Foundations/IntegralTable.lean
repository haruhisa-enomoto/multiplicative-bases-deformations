import MultiplicativeBasisDeformations.Foundations.IntegralModuleLift
import MultiplicativeBasisDeformations.Foundations.TableAlg

/-!
# The graded algebra `𝒪P` and its reduction

For a ray table `P` with a degree function on the rays, the linearization `𝒪P` over any
commutative ring is graded by the degrees of the rays (`galgLin`), and reduction of
coefficients along a ring map is a ring map `𝒪P → kP` (`redLin`). This is the algebra
`A^{(4)} = 𝒪P` of `integral-deformations.tex`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] (P : Mult V R)
  (d : R → ℤ) (hde : ∀ x, d (P.e x) = 0) (hdm : ∀ r s t, P.mul r s = some t → d t = d r + d s)

section Grading

variable (O : Type u) [CommRing O] [Nontrivial O]

/-- The degree projections of `𝒪P`. -/
def projLin (p : ℤ) : P.Lin O →ₗ[O] P.Lin O :=
  (P.basis O).constr O fun r ↦ if d r = p then P.b O r else 0

theorem projLin_b (p : ℤ) (r : R) : P.projLin d O p (P.b O r) = if d r = p then P.b O r else 0 := by
  rw [projLin, ← basis_apply, Module.Basis.constr_basis]
  simp only [basis_apply]

theorem projLin_comp (p q : ℤ) : (P.projLin d O p).comp (P.projLin d O q) =
    if q = p then P.projLin d O q else 0 := by
  refine (P.basis O).ext fun r ↦ ?_
  simp only [LinearMap.comp_apply, basis_apply, projLin_b]
  by_cases hq : d r = q
  · rw [if_pos hq, projLin_b]
    by_cases hqp : q = p
    · subst hqp; rw [if_pos hq, if_pos rfl, projLin_b, if_pos hq]
    · rw [if_neg (by rw [hq]; exact hqp), if_neg hqp]; rfl
  · rw [if_neg hq, map_zero]
    split_ifs with hqp
    · rw [projLin_b, if_neg hq]
    · rfl

theorem projLin_sum : (∑ p ∈ Finset.univ.image d, P.projLin d O p) = LinearMap.id := by
  refine (P.basis O).ext fun r ↦ ?_
  rw [basis_apply, LinearMap.id_apply, LinearMap.sum_apply]
  simp only [projLin_b]
  rw [Finset.sum_ite_eq (Finset.univ.image d) (d r), if_pos
    (Finset.mem_image_of_mem _ (Finset.mem_univ r))]

theorem repr_projLin (p : ℤ) (x : P.Lin O) (r : R) :
    (P.basis O).repr (P.projLin d O p x) r = if d r = p then (P.basis O).repr x r else 0 := by
  have : (Finsupp.lapply r ∘ₗ (P.basis O).repr.toLinearMap) ∘ₗ P.projLin d O p =
      if d r = p then Finsupp.lapply r ∘ₗ (P.basis O).repr.toLinearMap else 0 := by
    refine (P.basis O).ext fun s ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply, basis_apply,
      projLin_b]
    by_cases hs : d s = p
    · rw [if_pos hs, ← basis_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with h1 h2 <;> simp_all
    · rw [if_neg hs, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with h1
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
          ← basis_apply, Module.Basis.repr_self, Finsupp.single_apply]
        rw [if_neg]; rintro rfl; exact hs h1
      · rfl
  have h := congrArg (fun f ↦ f x) this
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply] at h
  rw [h]
  split_ifs <;> rfl

/-- **The grading of `𝒪P` by the degrees of the rays.** -/
def grLin : GExt.ZGr (R := O) (P.Lin O) where
  proj := P.projLin d O
  supp := Finset.univ.image d
  proj_proj p q x := by
    have h := congrArg (fun f ↦ f x) (P.projLin_comp d O p q)
    simp only [LinearMap.comp_apply] at h
    rw [h]
    split_ifs <;> rfl
  proj_out p hp := by
    refine (P.basis O).ext fun r ↦ ?_
    rw [basis_apply, projLin_b, if_neg, LinearMap.zero_apply]
    rintro rfl; exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ r))
  sum x := by
    conv_lhs => rw [← LinearMap.id_apply (R := O) x, ← P.projLin_sum d O]
    rw [LinearMap.sum_apply]

theorem grLin_b (r : R) : (P.grLin d O).IsHom (d r) (P.b O r) := by
  change P.projLin d O (d r) (P.b O r) = P.b O r
  rw [projLin_b, if_pos rfl]

theorem repr_eq_zero_of_isHom {p : ℤ} {x : P.Lin O} (hx : (P.grLin d O).IsHom p x) {r : R}
    (hr : d r ≠ p) : (P.basis O).repr x r = 0 := by
  rw [← hx]
  change (P.basis O).repr (P.projLin d O p x) r = 0
  rw [repr_projLin, if_neg hr]

include hdm in
/-- **`𝒪P` as a graded algebra.** -/
def galgLin (hde' : ∀ x, d (P.e x) = 0) : GExt.GAlg (R := O) (P.Lin O) where
  gr := P.grLin d O
  mul_hom p q a b ha hb := by
    rw [← (P.basis O).sum_repr a, ← (P.basis O).sum_repr b, Finset.sum_mul]
    refine (P.grLin d O).isHom_sum _ _ fun r _ ↦ ?_
    rw [Finset.mul_sum]
    refine (P.grLin d O).isHom_sum _ _ fun s _ ↦ ?_
    by_cases hr : d r = p
    · by_cases hs : d s = q
      · rw [smul_mul_smul_comm, basis_apply, basis_apply, b_mul]
        refine (P.grLin d O).isHom_smul _ ?_
        cases h : P.mul r s with
        | none => exact (P.grLin d O).isHom_zero _
        | some t => rw [Option.elim_some, ← hr, ← hs, ← hdm r s t h]; exact P.grLin_b d O t
      · rw [P.repr_eq_zero_of_isHom d O hb hs, zero_smul, mul_zero]
        exact (P.grLin d O).isHom_zero _
    · rw [P.repr_eq_zero_of_isHom d O ha hr, zero_smul, zero_mul]
      exact (P.grLin d O).isHom_zero _
  one_hom := by
    rw [← sum_b_e]
    refine (P.grLin d O).isHom_sum _ _ fun x _ ↦ ?_
    rw [← hde' x]; exact P.grLin_b d O _

end Grading

/-! ### Reduction of coefficients -/

section Red

variable {O K : Type u} [CommRing O] [Nontrivial O] [CommRing K] [Nontrivial K] (red : O →+* K)

theorem map_mem_Lin (x : P.Lin O) : x.1.map red ∈ P.Lin K := by
  have hx : x = ∑ r, (P.basis O).repr x r • P.b O r := by
    conv_lhs => rw [← (P.basis O).sum_repr x]
    simp only [basis_apply]
  have e : x.1.map red = ∑ r, red ((P.basis O).repr x r) • (P.b K r).1 := by
    conv_lhs => rw [hx]
    ext i j
    rw [Matrix.map_apply, AddSubmonoidClass.coe_finset_sum, Matrix.sum_apply, map_sum,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    simp only [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, map_mul, b, rho]
    split_ifs <;> simp
  rw [e]
  exact Subalgebra.sum_mem _ fun r _ ↦ Subalgebra.smul_mem _ (P.b K r).2 _

/-- **Reduction `𝒪P → kP`.** -/
def redLin : P.Lin O →+* P.Lin K where
  toFun x := ⟨x.1.map red, P.map_mem_Lin red x⟩
  map_one' := Subtype.ext (by simp [Matrix.map_one])
  map_mul' x y := Subtype.ext (by simp [Matrix.map_mul])
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [Matrix.map_add])

theorem redLin_b (r : R) : P.redLin red (P.b O r) = P.b K r := by
  apply Subtype.ext
  change (P.rho O r).map red = P.rho K r
  ext i j
  simp only [Matrix.map_apply, rho]
  split_ifs <;> simp

theorem redLin_smul (a : O) (x : P.Lin O) : P.redLin red (a • x) = red a • P.redLin red x :=
  Subtype.ext (by ext i j; simp [redLin])

theorem repr_redLin (x : P.Lin O) (r : R) :
    (P.basis K).repr (P.redLin red x) r = red ((P.basis O).repr x r) := by
  have hx : P.redLin red x = ∑ s, red ((P.basis O).repr x s) • P.b K s := by
    conv_lhs => rw [← (P.basis O).sum_repr x]
    simp only [map_sum, redLin_smul, basis_apply, redLin_b]
  rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp only [map_smul, ← basis_apply, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ r, if_pos (Finset.mem_univ r)]

end Red

end Mult

end RaySys

end MultiplicativeBasisDeformations
