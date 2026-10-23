module

public import MultiplicativeBasisDeformations.Foundations.SquareZero

/-!
# Unit-normalized representatives of Hochschild two-classes

Every Hochschild two-cocycle `μ` of internal degree `q` is cohomologous, by the coboundary of the
degree-`q` one-cochain `h(a) = a μ(1, 1)`, to a cocycle vanishing when either argument is `1`
(`exists_unit_normalized`). So statements about the classes of `HH²(Λ)_q` may be checked on
unit-normalized cocycles; this is how the Bockstein statement of Proposition 10.3
(`BocksteinStmt`) covers every class of `HH²(A⁽²⁾)_q`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}

theorem isHCocycle_hcobdry (h : Λ →ₗ[R] Λ) : IsHCocycle (hcobdry h) := by
  intro a b c
  simp only [hcobdry_apply, mul_add, mul_sub, add_mul, sub_mul, mul_assoc]
  abel

/-- **Every Hochschild two-cocycle of internal degree `q` is cohomologous to a unit-normalized
one**: subtract the coboundary of `h(a) = a μ(1, 1)`, of degree `q`. -/
theorem exists_unit_normalized {μ : Λ →ₗ[R] Λ →ₗ[R] Λ} (hμ : IsHCocycle μ) {q : ℤ}
    (hd : HDeg GΛ μ q) :
    ∃ h : Λ →ₗ[R] Λ, (∀ p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom (p + q) (h a)) ∧
      IsHCocycle (μ - hcobdry h) ∧ (∀ a, (μ - hcobdry h) 1 a = 0) ∧
        ∀ a, (μ - hcobdry h) a 1 = 0 := by
  set c := μ 1 1
  refine ⟨LinearMap.mulRight R c, fun p a ha ↦ ?_, fun a b d ↦ ?_, fun b ↦ ?_, fun a ↦ ?_⟩
  · have hc : GΛ.gr.IsHom (0 + 0 + q) c := hd 0 0 1 1 GΛ.one_hom GΛ.one_hom
    have := GΛ.mul_hom _ _ _ _ ha hc
    simpa using this
  · have h1 := hμ a b d
    have h2 := isHCocycle_hcobdry (LinearMap.mulRight R c) a b d
    simp only [LinearMap.sub_apply, mul_sub, sub_mul]
    rw [← sub_eq_zero.mpr (show a * μ b d - μ (a * b) d + μ a (b * d) - μ a b * d =
      a * hcobdry (LinearMap.mulRight R c) b d - hcobdry (LinearMap.mulRight R c) (a * b) d +
        hcobdry (LinearMap.mulRight R c) a (b * d) - hcobdry (LinearMap.mulRight R c) a b * d by
      rw [h1, h2])]
    abel
  · have := hμ 1 1 b
    simp only [one_mul, sub_self, zero_add] at this
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hcobdry_apply]
    simp only [LinearMap.mulRight_apply, one_mul]
    rw [sub_eq_zero] at this
    rw [this]; abel
  · have := hμ a 1 1
    simp only [mul_one, add_sub_cancel_right] at this
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hcobdry_apply]
    simp only [LinearMap.mulRight_apply, one_mul, mul_one]
    rw [sub_eq_zero] at this
    rw [← this]; abel

end GExt

end MultiplicativeBasisDeformations
