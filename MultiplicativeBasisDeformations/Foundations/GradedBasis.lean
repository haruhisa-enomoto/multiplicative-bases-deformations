module

public import MultiplicativeBasisDeformations.Foundations.CharDecomp

/-!
# Gradings with a homogeneous basis

For a graded algebra with a basis of homogeneous vectors: the coordinates of a homogeneous
element vanish off its degree, and a bilinear map is homogeneous of a given degree (or
character) as soon as its values on pairs of basis vectors are.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] (G : LenGrading k Λ)
  {ι : Type*} [Fintype ι] (β : Module.Basis ι k Λ) (δ : ι → ℕ) (hβ : ∀ i, G.IsHom (δ i) (β i))

theorem isHom_smul' {d : ℕ} (c : k) {x : Λ} (hx : G.IsHom d x) : G.IsHom d (c • x) := by
  unfold IsHom at *; rw [map_smul, hx]

theorem isHom_zero' (d : ℕ) : G.IsHom d (0 : Λ) := by unfold IsHom; rw [map_zero]

include hβ in
/-- The coordinates of a homogeneous element vanish off its degree. -/
theorem repr_eq_zero_of_isHom {d : ℕ} {a : Λ} (ha : G.IsHom d a) {i : ι} (hi : δ i ≠ d) :
    β.repr a i = 0 := by
  classical
  have key : a = β.equivFun.symm (fun j ↦ if δ j = d then β.repr a j else 0) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← ha, ← β.sum_repr a, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, G.proj_of_isHom (hβ j)]
    split_ifs <;> simp
  have := congrArg (fun z ↦ β.equivFun z i) key
  simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at this
  rw [this, if_neg hi]

include hβ in
/-- **A bilinear map homogeneous on basis pairs is homogeneous.** -/
theorem hasDeg₂_of_basis (q : ℕ) (μ : Λ →ₗ[k] Λ →ₗ[k] Λ)
    (h : ∀ i j, G.IsHom (δ i + δ j + q) (μ (β i) (β j))) : HasDeg₂ G q μ := by
  intro d e a b ha hb
  rw [← β.sum_repr a, ← β.sum_repr b, map_sum]
  refine isHom_sum G _ _ fun j _ ↦ ?_
  rw [map_smul, map_sum, LinearMap.sum_apply, Finset.smul_sum]
  refine isHom_sum G _ _ fun i _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hi : δ i = d
  · by_cases hj : δ j = e
    · subst hi hj
      exact G.isHom_smul' _ (G.isHom_smul' _ (h i j))
    · rw [G.repr_eq_zero_of_isHom β δ hβ hb hj, zero_smul]; exact G.isHom_zero' _
  · rw [G.repr_eq_zero_of_isHom β δ hβ ha hi, zero_smul, smul_zero]; exact G.isHom_zero' _

end LenGrading

namespace LatGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {L : Type} [AddCommGroup L]
  [DecidableEq L] (W : LatGrading k Λ L)
  {ι : Type*} [Fintype ι] (β : Module.Basis ι k Λ) (ω : ι → L) (hβ : ∀ i, W.IsHom (ω i) (β i))

include hβ in
theorem repr_eq_zero_of_isHom {l : L} {a : Λ} (ha : W.IsHom l a) {i : ι} (hi : ω i ≠ l) :
    β.repr a i = 0 := by
  classical
  have key : a = β.equivFun.symm (fun j ↦ if ω j = l then β.repr a j else 0) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← ha, ← β.sum_repr a, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, W.proj_of_isHom (hβ j)]
    split_ifs <;> simp
  have := congrArg (fun z ↦ β.equivFun z i) key
  simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at this
  rw [this, if_neg hi]

include hβ in
/-- **A bilinear map of character `χ` on basis pairs has character `χ`.** -/
theorem char₂_of_basis (χ : L) (μ : Λ →ₗ[k] Λ →ₗ[k] Λ)
    (h : ∀ i j, W.IsHom (ω i + ω j + χ) (μ (β i) (β j))) : W.Char₂ χ μ := by
  intro α γ a b ha hb
  rw [← β.sum_repr a, ← β.sum_repr b, map_sum]
  refine W.isHom_sum _ _ fun j _ ↦ ?_
  rw [map_smul, map_sum, LinearMap.sum_apply, Finset.smul_sum]
  refine W.isHom_sum _ _ fun i _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hi : ω i = α
  · by_cases hj : ω j = γ
    · subst hi hj
      exact W.isHom_smul _ (W.isHom_smul _ (h i j))
    · rw [W.repr_eq_zero_of_isHom β ω hβ hb hj, zero_smul]; exact W.isHom_zero _
  · rw [W.repr_eq_zero_of_isHom β ω hβ ha hi, zero_smul, smul_zero]; exact W.isHom_zero _

end LatGrading

end MultiplicativeBasisDeformations
