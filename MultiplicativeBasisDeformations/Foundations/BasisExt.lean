import Mathlib

/-!
# Extending a dual family to a basis

For Proposition 7.5: in a free abelian group of finite rank, elements `x_i` admitting
integer functionals `h_j` with `h_j(x_i) = δ_ij` are part of a basis
(`exists_basis_of_dual`). The projection `v ↦ ∑ h_i(v) x_i` splits off the span of the
`x_i`, with basis the `x_i`; its kernel is free, being finite and torsion-free.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

variable {N : Type} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- **A dual family is part of a basis.** -/
theorem exists_basis_of_dual {n : ℕ} (x : Fin n → N) (h : Fin n → N →ₗ[ℤ] ℤ)
    (hd : ∀ i j, h i (x j) = if i = j then 1 else 0) :
    ∃ (ι : Type) (b : Module.Basis ι ℤ N) (j : Fin n → ι), Function.Injective j ∧
      ∀ i, b (j i) = x i := by
  classical
  set P : N →ₗ[ℤ] N := ∑ i, (h i).smulRight (x i)
  have hP : ∀ v, P v = ∑ i, h i v • x i := fun v ↦ by
    simp [P, LinearMap.sum_apply]
  have hPx : ∀ j, P (x j) = x j := fun j ↦ by
    rw [hP]; simp only [hd, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq']; simp
  have hidem : IsIdempotentElem P := by
    refine LinearMap.ext fun v ↦ ?_
    rw [Module.End.mul_apply, hP v, map_sum]
    simp only [map_zsmul, hPx]
  have hc := LinearMap.IsIdempotentElem.isCompl hidem
  -- the basis of the range
  have hxr : ∀ i, x i ∈ LinearMap.range P := fun i ↦ ⟨x i, hPx i⟩
  let xr : Fin n → LinearMap.range P := fun i ↦ ⟨x i, hxr i⟩
  have hli : LinearIndependent ℤ xr := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun v : LinearMap.range P ↦ h i v.1) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, hd, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, xr,
      ZeroMemClass.coe_zero, map_zero] at this
    exact this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range xr) := by
    rintro ⟨v, w, rfl⟩ -
    have : (⟨P w, w, rfl⟩ : LinearMap.range P) = ∑ i, h i w • xr i := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, xr, hP]
    rw [this]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bR : Module.Basis (Fin n) ℤ (LinearMap.range P) := Module.Basis.mk hli hsp
  -- the kernel is free
  haveI : Module.Finite ℤ (LinearMap.ker P) := inferInstance
  haveI : Module.IsTorsionFree ℤ (LinearMap.ker P) := inferInstance
  haveI : Module.Free ℤ (LinearMap.ker P) := Module.free_of_finite_type_torsion_free'
  let bK := Module.Free.chooseBasis ℤ (LinearMap.ker P)
  let b : Module.Basis (Fin n ⊕ Module.Free.ChooseBasisIndex ℤ (LinearMap.ker P)) ℤ N :=
    (bR.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hc)
  refine ⟨_, b, Sum.inl, Sum.inl_injective, fun i ↦ ?_⟩
  simp only [b, Module.Basis.map_apply, Module.Basis.prod_apply_inl_fst,
    Submodule.coe_prodEquivOfIsCompl']
  simp [bR, xr]

end MultiplicativeBasisDeformations
