module

public import MultiplicativeBasisDeformations.Foundations.IntegralTransport

/-!
# Regular lifts of cyclic projectives

`integral-deformations.tex`: "At projective labels the modules are `e_xA^{(4)}`."

If a graded module `M` over `Λ` is cyclic projective, `M ≅ e Λ` through a generator `u` and an
inverse `ψ`, and `e = π ẽ` for an idempotent `ẽ` of `Λ̃`, then every lift `M̃` of `M` is
`ẽΛ̃` through the generator `w = ũ ẽ` (`exists_act_w`, `eq_zero_of_act_w`), with inverse `ψ̃`
lifting `ψ` (`ψO`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace WLift

open GExt

variable {Λ : Type*} [Ring Λ] [Algebra 𝔽₂ Λ] {GΛ : GAlg (R := 𝔽₂) Λ}
  {Λ' : Type*} [Ring Λ'] [Algebra (ZMod 4) Λ'] {GΛ' : GAlg (R := ZMod 4) Λ'} {π : Λ' →+* Λ}
  {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρ : M' →+ M}
  (hπ : IsRed GΛ' GΛ π) (H : IsLift MM' MM π ρ)
  (e' : Λ') (he' : e' * e' = e') (u : M) (ψ : M →ₗ[𝔽₂] Λ)
  (hψ1 : ∀ m, MM.act u (ψ m) = m) (hψ2 : ∀ x, ψ (MM.act u x) = π e' * x)

theorem four_smul' {N : Type*} [AddCommGroup N] [Module (ZMod 4) N] (m : N) :
    (2 : ZMod 4) • (2 : ZMod 4) • m = 0 := by
  rw [smul_smul, Z4.four_eq_zero, zero_smul]

/-- The generator `w = ũ ẽ`. -/
def wG : M' := MM'.act (Classical.choose (H.ρ_surj u)) e'

include hψ1 hψ2 in
theorem ρ_wG : ρ (wG H e' u) = u := by
  rw [wG, H.act, Classical.choose_spec (H.ρ_surj u)]
  have h1 : ψ u = π e' := by
    conv_lhs => rw [← MM.act_one u]
    rw [hψ2, mul_one]
  rw [← h1, hψ1]

include he' in
theorem act_wG_e (b : Λ') : MM'.act (wG H e' u) (e' * b) = MM'.act (wG H e' u) b := by
  have h : MM'.act (wG H e' u) e' = wG H e' u := by rw [wG, MM'.act_mul, he']
  rw [← MM'.act_mul, h]

include hψ1 hψ2 in
theorem ρ_act_wG (b : Λ') : ρ (MM'.act (wG H e' u) b) = MM.act u (π b) := by
  rw [H.act, ρ_wG H e' u ψ hψ1 hψ2]

include hπ hψ1 hψ2 in
theorem exists_act_wG (n : M') : ∃ b, MM'.act (wG H e' u) b = n := by
  have step : ∀ n : M', ∃ b n', n = MM'.act (wG H e' u) b + (2 : ZMod 4) • n' := by
    intro n
    obtain ⟨b, hb⟩ := hπ.surj (ψ (ρ n))
    refine ⟨b, ?_⟩
    obtain ⟨n', hn'⟩ := H.ker (n - MM'.act (wG H e' u) b) (by
      rw [map_sub, ρ_act_wG H e' u ψ hψ1 hψ2, hb, hψ1, sub_self])
    exact ⟨n', by rw [← hn', add_sub_cancel]⟩
  obtain ⟨b, n₁, rfl⟩ := step n
  obtain ⟨b₁, n₂, rfl⟩ := step n₁
  refine ⟨b + (2 : ZMod 4) • b₁, ?_⟩
  rw [map_add, map_smul, smul_add, four_smul', add_zero]

include hψ1 hψ2 in
theorem π_eq_zero_of_wG {b : Λ'} (hb : e' * b = b) (h : ρ (MM'.act (wG H e' u) b) = 0) :
    π b = 0 := by
  rw [ρ_act_wG H e' u ψ hψ1 hψ2] at h
  have := congrArg ψ h
  rwa [hψ2, map_zero, ← map_mul, hb] at this

include hπ he' hψ1 hψ2 in
theorem eq_zero_of_act_wG {b : Λ'} (hb : e' * b = b) (h : MM'.act (wG H e' u) b = 0) : b = 0 := by
  obtain ⟨b', hb'⟩ := hπ.ker b (π_eq_zero_of_wG H e' u ψ hψ1 hψ2 hb (by rw [h, map_zero]))
  have e1 : b = (2 : ZMod 4) • (e' * b') := by
    rw [← mul_smul_comm, ← hb', hb]
  have h2 : ρ (MM'.act (wG H e' u) (e' * b')) = 0 := by
    refine H.ann _ ?_
    rw [← map_smul, ← e1, h]
  obtain ⟨c', hc'⟩ := hπ.ker _ (π_eq_zero_of_wG H e' u ψ hψ1 hψ2
    (by rw [← mul_assoc, he']) h2)
  rw [e1, hc', four_smul']

/-- The inverse `ψ̃ : M̃ → ẽΛ̃`. -/
def ψGf (n : M') : Λ' := e' * Classical.choose (exists_act_wG hπ H e' u ψ hψ1 hψ2 n)

include he' in
theorem ψGf_eq {n : M'} {b : Λ'} (h : MM'.act (wG H e' u) b = n) :
    ψGf hπ H e' u ψ hψ1 hψ2 n = e' * b := by
  rw [ψGf, ← sub_eq_zero]
  refine eq_zero_of_act_wG hπ H e' he' u ψ hψ1 hψ2
    (by rw [mul_sub, ← mul_assoc, ← mul_assoc, he']) ?_
  rw [map_sub, act_wG_e H e' he', act_wG_e H e' he',
    Classical.choose_spec (exists_act_wG hπ H e' u ψ hψ1 hψ2 n), h, sub_self]

include he' in
/-- **The regular corner `M̃ ≅ ẽΛ̃`.** -/
def ψG : M' →ₗ[ZMod 4] Λ' where
  toFun := ψGf hπ H e' u ψ hψ1 hψ2
  map_add' n n' := by
    obtain ⟨b, rfl⟩ := exists_act_wG hπ H e' u ψ hψ1 hψ2 n
    obtain ⟨b', rfl⟩ := exists_act_wG hπ H e' u ψ hψ1 hψ2 n'
    rw [ψGf_eq hπ H e' he' u ψ hψ1 hψ2 rfl, ψGf_eq hπ H e' he' u ψ hψ1 hψ2 rfl, ← map_add,
      ψGf_eq hπ H e' he' u ψ hψ1 hψ2 rfl, mul_add]
  map_smul' t n := by
    obtain ⟨b, rfl⟩ := exists_act_wG hπ H e' u ψ hψ1 hψ2 n
    rw [ψGf_eq hπ H e' he' u ψ hψ1 hψ2 rfl, ← map_smul (MM'.act (wG H e' u)) t b,
      ψGf_eq hπ H e' he' u ψ hψ1 hψ2 rfl, RingHom.id_apply, mul_smul_comm]

theorem ψG_w (b : Λ') : ψG hπ H e' he' u ψ hψ1 hψ2 (MM'.act (wG H e' u) b) = e' * b :=
  ψGf_eq hπ H e' he' u ψ hψ1 hψ2 rfl

theorem w_ψG (n : M') : MM'.act (wG H e' u) (ψG hπ H e' he' u ψ hψ1 hψ2 n) = n := by
  obtain ⟨b, rfl⟩ := exists_act_wG hπ H e' u ψ hψ1 hψ2 n
  rw [ψG_w, act_wG_e H e' he']

theorem π_ψG (n : M') : π (ψG hπ H e' he' u ψ hψ1 hψ2 n) = ψ (ρ n) := by
  obtain ⟨b, rfl⟩ := exists_act_wG hπ H e' u ψ hψ1 hψ2 n
  rw [ψG_w, ρ_act_wG H e' u ψ hψ1 hψ2, hψ2, map_mul]

end WLift

end MultiplicativeBasisDeformations
