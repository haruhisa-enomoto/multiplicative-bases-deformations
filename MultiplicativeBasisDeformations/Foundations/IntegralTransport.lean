import MultiplicativeBasisDeformations.Foundations.IntegralMesh
import MultiplicativeBasisDeformations.Foundations.SquareZero
import MultiplicativeBasisDeformations.Foundations.GModLemmas

/-!
# Twice a first-order lift

`integral-deformations.tex:173–177` (proof of Lemma 10.2): "take module and map corrections for
a first-order `𝔽₂`-cocycle and use twice their lifts over `𝒪`. Every equation is linear in `ε`;
multiplication by two makes it depend only on the modulo-two base matrices."

For a cocycle `μ̃ = 2μ̄` over `𝒪`, a lifted action `ν` of `M` for `μ̄` gives the lifted action
`2ν` of a lift `M̃` (`actLiftTw`), and a lifted map `(f, g)` gives `(f̃, 2g)` (`isLiftHom_tw`).
-/

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
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρM : M' →+ M}
  {N : Type*} [AddCommGroup N] [Module 𝔽₂ N] {N' : Type*} [AddCommGroup N']
  [Module (ZMod 4) N'] {NN' : GMod GΛ' N'} {NN : GMod GΛ N} {ρN : N' →+ N}
  (HM : IsLift MM' MM π ρM) (HN : IsLift NN' NN π ρN)

/-- A lift through a reduction. -/
def liftR (hπ : IsRed GΛ' GΛ π) (x : Λ) : Λ' := Classical.choose (hπ.surj x)

theorem liftR_spec (hπ : IsRed GΛ' GΛ π) (x : Λ) : π (liftR hπ x) = x :=
  Classical.choose_spec (hπ.surj x)

/-! ### `twMap` -/

theorem twMap_add (φ ψ : M →ₗ[𝔽₂] N) : twMap HM HN (φ + ψ) = twMap HM HN φ + twMap HM HN ψ := by
  ext m; simp [twMap_apply, map_add]

theorem twMap_sub (φ ψ : M →ₗ[𝔽₂] N) : twMap HM HN (φ - ψ) = twMap HM HN φ - twMap HM HN ψ := by
  ext m; simp [twMap_apply, map_sub]

theorem twMap_smul (t : 𝔽₂) (φ : M →ₗ[𝔽₂] N) : twMap HM HN (t • φ) = Z4.lift t • twMap HM HN φ := by
  ext m; simp [twMap_apply, HN.tw_smul_k]

theorem twMap_red_smul (a : ZMod 4) (φ : M →ₗ[𝔽₂] N) :
    twMap HM HN (Z4.red a • φ) = a • twMap HM HN φ := by
  ext m
  rw [LinearMap.smul_apply, twMap_apply, twMap_apply, LinearMap.smul_apply, HN.tw_smul]

theorem twMap_sum {κ : Type*} (s : Finset κ) (φ : κ → M →ₗ[𝔽₂] N) :
    twMap HM HN (∑ i ∈ s, φ i) = ∑ i ∈ s, twMap HM HN (φ i) := by
  ext m; simp [twMap_apply, map_sum, LinearMap.sum_apply]

theorem twMap_zero : twMap HM HN (0 : M →ₗ[𝔽₂] N) = 0 := by
  ext m; simp [twMap_apply]

/-- A lift of a map commutes with twice. -/
theorem lift_tw {f : M →ₗ[𝔽₂] N} {f' : M' →ₗ[ZMod 4] N'} (hf' : ∀ m, ρN (f' m) = f (ρM m)) (v : M) :
    f' (HM.tw v) = HN.tw (f v) := by
  obtain ⟨m, rfl⟩ := HM.ρ_surj v
  rw [HM.tw_ρ, map_smul, ← hf', HN.tw_ρ]

theorem comp_twMap {P : Type*} [AddCommGroup P] [Module 𝔽₂ P] {P' : Type*} [AddCommGroup P']
    [Module (ZMod 4) P'] {PP' : GMod GΛ' P'} {PP : GMod GΛ P} {ρP : P' →+ P}
    (HP : IsLift PP' PP π ρP) {f : N →ₗ[𝔽₂] P} {f' : N' →ₗ[ZMod 4] P'}
    (hf' : ∀ m, ρP (f' m) = f (ρN m)) (g : M →ₗ[𝔽₂] N) :
    f' ∘ₗ twMap HM HN g = twMap HM HP (f ∘ₗ g) := by
  ext m
  simp only [LinearMap.comp_apply, twMap_apply]
  exact lift_tw HN HP hf' _

theorem twMap_comp {P : Type*} [AddCommGroup P] [Module 𝔽₂ P] {P' : Type*} [AddCommGroup P']
    [Module (ZMod 4) P'] {PP' : GMod GΛ' P'} {PP : GMod GΛ P} {ρP : P' →+ P}
    (HP : IsLift PP' PP π ρP) {f : M →ₗ[𝔽₂] N} {f' : M' →ₗ[ZMod 4] N'}
    (hf' : ∀ m, ρN (f' m) = f (ρM m)) (g : N →ₗ[𝔽₂] P) :
    twMap HN HP g ∘ₗ f' = twMap HM HP (g ∘ₗ f) := by
  ext m
  simp only [LinearMap.comp_apply, twMap_apply, hf']

/-! ### Twice a lifted action -/

section Act

variable (hπ : IsRed GΛ' GΛ π) {μ : Λ →ₗ[𝔽₂] Λ →ₗ[𝔽₂] Λ} {μ' : Λ' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] Λ'}
  (hμ' : ∀ a b x, π x = μ (π a) (π b) → μ' a b = (2 : ZMod 4) • x) {q : ℤ}

/-- The sequence of reductions. -/
abbrev πs (a : ℕ → Λ') : ℕ → Λ := fun i ↦ π (a i)

theorem πs_tr (n : ℕ) (a : ℕ → Λ') : πs (π := π) (Bar.tr n a) = Bar.tr n (πs (π := π) a) := by
  funext i; simp only [πs, Bar.tr]; split_ifs <;> simp

theorem πs_sh (a : ℕ → Λ') : πs (π := π) (Bar.sh a) = Bar.sh (πs (π := π) a) := rfl

theorem πs_ct (a : ℕ → Λ') : πs (π := π) (Bar.ct 0 a) = Bar.ct 0 (πs (π := π) a) := by
  funext i; simp only [πs, Bar.ct]; split_ifs <;> simp

theorem πs_update (a : ℕ → Λ') (i : ℕ) (x : Λ') :
    πs (π := π) (Function.update a i x) = Function.update (πs (π := π) a) i (π x) := by
  funext j
  simp only [πs, Function.update]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem πs_single (b : Λ') : πs (π := π) (single b) = single (π b) := by
  funext i; simp only [πs, single, Bar.cons]; split_ifs <;> simp

include hπ hμ' in
/-- **Twice a lifted action** (`integral-deformations.tex:173–177`). -/
def actLiftTw (L : ActLift μ q MM) : ActLift μ' q MM' where
  ν a := twMap HM HM (L.ν (πs (π := π) a))
  good :=
    { tr := fun a ↦ by rw [πs_tr, ← L.good.tr]
      add := fun a i x y hi ↦ by
        rw [πs_update, map_add, L.good.add _ _ _ _ hi, twMap_add, πs_update, πs_update]
      smul := fun a i c x hi ↦ by
        rw [πs_update, hπ.smul, L.good.smul _ _ _ _ hi, twMap_red_smul, πs_update]
      deg := fun a ds p m ha hm ↦ by
        rw [twMap_apply]
        exact HM.tw_deg (L.good.deg _ ds p _ (fun i hi ↦ hπ.deg _ _ (ha i hi)) (HM.deg _ _ hm)) }
  eq := by
    funext a
    ext m
    rw [Bar.d_one_apply]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r, twMap_apply,
      muCochain_apply]
    rw [HM.act, HM.tw_act, πs_sh, πs_ct, πs_tr, ← map_sub, ← map_add]
    have h := congrArg (fun G : Bar.Cochain Λ (M →ₗ[𝔽₂] M) ↦ G (πs (π := π) a) (ρM m)) L.eq
    simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r,
      muCochain_apply] at h
    rw [h, hμ' (a 0) (a 1) (liftR hπ (μ (π (a 0)) (π (a 1)))) (liftR_spec hπ _), map_smul,
      ← HM.tw_ρ, HM.act, liftR_spec]

theorem actLiftTw_act (L : ActLift μ q MM) (m : M') (b : Λ') :
    (actLiftTw HM hπ hμ' L).act m b = HM.tw (L.act (ρM m) (π b)) := by
  change twMap HM HM (L.ν (πs (π := π) (single b))) m = _
  rw [πs_single, twMap_apply]
  rfl

/-- **Twice a lifted map.** -/
theorem isLiftHom_tw (L₁ : ActLift μ q MM) (L₂ : ActLift μ q NN) {f g : M →ₗ[𝔽₂] N}
    (h : IsLiftHom L₁ L₂ f g) {f' : M' →ₗ[ZMod 4] N'}
    (hf'act : ∀ m b, f' (MM'.act m b) = NN'.act (f' m) b) (hf' : ∀ m, ρN (f' m) = f (ρM m)) :
    IsLiftHom (actLiftTw HM hπ hμ' L₁) (actLiftTw HN hπ hμ' L₂) f' (twMap HM HN g) := by
  refine ⟨hf'act, fun m b ↦ ?_⟩
  rw [twMap_apply, twMap_apply, actLiftTw_act, actLiftTw_act, HM.act, HN.tw_act, hf',
    lift_tw HM HN hf', ← map_sub, ← map_sub, h.2]

end Act

end WLift

end MultiplicativeBasisDeformations
