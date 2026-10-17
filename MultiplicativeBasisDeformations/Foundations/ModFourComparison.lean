import MultiplicativeBasisDeformations.Foundations.IntegralPsi
import MultiplicativeBasisDeformations.Foundations.IntegralWeightInstance

/-!
# Lemma 10.2 as stated: normalized, and in every weight

`lem:mod-four-comparison` (`integral-deformations.tex:112–116`): "Let `μ̄` be a normalized
Hochschild two-cocycle of `A⁽²⁾` of internal degree `q > 0`. Then `2μ̃` is a coboundary in the
normalized Hochschild complex of `A⁽⁴⁾`. The assertion holds separately in every simultaneous
integer weight."

`2μ̃` is any `μO` with `μO(a, b) = 2x` whenever `x` lifts `μ̄(πa, πb)`; it is a cocycle
(`isHCocycle_twice`) and normalized (`twice_one_left`, `twice_one_right`). The coboundary of
`exists_hcobdry_twice` is then normalized, `h(1) = 0` (`exists_normalized_cobdry`). For ray weights
`hv : R → M` lifting a mesh weight `W` (the rays `Θ(b_r)` homogeneous of weight `hv r`), the
weight projections `wProjO m` of `𝒪P` shift along products of ray vectors (`wProjO_mul_left`,
`wProjO_mul_right`); if `μ̄` has character `χ`, so has `2μ̃` (`twice_char`), and the
weight-`χ` part of the coboundary is again a normalized coboundary of `2μ̃`
(`exists_normalized_cobdry_weight`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MGr

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [DecidableEq M] {N : Type*}
  [AddCommGroup N] [Module K N] (G : MGr K M N)

/-- Coefficients of a homogeneous element along a homogeneous basis vanish off its weight. -/
theorem repr_eq_zero {ι : Type*} [Fintype ι] (β : Module.Basis ι K N) (w : ι → M)
    (hβ : ∀ i, G.IsHom (w i) (β i)) {m : M} {n : N} (hn : G.IsHom m n) {i : ι} (hi : w i ≠ m) :
    β.repr n i = 0 := by
  classical
  have key : n = β.equivFun.symm (fun j ↦ if w j = m then β.repr n j else 0) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← hn, ← β.sum_repr n, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, G.proj_of_isHom (hβ j)]
    split_ifs <;> simp
  have := congrArg (fun z ↦ β.equivFun z i) key
  simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at this
  rw [this, if_neg hi]

end MGr

namespace RaySys.Mult

attribute [local instance] Classical.decEq

variable {V' R : Type} [Fintype V'] [DecidableEq V'] [Fintype R] [DecidableEq R]
  (P : RaySys.Mult V' R) {M : Type} [AddCommGroup M] (hv : R → M)
  (hv_mul : ∀ a b t, P.mul a b = some t → hv t = hv a + hv b)

/-- The weight-`m` projection of `𝒪P` along the ray basis. -/
def wProjO (m : M) : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4) :=
  (P.basis (ZMod 4)).constr (ZMod 4) fun t ↦ if hv t = m then P.b (ZMod 4) t else 0

theorem wProjO_b (m : M) (t : R) :
    wProjO P hv m (P.b (ZMod 4) t) = if hv t = m then P.b (ZMod 4) t else 0 := by
  rw [wProjO, ← RaySys.Mult.basis_apply, Module.Basis.constr_basis, RaySys.Mult.basis_apply]

theorem wProjO_wProjO (m : M) (y : P.Lin (ZMod 4)) : wProjO P hv m (wProjO P hv m y) = wProjO P hv m y := by
  have : (wProjO P hv m).comp (wProjO P hv m) = wProjO P hv m := by
    refine (P.basis (ZMod 4)).ext fun t ↦ ?_
    simp only [LinearMap.comp_apply, RaySys.Mult.basis_apply, wProjO_b]
    split_ifs with h
    · rw [wProjO_b, if_pos h]
    · rw [map_zero]
  exact congrArg (fun f ↦ f y) this

include hv_mul in
theorem wProjO_mul_left (r : R) (m : M) (y : P.Lin (ZMod 4)) :
    wProjO P hv m (P.b (ZMod 4) r * y) = P.b (ZMod 4) r * wProjO P hv (m - hv r) y := by
  have : (wProjO P hv m).comp (LinearMap.mulLeft (ZMod 4) (P.b (ZMod 4) r)) =
      (LinearMap.mulLeft (ZMod 4) (P.b (ZMod 4) r)).comp (wProjO P hv (m - hv r)) := by
    refine (P.basis (ZMod 4)).ext fun t ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, RaySys.Mult.basis_apply, wProjO_b]
    cases h : P.mul r t with
    | none =>
        rw [P.b_mul_of_none (k := ZMod 4) h, map_zero]
        split_ifs
        · rw [P.b_mul_of_none (k := ZMod 4) h]
        · rw [mul_zero]
    | some u =>
        rw [P.b_mul_of_some (k := ZMod 4) h, wProjO_b, hv_mul r t u h]
        by_cases hm : hv r + hv t = m
        · rw [if_pos hm, if_pos (by rw [← hm]; abel), P.b_mul_of_some (k := ZMod 4) h]
        · rw [if_neg hm, if_neg (fun h' ↦ hm (by rw [h']; abel)), mul_zero]
  exact congrArg (fun f ↦ f y) this

include hv_mul in
theorem wProjO_mul_right (s : R) (m : M) (y : P.Lin (ZMod 4)) :
    wProjO P hv m (y * P.b (ZMod 4) s) = wProjO P hv (m - hv s) y * P.b (ZMod 4) s := by
  have : (wProjO P hv m).comp (LinearMap.mulRight (ZMod 4) (P.b (ZMod 4) s)) =
      (LinearMap.mulRight (ZMod 4) (P.b (ZMod 4) s)).comp (wProjO P hv (m - hv s)) := by
    refine (P.basis (ZMod 4)).ext fun t ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, RaySys.Mult.basis_apply, wProjO_b]
    cases h : P.mul t s with
    | none =>
        rw [P.b_mul_of_none (k := ZMod 4) h, map_zero]
        split_ifs
        · rw [P.b_mul_of_none (k := ZMod 4) h]
        · rw [zero_mul]
    | some u =>
        rw [P.b_mul_of_some (k := ZMod 4) h, wProjO_b, hv_mul t s u h]
        by_cases hm : hv t + hv s = m
        · rw [if_pos hm, if_pos (by rw [← hm]; abel), P.b_mul_of_some (k := ZMod 4) h]
        · rw [if_neg hm, if_neg (fun h' ↦ hm (by rw [h']; abel)), zero_mul]
  exact congrArg (fun f ↦ f y) this

end RaySys.Mult

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} (T : TabIso D P)

variable (D) in
/-- Two-cochains of `A⁽²⁾`. -/
abbrev Coch2 := (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ

variable (P) in
/-- Two-cochains of `𝒪P`. -/
abbrev Coch2O := P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4)

variable {μ : Coch2 D} {μO : Coch2O P}
  (hμO : ∀ a b x, πO T x = μ (πO T a) (πO T b) → μO a b = (2 : ZMod 4) • x)

/-! ### `2μ̃` is a normalized cocycle -/

/-- Twice an element of `𝒪P` depends only on its reduction. -/
theorem two_smul_eq_of_πO {x y : P.Lin (ZMod 4)} (h : πO T x = πO T y) :
    (2 : ZMod 4) • x = (2 : ZMod 4) • y := by
  obtain ⟨z, hz⟩ := (isRed_πO T).ker (x - y) (by rw [map_sub, h, sub_self])
  calc (2 : ZMod 4) • x = (2 : ZMod 4) • y + (2 : ZMod 4) • (x - y) := by
        rw [← smul_add, add_sub_cancel]
    _ = (2 : ZMod 4) • y := by rw [hz, smul_smul, Z4.four_eq_zero, zero_smul, add_zero]

include hμO in
/-- **`2μ̃` is a cocycle.** -/
theorem isHCocycle_twice (hμ : IsHCocycle μ) : IsHCocycle μO := by
  intro a b z
  obtain ⟨x1, h1⟩ := (isRed_πO T).surj (μ (πO T b) (πO T z))
  obtain ⟨x2, h2⟩ := (isRed_πO T).surj (μ (πO T (a * b)) (πO T z))
  obtain ⟨x3, h3⟩ := (isRed_πO T).surj (μ (πO T a) (πO T (b * z)))
  obtain ⟨x4, h4⟩ := (isRed_πO T).surj (μ (πO T a) (πO T b))
  rw [hμO b z x1 h1, hμO (a * b) z x2 h2, hμO a (b * z) x3 h3, hμO a b x4 h4, mul_smul_comm,
    smul_mul_assoc]
  have e : (2 : ZMod 4) • (a * x1) - (2 : ZMod 4) • x2 + (2 : ZMod 4) • x3 -
      (2 : ZMod 4) • (x4 * z) = (2 : ZMod 4) • (a * x1 - x2 + x3 - x4 * z) := by
    simp only [smul_sub, smul_add]
  rw [e, two_smul_eq_of_πO T (y := 0) (by
    simp only [map_sub, map_add, map_mul, h1, h2, h3, h4, map_zero]
    simpa only [map_mul] using hμ (πO T a) (πO T b) (πO T z)), smul_zero]

include hμO in
theorem twice_one_left (hn : ∀ b, μ 1 b = 0) (b : P.Lin (ZMod 4)) : μO 1 b = 0 := by
  rw [hμO 1 b 0 (by rw [map_one, hn, map_zero]), smul_zero]

include hμO in
theorem twice_one_right (hn : ∀ a, μ a 1 = 0) (a : P.Lin (ZMod 4)) : μO a 1 = 0 := by
  rw [hμO a 1 0 (by rw [map_one, hn, map_zero]), smul_zero]

/-! ### The normalized coboundary -/

section Main

variable (J : InjData D) (h1 : DegOne D) {S : RowSet Q} (hspan : CokerSpan c S)
  (htwo : TwoRows.{0} Q S) {q : ℕ} (hq : 1 ≤ q)

include hμO J h1 hspan htwo hq in
/-- **Lemma 10.2** (`lem:mod-four-comparison`): for a normalized cocycle `μ̄` of `A⁽²⁾` of internal
degree `q > 0`, `2μ̃` is the coboundary of a normalized one-cochain `h` of `A⁽⁴⁾ = 𝒪P`. -/
theorem exists_normalized_cobdry (hμ : IsHCocycle μ)
    (hdeg : HDeg (galgA0 D (hfin2 (c := c))) μ (q : ℤ)) (hn : ∀ b, μ 1 b = 0) :
    ∃ h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), μO = hcobdry h ∧ h 1 = 0 := by
  obtain ⟨h, hh⟩ := exists_hcobdry_twice (T := T) J h1 hspan htwo hq hμ hdeg hμO
    (isHCocycle_twice T hμO hμ)
  refine ⟨h, hh, ?_⟩
  have e := congrArg (fun φ ↦ φ 1 1) hh
  simp only [hcobdry_apply, one_mul, mul_one, sub_self, zero_add] at e
  rw [← e, twice_one_left T hμO hn]

end Main

/-! ### Weights -/

section Weight

variable {M : Type} [AddCommGroup M] (W : MeshWt Q M) (hv : R → M)
  (hv_mul : ∀ a b t, P.mul a b = some t → hv t = hv a + hv b) (hv_e : ∀ x, hv (P.e x) = 0)
  (hΘ : ∀ a, (grA0 W (hfin2 (c := c)) D).IsHom (hv a) (T.Θ (P.b 𝔽₂ a)))

variable {χ : M}
  (hχ : ∀ α β a b, (grA0 W (hfin2 (c := c)) D).IsHom α a → (grA0 W (hfin2 (c := c)) D).IsHom β b →
    (grA0 W (hfin2 (c := c)) D).IsHom (α + β + χ) (μ a b))

include hμO hΘ hχ in
/-- **`2μ̃` has the character of `μ̄`.** -/
theorem twice_char (r s : R) :
    RaySys.Mult.wProjO P hv (hv r + hv s + χ) (μO (P.b (ZMod 4) r) (P.b (ZMod 4) s)) =
      μO (P.b (ZMod 4) r) (P.b (ZMod 4) s) := by
  set m := hv r + hv s + χ
  set a := μ (T.Θ (P.b 𝔽₂ r)) (T.Θ (P.b 𝔽₂ s))
  have ha : (grA0 W (hfin2 (c := c)) D).IsHom m a := hχ _ _ _ _ (hΘ r) (hΘ s)
  set β : Module.Basis R 𝔽₂ (Alg D.F0)ᵐᵒᵖ := (P.basis 𝔽₂).map T.Θ.toLinearEquiv
  have hβ : ∀ t, β t = T.Θ (P.b 𝔽₂ t) := fun t ↦ by
    simp only [β, Module.Basis.map_apply, RaySys.Mult.basis_apply]; rfl
  have hz : ∀ t, hv t ≠ m → β.repr a t = 0 := fun t ht ↦
    MGr.repr_eq_zero _ β hv (fun t ↦ by rw [hβ]; exact hΘ t) ha ht
  set x : P.Lin (ZMod 4) := ∑ t, (if hv t = m then Z4.lift (β.repr a t) else 0) • P.b (ZMod 4) t
  have hx : πO T x = a := by
    simp only [x, map_sum, πO_smul, πO_b]
    conv_rhs => rw [← β.sum_repr a]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [hβ]
    split_ifs with h
    · rw [Z4.red_lift]
    · simp [hz t h]
  have hx' : RaySys.Mult.wProjO P hv m x = x := by
    simp only [x, map_sum, map_smul, RaySys.Mult.wProjO_b]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    split_ifs <;> simp
  rw [hμO _ _ x (by rw [hx, πO_b, πO_b]), map_smul, hx']

include hμO hv_mul hv_e hΘ hχ in
/-- **Lemma 10.2, in each weight**: the weight-`χ` part of a normalized coboundary of `2μ̃` is a
normalized coboundary of `2μ̃`, homogeneous of weight `χ`. -/
theorem cobdry_weight {h0 : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4)} (hh0 : μO = hcobdry h0)
    (h01 : h0 1 = 0) :
    ∃ h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), μO = hcobdry h ∧ h 1 = 0 ∧
      ∀ r, RaySys.Mult.wProjO P hv (hv r + χ) (h (P.b (ZMod 4) r)) = h (P.b (ZMod 4) r) := by
  set h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4) :=
    (P.basis (ZMod 4)).constr (ZMod 4) fun r ↦ RaySys.Mult.wProjO P hv (hv r + χ) (h0 (P.b (ZMod 4) r))
  have hb : ∀ r, h (P.b (ZMod 4) r) = RaySys.Mult.wProjO P hv (hv r + χ) (h0 (P.b (ZMod 4) r)) := fun r ↦ by
    simp only [h]; rw [← RaySys.Mult.basis_apply, Module.Basis.constr_basis, RaySys.Mult.basis_apply]
  refine ⟨h, ?_, ?_, fun r ↦ by rw [hb, RaySys.Mult.wProjO_wProjO]⟩
  · refine (P.basis (ZMod 4)).ext fun r ↦ (P.basis (ZMod 4)).ext fun s ↦ ?_
    simp only [RaySys.Mult.basis_apply]
    rw [← twice_char T hμO W hv hΘ hχ r s, hh0, hcobdry_apply, hcobdry_apply, map_add, map_sub,
      RaySys.Mult.wProjO_mul_left P hv hv_mul, RaySys.Mult.wProjO_mul_right P hv hv_mul,
      show hv r + hv s + χ - hv r = hv s + χ by abel,
      show hv r + hv s + χ - hv s = hv r + χ by abel, ← hb, ← hb]
    congr 1
    cases hm : P.mul r s with
    | none => rw [P.b_mul_of_none (k := ZMod 4) hm, map_zero, map_zero, map_zero]
    | some t =>
        rw [P.b_mul_of_some (k := ZMod 4) hm, hb t, hv_mul r s t hm]
  · rw [← RaySys.Mult.sum_b_e, map_sum]
    have : ∀ x, h (P.b (ZMod 4) (P.e x)) = RaySys.Mult.wProjO P hv χ (h0 (P.b (ZMod 4) (P.e x))) := fun x ↦ by
      rw [hb, hv_e, zero_add]
    simp only [this, ← map_sum, RaySys.Mult.sum_b_e, h01, map_zero]

variable (J : InjData D) (h1 : DegOne D) {S : RowSet Q} (hspan : CokerSpan c S)
  (htwo : TwoRows.{0} Q S) {q : ℕ} (hq : 1 ≤ q)

include hμO hv_mul hv_e hΘ hχ J h1 hspan htwo hq in
/-- **Lemma 10.2 in every weight**: for a normalized cocycle `μ̄` of positive degree and
character `χ`, `2μ̃` is the coboundary of a normalized one-cochain homogeneous of weight `χ`. -/
theorem exists_normalized_cobdry_weight (hμ : IsHCocycle μ)
    (hdeg : HDeg (galgA0 D (hfin2 (c := c))) μ (q : ℤ)) (hn : ∀ b, μ 1 b = 0) :
    ∃ h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), μO = hcobdry h ∧ h 1 = 0 ∧
      ∀ r, RaySys.Mult.wProjO P hv (hv r + χ) (h (P.b (ZMod 4) r)) = h (P.b (ZMod 4) r) := by
  obtain ⟨h0, hh0, h01⟩ := exists_normalized_cobdry T hμO J h1 hspan htwo hq hμ hdeg hn
  exact cobdry_weight T hμO W hv hv_mul hv_e hΘ hχ hh0 h01

/-- **The statement of Lemma 10.2** for the table `T`: for every normalized Hochschild
two-cocycle `μ̄` of `A⁽²⁾` of internal degree `q > 0`, every `2μ̃` is a coboundary in the
normalized Hochschild complex of `A⁽⁴⁾ = 𝒪P`. -/
def ModFourStmt : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ μ : Coch2 D, IsHCocycle μ → HDeg (galgA0 D (hfin2 (c := c))) μ (q : ℤ) →
    (∀ a, μ 1 a = 0) → (∀ a, μ a 1 = 0) → ∀ μO : Coch2O P,
    (∀ a b x, πO T x = μ (πO T a) (πO T b) → μO a b = (2 : ZMod 4) • x) →
    ∃ h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), μO = hcobdry h ∧ h 1 = 0

/-- **The statement of Lemma 10.2 in every weight**: for ray weights `hv`, if moreover `μ̄` has
character `χ` for the mesh weight `W`, the normalized coboundary can be chosen homogeneous of
weight `χ`. -/
def ModFourWeightStmt : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ μ : Coch2 D, IsHCocycle μ → HDeg (galgA0 D (hfin2 (c := c))) μ (q : ℤ) →
    (∀ a, μ 1 a = 0) → (∀ a, μ a 1 = 0) → ∀ μO : Coch2O P,
    (∀ a b x, πO T x = μ (πO T a) (πO T b) → μO a b = (2 : ZMod 4) • x) →
    ∀ χ : M, (∀ α β a b, (grA0 W (hfin2 (c := c)) D).IsHom α a →
      (grA0 W (hfin2 (c := c)) D).IsHom β b →
      (grA0 W (hfin2 (c := c)) D).IsHom (α + β + χ) (μ a b)) →
    ∃ h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), μO = hcobdry h ∧ h 1 = 0 ∧
      ∀ r, RaySys.Mult.wProjO P hv (hv r + χ) (h (P.b (ZMod 4) r)) = h (P.b (ZMod 4) r)

include J h1 hspan htwo in
theorem modFourStmt : ModFourStmt T := fun _ hq _ hμ hdeg hn _ _ hμO ↦
  exists_normalized_cobdry T hμO J h1 hspan htwo hq hμ hdeg hn

include J h1 hspan htwo hv_mul hv_e hΘ in
theorem modFourWeightStmt : ModFourWeightStmt T W hv := fun _ hq _ hμ hdeg hn _ _ hμO _ hχ ↦
  exists_normalized_cobdry_weight T hμO W hv hv_mul hv_e hΘ hχ J h1 hspan htwo hq hμ hdeg hn

end Weight

/-! ### Proposition 10.3: the connecting map -/

section Bockstein

/-- The basis of `A⁽²⁾` transported from the ray basis. -/
abbrev basis2 : Module.Basis R 𝔽₂ (Alg D.F0)ᵐᵒᵖ := (P.basis 𝔽₂).map T.Θ.toLinearEquiv

theorem basis2_apply (r : R) : basis2 T r = T.Θ (P.b 𝔽₂ r) := by
  simp only [basis2, Module.Basis.map_apply, RaySys.Mult.basis_apply]; rfl

theorem πO_eq_sum (a : P.Lin (ZMod 4)) :
    πO T a = ∑ r, Z4.red ((P.basis (ZMod 4)).repr a r) • T.Θ (P.b 𝔽₂ r) := by
  conv_lhs => rw [← (P.basis (ZMod 4)).sum_repr a]
  simp only [map_sum, πO_smul, RaySys.Mult.basis_apply, πO_b]

/-- **Reduction of a one-cochain of `𝒪P`** to `A⁽²⁾`. -/
def redOne (h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4)) :
    (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ :=
  (basis2 T).constr 𝔽₂ fun r ↦ πO T (h (P.b (ZMod 4) r))

theorem redOne_spec (h : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4)) (a : P.Lin (ZMod 4)) :
    πO T (h a) = redOne T h (πO T a) := by
  conv_rhs => rw [πO_eq_sum T a]
  conv_lhs => rw [← (P.basis (ZMod 4)).sum_repr a]
  simp only [map_sum, map_smul, πO_smul, RaySys.Mult.basis_apply]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  congr 1
  have := (basis2 T).constr_basis 𝔽₂ (fun r ↦ πO T (h (P.b (ZMod 4) r))) r
  rw [basis2_apply] at this
  exact this.symm

theorem bilin_sum {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {ι : Type*}
    (s : Finset ι) (f : N →ₗ[K] N →ₗ[K] N) (α β : ι → K) (u : ι → N) :
    f (∑ r ∈ s, α r • u r) (∑ t ∈ s, β t • u t) = ∑ r ∈ s, ∑ t ∈ s, (α r * β t) • f (u r) (u t) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun t _ ↦ by
    rw [mul_comm])

/-- **`2c̃`**: twice a coefficient lift of a two-cochain of `A⁽²⁾`. -/
def twiceO (cb : Coch2 D) : Coch2O P :=
  (P.basis (ZMod 4)).constr (ZMod 4) fun r ↦ (P.basis (ZMod 4)).constr (ZMod 4) fun s ↦
    (2 : ZMod 4) • liftO T (cb (T.Θ (P.b 𝔽₂ r)) (T.Θ (P.b 𝔽₂ s)))

theorem twiceO_b (cb : Coch2 D) (r t : R) :
    twiceO T cb (P.b (ZMod 4) r) (P.b (ZMod 4) t) =
      (2 : ZMod 4) • liftO T (cb (T.Θ (P.b 𝔽₂ r)) (T.Θ (P.b 𝔽₂ t))) := by
  have h1 := (P.basis (ZMod 4)).constr_basis (ZMod 4) (fun r ↦ (P.basis (ZMod 4)).constr (ZMod 4)
    fun t ↦ (2 : ZMod 4) • liftO T (cb (T.Θ (P.b 𝔽₂ r)) (T.Θ (P.b 𝔽₂ t)))) r
  have h2 := (P.basis (ZMod 4)).constr_basis (ZMod 4)
    (fun t ↦ (2 : ZMod 4) • liftO T (cb (T.Θ (P.b 𝔽₂ r)) (T.Θ (P.b 𝔽₂ t)))) t
  rw [RaySys.Mult.basis_apply] at h1 h2
  rw [twiceO, h1, h2]

theorem twiceO_spec (cb : Coch2 D) (a b x : P.Lin (ZMod 4))
    (hx : πO T x = cb (πO T a) (πO T b)) : twiceO T cb a b = (2 : ZMod 4) • x := by
  set α := (P.basis (ZMod 4)).repr a
  set β := (P.basis (ZMod 4)).repr b
  set y : P.Lin (ZMod 4) := ∑ r, ∑ t, (α r * β t) • liftO T (cb (T.Θ (P.b 𝔽₂ r)) (T.Θ (P.b 𝔽₂ t)))
  have ea : a = ∑ r, α r • P.b (ZMod 4) r := by
    conv_lhs => rw [← (P.basis (ZMod 4)).sum_repr a]
    simp only [RaySys.Mult.basis_apply, α]
  have eb : b = ∑ t, β t • P.b (ZMod 4) t := by
    conv_lhs => rw [← (P.basis (ZMod 4)).sum_repr b]
    simp only [RaySys.Mult.basis_apply, β]
  have hy : twiceO T cb a b = (2 : ZMod 4) • y := by
    rw [ea, eb, bilin_sum]
    simp only [twiceO_b, y, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun t _ ↦ by rw [mul_comm]
  have hπy : πO T y = cb (πO T a) (πO T b) := by
    rw [πO_eq_sum T a, πO_eq_sum T b, bilin_sum]
    simp only [y, map_sum, πO_smul, πO_liftO, map_mul]
    rfl
  rw [hy, two_smul_eq_of_πO T (hπy.trans hx.symm)]

variable (J : InjData D) (h1 : DegOne D) {S : RowSet Q} (hspan : CokerSpan c S)
  (htwo : TwoRows.{0} Q S)

/-- **The statement of Proposition 10.3** for the table `T`: for every normalized two-cocycle
`c̄` of `A⁽²⁾` of internal degree `q > 0` there is a derivation `δ̄` of `A⁽²⁾` and a normalized
lift `δ` over `𝒪` with `dδ = 2c̃`, i.e. `c̄ = β(δ̄) = (dδ)/2` (the connecting map is surjective);
and every other lift `δ'` of `δ̄` gives `(dδ')/2 = c̄ + dε̄`, the same class. -/
def BocksteinStmt : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ cb : Coch2 D, IsHCocycle cb → HDeg (galgA0 D (hfin2 (c := c))) cb (q : ℤ) →
    (∀ a, cb 1 a = 0) → (∀ a, cb a 1 = 0) →
    ∃ δ : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), δ 1 = 0 ∧
      (∀ a b x, πO T x = cb (πO T a) (πO T b) → hcobdry δ a b = (2 : ZMod 4) • x) ∧
      ∃ δb : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ, (∀ a, πO T (δ a) = δb (πO T a)) ∧
        (∀ a b, δb (a * b) = a * δb b + δb a * b) ∧
        ∀ δ' : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), (∀ a, πO T (δ' a) = δb (πO T a)) →
          ∃ εb : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ, ∀ a b x,
            πO T x = cb (πO T a) (πO T b) + hcobdry εb (πO T a) (πO T b) →
              hcobdry δ' a b = (2 : ZMod 4) • x

/-- From a coboundary of `2c̃`: the reduction is a derivation, and other lifts are cohomologous. -/
theorem bockstein_of_cobdry {cb : Coch2 D} {δ : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4)}
    (hδ : twiceO T cb = hcobdry δ) :
    (∀ a b x, πO T x = cb (πO T a) (πO T b) → hcobdry δ a b = (2 : ZMod 4) • x) ∧
      ∃ δb : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ, (∀ a, πO T (δ a) = δb (πO T a)) ∧
        (∀ a b, δb (a * b) = a * δb b + δb a * b) ∧
        ∀ δ' : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), (∀ a, πO T (δ' a) = δb (πO T a)) →
          ∃ εb : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ, ∀ a b x,
            πO T x = cb (πO T a) (πO T b) + hcobdry εb (πO T a) (πO T b) →
              hcobdry δ' a b = (2 : ZMod 4) • x := by
  have hrep : ∀ a b x, πO T x = cb (πO T a) (πO T b) → hcobdry δ a b = (2 : ZMod 4) • x :=
    fun a b x hx ↦ by rw [← hδ]; exact twiceO_spec T cb a b x hx
  refine ⟨hrep, redOne T δ, redOne_spec T δ, fun a b ↦ ?_, fun δ' hδ' ↦ ?_⟩
  · -- the reduction is a derivation
    obtain ⟨a', rfl⟩ := (isRed_πO T).surj a
    obtain ⟨b', rfl⟩ := (isRed_πO T).surj b
    obtain ⟨x, hx⟩ := (isRed_πO T).surj (cb (πO T a') (πO T b'))
    have e := hrep a' b' x hx
    rw [hcobdry_apply] at e
    have e2 : δ (a' * b') = a' * δ b' + δ a' * b' - (2 : ZMod 4) • x := by
      rw [← e]; abel
    rw [← (πO T).map_mul, ← redOne_spec, e2, map_sub, map_add, (πO T).map_mul, (πO T).map_mul,
      redOne_spec, redOne_spec, πO_smul, show Z4.red 2 = 0 by decide, zero_smul, sub_zero]
  · -- another lift differs by twice a cochain
    have hdiff : ∀ r, ∃ e, δ' (P.b (ZMod 4) r) - δ (P.b (ZMod 4) r) = (2 : ZMod 4) • e := fun r ↦
      (isRed_πO T).ker _ (by rw [map_sub, hδ', redOne_spec, sub_self])
    choose e he using hdiff
    set ε : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4) := (P.basis (ZMod 4)).constr (ZMod 4) e
    have hε : ∀ r, ε (P.b (ZMod 4) r) = e r := fun r ↦ by
      have := (P.basis (ZMod 4)).constr_basis (ZMod 4) e r
      rwa [RaySys.Mult.basis_apply] at this
    have hεδ : δ' = δ + (2 : ZMod 4) • ε := (P.basis (ZMod 4)).ext fun r ↦ by
      rw [RaySys.Mult.basis_apply, LinearMap.add_apply, LinearMap.smul_apply, hε, ← he,
        add_sub_cancel]
    refine ⟨redOne T ε, fun a b x hx ↦ ?_⟩
    have hπε : πO T (hcobdry ε a b) = hcobdry (redOne T ε) (πO T a) (πO T b) := by
      simp only [hcobdry_apply, map_add, map_sub, map_mul, redOne_spec]
    have hx' : πO T (x - hcobdry ε a b) = cb (πO T a) (πO T b) := by
      rw [map_sub, hx, hπε, add_sub_cancel_right]
    have h0 := hrep a b _ hx'
    rw [hεδ]
    simp only [hcobdry_apply, LinearMap.add_apply, LinearMap.smul_apply] at h0 ⊢
    rw [smul_sub] at h0
    have : a * δ b - δ (a * b) + δ a * b = (2 : ZMod 4) • x -
        (2 : ZMod 4) • (a * ε b - ε (a * b) + ε a * b) := h0
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [show a * δ b + (2 : ZMod 4) • (a * ε b) - (δ (a * b) + (2 : ZMod 4) • ε (a * b)) +
        (δ a * b + (2 : ZMod 4) • (ε a * b)) = (a * δ b - δ (a * b) + δ a * b) +
        (2 : ZMod 4) • (a * ε b - ε (a * b) + ε a * b) by
      simp only [smul_sub, smul_add]; abel, this, sub_add_cancel]

include J h1 hspan htwo in
/-- **Proposition 10.3** (`prop:integral-bockstein`) for the table `T`. -/
theorem bockstein : BocksteinStmt T := by
  intro q hq cb hcb hdeg hn _
  obtain ⟨δ, hδ, hδ1⟩ := exists_normalized_cobdry T (μO := twiceO T cb)
    (twiceO_spec T cb) J h1 hspan htwo hq hcb hdeg hn
  exact ⟨δ, hδ1, bockstein_of_cobdry T hδ⟩

section BocksteinWeight

variable {M : Type} [AddCommGroup M] (W : MeshWt Q M) (hv : R → M)
  (hv_mul : ∀ a b t, P.mul a b = some t → hv t = hv a + hv b) (hv_e : ∀ x, hv (P.e x) = 0)
  (hΘ : ∀ a, (grA0 W (hfin2 (c := c)) D).IsHom (hv a) (T.Θ (P.b 𝔽₂ a)))

/-- **Proposition 10.3 in every weight**: if `c̄` has character `χ` for the mesh weight `W`, the
lift `δ` can be chosen homogeneous of weight `χ` for the ray weights `hv`. -/
def BocksteinWeightStmt : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ cb : Coch2 D, IsHCocycle cb → HDeg (galgA0 D (hfin2 (c := c))) cb (q : ℤ) →
    (∀ a, cb 1 a = 0) → (∀ a, cb a 1 = 0) → ∀ χ : M,
    (∀ α β a b, (grA0 W (hfin2 (c := c)) D).IsHom α a → (grA0 W (hfin2 (c := c)) D).IsHom β b →
      (grA0 W (hfin2 (c := c)) D).IsHom (α + β + χ) (cb a b)) →
    ∃ δ : P.Lin (ZMod 4) →ₗ[ZMod 4] P.Lin (ZMod 4), δ 1 = 0 ∧
      (∀ r, RaySys.Mult.wProjO P hv (hv r + χ) (δ (P.b (ZMod 4) r)) = δ (P.b (ZMod 4) r)) ∧
      (∀ a b x, πO T x = cb (πO T a) (πO T b) → hcobdry δ a b = (2 : ZMod 4) • x) ∧
      ∃ δb : (Alg D.F0)ᵐᵒᵖ →ₗ[𝔽₂] (Alg D.F0)ᵐᵒᵖ, (∀ a, πO T (δ a) = δb (πO T a)) ∧
        ∀ a b, δb (a * b) = a * δb b + δb a * b

include J h1 hspan htwo hv_mul hv_e hΘ in
theorem bocksteinWeight : BocksteinWeightStmt T W hv := by
  intro q hq cb hcb hdeg hn _ χ hχ
  obtain ⟨δ, hδ, hδ1, hδw⟩ := exists_normalized_cobdry_weight T (μO := twiceO T cb)
    (twiceO_spec T cb) W hv hv_mul hv_e hΘ hχ J h1 hspan htwo hq hcb hdeg hn
  obtain ⟨hrep, δb, hδb, hder, -⟩ := bockstein_of_cobdry T hδ
  exact ⟨δ, hδ1, hδw, hrep, δb, hδb, hder⟩

end BocksteinWeight

end Bockstein

end MeshWalk

end MultiplicativeBasisDeformations
