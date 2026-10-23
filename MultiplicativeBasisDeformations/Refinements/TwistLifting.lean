module

public import MultiplicativeBasisDeformations.Refinements.ConeLifting
public import MultiplicativeBasisDeformations.Refinements.Twist

/-!
# Twisted lifts satisfy the lifting identities (toward Proposition 12.8)

If a family of lifted actions (`assocErr`) or of lifted maps (`interErr`) built at the fibre
`t = 1` has all relative weights in the cone, then the twisted family satisfies the same identities
for the twisted deformation at every parameter `t`: on the torus the twist is conjugation by the
diagonal scalings, and the identities are polynomial in `t` (`IsPoly.eq_zero_of_torus`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

namespace GExt

open MGr

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ]
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {Wt : Type*} [AddCommGroup Wt] [DecidableEq Wt] {I : Type} [Fintype I] [DecidableEq I]
  {coords : Wt →+ (I → ℤ)} {C : AddSubmonoid Wt} (hC : ∀ γ ∈ C, ∀ i, 0 ≤ coords γ i)
  {wΛ : MGr k Wt Λ} {wM : MGr k Wt M} {wN : MGr k Wt N}

/-- Evaluation of `φ (ψ m a) b`, bilinearly in `(φ, ψ)`. -/
def evalAA (m : M) (a b : Λ) :
    (M →ₗ[k] Λ →ₗ[k] M) →ₗ[k] (M →ₗ[k] Λ →ₗ[k] M) →ₗ[k] M :=
  LinearMap.mk₂ k (fun φ ψ ↦ φ (ψ m a) b) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun φ ψ ψ' ↦ by simp only [LinearMap.add_apply, map_add])
    (fun c φ ψ ↦ by simp only [LinearMap.smul_apply, map_smul])

/-- Evaluation of `φ m (ψ a b)`, bilinearly in `(φ, ψ)`. -/
def evalAM (m : M) (a b : Λ) :
    (M →ₗ[k] Λ →ₗ[k] M) →ₗ[k] (Λ →ₗ[k] Λ →ₗ[k] Λ) →ₗ[k] M :=
  LinearMap.mk₂ k (fun φ ψ ↦ φ m (ψ a b)) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun φ ψ ψ' ↦ by simp only [LinearMap.add_apply, map_add])
    (fun c φ ψ ↦ by simp only [LinearMap.smul_apply, map_smul])

/-- Evaluation of `F (ν m a)`, bilinearly in `(F, ν)`. -/
def evalFA (m : M) (a : Λ) : (M →ₗ[k] N) →ₗ[k] (M →ₗ[k] Λ →ₗ[k] M) →ₗ[k] N :=
  LinearMap.mk₂ k (fun F ν ↦ F (ν m a)) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun F ν ν' ↦ by simp only [LinearMap.add_apply, map_add])
    (fun c F ν ↦ by simp only [LinearMap.smul_apply, map_smul])

/-- Evaluation of `ν' (F m) a`, bilinearly in `(ν', F)`. -/
def evalAF (m : M) (a : Λ) : (N →ₗ[k] Λ →ₗ[k] N) →ₗ[k] (M →ₗ[k] N) →ₗ[k] N :=
  LinearMap.mk₂ k (fun ν' F ↦ ν' (F m) a) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun ν' F F' ↦ by simp only [LinearMap.add_apply, map_add])
    (fun c ν' F ↦ by simp only [LinearMap.smul_apply, map_smul])

variable [Infinite k]

include hC in
/-- **Twisting preserves the action identities.** -/
theorem assocErr_twb {ν : ℕ → M →ₗ[k] Λ →ₗ[k] M} {μ : ℕ → Λ →ₗ[k] Λ →ₗ[k] Λ}
    (hν : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν i))
    (hμ : ∀ j, ConeBil (C := C) (G := wΛ) (G' := wΛ) (G'' := wΛ) 0 (μ j)) {n : ℕ}
    (h : ∀ m a b, assocErr ν μ n m a b = 0) (t : I → k) (m : M) (a b : Λ) :
    assocErr (fun i ↦ twb coords wM wΛ wM t 0 (ν i)) (fun j ↦ twb coords wΛ wΛ wΛ t 0 (μ j))
      n m a b = 0 := by
  refine IsPoly.eq_zero_of_torus (f := fun t ↦ assocErr (fun i ↦ twb coords wM wΛ wM t 0 (ν i))
    (fun j ↦ twb coords wΛ wΛ wΛ t 0 (μ j)) n m a b) ?_ (fun t ht ↦ ?_) t
  · unfold assocErr
    refine IsPoly.sub (IsPoly.sum _ fun x _ ↦ ?_) (IsPoly.sum _ fun x _ ↦ ?_)
    · exact IsPoly.bilin (evalAA (k := k) m a b) (isPoly_twb (coords := coords) wM wΛ wM 0 _)
        (isPoly_twb (coords := coords) wM wΛ wM 0 _)
    · exact IsPoly.bilin (evalAM (k := k) m a b) (isPoly_twb (coords := coords) wM wΛ wM 0 _)
        (isPoly_twb (coords := coords) wΛ wΛ wΛ 0 _)
  · have e : assocErr (fun i ↦ twb coords wM wΛ wM t 0 (ν i))
        (fun j ↦ twb coords wΛ wΛ wΛ t 0 (μ j)) n m a b =
        scale coords wM t (assocErr ν μ n (scale coords wM (fun i ↦ (t i)⁻¹) m)
          (scale coords wΛ (fun i ↦ (t i)⁻¹) a) (scale coords wΛ (fun i ↦ (t i)⁻¹) b)) := by
      unfold assocErr
      simp only [twb_torus hC ht (hν _), twb_torus hC ht (hμ _), chz_zero, inv_one, one_smul,
        scale_inv_scale wM ht, scale_inv_scale wΛ ht, map_sub, map_sum]
    rw [e, h, map_zero]

include hC in
/-- **Twisting preserves the linearity identities of lifted maps.** -/
theorem interErr_twl {ρ : Wt} {F : ℕ → M →ₗ[k] N} {ν : ℕ → M →ₗ[k] Λ →ₗ[k] M}
    {ν' : ℕ → N →ₗ[k] Λ →ₗ[k] N}
    (hF : ∀ i, ConeLin (C := C) (G := wM) (G' := wN) ρ (F i))
    (hν : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν i))
    (hν' : ∀ i, ConeBil (C := C) (G := wN) (G' := wΛ) (G'' := wN) 0 (ν' i)) {n : ℕ}
    (h : ∀ m a, interErr F ν ν' n m a = 0) (t : I → k) (m : M) (a : Λ) :
    interErr (fun i ↦ twl coords wM wN t ρ (F i)) (fun i ↦ twb coords wM wΛ wM t 0 (ν i))
      (fun i ↦ twb coords wN wΛ wN t 0 (ν' i)) n m a = 0 := by
  refine IsPoly.eq_zero_of_torus (f := fun t ↦ interErr (fun i ↦ twl coords wM wN t ρ (F i))
    (fun i ↦ twb coords wM wΛ wM t 0 (ν i)) (fun i ↦ twb coords wN wΛ wN t 0 (ν' i)) n m a)
    ?_ (fun t ht ↦ ?_) t
  · unfold interErr
    refine IsPoly.sub (IsPoly.sum _ fun x _ ↦ ?_) (IsPoly.sum _ fun x _ ↦ ?_)
    · exact IsPoly.bilin (evalFA (k := k) m a) (isPoly_twl (coords := coords) wM wN ρ _)
        (isPoly_twb (coords := coords) wM wΛ wM 0 _)
    · exact IsPoly.bilin (evalAF (k := k) m a) (isPoly_twb (coords := coords) wN wΛ wN 0 _)
        (isPoly_twl (coords := coords) wM wN ρ _)
  · have e : interErr (fun i ↦ twl coords wM wN t ρ (F i)) (fun i ↦ twb coords wM wΛ wM t 0 (ν i))
        (fun i ↦ twb coords wN wΛ wN t 0 (ν' i)) n m a =
        (chz coords t ρ)⁻¹ • scale coords wN t (interErr F ν ν' n
          (scale coords wM (fun i ↦ (t i)⁻¹) m) (scale coords wΛ (fun i ↦ (t i)⁻¹) a)) := by
      unfold interErr
      simp only [twl_torus hC ht (hF _), twb_torus hC ht (hν _), twb_torus hC ht (hν' _),
        chz_zero, inv_one, one_smul, scale_inv_scale wM ht, scale_inv_scale wN ht, map_sub,
        map_sum, map_smul, LinearMap.map_smul₂, LinearMap.smul_apply, smul_sub, Finset.smul_sum]
    rw [e, h, map_zero, smul_zero]

/-! ### Twisting total maps -/

section Totals

variable {P : Type*} [AddCommGroup P] [Module k P] {wP : MGr k Wt P}

omit [Infinite k] in
theorem twl_add (t : I → k) (ρ : Wt) (f g : M →ₗ[k] N) :
    twl coords wM wN t ρ (f + g) = twl coords wM wN t ρ f + twl coords wM wN t ρ g := by
  simp only [twl, LinearMap.add_comp, LinearMap.comp_add, smul_add, Finset.sum_add_distrib]

omit [Infinite k] in
theorem twl_smul (t : I → k) (ρ : Wt) (c : k) (f : M →ₗ[k] N) :
    twl coords wM wN t ρ (c • f) = c • twl coords wM wN t ρ f := by
  simp only [twl, LinearMap.smul_comp, LinearMap.comp_smul, Finset.smul_sum, smul_comm c]

omit [Infinite k] in
theorem twl_zero (t : I → k) (ρ : Wt) : twl coords wM wN t ρ (0 : M →ₗ[k] N) = 0 := by
  simpa using twl_smul (wM := wM) (wN := wN) (coords := coords) t ρ 0 0

omit [Infinite k] in
theorem twl_sub (t : I → k) (ρ : Wt) (f g : M →ₗ[k] N) :
    twl coords wM wN t ρ (f - g) = twl coords wM wN t ρ f - twl coords wM wN t ρ g := by
  rw [sub_eq_add_neg, twl_add, ← neg_one_smul k g, twl_smul, neg_one_smul, sub_eq_add_neg]

omit [Infinite k] in
theorem twl_sum {κ : Type*} (s : Finset κ) (t : I → k) (ρ : Wt) (f : κ → M →ₗ[k] N) :
    twl coords wM wN t ρ (∑ j ∈ s, f j) = ∑ j ∈ s, twl coords wM wN t ρ (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twl_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, twl_add, ih]

omit [Infinite k] in
theorem twb_add (t : I → k) (ρ : Wt) (φ ψ : M →ₗ[k] Λ →ₗ[k] M) :
    twb coords wM wΛ wM t ρ (φ + ψ) = twb coords wM wΛ wM t ρ φ + twb coords wM wΛ wM t ρ ψ := by
  refine LinearMap.ext fun m ↦ LinearMap.ext fun a ↦ ?_
  simp only [twb, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, map_add, smul_add, Finset.sum_add_distrib]

omit [Infinite k] in
theorem twb_sum {κ : Type*} (s : Finset κ) (t : I → k) (ρ : Wt) (φ : κ → M →ₗ[k] Λ →ₗ[k] M) :
    twb coords wM wΛ wM t ρ (∑ j ∈ s, φ j) = ∑ j ∈ s, twb coords wM wΛ wM t ρ (φ j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine LinearMap.ext fun m ↦ LinearMap.ext fun a ↦ ?_
    simp [twb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, twb_add, ih]

omit [Infinite k] [DecidableEq I] in
theorem ConeLin.comp' {ρ ρ' : Wt} {f : M →ₗ[k] N} {g : N →ₗ[k] P}
    (hf : ConeLin (C := C) (G := wM) (G' := wN) ρ f) (hg : ConeLin (C := C) (G := wN) (G' := wP) ρ' g) :
    ConeLin (C := C) (G := wM) (G' := wP) (ρ + ρ') (g ∘ₗ f) := fun β m hm ↦ by
  rw [LinearMap.comp_apply, ← add_assoc]; exact hg.apply (hf β m hm)

omit [Infinite k] in
theorem twl_one (ρ : Wt) (f : M →ₗ[k] N) : twl coords wM wN (fun _ ↦ 1) ρ f = f :=
  wM.ext_of_hom fun β m hm ↦ by
    rw [twl_hom _ _ _ _ f hm]
    simp only [ch_one, one_smul]
    exact (wN.sum (f m)).symm

omit [Infinite k] in
theorem twb_one (ρ : Wt) (φ : M →ₗ[k] Λ →ₗ[k] M) : twb coords wM wΛ wM (fun _ ↦ 1) ρ φ = φ :=
  bil_ext_of_hom fun β α m a hm ha ↦ by
    rw [twb_hom _ _ _ _ _ φ hm ha]
    simp only [ch_one, one_smul]
    exact (wM.sum (φ m a)).symm

include hC in
/-- **Twisting is multiplicative on maps in the cone.** -/
theorem twl_comp {ρ ρ' : Wt} {f : M →ₗ[k] N} {g : N →ₗ[k] P}
    (hf : ConeLin (C := C) (G := wM) (G' := wN) ρ f) (hg : ConeLin (C := C) (G := wN) (G' := wP) ρ' g)
    (t : I → k) :
    twl coords wM wP t (ρ + ρ') (g ∘ₗ f) = twl coords wN wP t ρ' g ∘ₗ twl coords wM wN t ρ f := by
  have key : ∀ m, twl coords wM wP t (ρ + ρ') (g ∘ₗ f) m -
      (twl coords wN wP t ρ' g ∘ₗ twl coords wM wN t ρ f) m = 0 := by
    intro m
    refine IsPoly.eq_zero_of_torus (f := fun t ↦ twl coords wM wP t (ρ + ρ') (g ∘ₗ f) m -
      (twl coords wN wP t ρ' g ∘ₗ twl coords wM wN t ρ f) m) ?_ (fun t ht ↦ ?_) t
    · refine IsPoly.sub (IsPoly.map (LinearMap.applyₗ m) (isPoly_twl _ _ _ _)) ?_
      exact IsPoly.bilin ((LinearMap.llcomp k M N P).flip.compr₂ (LinearMap.applyₗ m))
        (isPoly_twl (coords := coords) wM wN ρ f) (isPoly_twl (coords := coords) wN wP ρ' g)
    · simp only [LinearMap.comp_apply]
      rw [twl_torus hC ht (ConeLin.comp' hf hg), twl_torus hC ht hf, twl_torus hC ht hg, map_smul,
        map_smul, scale_inv_scale wN ht, chz_add ht, mul_inv, map_smul, smul_smul,
        LinearMap.comp_apply, mul_comm, sub_self]
  exact LinearMap.ext fun m ↦ sub_eq_zero.1 (key m)

include hC in
/-- **Twisting preserves module-linearity of total maps.** -/
theorem twl_lin {ρ : Wt} {g : M →ₗ[k] N} {A : M →ₗ[k] Λ →ₗ[k] M} {A' : N →ₗ[k] Λ →ₗ[k] N}
    (hg : ConeLin (C := C) (G := wM) (G' := wN) ρ g)
    (hA : ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 A)
    (hA' : ConeBil (C := C) (G := wN) (G' := wΛ) (G'' := wN) 0 A')
    (h : ∀ m a, g (A m a) = A' (g m) a) (t : I → k) (m : M) (a : Λ) :
    twl coords wM wN t ρ g (twb coords wM wΛ wM t 0 A m a) =
      twb coords wN wΛ wN t 0 A' (twl coords wM wN t ρ g m) a := by
  rw [← sub_eq_zero]
  refine IsPoly.eq_zero_of_torus (f := fun t ↦ twl coords wM wN t ρ g (twb coords wM wΛ wM t 0 A m a) -
    twb coords wN wΛ wN t 0 A' (twl coords wM wN t ρ g m) a) ?_ (fun t ht ↦ ?_) t
  · exact IsPoly.sub (IsPoly.bilin (evalFA (k := k) m a) (isPoly_twl (coords := coords) wM wN ρ g)
      (isPoly_twb (coords := coords) wM wΛ wM 0 A))
      (IsPoly.bilin (evalAF (k := k) m a) (isPoly_twb (coords := coords) wN wΛ wN 0 A')
        (isPoly_twl (coords := coords) wM wN ρ g))
  · rw [twl_torus hC ht hg, twb_torus hC ht hA, twb_torus hC ht hA', twl_torus hC ht hg]
    simp only [chz_zero, inv_one, one_smul, scale_inv_scale wM ht, map_smul,
      LinearMap.map_smul₂, LinearMap.smul_apply, scale_inv_scale wN ht, h, sub_self]

omit [Infinite k] in
theorem twl_id (t : I → k) : twl coords wM wM t 0 (LinearMap.id : M →ₗ[k] M) = LinearMap.id :=
  wM.ext_of_hom fun β m hm ↦ by
    rw [twl_hom _ _ _ _ _ hm, LinearMap.id_apply,
      Finset.sum_eq_single β (fun δ _ hδ ↦ by rw [wM.proj_of_isHom hm, if_neg (Ne.symm hδ),
        smul_zero]) (fun h ↦ by rw [wM.eq_zero_of_isHom_out hm h]; simp)]
    rw [hm, sub_self, sub_zero, ch, mono]
    simp

omit [Infinite k] in
theorem ch_add {t : I → k} {γ δ : Wt} (hγ : ∀ i, 0 ≤ coords γ i) (hδ : ∀ i, 0 ≤ coords δ i) :
    ch coords t (γ + δ) = ch coords t γ * ch coords t δ := by
  simp only [ch, ← mono_add]
  congr 1
  funext i
  simp only [map_add, Pi.add_apply]
  exact Int.toNat_add (hγ i) (hδ i)

omit [Infinite k] in
include hC in
/-- **Moving the reference weight by a cone weight multiplies the twist by its character.** -/
theorem twl_shift {ρ γ : Wt} {f : M →ₗ[k] N} (hf : ConeLin (C := C) (G := wM) (G' := wN) (ρ + γ) f)
    (hγ : γ ∈ C) (t : I → k) :
    twl coords wM wN t ρ f = ch coords t γ • twl coords wM wN t (ρ + γ) f :=
  wM.ext_of_hom fun β m hm ↦ by
    rw [LinearMap.smul_apply, twl_hom _ _ _ _ _ hm, twl_hom _ _ _ _ _ hm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    rw [smul_smul]
    by_cases hδ : δ - (β + (ρ + γ)) ∈ C
    · congr 1
      rw [show δ - β - ρ = γ + (δ - β - (ρ + γ)) by abel,
        ch_add (hC _ hγ) (hC _ (by rwa [show δ - β - (ρ + γ) = δ - (β + (ρ + γ)) by abel]))]
    · rw [hf β m hm δ hδ, smul_zero, smul_zero]

omit [Infinite k] [DecidableEq I] in
theorem coneBil_add {ρ : Wt} {φ ψ : M →ₗ[k] Λ →ₗ[k] M}
    (hφ : ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ φ)
    (hψ : ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ ψ) :
    ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ (φ + ψ) :=
  fun β α m a hm ha ↦ by
    simp only [LinearMap.add_apply]; exact (hφ β α m a hm ha).add (hψ β α m a hm ha)

omit [Infinite k] [DecidableEq I] in
theorem coneBil_sum {ρ : Wt} {κ : Type*} (s : Finset κ) {φ : κ → M →ₗ[k] Λ →ₗ[k] M}
    (hφ : ∀ j ∈ s, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ (φ j)) :
    ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ (∑ j ∈ s, φ j) :=
  fun β α m a hm ha ↦ by
    simp only [LinearMap.coe_sum, Finset.sum_apply]
    exact ConeAt.sum _ fun j hj ↦ hφ j hj β α m a hm ha

end Totals

end GExt

end MultiplicativeBasisDeformations
