import MultiplicativeBasisDeformations.Foundations.GradedExt
import MultiplicativeBasisDeformations.Foundations.IntegralCoker

/-!
# Lifting graded modules and maps to `ℤ/4` (Proposition 10.1, the lifting steps)

`integral-deformations.tex:76–90` (proof of `prop:fixed-integral-companion`): "Lift the action
matrices arbitrarily to free graded `𝒪`-modules. Their associativity defect is even. Division
by two, followed by reduction, gives an `Ext²` class of degree zero. Equation
(prime-field-ext-vanishing) supplies a correction. Since `(2𝒪)² = 0`, this single correction
makes the action associative. The same bar calculation, using `Ext¹`, gives uniqueness and
lifts all homogeneous maps of nonnegative degree."

Setting: a graded `𝔽₂`-algebra `Λ`, a graded `𝒪`-algebra `Λ̃` (`𝒪 = ℤ/4`) and a reduction
`π : Λ̃ → Λ`. A *lift* of a graded `Λ`-module `M` is a graded `Λ̃`-module `M̃` with a reduction
`ρ : M̃ → M` whose kernel is `2M̃` and the annihilator of two (`IsLift`). Twice a lift
(`tw`) and division by two (`half`) are well defined; maps of degree `d` lift when
`Ext¹_d` vanishes (`exists_liftHom`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace WLift

open GExt

variable {Λ : Type*} [Ring Λ] [Algebra 𝔽₂ Λ] {GΛ : GAlg (R := 𝔽₂) Λ}
  {Λ' : Type*} [Ring Λ'] [Algebra (ZMod 4) Λ'] {GΛ' : GAlg (R := ZMod 4) Λ'}

/-- **A reduction of graded algebras** `Λ̃ → Λ` along `ℤ/4 → 𝔽₂`. -/
structure IsRed (GΛ' : GAlg (R := ZMod 4) Λ') (GΛ : GAlg (R := 𝔽₂) Λ) (π : Λ' →+* Λ) : Prop where
  smul : ∀ (a : ZMod 4) x, π (a • x) = Z4.red a • π x
  deg : ∀ p x, GΛ'.gr.IsHom p x → GΛ.gr.IsHom p (π x)
  lift : ∀ p x, GΛ.gr.IsHom p x → ∃ x', GΛ'.gr.IsHom p x' ∧ π x' = x
  ker : ∀ x, π x = 0 → ∃ y, x = (2 : ZMod 4) • y
  ann : ∀ x, (2 : ZMod 4) • x = 0 → π x = 0

theorem IsRed.surj {π : Λ' →+* Λ} (hπ : IsRed GΛ' GΛ π) (x : Λ) : ∃ x', π x' = x := by
  rw [GΛ.gr.sum x]
  have : ∀ p ∈ GΛ.gr.supp, ∃ x', π x' = GΛ.gr.proj p x := fun p _ ↦ by
    obtain ⟨x', -, h⟩ := hπ.lift p _ (GΛ.gr.isHom_proj p x); exact ⟨x', h⟩
  choose! f hf using this
  exact ⟨∑ p ∈ GΛ.gr.supp, f p, by rw [map_sum]; exact Finset.sum_congr rfl hf⟩

variable {π : Λ' →+* Λ}

/-- **A lift of a graded module.** -/
structure IsLift {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
    [Module (ZMod 4) M'] (MM' : GMod GΛ' M') (MM : GMod GΛ M) (π : Λ' →+* Λ) (ρ : M' →+ M) :
    Prop where
  smul : ∀ (a : ZMod 4) m, ρ (a • m) = Z4.red a • ρ m
  act : ∀ m b, ρ (MM'.act m b) = MM.act (ρ m) (π b)
  deg : ∀ p m, MM'.gr.IsHom p m → MM.gr.IsHom p (ρ m)
  lift : ∀ p m, MM.gr.IsHom p m → ∃ m', MM'.gr.IsHom p m' ∧ ρ m' = m
  ker : ∀ m, ρ m = 0 → ∃ m', m = (2 : ZMod 4) • m'
  ann : ∀ m, (2 : ZMod 4) • m = 0 → ρ m = 0

namespace IsLift

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρ : M' →+ M}
  (H : IsLift MM' MM π ρ)
include H

theorem ρ_surj (m : M) : ∃ m', ρ m' = m := by
  rw [MM.gr.sum m]
  have : ∀ p ∈ MM.gr.supp, ∃ m', ρ m' = MM.gr.proj p m := fun p _ ↦ by
    obtain ⟨m', -, h⟩ := H.lift p _ (MM.gr.isHom_proj p m); exact ⟨m', h⟩
  choose! f hf using this
  exact ⟨∑ p ∈ MM.gr.supp, f p, by rw [map_sum]; exact Finset.sum_congr rfl hf⟩

theorem two_smul_eq_of_ρ {m n : M'} (h : ρ m = ρ n) : (2 : ZMod 4) • m = (2 : ZMod 4) • n := by
  obtain ⟨d, hd⟩ := H.ker (m - n) (by rw [map_sub, h, sub_self])
  rw [← sub_eq_zero, ← smul_sub, hd, smul_smul, Z4.four_eq_zero, zero_smul]

theorem ρ_two_smul (m : M') : ρ ((2 : ZMod 4) • m) = 0 := by
  rw [H.smul, Z4.red_two, zero_smul]

theorem two_smul_two_smul (m : M') : (2 : ZMod 4) • (2 : ZMod 4) • m = 0 := by
  rw [smul_smul, Z4.four_eq_zero, zero_smul]

/-- **Twice a lift**, `M → 2M̃`. -/
def tw : M →+ M' where
  toFun m := (2 : ZMod 4) • Classical.choose (H.ρ_surj m)
  map_zero' := by
    rw [H.two_smul_eq_of_ρ (n := 0) (by rw [Classical.choose_spec (H.ρ_surj 0), map_zero]),
      smul_zero]
  map_add' m n := by
    rw [← smul_add]
    exact H.two_smul_eq_of_ρ (by rw [map_add, Classical.choose_spec (H.ρ_surj _),
      Classical.choose_spec (H.ρ_surj m), Classical.choose_spec (H.ρ_surj n)])

theorem tw_ρ (m : M') : H.tw (ρ m) = (2 : ZMod 4) • m :=
  H.two_smul_eq_of_ρ (Classical.choose_spec (H.ρ_surj _))

theorem tw_smul (a : ZMod 4) (m : M) : H.tw (Z4.red a • m) = a • H.tw m := by
  obtain ⟨m', rfl⟩ := H.ρ_surj m
  rw [← H.smul, tw_ρ, tw_ρ, smul_comm]

theorem tw_smul_k (a : 𝔽₂) (m : M) : H.tw (a • m) = Z4.lift a • H.tw m := by
  rw [← tw_smul, Z4.red_lift]

theorem ρ_tw (m : M) : ρ (H.tw m) = 0 := by
  obtain ⟨m', rfl⟩ := H.ρ_surj m
  rw [tw_ρ, H.ρ_two_smul]

theorem two_smul_tw (m : M) : (2 : ZMod 4) • H.tw m = 0 := by
  obtain ⟨m', rfl⟩ := H.ρ_surj m
  rw [tw_ρ, H.two_smul_two_smul]

theorem tw_eq_zero_iff (m : M) : H.tw m = 0 ↔ m = 0 := by
  constructor
  · intro h
    obtain ⟨m', rfl⟩ := H.ρ_surj m
    rw [tw_ρ] at h
    exact H.ann m' h
  · rintro rfl; exact map_zero _

theorem tw_injective : Function.Injective H.tw := fun m n h ↦ by
  rw [← sub_eq_zero, ← H.tw_eq_zero_iff, map_sub, h, sub_self]

theorem tw_act (m : M) (b : Λ') : MM'.act (H.tw m) b = H.tw (MM.act m (π b)) := by
  obtain ⟨m', rfl⟩ := H.ρ_surj m
  rw [tw_ρ, map_smul, LinearMap.smul_apply, ← H.act, tw_ρ]

theorem tw_deg {p : ℤ} {m : M} (hm : MM.gr.IsHom p m) : MM'.gr.IsHom p (H.tw m) := by
  obtain ⟨m', hm', rfl⟩ := H.lift p m hm
  rw [tw_ρ]
  exact MM'.gr.isHom_smul _ hm'

open Classical in
/-- **Division by two** on the kernel of the reduction: `half m` with `tw (half m) = m`. -/
def half (m : M') : M := if h : ρ m = 0 then ρ (Classical.choose (H.ker m h)) else 0

theorem tw_half {m : M'} (h : ρ m = 0) : H.tw (H.half m) = m := by
  rw [half, dif_pos h, tw_ρ]
  exact (Classical.choose_spec (H.ker m h)).symm

theorem half_eq_of_tw {m : M'} {n : M} (h : H.tw n = m) : H.half m = n := by
  have hm : ρ m = 0 := by rw [← h, ρ_tw]
  apply H.tw_injective
  rw [tw_half H hm, h]

theorem half_add {m n : M'} (hm : ρ m = 0) (hn : ρ n = 0) :
    H.half (m + n) = H.half m + H.half n :=
  half_eq_of_tw H (by rw [map_add, tw_half H hm, tw_half H hn])

theorem half_sub {m n : M'} (hm : ρ m = 0) (hn : ρ n = 0) :
    H.half (m - n) = H.half m - H.half n :=
  half_eq_of_tw H (by rw [map_sub, tw_half H hm, tw_half H hn])

theorem half_zero : H.half 0 = 0 := half_eq_of_tw H (map_zero _)

theorem half_smul (a : ZMod 4) {m : M'} (hm : ρ m = 0) : H.half (a • m) = Z4.red a • H.half m :=
  half_eq_of_tw H (by rw [tw_smul, tw_half H hm])

theorem half_two_smul (m : M') : H.half ((2 : ZMod 4) • m) = ρ m :=
  half_eq_of_tw H (tw_ρ H m)

theorem half_deg {p : ℤ} {m : M'} (hm : MM'.gr.IsHom p m) (h0 : ρ m = 0) :
    MM.gr.IsHom p (H.half m) := by
  obtain ⟨m', hm'⟩ := H.ker m h0
  have e : m = (2 : ZMod 4) • MM'.gr.proj p m' := by
    rw [← map_smul, ← hm']; exact hm.symm
  rw [half_eq_of_tw H (n := ρ (MM'.gr.proj p m')) (by rw [tw_ρ, ← e])]
  exact H.deg p _ (MM'.gr.isHom_proj p m')

theorem half_act {m : M'} (h0 : ρ m = 0) (b : Λ') :
    H.half (MM'.act m b) = MM.act (H.half m) (π b) :=
  half_eq_of_tw H (by rw [← tw_act, tw_half H h0])

end IsLift

/-! ### Lifting maps -/

section Hom

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρM : M' →+ M}
  {N : Type*} [AddCommGroup N] [Module 𝔽₂ N] {N' : Type*} [AddCommGroup N']
  [Module (ZMod 4) N'] {NN' : GMod GΛ' N'} {NN : GMod GΛ N} {ρN : N' →+ N}
  (hπ : IsRed GΛ' GΛ π) (HM : IsLift MM' MM π ρM) (HN : IsLift NN' NN π ρN)

include hπ HM HN in
theorem half_indep (E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N') (hE : ∀ m b, ρN (E m b) = 0)
    {m₁ m₂ : M'} {b₁ b₂ : Λ'} (hm : ρM m₁ = ρM m₂) (hb : π b₁ = π b₂) :
    HN.half (E m₁ b₁) = HN.half (E m₂ b₂) := by
  obtain ⟨x, hx⟩ := HM.ker (m₁ - m₂) (by rw [map_sub, hm, sub_self])
  obtain ⟨y, hy⟩ := hπ.ker (b₁ - b₂) (by rw [map_sub, hb, sub_self])
  have e : E m₁ b₁ = E m₂ b₂ + ((2 : ZMod 4) • E x b₁ + (2 : ZMod 4) • E m₂ y) :=
    calc E m₁ b₁ = E (m₂ + (2 : ZMod 4) • x) b₁ := by rw [← hx, add_sub_cancel]
      _ = E m₂ b₁ + (2 : ZMod 4) • E x b₁ := by rw [map_add, map_smul]; rfl
      _ = E m₂ (b₂ + (2 : ZMod 4) • y) + (2 : ZMod 4) • E x b₁ := by rw [← hy, add_sub_cancel]
      _ = E m₂ b₂ + ((2 : ZMod 4) • E x b₁ + (2 : ZMod 4) • E m₂ y) := by
        rw [map_add, map_smul]; abel
  rw [e, HN.half_add (hE _ _) (by rw [map_add, HN.ρ_two_smul, HN.ρ_two_smul, add_zero]),
    HN.half_add (HN.ρ_two_smul _) (HN.ρ_two_smul _), HN.half_two_smul, HN.half_two_smul, hE, hE,
    add_zero, add_zero]

/-- **Halving a bilinear map with values in the kernel of the reduction.** -/
def halfBil (E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N') (hE : ∀ m b, ρN (E m b) = 0) (a : Λ) :
    M →ₗ[𝔽₂] N where
  toFun m := HN.half (E (Classical.choose (HM.ρ_surj m)) (Classical.choose (hπ.surj a)))
  map_add' m n := by
    rw [← HN.half_add (hE _ _) (hE _ _), ← LinearMap.add_apply, ← map_add]
    exact half_indep hπ HM HN E hE (by rw [map_add, Classical.choose_spec (HM.ρ_surj _),
      Classical.choose_spec (HM.ρ_surj _), Classical.choose_spec (HM.ρ_surj _)]) rfl
  map_smul' c m := by
    rw [RingHom.id_apply, ← Z4.red_lift c, ← HN.half_smul _ (hE _ _), ← LinearMap.smul_apply,
      ← map_smul]
    exact half_indep hπ HM HN E hE (by rw [HM.smul, Classical.choose_spec (HM.ρ_surj _),
      Classical.choose_spec (HM.ρ_surj _), Z4.red_lift]) rfl

theorem halfBil_spec (E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N') (hE : ∀ m b, ρN (E m b) = 0) (m : M')
    (b : Λ') : halfBil hπ HM HN E hE (π b) (ρM m) = HN.half (E m b) :=
  half_indep hπ HM HN E hE (Classical.choose_spec (HM.ρ_surj _))
    (Classical.choose_spec (hπ.surj _))

theorem halfBil_add (E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N') (hE : ∀ m b, ρN (E m b) = 0) (a a' : Λ) :
    halfBil hπ HM HN E hE (a + a') = halfBil hπ HM HN E hE a + halfBil hπ HM HN E hE a' := by
  ext m
  obtain ⟨m', rfl⟩ := HM.ρ_surj m
  obtain ⟨b, rfl⟩ := hπ.surj a
  obtain ⟨b', rfl⟩ := hπ.surj a'
  rw [LinearMap.add_apply, ← map_add, halfBil_spec, halfBil_spec, halfBil_spec, map_add,
    HN.half_add (hE _ _) (hE _ _)]

theorem halfBil_smul (E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N') (hE : ∀ m b, ρN (E m b) = 0) (c : 𝔽₂)
    (a : Λ) : halfBil hπ HM HN E hE (c • a) = c • halfBil hπ HM HN E hE a := by
  ext m
  obtain ⟨m', rfl⟩ := HM.ρ_surj m
  obtain ⟨b, rfl⟩ := hπ.surj a
  rw [LinearMap.smul_apply, ← Z4.red_lift c, ← hπ.smul, halfBil_spec, halfBil_spec, map_smul,
    HN.half_smul _ (hE _ _)]

theorem halfBil_deg (E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N') (hE : ∀ m b, ρN (E m b) = 0) {t : ℤ}
    (hEd : ∀ p q m b, MM'.gr.IsHom p m → GΛ'.gr.IsHom q b → NN'.gr.IsHom (p + q + t) (E m b))
    {p q : ℤ} {a : Λ} {m : M} (ha : GΛ.gr.IsHom q a) (hm : MM.gr.IsHom p m) :
    NN.gr.IsHom (p + q + t) (halfBil hπ HM HN E hE a m) := by
  obtain ⟨m', hm', rfl⟩ := HM.lift p m hm
  obtain ⟨b, hb, rfl⟩ := hπ.lift q a ha
  rw [halfBil_spec]
  exact HN.half_deg (hEd _ _ _ _ hm' hb) (hE _ _)

/-- The `O`-linear map `tw ∘ φ ∘ ρ`. -/
def twMap (φ : M →ₗ[𝔽₂] N) : M' →ₗ[ZMod 4] N' where
  toFun m := HN.tw (φ (ρM m))
  map_add' m n := by rw [map_add, map_add, map_add]
  map_smul' a m := by rw [HM.smul, map_smul, HN.tw_smul, RingHom.id_apply]

theorem twMap_apply (φ : M →ₗ[𝔽₂] N) (m : M') : twMap HM HN φ m = HN.tw (φ (ρM m)) := rfl

include hπ HM HN in
/-- **Lifting maps** (`Ext¹` vanishing): an `A`-linear map of degree `d` between modules with
lifts has a lift of degree `d`, starting from any `𝒪`-linear lift. -/
theorem exists_liftHom (f : M →ₗ[𝔽₂] N) (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a) {d : ℤ}
    (hExt : ExtVanish MM NN 0 d) (f₀ : M' →ₗ[ZMod 4] N') (hf₀ : ∀ m, ρN (f₀ m) = f (ρM m))
    (hf₀d : ∀ p m, MM'.gr.IsHom p m → NN'.gr.IsHom (p + d) (f₀ m)) :
    ∃ f' : M' →ₗ[ZMod 4] N', (∀ m b, f' (MM'.act m b) = NN'.act (f' m) b) ∧
      (∀ m, ρN (f' m) = f (ρM m)) ∧ (∀ p m, MM'.gr.IsHom p m → NN'.gr.IsHom (p + d) (f' m)) := by
  set E : M' →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] N' := LinearMap.mk₂ (ZMod 4)
    (fun m b ↦ f₀ (MM'.act m b) - NN'.act (f₀ m) b)
    (fun m m' b ↦ by simp only [map_add, LinearMap.add_apply]; abel)
    (fun c m b ↦ by simp only [map_smul, LinearMap.smul_apply, smul_sub])
    (fun m b b' ↦ by simp only [map_add]; abel)
    (fun c m b ↦ by simp only [map_smul, smul_sub])
  have hEa : ∀ m b, E m b = f₀ (MM'.act m b) - NN'.act (f₀ m) b := fun _ _ ↦ rfl
  have hE : ∀ m b, ρN (E m b) = 0 := by
    intro m b
    rw [hEa, map_sub, hf₀, HM.act, hf, HN.act, hf₀, sub_self]
  have hEd : ∀ p q m b, MM'.gr.IsHom p m → GΛ'.gr.IsHom q b → NN'.gr.IsHom (p + q + d) (E m b) := by
    intro p q m b hm hb
    rw [hEa, sub_eq_add_neg]
    refine NN'.gr.isHom_add ?_ (NN'.gr.isHom_neg ?_)
    · have := hf₀d _ _ (MM'.act_hom _ _ _ _ hm hb); rwa [show p + q + d = p + q + d from rfl] at this
    · have := NN'.act_hom _ _ _ _ (hf₀d _ _ hm) hb; convert this using 1; ring
  set F : Bar.Cochain Λ (M →ₗ[𝔽₂] N) := fun a ↦ halfBil hπ HM HN E hE (a 0)
  have hF : Good MM NN 1 d F :=
    { tr := fun a ↦ by simp [F, Bar.tr]
      add := fun a i x y hi ↦ by
        obtain rfl : i = 0 := by omega
        simp only [F, Function.update_self]; exact halfBil_add hπ HM HN E hE x y
      smul := fun a i c x hi ↦ by
        obtain rfl : i = 0 := by omega
        simp only [F, Function.update_self]; exact halfBil_smul hπ HM HN E hE c x
      deg := fun a ds p m ha hm ↦ by
        simp only [F, Finset.sum_range_one]
        exact halfBil_deg hπ HM HN E hE hEd (ha 0 (by norm_num)) hm }
  have hdF : Bar.d (homAct MM NN) 1 F = 0 := by
    funext a
    ext m
    rw [Bar.d_one_apply]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r, Pi.zero_apply,
      LinearMap.zero_apply, F]
    obtain ⟨m', rfl⟩ := HM.ρ_surj m
    obtain ⟨b0, hb0⟩ := hπ.surj (a 0)
    obtain ⟨b1, hb1⟩ := hπ.surj (a 1)
    have e0 : (Bar.sh a) 0 = π b1 := by simp [Bar.sh, hb1]
    have e1 : (Bar.ct 0 a) 0 = π (b0 * b1) := by simp [Bar.ct, hb0, hb1]
    have e2 : (Bar.tr 1 a) 0 = π b0 := by simp [Bar.tr, hb0]
    rw [e0, e1, e2, ← hb0, ← hb1, ← HM.act, halfBil_spec, halfBil_spec, halfBil_spec,
      ← HN.half_act (hE _ _), ← HN.half_sub (hE _ _) (hE _ _),
      ← HN.half_add (by rw [map_sub, hE, hE, sub_self])
        (by rw [HN.act, hE, map_zero, LinearMap.zero_apply])]
    have e : E (MM'.act m' b0) b1 - E m' (b0 * b1) + NN'.act (E m' b0) b1 = 0 := by
      rw [hEa, hEa, hEa, MM'.act_mul, map_sub, LinearMap.sub_apply, NN'.act_mul]; abel
    rw [e, HN.half_zero]
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  set φ : M →ₗ[𝔽₂] N := H (fun _ ↦ 0)
  have hφ : ∀ m a, φ (MM.act m a) - NN.act (φ m) a = halfBil hπ HM HN E hE a m := by
    intro m a
    have h := congrArg (fun G : Bar.Cochain Λ (M →ₗ[𝔽₂] N) ↦ G (single a) m) hdH
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r] at h
    have hc : ∀ b, H b = φ := fun b ↦ by
      rw [hH.tr b]; congr 1
    rw [hc, hc] at h
    simpa [F, single, Bar.cons] using h
  have hφd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + d) (φ m) := by
    intro p m hm
    have := hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
    simpa [φ] using this
  refine ⟨f₀ - twMap HM HN φ, fun m b ↦ ?_, fun m ↦ ?_, fun p m hm ↦ ?_⟩
  · simp only [LinearMap.sub_apply, twMap_apply, map_sub, HM.act]
    rw [HN.tw_act, ← sub_eq_zero]
    have h := hφ (ρM m) (π b)
    rw [halfBil_spec] at h
    have := congrArg HN.tw h
    rw [map_sub, HN.tw_half (hE _ _), hEa] at this
    calc _ = (f₀ (MM'.act m b) - NN'.act (f₀ m) b) -
          (HN.tw (φ (MM.act (ρM m) (π b))) - HN.tw (NN.act (φ (ρM m)) (π b))) := by abel
      _ = 0 := by rw [this, sub_self]
  · simp only [LinearMap.sub_apply, twMap_apply, map_sub, HN.ρ_tw, sub_zero, hf₀]
  · simp only [LinearMap.sub_apply, twMap_apply, sub_eq_add_neg]
    exact NN'.gr.isHom_add (hf₀d p m hm) (NN'.gr.isHom_neg (HN.tw_deg (hφd p _ (HM.deg p m hm))))

end Hom

end WLift

end MultiplicativeBasisDeformations
