import MultiplicativeBasisDeformations.Foundations.IntegralModuleLift
import MultiplicativeBasisDeformations.Foundations.IntegralModules
import MultiplicativeBasisDeformations.Foundations.WeightExt

/-!
# Weight-homogeneous lifts (Proposition 10.1, weight refinement)

`integral-deformations.tex:63–67`: "All these constructions can be chosen to preserve the
simultaneous integer weights: […] the corrections can be chosen in each weight component."

Given finitely many integer weight gradings on `Λ = A⁽²⁾`, `Λ' = A⁽⁴⁾` and a module `M`,
compatible with the reduction, the action, the homogeneous bases and the internal degree, the
module lift of `exists_liftMod` can be chosen with an action homogeneous for every weight
(`exists_liftMod_weights`), and the arrow lifts of `exists_liftHom` homogeneous for every weight
(`exists_liftHom_weights`). The corrections come from `extVanish_weights1` and
`extVanish_weights0`; the arbitrary lifts through homogeneous bases are homogeneous for every
weight by the same computation as for the degree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace WLift

open GExt

variable {Λ : Type*} [Ring Λ] [Algebra 𝔽₂ Λ] {GΛ : GAlg (R := 𝔽₂) Λ}
  {Λ' : Type*} [Ring Λ'] [Algebra (ZMod 4) Λ'] {GΛ' : GAlg (R := ZMod 4) Λ'}
  {π : Λ' →+* Λ}

/-- A module with another grading of the same algebra, compatible with the action. -/
def regrade {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]
    {GΛ GΛ₁ : GAlg (R := R) Λ} {M : Type*} [AddCommGroup M] [Module R M]
    (MM : GMod GΛ M) (g : ZGr (R := R) M)
    (hg : ∀ p q m a, g.IsHom p m → GΛ₁.gr.IsHom q a → g.IsHom (p + q) (MM.act m a)) :
    GMod GΛ₁ M where
  act := MM.act
  act_one := MM.act_one
  act_mul := MM.act_mul
  gr := g
  act_hom := hg

section Mod

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (β : Module.Basis ι 𝔽₂ M) (dβ : ι → ℤ) {MM : GMod GΛ M}
  {κ : Type*} [Fintype κ] (bΛ : Module.Basis κ (ZMod 4) Λ') (hπ : IsRed GΛ' GΛ π)
  (dΛ : κ → ℤ) (hbΛ : ∀ κ', GΛ'.gr.IsHom (dΛ κ') (bΛ κ')) (hβ : ∀ i, MM.gr.IsHom (dβ i) (β i))
  {r : ℕ} {GΛw : Fin r → GAlg (R := 𝔽₂) Λ} {GΛ'w : Fin r → GAlg (R := ZMod 4) Λ'}
  (hπw : ∀ i, IsRed (GΛ'w i) (GΛw i) π)
  (gw : Fin r → ZGr (R := 𝔽₂) M)
  (hgw : ∀ i p q m a, (gw i).IsHom p m → (GΛw i).gr.IsHom q a →
    (gw i).IsHom (p + q) (MM.act m a))
  (wβ : Fin r → ι → ℤ) (hβw : ∀ i j, (gw i).IsHom (wβ i j) (β j))
  (wΛ : Fin r → κ → ℤ) (hbΛw : ∀ i κ', (GΛ'w i).gr.IsHom (wΛ i κ') (bΛ κ'))
  (hΛc : ∀ i v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p ((GΛw i).gr.proj v a))
  (hMc : ∀ i u p m, MM.gr.IsHom p m → MM.gr.IsHom p ((gw i).proj u m))
  (hΛcw : ∀ i j v p a, (GΛw j).gr.IsHom p a → (GΛw j).gr.IsHom p ((GΛw i).gr.proj v a))
  (hMcw : ∀ i j u p m, (gw j).IsHom p m → (gw j).IsHom p ((gw i).proj u m))

include hπ hbΛ hβ hπw hgw hβw hbΛw hΛc hMc hΛcw hMcw in
/-- **Proposition 10.1, the module lifts, weight-homogeneous**: the lifted action can be chosen
homogeneous for every weight. -/
theorem exists_liftMod_weights (hExt : ExtVanish MM MM 1 0) :
    ∃ MM' : GMod GΛ' (ι → ZMod 4), IsLift MM' MM π (ρF β) ∧ MM'.gr = grF dβ ∧
      ∀ i p q (m : ι → ZMod 4) a, (grF (wβ i)).IsHom p m → (GΛ'w i).gr.IsHom q a →
        (grF (wβ i)).IsHom (p + q) (MM'.act m a) := by
  let MMw : ∀ i, GMod (GΛw i) M := fun i ↦ regrade MM (gw i) (hgw i)
  have hFw : ∀ i, Good (MMw i) (MMw i) 2 0 (cochainF (MM := MM) β bΛ hπ) := fun i ↦
    cochainF_good (MM := MMw i) β (wβ i) bΛ (hπw i) (wΛ i) (hbΛw i) (hβw i)
  obtain ⟨H, hH, hHw, hdH⟩ := extVanish_weights1 MMw MMw (fun _ ↦ rfl) (fun _ ↦ rfl) hΛc hMc hMc
    hΛcw hMcw hMcw hExt (fun _ ↦ 0) _ (cochainF_good β dβ bΛ hπ dΛ hbΛ hβ) hFw
    (cochainF_d β bΛ hπ)
  have hTw : ∀ {r' : ℤ} {v : M}, MM.gr.IsHom r' v → (grF dβ).IsHom r' (twF β v) := fun hv ↦ by
    rw [twF_eq]; exact (grF dβ).isHom_smul _ (lv_isHom β dβ hβ hv)
  have hTww : ∀ i {r' : ℤ} {v : M}, (gw i).IsHom r' v → (grF (wβ i)).IsHom r' (twF β v) :=
    fun i _ _ hv ↦ by
      rw [twF_eq]
      exact (grF (wβ i)).isHom_smul _ (lv_isHom (MM := MMw i) β (wβ i) (hβw i) hv)
  refine ⟨{ act := act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH
            act_one := act1_one β bΛ hπ H hH hdH
            act_mul := fun m a b ↦ act1_assoc β bΛ hπ H hH hdH m a b
            gr := grF dβ
            act_hom := fun p q m a hm ha ↦ by
              rw [act1_apply]
              refine (grF dβ).isHom_add (act0_isHom β dβ bΛ hπ dΛ hbΛ hβ hm ha) (hTw ?_)
              have := hH.deg (single (π a)) (fun _ ↦ q) p (ρF β m) (fun i hi ↦ by
                obtain rfl : i = 0 := by omega
                simpa [single, Bar.cons] using hπ.deg _ _ ha) (ρF_isHom β dβ hβ hm)
              simpa using this }, ?_, rfl, fun i p q m a hm ha ↦ ?_⟩
  · exact { smul := ρF_smul β
            act := fun m b ↦ ρF_act1 β bΛ hπ H hH m b
            deg := fun p m hm ↦ ρF_isHom β dβ hβ hm
            lift := fun p m hm ↦ ⟨lv β m, lv_isHom β dβ hβ hm, ρF_lv β m⟩
            ker := fun m h ↦ ker_ρF β h
            ann := fun m h ↦ ann_ρF β h }
  · change (grF (wβ i)).IsHom (p + q) (act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH m a)
    rw [act1_apply]
    refine (grF (wβ i)).isHom_add ?_ (hTww i ?_)
    · exact act0_isHom (MM := MMw i) β (wβ i) bΛ (hπw i) (wΛ i) (hbΛw i) (hβw i) hm ha
    · have := (hHw i).deg (single (π a)) (fun _ ↦ q) p (ρF β m) (fun j hj ↦ by
        obtain rfl : j = 0 := by omega
        simpa [single, Bar.cons] using (hπw i).deg _ _ ha)
        (ρF_isHom (MM := MMw i) β (wβ i) (hβw i) hm)
      simp only [Finset.sum_range_one, add_zero] at this
      exact this

end Mod

/-! ### Weight-homogeneous arrow lifts -/

section Hom

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρM : M' →+ M}
  {N : Type*} [AddCommGroup N] [Module 𝔽₂ N] {N' : Type*} [AddCommGroup N']
  [Module (ZMod 4) N'] {NN' : GMod GΛ' N'} {NN : GMod GΛ N} {ρN : N' →+ N}
  (hπ : IsRed GΛ' GΛ π) (HM : IsLift MM' MM π ρM) (HN : IsLift NN' NN π ρN)
  {r : ℕ} {GΛw : Fin r → GAlg (R := 𝔽₂) Λ} {GΛ'w : Fin r → GAlg (R := ZMod 4) Λ'}
  (hπw : ∀ i, IsRed (GΛ'w i) (GΛw i) π)
  (gM : Fin r → ZGr (R := 𝔽₂) M)
  (hgM : ∀ i p q m a, (gM i).IsHom p m → (GΛw i).gr.IsHom q a → (gM i).IsHom (p + q) (MM.act m a))
  (gN : Fin r → ZGr (R := 𝔽₂) N)
  (hgN : ∀ i p q n a, (gN i).IsHom p n → (GΛw i).gr.IsHom q a → (gN i).IsHom (p + q) (NN.act n a))
  (gM' : Fin r → ZGr (R := ZMod 4) M')
  (hgM' : ∀ i p q m a, (gM' i).IsHom p m → (GΛ'w i).gr.IsHom q a →
    (gM' i).IsHom (p + q) (MM'.act m a))
  (gN' : Fin r → ZGr (R := ZMod 4) N')
  (hgN' : ∀ i p q n a, (gN' i).IsHom p n → (GΛ'w i).gr.IsHom q a →
    (gN' i).IsHom (p + q) (NN'.act n a))
  (HMw : ∀ i, IsLift (regrade MM' (gM' i) (hgM' i)) (regrade MM (gM i) (hgM i)) π ρM)
  (HNw : ∀ i, IsLift (regrade NN' (gN' i) (hgN' i)) (regrade NN (gN i) (hgN i)) π ρN)
  (hMc : ∀ i u p m, MM.gr.IsHom p m → MM.gr.IsHom p ((gM i).proj u m))
  (hNc : ∀ i x p n, NN.gr.IsHom p n → NN.gr.IsHom p ((gN i).proj x n))
  (hMcw : ∀ i j u p m, (gM j).IsHom p m → (gM j).IsHom p ((gM i).proj u m))
  (hNcw : ∀ i j x p n, (gN j).IsHom p n → (gN j).IsHom p ((gN i).proj x n))

include hπ HM HN hπw HMw HNw hMc hNc hMcw hNcw in
/-- **Proposition 10.1, the arrow lifts, weight-homogeneous**: a map homogeneous of degree `d`
and of weights `e i`, with a lift `f₀` of the same degree and weights, has a lift with the same
degree and weights. -/
theorem exists_liftHom_weights (f : M →ₗ[𝔽₂] N) (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    {d : ℤ} (e : Fin r → ℤ) (hExt : ExtVanish MM NN 0 d) (f₀ : M' →ₗ[ZMod 4] N')
    (hf₀ : ∀ m, ρN (f₀ m) = f (ρM m))
    (hf₀d : ∀ p m, MM'.gr.IsHom p m → NN'.gr.IsHom (p + d) (f₀ m))
    (hf₀w : ∀ i p m, (gM' i).IsHom p m → (gN' i).IsHom (p + e i) (f₀ m)) :
    ∃ f' : M' →ₗ[ZMod 4] N', (∀ m b, f' (MM'.act m b) = NN'.act (f' m) b) ∧
      (∀ m, ρN (f' m) = f (ρM m)) ∧ (∀ p m, MM'.gr.IsHom p m → NN'.gr.IsHom (p + d) (f' m)) ∧
      ∀ i p m, (gM' i).IsHom p m → (gN' i).IsHom (p + e i) (f' m) := by
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
  have hEdw : ∀ i p q m b, (gM' i).IsHom p m → (GΛ'w i).gr.IsHom q b →
      (gN' i).IsHom (p + q + e i) (E m b) := by
    intro i p q m b hm hb
    rw [hEa, sub_eq_add_neg]
    refine (gN' i).isHom_add ?_ ((gN' i).isHom_neg ?_)
    · exact hf₀w i _ _ (hgM' i _ _ _ _ hm hb)
    · have := hgN' i _ _ _ _ (hf₀w i _ _ hm) hb; convert this using 1; ring
  let MMw : ∀ i, GMod (GΛw i) M := fun i ↦ regrade MM (gM i) (hgM i)
  let NNw : ∀ i, GMod (GΛw i) N := fun i ↦ regrade NN (gN i) (hgN i)
  have hFw : ∀ i, Good (MMw i) (NNw i) 1 (e i) F := fun i ↦
    { tr := hF.tr
      add := hF.add
      smul := hF.smul
      deg := fun a ds p m ha hm ↦ by
        simp only [F, Finset.sum_range_one]
        exact halfBil_deg (hπw i) (HMw i) (HNw i) E hE (hEdw i) (ha 0 (by norm_num)) hm }
  obtain ⟨H, hH, hHw, hdH⟩ := extVanish_weights0 MMw NNw (fun _ ↦ rfl) (fun _ ↦ rfl) hMc hNc
    hMcw hNcw hExt e F hF hFw hdF
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
  have hφw : ∀ i p m, (gM i).IsHom p m → (gN i).IsHom (p + e i) (φ m) := by
    intro i p m hm
    have := (hHw i).deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
    simp only [Finset.sum_range_zero, add_zero] at this
    exact this
  refine ⟨f₀ - twMap HM HN φ, fun m b ↦ ?_, fun m ↦ ?_, fun p m hm ↦ ?_, fun i p m hm ↦ ?_⟩
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
  · simp only [LinearMap.sub_apply, twMap_apply, sub_eq_add_neg]
    exact (gN' i).isHom_add (hf₀w i p m hm)
      ((gN' i).isHom_neg ((HNw i).tw_deg (hφw i p _ ((HMw i).deg p m hm))))

end Hom

end WLift

end MultiplicativeBasisDeformations
