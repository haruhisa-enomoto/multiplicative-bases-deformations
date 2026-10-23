module

public import MultiplicativeBasisDeformations.Foundations.WeightExt
public import MultiplicativeBasisDeformations.Foundations.MGrading

/-!
# Corrections in each weight component, for a grading by any abelian group

The version of `WeightExt.lean` for an additional grading by an arbitrary abelian group `Γ`
(`lem:square-zero-selected-lifts`, last sentence): a `Γ`-grading of `Λ` (`GrΓ`), of the modules
(`MGr` compatible with the actions), and a correction `H` with `dH = F` for `F` of weight `w`
replaced by its weight-`w` component (`PW0Γ`, `PW1Γ`, `dPW0Γ`, `dPW1Γ`). The component is
computed on homogeneous inputs (`PW0Γ_hom`, `PW1Γ_hom`); cochains agreeing on homogeneous inputs
agree (`ext_oneΓ`, `ext_twoΓ`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]

/-- **A grading of `Λ` by `Γ`**, multiplicative. -/
structure GrΓ (Λ : Type*) [Ring Λ] [Algebra R Λ] (Γ : Type*) [AddCommGroup Γ] [DecidableEq Γ] where
  g : MGr R Γ Λ
  mul : ∀ a b x y, g.IsHom a x → g.IsHom b y → g.IsHom (a + b) (x * y)

variable (gΛ : GrΓ (R := R) Λ Γ)

/-- A `Γ`-homogeneous cochain of weight `w` (only the weights; the algebraic properties are those
of `Good`). -/
def GoodΓ (gM : MGr R Γ M) (gN : MGr R Γ N) (n : ℕ) (w : Γ) (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    Prop :=
  ∀ (a : ℕ → Λ) (ds : ℕ → Γ) u m, (∀ i < n, gΛ.g.IsHom (ds i) (a i)) → gM.IsHom u m →
    gN.IsHom (u + ∑ i ∈ Finset.range n, ds i + w) (F a m)

variable (gM : MGr R Γ M) (gN : MGr R Γ N)

/-- The weight-`w` component of a `0`-cochain. -/
def PW0Γ (w : Γ) (H : Bar.Cochain Λ (M →ₗ[R] N)) : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦
  ∑ u ∈ gM.supp, gN.proj (u + w) ∘ₗ H a ∘ₗ gM.proj u

/-- The weight-`w` component of a `1`-cochain. -/
def PW1Γ (w : Γ) (H : Bar.Cochain Λ (M →ₗ[R] N)) : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦
  ∑ v ∈ gΛ.g.supp, ∑ u ∈ gM.supp,
    gN.proj (u + v + w) ∘ₗ H (single (gΛ.g.proj v (a 0))) ∘ₗ gM.proj u

theorem PW0Γ_hom (w : Γ) (H : Bar.Cochain Λ (M →ₗ[R] N)) (a : ℕ → Λ) {u₀ : Γ} {m : M}
    (hm : gM.IsHom u₀ m) : PW0Γ gM gN w H a m = gN.proj (u₀ + w) (H a m) := by
  classical
  simp only [PW0Γ, LinearMap.sum_apply, LinearMap.comp_apply]
  simp_rw [gM.proj_of_isHom hm]
  by_cases hu : u₀ ∈ gM.supp
  · rw [Finset.sum_eq_single_of_mem u₀ hu]
    · rw [if_pos rfl]
    · intro u _ hne; rw [if_neg (Ne.symm hne), map_zero, map_zero]
  · rw [gM.eq_zero_of_isHom_out hm hu]
    simp

variable {GΛo : GAlg (R := R) Λ} {MMo : GMod GΛo M} {NNo : GMod GΛo N} {t : ℤ}

theorem PW1Γ_hom (w : Γ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) (a : ℕ → Λ)
    {v₀ u₀ : Γ} {m : M} (ha : gΛ.g.IsHom v₀ (a 0)) (hm : gM.IsHom u₀ m) :
    PW1Γ gΛ gM gN w H a m = gN.proj (u₀ + v₀ + w) (H (single (a 0)) m) := by
  classical
  have h0 := single_zero_eq hH
  simp only [PW1Γ, LinearMap.sum_apply, LinearMap.comp_apply]
  simp_rw [gΛ.g.proj_of_isHom ha, gM.proj_of_isHom hm]
  by_cases hv : v₀ ∈ gΛ.g.supp
  · rw [Finset.sum_eq_single_of_mem v₀ hv]
    · rw [if_pos rfl]
      by_cases hu : u₀ ∈ gM.supp
      · rw [Finset.sum_eq_single_of_mem u₀ hu]
        · rw [if_pos rfl]
        · intro u _ hne; rw [if_neg (Ne.symm hne), map_zero, map_zero]
      · rw [gM.eq_zero_of_isHom_out hm hu]; simp
    · intro v _ hne
      rw [if_neg (Ne.symm hne), h0]
      simp
  · rw [gΛ.g.eq_zero_of_isHom_out ha hv, h0]
    simp [h0]

theorem PW1Γ_good (w : Γ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H)
    (hΛ : ∀ v p a, GΛo.gr.IsHom p a → GΛo.gr.IsHom p (gΛ.g.proj v a))
    (hMp : ∀ u p m, MMo.gr.IsHom p m → MMo.gr.IsHom p (gM.proj u m))
    (hNp : ∀ x p n, NNo.gr.IsHom p n → NNo.gr.IsHom p (gN.proj x n)) :
    Good MMo NNo 1 t (PW1Γ gΛ gM gN w H) where
  tr a := by simp [PW1Γ, Bar.tr]
  add a i x y hi := by
    obtain rfl : i = 0 := by omega
    simp only [PW1Γ, Function.update_self, map_add, hH.single_add, LinearMap.add_comp,
      LinearMap.comp_add, Finset.sum_add_distrib]
  smul a i c x hi := by
    obtain rfl : i = 0 := by omega
    simp only [PW1Γ, Function.update_self, map_smul, hH.single_smul, LinearMap.smul_comp,
      LinearMap.comp_smul, Finset.smul_sum]
  deg a ds p m ha hm := by
    simp only [PW1Γ, LinearMap.sum_apply, LinearMap.comp_apply]
    refine NNo.gr.isHom_sum _ _ fun v _ ↦ NNo.gr.isHom_sum _ _ fun u _ ↦ hNp _ _ _ ?_
    refine hH.deg _ ds p _ (fun i hi ↦ ?_) (hMp _ _ _ hm)
    obtain rfl : i = 0 := by omega
    simpa [single, Bar.cons] using hΛ v _ _ (ha 0 (by omega))

theorem PW1Γ_goodΓ (w : Γ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) :
    GoodΓ gΛ gM gN 1 w (PW1Γ gΛ gM gN w H) := by
  intro a ds u m ha hm
  rw [PW1Γ_hom gΛ gM gN w hH a (ha 0 (by omega)) hm, Finset.sum_range_one]
  exact gN.isHom_proj _ _

theorem PW0Γ_good (w : Γ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 0 t H)
    (hMp : ∀ u p m, MMo.gr.IsHom p m → MMo.gr.IsHom p (gM.proj u m))
    (hNp : ∀ x p n, NNo.gr.IsHom p n → NNo.gr.IsHom p (gN.proj x n)) :
    Good MMo NNo 0 t (PW0Γ gM gN w H) where
  tr a := by simp only [PW0Γ]; rw [hH.tr a]
  add a i x y hi := absurd hi (Nat.not_lt_zero _)
  smul a i c x hi := absurd hi (Nat.not_lt_zero _)
  deg a ds p m ha hm := by
    simp only [PW0Γ, LinearMap.sum_apply, LinearMap.comp_apply]
    exact NNo.gr.isHom_sum _ _ fun u _ ↦ hNp _ _ _ (hH.deg a ds p _ ha (hMp _ _ _ hm))

theorem PW0Γ_goodΓ (w : Γ) (H : Bar.Cochain Λ (M →ₗ[R] N)) :
    GoodΓ gΛ gM gN 0 w (PW0Γ gM gN w H) := by
  intro a ds u m _ hm
  rw [PW0Γ_hom gM gN w H a hm, Finset.sum_range_zero, add_zero]
  exact gN.isHom_proj _ _

/-! ### Agreement on homogeneous inputs -/

theorem ext_oneΓ {G G' : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 1 t G)
    (hG' : Good MMo NNo 1 t G')
    (h : ∀ (a : Λ) (m : M) (v u : Γ), gΛ.g.IsHom v a → gM.IsHom u m →
      G (single a) m = G' (single a) m) : G = G' := by
  funext a
  rw [hG.one_eq a, hG'.one_eq a]
  let φ : Λ →+ (M →ₗ[R] N) := ⟨⟨fun x ↦ G (single x), single_zero_eq hG⟩, hG.single_add⟩
  let φ' : Λ →+ (M →ₗ[R] N) := ⟨⟨fun x ↦ G' (single x), single_zero_eq hG'⟩, hG'.single_add⟩
  change φ (a 0) = φ' (a 0)
  rw [gΛ.g.sum (a 0), map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  apply LinearMap.ext
  intro m
  rw [gM.sum m, map_sum, map_sum]
  exact Finset.sum_congr rfl fun u _ ↦ h _ _ v u (gΛ.g.isHom_proj v _) (gM.isHom_proj u m)

theorem ext_twoΓ {G G' : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G)
    (hG' : Good MMo NNo 2 t G')
    (h : ∀ (a b : Λ) (m : M) (v₀ v₁ u : Γ), gΛ.g.IsHom v₀ a → gΛ.g.IsHom v₁ b →
      gM.IsHom u m → G (pair a b) m = G' (pair a b) m) : G = G' := by
  funext a
  rw [hG.pair_eq a, hG'.pair_eq a]
  change bil hG (a 0) (a 1) = bil hG' (a 0) (a 1)
  rw [gΛ.g.sum (a 0), map_sum, map_sum, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun v₀ _ ↦ ?_
  rw [gΛ.g.sum (a 1), map_sum, map_sum]
  refine Finset.sum_congr rfl fun v₁ _ ↦ ?_
  apply LinearMap.ext
  intro m
  rw [gM.sum m, map_sum, map_sum]
  exact Finset.sum_congr rfl fun u _ ↦ h _ _ _ v₀ v₁ u (gΛ.g.isHom_proj _ _)
    (gΛ.g.isHom_proj _ _) (gM.isHom_proj u m)

/-! ### The corrections, weight by weight -/

section Refine

variable {GΛ : GAlg (R := R) Λ} {MM : GMod GΛ M} {NN : GMod GΛ N}

theorem proj_actΓ (hNa : ∀ u v n a, gN.IsHom u n → gΛ.g.IsHom v a → gN.IsHom (u + v) (NN.act n a))
    {q : Γ} {a : Λ} (ha : gΛ.g.IsHom q a) (p : Γ) (y : N) :
    gN.proj (p + q) (NN.act y a) = NN.act (gN.proj p y) a := by
  classical
  conv_lhs => rw [gN.sum y, map_sum, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single p]
  · rw [gN.proj_of_isHom (hNa _ _ _ _ (gN.isHom_proj _ _) ha), if_pos rfl]
  · intro s _ hs
    rw [gN.proj_of_isHom (hNa _ _ _ _ (gN.isHom_proj _ _) ha), if_neg (fun h ↦ hs (add_right_cancel h))]
  · intro h
    rw [gN.proj_out _ h, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, map_zero]

/-- **`d` of the component of a `1`-cochain** is the given weight-`w` cocycle. -/
theorem dPW1Γ (hMa : ∀ u v m a, gM.IsHom u m → gΛ.g.IsHom v a → gM.IsHom (u + v) (MM.act m a))
    (hNa : ∀ u v n a, gN.IsHom u n → gΛ.g.IsHom v a → gN.IsHom (u + v) (NN.act n a))
    (hΛ : ∀ v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p (gΛ.g.proj v a))
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (gM.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (gN.proj x n))
    {t : ℤ} {w : Γ} {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MM NN 1 t H)
    {F : Bar.Cochain Λ (M →ₗ[R] N)} (hFw : GoodΓ gΛ gM gN 2 w F)
    (hd : Bar.d (homAct MM NN) 1 H = F) :
    Bar.d (homAct MM NN) 1 (PW1Γ gΛ gM gN w H) = F := by
  have hF : Good MM NN 2 t F := hd ▸ hH.d
  refine ext_twoΓ gΛ gM (PW1Γ_good gΛ gM gN w hH hΛ hMp hNp).d hF
    fun a b m v₀ v₁ u ha hb hm ↦ ?_
  have hma : gM.IsHom (u + v₀) (MM.act m a) := hMa _ _ _ _ hm ha
  have hab : gΛ.g.IsHom (v₀ + v₁) (a * b) := gΛ.mul _ _ _ _ ha hb
  have hFh : gN.IsHom (u + v₀ + v₁ + w) (F (pair a b) m) := by
    have := hFw (pair a b) (fun i ↦ if i = 0 then v₀ else v₁) u m (fun i hi ↦ by
      rcases i with _ | _ | i
      · simpa [pair, Bar.cons] using ha
      · simpa [pair, single, Bar.cons] using hb
      · omega) hm
    simpa [Finset.sum_range_succ, add_assoc] using this
  rw [← hFh, ← hd, Bar.d_one_apply, Bar.d_one_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r]
  rw [show pair a b 0 = a from rfl, show pair a b 1 = b from rfl]
  rw [PW1Γ_hom gΛ gM gN w hH _ (v₀ := v₁) (by rw [pair_sh]; exact hb) hma,
    PW1Γ_hom gΛ gM gN w hH _ (v₀ := v₀ + v₁) (by rw [pair_ct]; exact hab) hm,
    PW1Γ_hom gΛ gM gN w hH _ (v₀ := v₀) (by rw [pair_tr]; exact ha) hm,
    hH.one_eq (Bar.sh _), hH.one_eq (Bar.ct 0 _), hH.one_eq (Bar.tr 1 _), pair_sh, pair_ct,
    pair_tr, ← proj_actΓ gΛ gN hNa hb, map_add, map_sub]
  rw [show u + v₀ + v₁ + w = u + (v₀ + v₁) + w by abel,
    show u + (v₀ + v₁) + w = u + v₀ + w + v₁ by abel]

/-- **`d` of the component of a `0`-cochain** is the given weight-`w` cocycle. -/
theorem dPW0Γ (hMa : ∀ u v m a, gM.IsHom u m → gΛ.g.IsHom v a → gM.IsHom (u + v) (MM.act m a))
    (hNa : ∀ u v n a, gN.IsHom u n → gΛ.g.IsHom v a → gN.IsHom (u + v) (NN.act n a))
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (gM.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (gN.proj x n))
    {t : ℤ} {w : Γ} {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MM NN 0 t H)
    {F : Bar.Cochain Λ (M →ₗ[R] N)} (hFw : GoodΓ gΛ gM gN 1 w F)
    (hd : Bar.d (homAct MM NN) 0 H = F) :
    Bar.d (homAct MM NN) 0 (PW0Γ gM gN w H) = F := by
  have hF : Good MM NN 1 t F := hd ▸ hH.d
  refine ext_oneΓ gΛ gM (PW0Γ_good gM gN w hH hMp hNp).d hF fun a m v u ha hm ↦ ?_
  have hma : gM.IsHom (u + v) (MM.act m a) := hMa _ _ _ _ hm ha
  have hFh : gN.IsHom (u + v + w) (F (single a) m) := by
    have := hFw (single a) (fun _ ↦ v) u m (fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simpa [single, Bar.cons] using ha) hm
    simpa using this
  rw [← hFh, ← hd, Bar.d_zero_apply, Bar.d_zero_apply]
  simp only [LinearMap.sub_apply, homAct_l, homAct_r]
  rw [show single a 0 = a from rfl]
  rw [PW0Γ_hom gM gN w H _ hma, PW0Γ_hom gM gN w H _ hm, ← proj_actΓ gΛ gN hNa ha, map_sub]
  rw [show u + w + v = u + v + w by abel]

/-- **`Ext²` corrections in a weight component** of a `Γ`-grading. -/
theorem extVanishΓ1 (hMa : ∀ u v m a, gM.IsHom u m → gΛ.g.IsHom v a → gM.IsHom (u + v) (MM.act m a))
    (hNa : ∀ u v n a, gN.IsHom u n → gΛ.g.IsHom v a → gN.IsHom (u + v) (NN.act n a))
    (hΛ : ∀ v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p (gΛ.g.proj v a))
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (gM.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (gN.proj x n))
    {t : ℤ} (hExt : ExtVanish MM NN 1 t) (w : Γ) (F : Bar.Cochain Λ (M →ₗ[R] N))
    (hF : Good MM NN 2 t F) (hFw : GoodΓ gΛ gM gN 2 w F) (hdF : Bar.d (homAct MM NN) 2 F = 0) :
    ∃ H, Good MM NN 1 t H ∧ GoodΓ gΛ gM gN 1 w H ∧ Bar.d (homAct MM NN) 1 H = F := by
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  exact ⟨PW1Γ gΛ gM gN w H, PW1Γ_good gΛ gM gN w hH hΛ hMp hNp, PW1Γ_goodΓ gΛ gM gN w hH,
    dPW1Γ gΛ gM gN hMa hNa hΛ hMp hNp hH hFw hdH⟩

/-- **`Ext¹` corrections in a weight component** of a `Γ`-grading. -/
theorem extVanishΓ0 (hMa : ∀ u v m a, gM.IsHom u m → gΛ.g.IsHom v a → gM.IsHom (u + v) (MM.act m a))
    (hNa : ∀ u v n a, gN.IsHom u n → gΛ.g.IsHom v a → gN.IsHom (u + v) (NN.act n a))
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (gM.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (gN.proj x n))
    {t : ℤ} (hExt : ExtVanish MM NN 0 t) (w : Γ) (F : Bar.Cochain Λ (M →ₗ[R] N))
    (hF : Good MM NN 1 t F) (hFw : GoodΓ gΛ gM gN 1 w F) (hdF : Bar.d (homAct MM NN) 1 F = 0) :
    ∃ H, Good MM NN 0 t H ∧ GoodΓ gΛ gM gN 0 w H ∧ Bar.d (homAct MM NN) 0 H = F := by
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  exact ⟨PW0Γ gM gN w H, PW0Γ_good gM gN w hH hMp hNp, PW0Γ_goodΓ gΛ gM gN w H,
    dPW0Γ gΛ gM gN hMa hNa hMp hNp hH hFw hdH⟩

end Refine

end GExt

end MultiplicativeBasisDeformations
