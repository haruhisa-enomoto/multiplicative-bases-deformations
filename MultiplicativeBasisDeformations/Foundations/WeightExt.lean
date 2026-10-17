import MultiplicativeBasisDeformations.Foundations.GradedExt

/-!
# Corrections in each weight component (Proposition 10.1, last paragraph)

`integral-deformations.tex`: "All these constructions can be chosen to preserve the
simultaneous integer weights: lifting a basis of `H_ℤ` to mesh weights by Lemma 7.4 gives the
modules `M_i⁽²⁾` compatible weight gradings, and the corrections can be chosen in each weight
component."

A second `ℤ`-grading (a weight) on `Λ`, `M`, `N`, compatible with the same actions and commuting
with the internal degree, refines graded `Ext`: the corrections used in Proposition 10.1 come from
`Ext¹` and `Ext²` (`ExtVanish _ _ 0 _`, `ExtVanish _ _ 1 _`), and a correction `H` with `dH = F`
can be replaced by its weight-`w` component `PW w H` when `F` has weight `w` (`dPW0`, `dPW1`).
The component is computed on homogeneous inputs, where it is the weight projection of the value;
two multilinear cochains agreeing on homogeneous inputs agree (`ext_one`, `ext_two`).
Several weights are treated one after another (`extVanish_weights`): each projection preserves the
degree and the earlier weights.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R]

namespace ZGr

variable {M : Type*} [AddCommGroup M] [Module R M] (g : ZGr (R := R) M)

/-- The projection of a sum of homogeneous terms. -/
theorem proj_sum_hom {ι : Type*} (s : Finset ι) (x : ι → M) (f : ι → ℤ)
    (h : ∀ i ∈ s, g.IsHom (f i) (x i)) (w : ℤ) :
    g.proj w (∑ i ∈ s, x i) = ∑ i ∈ s with f i = w, x i := by
  classical
  rw [map_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i hi ↦ g.proj_of_isHom (h i hi)

end ZGr

variable {Λ : Type*} [Ring Λ] [Algebra R Λ]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Proj

variable {GΛw : GAlg (R := R) Λ} (MMw : GMod GΛw M) (NNw : GMod GΛw N)

/-- The weight-`w` component of a `0`-cochain. -/
def PW0 (w : ℤ) (H : Bar.Cochain Λ (M →ₗ[R] N)) : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦
  ∑ u ∈ MMw.gr.supp, NNw.gr.proj (u + w) ∘ₗ H a ∘ₗ MMw.gr.proj u

/-- The weight-`w` component of a `1`-cochain. -/
def PW1 (w : ℤ) (H : Bar.Cochain Λ (M →ₗ[R] N)) : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦
  ∑ v ∈ GΛw.gr.supp, ∑ u ∈ MMw.gr.supp,
    NNw.gr.proj (u + v + w) ∘ₗ H (single (GΛw.gr.proj v (a 0))) ∘ₗ MMw.gr.proj u

/-- On a homogeneous input, the component of a `0`-cochain is the projection of the value. -/
theorem PW0_hom (w : ℤ) (H : Bar.Cochain Λ (M →ₗ[R] N)) (a : ℕ → Λ) {u₀ : ℤ} {m : M}
    (hm : MMw.gr.IsHom u₀ m) : PW0 MMw NNw w H a m = NNw.gr.proj (u₀ + w) (H a m) := by
  classical
  simp only [PW0, LinearMap.sum_apply, LinearMap.comp_apply]
  simp_rw [MMw.gr.proj_of_isHom hm]
  by_cases hu : u₀ ∈ MMw.gr.supp
  · rw [Finset.sum_eq_single_of_mem u₀ hu]
    · rw [if_pos rfl]
    · intro u _ hne; rw [if_neg (Ne.symm hne), map_zero, map_zero]
  · rw [MMw.gr.eq_zero_of_isHom_out hm hu]
    simp

variable {GΛo : GAlg (R := R) Λ} {MMo : GMod GΛo M} {NNo : GMod GΛo N} {t : ℤ}

theorem single_zero_eq {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) :
    H (single 0) = 0 := by
  have := hH.single_smul 0 0
  simpa using this

/-- On homogeneous inputs, the component of a `1`-cochain is the projection of the value. -/
theorem PW1_hom (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) (a : ℕ → Λ)
    {v₀ u₀ : ℤ} {m : M} (ha : GΛw.gr.IsHom v₀ (a 0)) (hm : MMw.gr.IsHom u₀ m) :
    PW1 MMw NNw w H a m = NNw.gr.proj (u₀ + v₀ + w) (H (single (a 0)) m) := by
  classical
  have h0 := single_zero_eq hH
  simp only [PW1, LinearMap.sum_apply, LinearMap.comp_apply]
  simp_rw [GΛw.gr.proj_of_isHom ha, MMw.gr.proj_of_isHom hm]
  by_cases hv : v₀ ∈ GΛw.gr.supp
  · rw [Finset.sum_eq_single_of_mem v₀ hv]
    · rw [if_pos rfl]
      by_cases hu : u₀ ∈ MMw.gr.supp
      · rw [Finset.sum_eq_single_of_mem u₀ hu]
        · rw [if_pos rfl]
        · intro u _ hne; rw [if_neg (Ne.symm hne), map_zero, map_zero]
      · rw [MMw.gr.eq_zero_of_isHom_out hm hu]; simp
    · intro v _ hne
      rw [if_neg (Ne.symm hne), h0]
      simp
  · rw [GΛw.gr.eq_zero_of_isHom_out ha hv, h0]
    simp [h0]

theorem PW1_tr (w : ℤ) (H : Bar.Cochain Λ (M →ₗ[R] N)) (a : ℕ → Λ) :
    PW1 MMw NNw w H a = PW1 MMw NNw w H (Bar.tr 1 a) := by
  simp [PW1, Bar.tr]

theorem PW1_add (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) (a : ℕ → Λ)
    (x y : Λ) : PW1 MMw NNw w H (Function.update a 0 (x + y)) =
      PW1 MMw NNw w H (Function.update a 0 x) + PW1 MMw NNw w H (Function.update a 0 y) := by
  simp only [PW1, Function.update_self, map_add, hH.single_add, LinearMap.add_comp,
    LinearMap.comp_add, Finset.sum_add_distrib]

theorem PW1_smul (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) (a : ℕ → Λ)
    (c : R) (x : Λ) : PW1 MMw NNw w H (Function.update a 0 (c • x)) =
      c • PW1 MMw NNw w H (Function.update a 0 x) := by
  simp only [PW1, Function.update_self, map_smul, hH.single_smul, LinearMap.smul_comp,
    LinearMap.comp_smul, Finset.smul_sum]

/-- **The component keeps every grading its projections preserve.** -/
theorem PW1_good (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H)
    (hΛ : ∀ v p a, GΛo.gr.IsHom p a → GΛo.gr.IsHom p (GΛw.gr.proj v a))
    (hMp : ∀ u p m, MMo.gr.IsHom p m → MMo.gr.IsHom p (MMw.gr.proj u m))
    (hNp : ∀ x p n, NNo.gr.IsHom p n → NNo.gr.IsHom p (NNw.gr.proj x n)) :
    Good MMo NNo 1 t (PW1 MMw NNw w H) where
  tr a := PW1_tr MMw NNw w H a
  add a i x y hi := by obtain rfl : i = 0 := by omega
                       exact PW1_add MMw NNw w hH a x y
  smul a i c x hi := by obtain rfl : i = 0 := by omega
                        exact PW1_smul MMw NNw w hH a c x
  deg a ds p m ha hm := by
    simp only [PW1, LinearMap.sum_apply, LinearMap.comp_apply]
    refine NNo.gr.isHom_sum _ _ fun v _ ↦ NNo.gr.isHom_sum _ _ fun u _ ↦ hNp _ _ _ ?_
    refine hH.deg _ ds p _ (fun i hi ↦ ?_) (hMp _ _ _ hm)
    obtain rfl : i = 0 := by omega
    simpa [single, Bar.cons] using hΛ v _ _ (ha 0 (by omega))

/-- **The component is homogeneous of weight `w`.** -/
theorem PW1_goodW (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 1 t H) :
    Good MMw NNw 1 w (PW1 MMw NNw w H) where
  tr a := PW1_tr MMw NNw w H a
  add a i x y hi := by obtain rfl : i = 0 := by omega
                       exact PW1_add MMw NNw w hH a x y
  smul a i c x hi := by obtain rfl : i = 0 := by omega
                        exact PW1_smul MMw NNw w hH a c x
  deg a ds p m ha hm := by
    rw [PW1_hom MMw NNw w hH a (ha 0 (by omega)) hm, Finset.sum_range_one]
    exact NNw.gr.isHom_proj _ _

/-- The `0`-cochain version. -/
theorem PW0_good (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 0 t H)
    (hMp : ∀ u p m, MMo.gr.IsHom p m → MMo.gr.IsHom p (MMw.gr.proj u m))
    (hNp : ∀ x p n, NNo.gr.IsHom p n → NNo.gr.IsHom p (NNw.gr.proj x n)) :
    Good MMo NNo 0 t (PW0 MMw NNw w H) where
  tr a := by simp only [PW0]; rw [hH.tr a]
  add a i x y hi := absurd hi (Nat.not_lt_zero _)
  smul a i c x hi := absurd hi (Nat.not_lt_zero _)
  deg a ds p m ha hm := by
    simp only [PW0, LinearMap.sum_apply, LinearMap.comp_apply]
    exact NNo.gr.isHom_sum _ _ fun u _ ↦ hNp _ _ _ (hH.deg a ds p _ ha (hMp _ _ _ hm))

theorem PW0_goodW (w : ℤ) {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MMo NNo 0 t H) :
    Good MMw NNw 0 w (PW0 MMw NNw w H) where
  tr a := by simp only [PW0]; rw [hH.tr a]
  add a i x y hi := absurd hi (Nat.not_lt_zero _)
  smul a i c x hi := absurd hi (Nat.not_lt_zero _)
  deg a ds p m ha hm := by
    rw [PW0_hom MMw NNw w H a hm, Finset.sum_range_zero, add_zero]
    exact NNw.gr.isHom_proj _ _

/-! ### Agreement on homogeneous inputs -/

/-- The sequence `(a, b, 0, …)`. -/
def pair (a b : Λ) : ℕ → Λ := Bar.cons a (single b)

theorem Good.pair_eq {G : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G) (a : ℕ → Λ) :
    G a = G (pair (a 0) (a 1)) := by
  rw [hG.tr, hG.tr (pair _ _)]
  congr 1
  funext k
  rcases k with _ | _ | k <;> simp [Bar.tr, pair, single, Bar.cons]

theorem Good.pair_add_left {G : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G)
    (x x' y : Λ) : G (pair (x + x') y) = G (pair x y) + G (pair x' y) := by
  have := hG.add (pair 0 y) 0 x x' (by omega)
  simpa [pair, Bar.update_cons_zero] using this

theorem Good.pair_add_right {G : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G)
    (x y y' : Λ) : G (pair x (y + y')) = G (pair x y) + G (pair x y') := by
  have := hG.add (pair x 0) 1 y y' (by omega)
  simpa [pair, single, Bar.update_cons_succ, Bar.update_cons_zero] using this

/-- **`1`-cochains agreeing on homogeneous inputs agree.** -/
theorem ext_one {G G' : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 1 t G)
    (hG' : Good MMo NNo 1 t G')
    (h : ∀ (a : Λ) (m : M) (v u : ℤ), GΛw.gr.IsHom v a → MMw.gr.IsHom u m →
      G (single a) m = G' (single a) m) : G = G' := by
  funext a
  rw [hG.one_eq a, hG'.one_eq a]
  let φ : Λ →+ (M →ₗ[R] N) := ⟨⟨fun x ↦ G (single x), single_zero_eq hG⟩, hG.single_add⟩
  let φ' : Λ →+ (M →ₗ[R] N) := ⟨⟨fun x ↦ G' (single x), single_zero_eq hG'⟩, hG'.single_add⟩
  change φ (a 0) = φ' (a 0)
  rw [GΛw.gr.sum (a 0), map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  apply LinearMap.ext
  intro m
  rw [MMw.gr.sum m, map_sum, map_sum]
  exact Finset.sum_congr rfl fun u _ ↦
    h _ _ v u (GΛw.gr.isHom_proj v _) (MMw.gr.isHom_proj u m)

theorem Good.pair_zero_left {G : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G) (y : Λ) :
    G (pair 0 y) = 0 := by
  have := hG.pair_add_left 0 0 y; simpa using this

theorem Good.pair_zero_right {G : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G) (x : Λ) :
    G (pair x 0) = 0 := by
  have := hG.pair_add_right x 0 0; simpa using this

/-- A good `2`-cochain as a biadditive map. -/
def bil {G : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G) : Λ →+ Λ →+ (M →ₗ[R] N) where
  toFun x := ⟨⟨fun y ↦ G (pair x y), hG.pair_zero_right x⟩, hG.pair_add_right x⟩
  map_zero' := AddMonoidHom.ext fun y ↦ hG.pair_zero_left y
  map_add' x x' := AddMonoidHom.ext fun y ↦ hG.pair_add_left x x' y

/-- **`2`-cochains agreeing on homogeneous inputs agree.** -/
theorem ext_two {G G' : Bar.Cochain Λ (M →ₗ[R] N)} (hG : Good MMo NNo 2 t G)
    (hG' : Good MMo NNo 2 t G')
    (h : ∀ (a b : Λ) (m : M) (v₀ v₁ u : ℤ), GΛw.gr.IsHom v₀ a → GΛw.gr.IsHom v₁ b →
      MMw.gr.IsHom u m → G (pair a b) m = G' (pair a b) m) : G = G' := by
  funext a
  rw [hG.pair_eq a, hG'.pair_eq a]
  change bil hG (a 0) (a 1) = bil hG' (a 0) (a 1)
  rw [GΛw.gr.sum (a 0), map_sum, map_sum, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun v₀ _ ↦ ?_
  rw [GΛw.gr.sum (a 1), map_sum, map_sum]
  refine Finset.sum_congr rfl fun v₁ _ ↦ ?_
  apply LinearMap.ext
  intro m
  rw [MMw.gr.sum m, map_sum, map_sum]
  exact Finset.sum_congr rfl fun u _ ↦ h _ _ _ v₀ v₁ u (GΛw.gr.isHom_proj _ _)
    (GΛw.gr.isHom_proj _ _) (MMw.gr.isHom_proj u m)

end Proj

/-! ### The corrections, weight by weight -/

section Refine

variable {GΛ GΛw : GAlg (R := R) Λ} {MM : GMod GΛ M} {NN : GMod GΛ N}
  {MMw : GMod GΛw M} {NNw : GMod GΛw N}

theorem pair_sh (a b : Λ) : Bar.sh (pair a b) 0 = b := rfl

theorem pair_ct (a b : Λ) : Bar.ct 0 (pair a b) 0 = a * b := Bar.ct_apply_self 0 _

theorem pair_tr (a b : Λ) : Bar.tr 1 (pair a b) 0 = a := rfl

/-- **`d` of the component of a `1`-cochain** is the given weight-`w` cocycle. -/
theorem dPW1 (hMa : MMw.act = MM.act) (hNa : NNw.act = NN.act)
    (hΛ : ∀ v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p (GΛw.gr.proj v a))
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (MMw.gr.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (NNw.gr.proj x n))
    {t w : ℤ} {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MM NN 1 t H)
    {F : Bar.Cochain Λ (M →ₗ[R] N)} (hFw : Good MMw NNw 2 w F)
    (hd : Bar.d (homAct MM NN) 1 H = F) :
    Bar.d (homAct MM NN) 1 (PW1 MMw NNw w H) = F := by
  have hF : Good MM NN 2 t F := hd ▸ hH.d
  refine ext_two (GΛw := GΛw) (MMw := MMw) (PW1_good MMw NNw w hH hΛ hMp hNp).d hF
    fun a b m v₀ v₁ u ha hb hm ↦ ?_
  have hma : MMw.gr.IsHom (u + v₀) (MM.act m a) := by rw [← hMa]; exact MMw.act_hom _ _ _ _ hm ha
  have hab : GΛw.gr.IsHom (v₀ + v₁) (a * b) := GΛw.mul_hom _ _ _ _ ha hb
  have hFh : NNw.gr.IsHom (u + v₀ + v₁ + w) (F (pair a b) m) := by
    have := hFw.deg (pair a b) (fun i ↦ if i = 0 then v₀ else v₁) u m (fun i hi ↦ by
      rcases i with _ | _ | i
      · simpa [pair, Bar.cons] using ha
      · simpa [pair, single, Bar.cons] using hb
      · omega) hm
    simpa [Finset.sum_range_succ, add_assoc] using this
  rw [← hFh, ← hd, Bar.d_one_apply, Bar.d_one_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r]
  rw [show pair a b 0 = a from rfl, show pair a b 1 = b from rfl]
  rw [PW1_hom MMw NNw w hH _ (v₀ := v₁) (by rw [pair_sh]; exact hb) hma,
    PW1_hom MMw NNw w hH _ (v₀ := v₀ + v₁) (by rw [pair_ct]; exact hab) hm,
    PW1_hom MMw NNw w hH _ (v₀ := v₀) (by rw [pair_tr]; exact ha) hm,
    hH.one_eq (Bar.sh _), hH.one_eq (Bar.ct 0 _), hH.one_eq (Bar.tr 1 _), pair_sh, pair_ct,
    pair_tr, ← hNa, ← proj_act NNw hb, map_add, map_sub]
  rw [show u + v₀ + v₁ + w = u + (v₀ + v₁) + w by ring,
    show u + (v₀ + v₁) + w = u + v₀ + w + v₁ by ring]

/-- **`d` of the component of a `0`-cochain** is the given weight-`w` cocycle. -/
theorem dPW0 (hMa : MMw.act = MM.act) (hNa : NNw.act = NN.act)
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (MMw.gr.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (NNw.gr.proj x n))
    {t w : ℤ} {H : Bar.Cochain Λ (M →ₗ[R] N)} (hH : Good MM NN 0 t H)
    {F : Bar.Cochain Λ (M →ₗ[R] N)} (hFw : Good MMw NNw 1 w F)
    (hd : Bar.d (homAct MM NN) 0 H = F) :
    Bar.d (homAct MM NN) 0 (PW0 MMw NNw w H) = F := by
  have hF : Good MM NN 1 t F := hd ▸ hH.d
  refine ext_one (GΛw := GΛw) (MMw := MMw) (PW0_good MMw NNw w hH hMp hNp).d hF
    fun a m v u ha hm ↦ ?_
  have hma : MMw.gr.IsHom (u + v) (MM.act m a) := by rw [← hMa]; exact MMw.act_hom _ _ _ _ hm ha
  have hFh : NNw.gr.IsHom (u + v + w) (F (single a) m) := by
    have := hFw.deg (single a) (fun _ ↦ v) u m (fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simpa [single, Bar.cons] using ha) hm
    simpa using this
  rw [← hFh, ← hd, Bar.d_zero_apply, Bar.d_zero_apply]
  simp only [LinearMap.sub_apply, homAct_l, homAct_r]
  rw [show single a 0 = a from rfl]
  rw [PW0_hom MMw NNw w H _ hma, PW0_hom MMw NNw w H _ hm, ← hNa, ← proj_act NNw ha, map_sub]
  rw [show u + w + v = u + v + w by ring]

/-- **`Ext²` corrections in a weight component.** -/
theorem extVanish_weight1 (hMa : MMw.act = MM.act) (hNa : NNw.act = NN.act)
    (hΛ : ∀ v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p (GΛw.gr.proj v a))
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (MMw.gr.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (NNw.gr.proj x n))
    {t : ℤ} (hExt : ExtVanish MM NN 1 t) (w : ℤ) (F : Bar.Cochain Λ (M →ₗ[R] N))
    (hF : Good MM NN 2 t F) (hFw : Good MMw NNw 2 w F) (hdF : Bar.d (homAct MM NN) 2 F = 0) :
    ∃ H, Good MM NN 1 t H ∧ Good MMw NNw 1 w H ∧ Bar.d (homAct MM NN) 1 H = F := by
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  exact ⟨PW1 MMw NNw w H, PW1_good MMw NNw w hH hΛ hMp hNp, PW1_goodW MMw NNw w hH,
    dPW1 hMa hNa hΛ hMp hNp hH hFw hdH⟩

/-- **`Ext¹` corrections in a weight component.** -/
theorem extVanish_weight0 (hMa : MMw.act = MM.act) (hNa : NNw.act = NN.act)
    (hMp : ∀ u p m, MM.gr.IsHom p m → MM.gr.IsHom p (MMw.gr.proj u m))
    (hNp : ∀ x p n, NN.gr.IsHom p n → NN.gr.IsHom p (NNw.gr.proj x n))
    {t : ℤ} (hExt : ExtVanish MM NN 0 t) (w : ℤ) (F : Bar.Cochain Λ (M →ₗ[R] N))
    (hF : Good MM NN 1 t F) (hFw : Good MMw NNw 1 w F) (hdF : Bar.d (homAct MM NN) 1 F = 0) :
    ∃ H, Good MM NN 0 t H ∧ Good MMw NNw 0 w H ∧ Bar.d (homAct MM NN) 0 H = F := by
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  exact ⟨PW0 MMw NNw w H, PW0_good MMw NNw w hH hMp hNp, PW0_goodW MMw NNw w hH,
    dPW0 hMa hNa hMp hNp hH hFw hdH⟩

/-! ### Several weights -/

section Several

variable {r : ℕ} {GΛw : Fin r → GAlg (R := R) Λ} (MMw : ∀ i, GMod (GΛw i) M)
  (NNw : ∀ i, GMod (GΛw i) N)
  (hMa : ∀ i, (MMw i).act = MM.act) (hNa : ∀ i, (NNw i).act = NN.act)
  (hΛ : ∀ i v p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p ((GΛw i).gr.proj v a))
  (hMp : ∀ i u p m, MM.gr.IsHom p m → MM.gr.IsHom p ((MMw i).gr.proj u m))
  (hNp : ∀ i x p n, NN.gr.IsHom p n → NN.gr.IsHom p ((NNw i).gr.proj x n))
  (hΛw : ∀ i j v p a, (GΛw j).gr.IsHom p a → (GΛw j).gr.IsHom p ((GΛw i).gr.proj v a))
  (hMw : ∀ i j u p m, (MMw j).gr.IsHom p m → (MMw j).gr.IsHom p ((MMw i).gr.proj u m))
  (hNw : ∀ i j x p n, (NNw j).gr.IsHom p n → (NNw j).gr.IsHom p ((NNw i).gr.proj x n))

/-- The successive components. -/
def seq1 (w : Fin r → ℤ) (H : Bar.Cochain Λ (M →ₗ[R] N)) : ℕ → Bar.Cochain Λ (M →ₗ[R] N)
  | 0 => H
  | j + 1 => if h : j < r then PW1 (MMw ⟨j, h⟩) (NNw ⟨j, h⟩) (w ⟨j, h⟩) (seq1 w H j)
      else seq1 w H j

/-- The successive components of a `0`-cochain. -/
def seq0 (w : Fin r → ℤ) (H : Bar.Cochain Λ (M →ₗ[R] N)) : ℕ → Bar.Cochain Λ (M →ₗ[R] N)
  | 0 => H
  | j + 1 => if h : j < r then PW0 (MMw ⟨j, h⟩) (NNw ⟨j, h⟩) (w ⟨j, h⟩) (seq0 w H j)
      else seq0 w H j

include hMa hNa hΛ hMp hNp hΛw hMw hNw in
/-- **`Ext²` corrections homogeneous for all the weights at once.** -/
theorem extVanish_weights1 {t : ℤ} (hExt : ExtVanish MM NN 1 t) (w : Fin r → ℤ)
    (F : Bar.Cochain Λ (M →ₗ[R] N)) (hF : Good MM NN 2 t F)
    (hFw : ∀ i, Good (MMw i) (NNw i) 2 (w i) F) (hdF : Bar.d (homAct MM NN) 2 F = 0) :
    ∃ H, Good MM NN 1 t H ∧ (∀ i, Good (MMw i) (NNw i) 1 (w i) H) ∧
      Bar.d (homAct MM NN) 1 H = F := by
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  have key : ∀ j ≤ r, Good MM NN 1 t (seq1 MMw NNw w H j) ∧
      (∀ i : Fin r, i.1 < j → Good (MMw i) (NNw i) 1 (w i) (seq1 MMw NNw w H j)) ∧
      Bar.d (homAct MM NN) 1 (seq1 MMw NNw w H j) = F := by
    intro j
    induction j with
    | zero => exact fun _ ↦ ⟨hH, fun i hi ↦ absurd hi (Nat.not_lt_zero _), hdH⟩
    | succ j ih =>
        intro hj
        obtain ⟨h1, h2, h3⟩ := ih (by omega)
        have hjr : j < r := by omega
        simp only [seq1, dif_pos hjr]
        refine ⟨PW1_good _ _ _ h1 (hΛ _) (hMp _) (hNp _), fun i hi ↦ ?_,
          dPW1 (hMa _) (hNa _) (hΛ _) (hMp _) (hNp _) h1 (hFw _) h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact PW1_good _ _ _ (h2 i hi) (hΛw _ i) (hMw _ i) (hNw _ i)
        · obtain rfl : i = ⟨j, hjr⟩ := Fin.ext hi
          exact PW1_goodW _ _ _ h1
  obtain ⟨h1, h2, h3⟩ := key r le_rfl
  exact ⟨_, h1, fun i ↦ h2 i i.2, h3⟩

include hMa hNa hMp hNp hMw hNw in
/-- **`Ext¹` corrections homogeneous for all the weights at once.** -/
theorem extVanish_weights0 {t : ℤ} (hExt : ExtVanish MM NN 0 t) (w : Fin r → ℤ)
    (F : Bar.Cochain Λ (M →ₗ[R] N)) (hF : Good MM NN 1 t F)
    (hFw : ∀ i, Good (MMw i) (NNw i) 1 (w i) F) (hdF : Bar.d (homAct MM NN) 1 F = 0) :
    ∃ H, Good MM NN 0 t H ∧ (∀ i, Good (MMw i) (NNw i) 0 (w i) H) ∧
      Bar.d (homAct MM NN) 0 H = F := by
  obtain ⟨H, hH, hdH⟩ := hExt F hF hdF
  have key : ∀ j ≤ r, Good MM NN 0 t (seq0 MMw NNw w H j) ∧
      (∀ i : Fin r, i.1 < j → Good (MMw i) (NNw i) 0 (w i) (seq0 MMw NNw w H j)) ∧
      Bar.d (homAct MM NN) 0 (seq0 MMw NNw w H j) = F := by
    intro j
    induction j with
    | zero => exact fun _ ↦ ⟨hH, fun i hi ↦ absurd hi (Nat.not_lt_zero _), hdH⟩
    | succ j ih =>
        intro hj
        obtain ⟨h1, h2, h3⟩ := ih (by omega)
        have hjr : j < r := by omega
        simp only [seq0, dif_pos hjr]
        refine ⟨PW0_good _ _ _ h1 (hMp _) (hNp _), fun i hi ↦ ?_,
          dPW0 (hMa _) (hNa _) (hMp _) (hNp _) h1 (hFw _) h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact PW0_good _ _ _ (h2 i hi) (hMw _ i) (hNw _ i)
        · obtain rfl : i = ⟨j, hjr⟩ := Fin.ext hi
          exact PW0_goodW _ _ _ h1
  obtain ⟨h1, h2, h3⟩ := key r le_rfl
  exact ⟨_, h1, fun i ↦ h2 i i.2, h3⟩

end Several

end Refine

end GExt

end MultiplicativeBasisDeformations
