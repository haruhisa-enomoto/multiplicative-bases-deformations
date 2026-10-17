import MultiplicativeBasisDeformations.Refinements.WeightCone
import MultiplicativeBasisDeformations.Refinements.PolyFamily

/-!
# Twisting weight-homogeneous data by parameters (toward Proposition 12.8)

`deformation-refinements.tex`: "Give `t_i` total weight `−χ_i`, or equivalently
coefficient weight `χ_i`. The choices above, made separately in each weight, make `F_j`
homogeneous". Conversely, data at `t = 1` whose components have relative weights in the monoid
`C` of the `χ_i` define polynomial families: the component of relative weight `γ` is multiplied by
`t^{coords γ}`, where `coords : Wt →+ (I → ℤ)` sends `χ_i` to the `i`-th unit vector
(`twl` for linear maps, `twb` for bilinear maps). For `t` in the torus this is conjugation by the
diagonal scaling `S_t` (`twb_torus`, `twl_torus`), so twisting preserves all identities there; the
twisted data are polynomial in `t` (`IsPoly`), so the identities hold for every `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace MGr

variable {k : Type*} [Field k] {Wt : Type*} [AddCommGroup Wt] [DecidableEq Wt]
  {I : Type} [Fintype I] [DecidableEq I] (coords : Wt →+ (I → ℤ))

/-- The polynomial character `t^{coords γ}` (exponents truncated at `0`). -/
def ch (t : I → k) (γ : Wt) : k := mono (fun i ↦ (coords γ i).toNat) t

/-- The torus character `t^{coords γ}` with integer exponents. -/
def chz (t : I → k) (γ : Wt) : k := ∏ i, t i ^ coords γ i

variable {coords}

theorem chz_add {t : I → k} (ht : ∀ i, t i ≠ 0) (γ δ : Wt) :
    chz coords t (γ + δ) = chz coords t γ * chz coords t δ := by
  simp only [chz, map_add, Pi.add_apply, zpow_add₀ (ht _), Finset.prod_mul_distrib]

theorem chz_zero (t : I → k) : chz coords t 0 = 1 := by simp [chz]

theorem chz_ne_zero {t : I → k} (ht : ∀ i, t i ≠ 0) (γ : Wt) : chz coords t γ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ ↦ zpow_ne_zero _ (ht i)

theorem chz_neg {t : I → k} (ht : ∀ i, t i ≠ 0) (γ : Wt) :
    chz coords t (-γ) = (chz coords t γ)⁻¹ := by
  have := chz_add (coords := coords) ht γ (-γ)
  rw [add_neg_cancel, chz_zero] at this
  exact (eq_inv_of_mul_eq_one_right this.symm)

theorem chz_sub {t : I → k} (ht : ∀ i, t i ≠ 0) (γ δ : Wt) :
    chz coords t (γ - δ) = chz coords t γ * (chz coords t δ)⁻¹ := by
  rw [sub_eq_add_neg, chz_add ht, chz_neg ht]

theorem ch_eq_chz {t : I → k} {γ : Wt} (hγ : ∀ i, 0 ≤ coords γ i) :
    ch coords t γ = chz coords t γ := by
  simp only [ch, chz, mono]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← zpow_natCast, Int.toNat_of_nonneg (hγ i)]

theorem ch_one (γ : Wt) : ch coords (fun _ ↦ (1 : k)) γ = 1 := mono_one _

variable {C : AddSubmonoid Wt}

/-- The weights of the cone have nonnegative coordinates when the generators do. -/
theorem coords_nonneg_of_le (hC : ∀ γ ∈ C, ∀ i, 0 ≤ coords γ i) {γ : Wt} (hγ : γ ∈ C) (i : I) :
    0 ≤ coords γ i := hC γ hγ i

variable {N N' N'' : Type*} [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']
  [AddCommGroup N''] [Module k N''] (G : MGr k Wt N) (G' : MGr k Wt N') (G'' : MGr k Wt N'')

variable (coords) in
/-- **The diagonal scaling** `m ↦ t^{coords β} m` on weight `β`. -/
def scale (t : I → k) : N →ₗ[k] N := ∑ β ∈ G.supp, chz coords t β • G.proj β

theorem scale_hom (t : I → k) {β : Wt} {n : N} (hn : G.IsHom β n) :
    scale coords G t n = chz coords t β • n := by
  simp only [scale, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  by_cases hβ : β ∈ G.supp
  · rw [Finset.sum_eq_single β]
    · rw [hn]
    · intro e _ he; rw [G.proj_of_isHom hn, if_neg (Ne.symm he), smul_zero]
    · intro h; exact absurd hβ h
  · rw [G.eq_zero_of_isHom_out hn hβ]; simp

theorem chz_inv (t : I → k) (β : Wt) :
    chz coords (fun i ↦ (t i)⁻¹) β = (chz coords t β)⁻¹ := by
  simp only [chz, inv_zpow, Finset.prod_inv_distrib]

theorem scale_inv_scale {t : I → k} (ht : ∀ i, t i ≠ 0) (n : N) :
    scale coords G (fun i ↦ (t i)⁻¹) (scale coords G t n) = n := by
  have ht' : ∀ β : Wt, chz coords (fun i ↦ (t i)⁻¹) β * chz coords t β = 1 := by
    intro β
    rw [chz_inv, inv_mul_cancel₀ (chz_ne_zero ht β)]
  have := G.ext_of_hom (f := scale coords G (fun i ↦ (t i)⁻¹) ∘ₗ scale coords G t)
    (f' := LinearMap.id) fun β n hn ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [scale_hom G t hn, map_smul, scale_hom G _ hn, smul_smul, mul_comm, ht', one_smul]
  exact LinearMap.congr_fun this n

theorem scale_scale_inv {t : I → k} (ht : ∀ i, t i ≠ 0) (n : N) :
    scale coords G t (scale coords G (fun i ↦ (t i)⁻¹) n) = n := by
  have := scale_inv_scale (coords := coords) G (t := fun i ↦ (t i)⁻¹)
    (fun i ↦ inv_ne_zero (ht i)) n
  simpa only [inv_inv] using this

/-! ### Twisting linear and bilinear maps -/

variable (coords) in
/-- **The twist of a linear map** relative to the weight `ρ`. -/
def twl (t : I → k) (ρ : Wt) (f : N →ₗ[k] N') : N →ₗ[k] N' :=
  ∑ β ∈ G.supp, ∑ δ ∈ G'.supp, ch coords t (δ - β - ρ) • (G'.proj δ ∘ₗ f ∘ₗ G.proj β)

variable (coords) in
/-- **The twist of a bilinear map** relative to the weight `ρ`. -/
def twb (t : I → k) (ρ : Wt) (φ : N →ₗ[k] N' →ₗ[k] N'') : N →ₗ[k] N' →ₗ[k] N'' :=
  ∑ β ∈ G.supp, ∑ α ∈ G'.supp, ∑ δ ∈ G''.supp,
    ch coords t (δ - β - α - ρ) • ((φ.compl₁₂ (G.proj β) (G'.proj α)).compr₂ (G''.proj δ))

theorem twl_hom (t : I → k) (ρ : Wt) (f : N →ₗ[k] N') {β : Wt} {n : N} (hn : G.IsHom β n) :
    twl coords G G' t ρ f n = ∑ δ ∈ G'.supp, ch coords t (δ - β - ρ) • G'.proj δ (f n) := by
  simp only [twl, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  by_cases hβ : β ∈ G.supp
  · rw [Finset.sum_eq_single β]
    · rw [show G.proj β n = n from hn]
    · intro e _ he
      refine Finset.sum_eq_zero fun δ _ ↦ ?_
      rw [G.proj_of_isHom hn, if_neg (Ne.symm he), map_zero, map_zero, smul_zero]
    · intro h; exact absurd hβ h
  · rw [G.eq_zero_of_isHom_out hn hβ]; simp

theorem twb_hom (t : I → k) (ρ : Wt) (φ : N →ₗ[k] N' →ₗ[k] N'') {β α : Wt} {n : N} {n' : N'}
    (hn : G.IsHom β n) (hn' : G'.IsHom α n') :
    twb coords G G' G'' t ρ φ n n' =
      ∑ δ ∈ G''.supp, ch coords t (δ - β - α - ρ) • G''.proj δ (φ n n') := by
  simp only [twb, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  by_cases hβ : β ∈ G.supp
  · rw [Finset.sum_eq_single β]
    · by_cases hα : α ∈ G'.supp
      · rw [Finset.sum_eq_single α]
        · rw [show G.proj β n = n from hn, show G'.proj α n' = n' from hn']
        · intro e _ he
          refine Finset.sum_eq_zero fun δ _ ↦ ?_
          rw [G'.proj_of_isHom hn', if_neg (Ne.symm he), map_zero, map_zero, smul_zero]
        · intro h; exact absurd hα h
      · rw [G'.eq_zero_of_isHom_out hn' hα]; simp
    · intro e _ he
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun δ _ ↦ ?_
      rw [G.proj_of_isHom hn, if_neg (Ne.symm he), LinearMap.map_zero₂, map_zero, smul_zero]
    · intro h; exact absurd hβ h
  · rw [G.eq_zero_of_isHom_out hn hβ]; simp

variable {G G' G''}

/-- **On the torus, twisting a bilinear map in the cone is conjugation by the scalings.** -/
theorem twb_torus (hC : ∀ γ ∈ C, ∀ i, 0 ≤ coords γ i) {t : I → k} (ht : ∀ i, t i ≠ 0)
    {ρ : Wt} {φ : N →ₗ[k] N' →ₗ[k] N''} (hφ : ConeBil (C := C) (G := G) (G' := G') (G'' := G'') ρ φ)
    (n : N) (n' : N') :
    twb coords G G' G'' t ρ φ n n' = (chz coords t ρ)⁻¹ • scale coords G'' t
      (φ (scale coords G (fun i ↦ (t i)⁻¹) n) (scale coords G' (fun i ↦ (t i)⁻¹) n')) := by
  have key := bil_ext_of_hom (G := G) (G' := G') (φ := twb coords G G' G'' t ρ φ)
    (ψ := (chz coords t ρ)⁻¹ • (((φ.compl₁₂ (scale coords G (fun i ↦ (t i)⁻¹))
      (scale coords G' (fun i ↦ (t i)⁻¹))).compr₂ (scale coords G'' t)))) fun β α n n' hn hn' ↦ by
    rw [twb_hom G G' G'' t ρ φ hn hn']
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    rw [scale_hom G _ hn, scale_hom G' _ hn']
    simp only [map_smul, LinearMap.map_smul₂, LinearMap.smul_apply]
    simp only [scale, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    rw [smul_smul, smul_smul, smul_smul]
    by_cases hδ : δ - (β + α + ρ) ∈ C
    · congr 1
      rw [ch_eq_chz (hC _ (by rwa [show δ - β - α - ρ = δ - (β + α + ρ) by abel])),
        chz_inv, chz_inv]
      rw [show δ - β - α - ρ = δ - (β + α) - ρ by abel, chz_sub ht, chz_sub ht, chz_add ht]
      field_simp
    · rw [hφ β α n n' hn hn' δ hδ, smul_zero, smul_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun key n) n'

/-- **On the torus, twisting a linear map in the cone is conjugation by the scalings.** -/
theorem twl_torus (hC : ∀ γ ∈ C, ∀ i, 0 ≤ coords γ i) {t : I → k} (ht : ∀ i, t i ≠ 0)
    {ρ : Wt} {f : N →ₗ[k] N'} (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) (n : N) :
    twl coords G G' t ρ f n =
      (chz coords t ρ)⁻¹ • scale coords G' t (f (scale coords G (fun i ↦ (t i)⁻¹) n)) := by
  have key := G.ext_of_hom (f := twl coords G G' t ρ f)
    (f' := (chz coords t ρ)⁻¹ • (scale coords G' t ∘ₗ f ∘ₗ scale coords G (fun i ↦ (t i)⁻¹)))
    fun β n hn ↦ by
      rw [twl_hom G G' t ρ f hn]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply]
      rw [scale_hom G _ hn, map_smul]
      simp only [scale, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun δ _ ↦ ?_
      rw [map_smul, smul_smul, smul_smul]
      by_cases hδ : δ - (β + ρ) ∈ C
      · congr 1
        rw [ch_eq_chz (hC _ (by rwa [show δ - β - ρ = δ - (β + ρ) by abel])), chz_inv]
        rw [chz_sub ht, chz_sub ht]
        field_simp
      · rw [hf β n hn δ hδ, smul_zero, smul_zero]
  exact LinearMap.congr_fun key n

/-! ### Polynomiality -/

theorem isPoly_ch (γ : Wt) : IsPoly (fun t : I → k ↦ ch coords t γ • (1 : k)) := by
  simpa [ch] using IsPoly.monomial (k := k) (fun i ↦ (coords γ i).toNat) (1 : k)

variable (G G' G'')

theorem isPoly_twl (ρ : Wt) (f : N →ₗ[k] N') :
    IsPoly (fun t : I → k ↦ twl coords G G' t ρ f) := by
  unfold twl
  exact IsPoly.sum _ fun β _ ↦ IsPoly.sum _ fun δ _ ↦ IsPoly.monomial _ _

theorem isPoly_twb (ρ : Wt) (φ : N →ₗ[k] N' →ₗ[k] N'') :
    IsPoly (fun t : I → k ↦ twb coords G G' G'' t ρ φ) := by
  unfold twb
  exact IsPoly.sum _ fun β _ ↦ IsPoly.sum _ fun α _ ↦ IsPoly.sum _ fun δ _ ↦
    IsPoly.monomial _ _

end MGr

end MultiplicativeBasisDeformations
