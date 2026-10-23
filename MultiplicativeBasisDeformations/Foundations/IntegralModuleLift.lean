module

public import MultiplicativeBasisDeformations.Foundations.IntegralModules

/-!
# Lifting a graded module to `ℤ/4` (Proposition 10.1)

`integral-deformations.tex`: "Lift the action matrices arbitrarily to free graded
`𝒪`-modules. Their associativity defect is even. Division by two, followed by reduction, gives
an `Ext²` class of degree zero. … Since `(2𝒪)² = 0`, this single correction makes the action
associative."

For a graded `Λ`-module `M` with a homogeneous basis `β` and `Ext²_0(M, M) = 0`, the free
module `ι → 𝒪` carries a graded `Λ̃`-action lifting that of `M` (`exists_liftMod`). The
unit is automatic: the action of `1` is an idempotent congruent to the identity.
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
  {Λ' : Type*} [Ring Λ'] [Algebra (ZMod 4) Λ'] {GΛ' : GAlg (R := ZMod 4) Λ'}
  {π : Λ' →+* Λ}

/-! ### The free lift of a graded module with a homogeneous basis -/

section Free

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (β : Module.Basis ι 𝔽₂ M) (dβ : ι → ℤ)

/-- The grading of `ι → 𝒪` by the degrees of the basis. -/
def grF : ZGr (R := ZMod 4) (ι → ZMod 4) where
  proj p := LinearMap.pi fun i ↦ if dβ i = p then LinearMap.proj i else 0
  supp := Finset.univ.image dβ
  proj_proj p q m := by
    funext i
    simp only [LinearMap.pi_apply]
    by_cases hq : dβ i = q <;> by_cases hp : dβ i = p <;> split_ifs <;> simp_all
  proj_out p hp := by
    refine LinearMap.ext fun m ↦ funext fun i ↦ ?_
    rw [LinearMap.pi_apply, if_neg]
    · rfl
    · rintro rfl; exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  sum m := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single (dβ i)]
    · simp [LinearMap.pi_apply]
    · intro p _ hp; simp [LinearMap.pi_apply, Ne.symm hp]
    · intro h; exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ i)) h

theorem grF_isHom {p : ℤ} {m : ι → ZMod 4} :
    (grF dβ).IsHom p m ↔ ∀ i, dβ i ≠ p → m i = 0 := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp only [grF, LinearMap.pi_apply, if_neg hi, LinearMap.zero_apply] at this
    exact this.symm
  · intro h
    funext i
    simp only [grF, LinearMap.pi_apply]
    split_ifs with hi
    · rfl
    · exact (h i hi).symm

/-- The reduction `ι → 𝒪 → M`. -/
def ρF : (ι → ZMod 4) →+ M where
  toFun m := ∑ i, Z4.red (m i) • β i
  map_zero' := by simp
  map_add' m n := by simp [add_smul, Finset.sum_add_distrib]

theorem ρF_apply (m : ι → ZMod 4) : ρF β m = ∑ i, Z4.red (m i) • β i := rfl

theorem ρF_eq_equivFun (m : ι → ZMod 4) : ρF β m = β.equivFun.symm (fun i ↦ Z4.red (m i)) := by
  rw [ρF_apply, Module.Basis.equivFun_symm_apply]

theorem ρF_smul (a : ZMod 4) (m : ι → ZMod 4) : ρF β (a • m) = Z4.red a • ρF β m := by
  simp only [ρF_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem ρF_single (i : ι) (a : ZMod 4) : ρF β (Pi.single i a) = Z4.red a • β i := by
  rw [ρF_apply, Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero,
    zero_smul]) (fun h ↦ absurd (Finset.mem_univ i) h), Pi.single_eq_same]

/-- The coordinatewise lift. -/
def lv (m : M) : ι → ZMod 4 := fun i ↦ Z4.lift (β.repr m i)

theorem ρF_lv (m : M) : ρF β (lv β m) = m := by
  simp only [ρF_apply, lv, Z4.red_lift]
  exact β.sum_repr m

variable {MM : GMod GΛ M} (hβ : ∀ i, MM.gr.IsHom (dβ i) (β i))

include hβ in
theorem repr_eq_zero_of_isHom {p : ℤ} {m : M} (hm : MM.gr.IsHom p m) {i : ι} (hi : dβ i ≠ p) :
    β.repr m i = 0 := by
  have key : m = β.equivFun.symm (fun j ↦ if dβ j = p then β.repr m j else 0) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← hm, ← β.sum_repr m, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, MM.gr.proj_of_isHom (hβ j)]
    split_ifs <;> simp
  have := congrArg (fun z ↦ β.equivFun z i) key
  simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at this
  rw [this, if_neg hi]

include hβ in
theorem lv_isHom {p : ℤ} {m : M} (hm : MM.gr.IsHom p m) : (grF dβ).IsHom p (lv β m) := by
  rw [grF_isHom]
  intro i hi
  rw [lv, repr_eq_zero_of_isHom β dβ hβ hm hi]
  rfl

include hβ in
theorem ρF_isHom {p : ℤ} {m : ι → ZMod 4} (hm : (grF dβ).IsHom p m) : MM.gr.IsHom p (ρF β m) := by
  rw [grF_isHom] at hm
  rw [ρF_apply]
  refine MM.gr.isHom_sum _ _ fun i _ ↦ ?_
  by_cases hi : dβ i = p
  · rw [← hi]; exact MM.gr.isHom_smul _ (hβ i)
  · rw [hm i hi, map_zero, zero_smul]; exact MM.gr.isHom_zero _

theorem ρF_eq_zero {m : ι → ZMod 4} (h : ρF β m = 0) : ∀ i, Z4.red (m i) = 0 := by
  intro i
  rw [ρF_eq_equivFun] at h
  have := congrArg (fun z ↦ β.equivFun z i) h
  simp only [LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] at this
  exact this

theorem ker_ρF {m : ι → ZMod 4} (h : ρF β m = 0) : ∃ m', m = (2 : ZMod 4) • m' := by
  choose m' hm' using fun i ↦ Z4.exists_two_mul_of_red (ρF_eq_zero β h i)
  exact ⟨m', funext fun i ↦ hm' i⟩

theorem ann_ρF {m : ι → ZMod 4} (h : (2 : ZMod 4) • m = 0) : ρF β m = 0 := by
  rw [ρF_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [(Z4.two_mul_eq_zero_iff _).1 this, zero_smul]

/-! ### Twice and half on the free lift -/

/-- Twice a lift: `v ↦ 2ṽ`. -/
def twF : M →+ (ι → ZMod 4) where
  toFun v i := Z4.tw (β.repr v i)
  map_zero' := by funext i; simp
  map_add' v w := by funext i; simp

theorem twF_apply (v : M) (i : ι) : twF β v i = Z4.tw (β.repr v i) := rfl

theorem twF_eq (v : M) : twF β v = (2 : ZMod 4) • lv β v := by
  funext i; rfl

theorem ρF_twF (v : M) : ρF β (twF β v) = 0 := by
  rw [ρF_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [twF_apply, Z4.tw_apply, map_mul, Z4.red_two, zero_mul, zero_smul]

theorem twF_ρF (m : ι → ZMod 4) : twF β (ρF β m) = (2 : ZMod 4) • m := by
  funext i
  rw [twF_apply, ρF_eq_equivFun, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
    Z4.tw_red]
  rfl

theorem twF_smul (a : ZMod 4) (v : M) : twF β (Z4.red a • v) = a • twF β v := by
  funext i
  show Z4.tw (β.repr (Z4.red a • v) i) = a * Z4.tw (β.repr v i)
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Z4.tw_apply, Z4.tw_apply, ← mul_assoc,
    mul_comm a, mul_assoc]
  exact Z4.two_mul_eq_of_red (by simp [Z4.lift])

theorem twF_injective : Function.Injective (twF β) := by
  intro v w h
  have : ∀ i, β.repr v i = β.repr w i := fun i ↦ Z4.tw_injective (congrFun h i)
  exact β.repr.injective (Finsupp.ext this)

/-- Half on the kernel of the reduction. -/
def halfF (m : ι → ZMod 4) : M := β.equivFun.symm fun i ↦ Z4.red (ScalarMeshCategory.half (m i))

theorem twF_halfF {m : ι → ZMod 4} (h : ρF β m = 0) : twF β (halfF β m) = m := by
  funext i
  rw [twF_apply, halfF, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
    Z4.tw_red]
  exact ScalarMeshCategory.two_mul_half (ρF_eq_zero β h i)

theorem halfF_eq {m : ι → ZMod 4} {v : M} (h : twF β v = m) : halfF β m = v :=
  twF_injective β (by rw [twF_halfF β (by rw [← h, ρF_twF]), h])

theorem halfF_add {m n : ι → ZMod 4} (hm : ρF β m = 0) (hn : ρF β n = 0) :
    halfF β (m + n) = halfF β m + halfF β n :=
  halfF_eq β (by rw [map_add, twF_halfF β hm, twF_halfF β hn])

theorem halfF_sub {m n : ι → ZMod 4} (hm : ρF β m = 0) (hn : ρF β n = 0) :
    halfF β (m - n) = halfF β m - halfF β n :=
  halfF_eq β (by rw [map_sub, twF_halfF β hm, twF_halfF β hn])

theorem halfF_smul (a : ZMod 4) {m : ι → ZMod 4} (hm : ρF β m = 0) :
    halfF β (a • m) = Z4.red a • halfF β m :=
  halfF_eq β (by rw [twF_smul, twF_halfF β hm])

theorem halfF_two_smul (m : ι → ZMod 4) : halfF β ((2 : ZMod 4) • m) = ρF β m :=
  halfF_eq β (twF_ρF β m)

end Free

/-! ### The lifted action -/

section Act

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (β : Module.Basis ι 𝔽₂ M) (dβ : ι → ℤ) {MM : GMod GΛ M}
  {κ : Type*} [Fintype κ] (bΛ : Module.Basis κ (ZMod 4) Λ')

variable (MM π) in
/-- **The arbitrary lift of the action matrices**, through the bases. -/
def act0 : (ι → ZMod 4) →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] (ι → ZMod 4) :=
  (Pi.basisFun (ZMod 4) ι).constr (ZMod 4) fun i ↦
    bΛ.constr (ZMod 4) fun κ ↦ lv β (MM.act (β i) (π (bΛ κ)))

theorem act0_single (i : ι) (κ' : κ) :
    act0 (π := π) (MM := MM) β bΛ (Pi.single i 1) (bΛ κ') = lv β (MM.act (β i) (π (bΛ κ'))) := by
  rw [act0, ← Pi.basisFun_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]

theorem act0_apply (m : ι → ZMod 4) (b : Λ') :
    act0 (π := π) (MM := MM) β bΛ m b =
      ∑ i, ∑ κ', (m i * bΛ.repr b κ') • lv β (MM.act (β i) (π (bΛ κ'))) := by
  conv_lhs => rw [← (Pi.basisFun (ZMod 4) ι).sum_repr m, ← bΛ.sum_repr b]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Pi.basisFun_apply,
    Pi.basisFun_repr, act0_single, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ' _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm]

variable (hπ : IsRed GΛ' GΛ π)

include hπ in
theorem π_eq_sum (b : Λ') : π b = ∑ κ', Z4.red (bΛ.repr b κ') • π (bΛ κ') := by
  conv_lhs => rw [← bΛ.sum_repr b]
  rw [map_sum]
  exact Finset.sum_congr rfl fun κ' _ ↦ hπ.smul _ _

include hπ in
theorem ρF_act0 (m : ι → ZMod 4) (b : Λ') :
    ρF β (act0 (π := π) (MM := MM) β bΛ m b) = MM.act (ρF β m) (π b) := by
  rw [act0_apply, map_sum, π_eq_sum bΛ hπ b, ρF_apply, map_sum]
  simp only [map_sum, ρF_smul, ρF_lv, map_mul, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun κ' _ ↦ ?_
  rw [mul_comm]

include hπ in
theorem act0_twF (v : M) (b : Λ') :
    act0 (π := π) (MM := MM) β bΛ (twF β v) b = twF β (MM.act v (π b)) := by
  rw [twF_eq β v, map_smul, LinearMap.smul_apply, ← twF_ρF β, ρF_act0 β bΛ hπ, ρF_lv]

include hπ in
theorem halfF_act0 {m : ι → ZMod 4} (hm : ρF β m = 0) (b : Λ') :
    halfF β (act0 (π := π) (MM := MM) β bΛ m b) = MM.act (halfF β m) (π b) :=
  halfF_eq β (by rw [← act0_twF β bΛ hπ, twF_halfF β hm])

variable (MM π) in
/-- The associativity defect of the arbitrary lift. -/
def defect (m : ι → ZMod 4) (a b : Λ') : ι → ZMod 4 :=
  act0 (π := π) (MM := MM) β bΛ (act0 (π := π) (MM := MM) β bΛ m a) b -
    act0 (π := π) (MM := MM) β bΛ m (a * b)

include hπ in
theorem ρF_defect (m : ι → ZMod 4) (a b : Λ') : ρF β (defect π β MM bΛ m a b) = 0 := by
  rw [defect, map_sub, ρF_act0 β bΛ hπ, ρF_act0 β bΛ hπ, ρF_act0 β bΛ hπ, MM.act_mul,
    ← map_mul π, sub_self]

include hπ in
/-- **The halved defect does not depend on the lifts.** -/
theorem halfF_defect_indep {m₁ m₂ : ι → ZMod 4} {a₁ a₂ b₁ b₂ : Λ'} (hm : ρF β m₁ = ρF β m₂)
    (ha : π a₁ = π a₂) (hb : π b₁ = π b₂) :
    halfF β (defect π β MM bΛ m₁ a₁ b₁) =
      halfF β (defect π β MM bΛ m₂ a₂ b₂) := by
  obtain ⟨x, hx⟩ := ker_ρF β (m := m₁ - m₂) (by rw [map_sub, hm, sub_self])
  obtain ⟨y, hy⟩ := hπ.ker (a₁ - a₂) (by rw [map_sub, ha, sub_self])
  obtain ⟨z, hz⟩ := hπ.ker (b₁ - b₂) (by rw [map_sub, hb, sub_self])
  rw [sub_eq_iff_eq_add] at hx hy hz
  rw [hx, hy, hz]
  set D := defect π β MM bΛ
  have e : D ((2 : ZMod 4) • x + m₂) ((2 : ZMod 4) • y + a₂) ((2 : ZMod 4) • z + b₂) =
      D m₂ a₂ b₂ + (2 : ZMod 4) • (D x ((2 : ZMod 4) • y + a₂) ((2 : ZMod 4) • z + b₂) +
        D m₂ y ((2 : ZMod 4) • z + b₂) + D m₂ a₂ z) := by
    simp only [D, defect, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, add_mul,
      mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
    abel
  have h2 : ∀ w : ι → ZMod 4, ρF β ((2 : ZMod 4) • w) = 0 := fun w ↦ by
    rw [ρF_smul, Z4.red_two,
      zero_smul]
  rw [e, halfF_add β (ρF_defect β bΛ hπ _ _ _) (h2 _), halfF_two_smul, map_add, map_add,
    ρF_defect β bΛ hπ, ρF_defect β bΛ hπ, ρF_defect β bΛ hπ, add_zero, add_zero, add_zero]


theorem defect_add_left (m n : ι → ZMod 4) (a b : Λ') :
    defect π β MM bΛ (m + n) a b = defect π β MM bΛ m a b + defect π β MM bΛ n a b := by
  simp only [defect, map_add, LinearMap.add_apply]; abel

theorem defect_smul_left (c : ZMod 4) (m : ι → ZMod 4) (a b : Λ') :
    defect π β MM bΛ (c • m) a b = c • defect π β MM bΛ m a b := by
  simp only [defect, map_smul, LinearMap.smul_apply, smul_sub]

theorem defect_add_mid (m : ι → ZMod 4) (a a' b : Λ') :
    defect π β MM bΛ m (a + a') b = defect π β MM bΛ m a b + defect π β MM bΛ m a' b := by
  simp only [defect, map_add, LinearMap.add_apply, add_mul]; abel

theorem defect_smul_mid (c : ZMod 4) (m : ι → ZMod 4) (a b : Λ') :
    defect π β MM bΛ m (c • a) b = c • defect π β MM bΛ m a b := by
  simp only [defect, map_smul, LinearMap.smul_apply, smul_mul_assoc, smul_sub]

theorem defect_add_right (m : ι → ZMod 4) (a b b' : Λ') :
    defect π β MM bΛ m a (b + b') = defect π β MM bΛ m a b + defect π β MM bΛ m a b' := by
  simp only [defect, map_add, mul_add]; abel

theorem defect_smul_right (c : ZMod 4) (m : ι → ZMod 4) (a b : Λ') :
    defect π β MM bΛ m a (c • b) = c • defect π β MM bΛ m a b := by
  simp only [defect, map_smul, mul_smul_comm, smul_sub]

/-- The halved defect as a `𝔽₂`-linear map. -/
def cbar (a b : Λ) : M →ₗ[𝔽₂] M where
  toFun v := halfF β (defect π β MM bΛ (lv β v) (Classical.choose (hπ.surj a))
    (Classical.choose (hπ.surj b)))
  map_add' v w := by
    rw [← halfF_add β (ρF_defect β bΛ hπ _ _ _) (ρF_defect β bΛ hπ _ _ _), ← defect_add_left]
    exact halfF_defect_indep β bΛ hπ (by rw [map_add, ρF_lv, ρF_lv, ρF_lv]) rfl rfl
  map_smul' c v := by
    rw [RingHom.id_apply, ← Z4.red_lift c, ← halfF_smul β _ (ρF_defect β bΛ hπ _ _ _),
      ← defect_smul_left]
    exact halfF_defect_indep β bΛ hπ (by rw [ρF_smul, ρF_lv, ρF_lv, Z4.red_lift]) rfl rfl

theorem cbar_spec (m : ι → ZMod 4) (a b : Λ') :
    cbar (MM := MM) β bΛ hπ (π a) (π b) (ρF β m) = halfF β (defect π β MM bΛ m a b) :=
  halfF_defect_indep β bΛ hπ (ρF_lv β _) (Classical.choose_spec (hπ.surj _))
    (Classical.choose_spec (hπ.surj _))

theorem cbar_add_left (a a' b : Λ) :
    cbar (MM := MM) β bΛ hπ (a + a') b = cbar (MM := MM) β bΛ hπ a b + cbar (MM := MM) β bΛ hπ a' b := by
  ext v
  obtain ⟨x, rfl⟩ := hπ.surj a
  obtain ⟨x', rfl⟩ := hπ.surj a'
  obtain ⟨y, rfl⟩ := hπ.surj b
  rw [← ρF_lv β v, LinearMap.add_apply, ← map_add, cbar_spec, cbar_spec, cbar_spec, defect_add_mid,
    halfF_add β (ρF_defect β bΛ hπ _ _ _) (ρF_defect β bΛ hπ _ _ _)]

theorem cbar_smul_left (c : 𝔽₂) (a b : Λ) :
    cbar (MM := MM) β bΛ hπ (c • a) b = c • cbar (MM := MM) β bΛ hπ a b := by
  ext v
  obtain ⟨x, rfl⟩ := hπ.surj a
  obtain ⟨y, rfl⟩ := hπ.surj b
  rw [← ρF_lv β v, LinearMap.smul_apply, ← Z4.red_lift c, ← hπ.smul, cbar_spec, cbar_spec,
    defect_smul_mid, halfF_smul β _ (ρF_defect β bΛ hπ _ _ _)]

theorem cbar_add_right (a b b' : Λ) :
    cbar (MM := MM) β bΛ hπ a (b + b') = cbar (MM := MM) β bΛ hπ a b + cbar (MM := MM) β bΛ hπ a b' := by
  ext v
  obtain ⟨x, rfl⟩ := hπ.surj a
  obtain ⟨y, rfl⟩ := hπ.surj b
  obtain ⟨y', rfl⟩ := hπ.surj b'
  rw [← ρF_lv β v, LinearMap.add_apply, ← map_add, cbar_spec, cbar_spec, cbar_spec,
    defect_add_right, halfF_add β (ρF_defect β bΛ hπ _ _ _) (ρF_defect β bΛ hπ _ _ _)]

theorem cbar_smul_right (c : 𝔽₂) (a b : Λ) :
    cbar (MM := MM) β bΛ hπ a (c • b) = c • cbar (MM := MM) β bΛ hπ a b := by
  ext v
  obtain ⟨x, rfl⟩ := hπ.surj a
  obtain ⟨y, rfl⟩ := hπ.surj b
  rw [← ρF_lv β v, LinearMap.smul_apply, ← Z4.red_lift c, ← hπ.smul, cbar_spec, cbar_spec,
    defect_smul_right, halfF_smul β _ (ρF_defect β bΛ hπ _ _ _)]

/-- The (negated) halved defect as a bar two-cochain. -/
def cochainF : Bar.Cochain Λ (M →ₗ[𝔽₂] M) := fun a ↦ -cbar (MM := MM) β bΛ hπ (a 0) (a 1)

include hπ in
theorem defect_pentagon (m : ι → ZMod 4) (a₀ a₁ a₂ : Λ') :
    defect π β MM bΛ (act0 (π := π) (MM := MM) β bΛ m a₀) a₁ a₂ - defect π β MM bΛ m (a₀ * a₁) a₂ +
      defect π β MM bΛ m a₀ (a₁ * a₂) - act0 (π := π) (MM := MM) β bΛ (defect π β MM bΛ m a₀ a₁) a₂ = 0 := by
  simp only [defect, map_sub, LinearMap.sub_apply, mul_assoc]
  abel

variable (dΛ : κ → ℤ) (hbΛ : ∀ κ', GΛ'.gr.IsHom (dΛ κ') (bΛ κ'))
  (hβ : ∀ i, MM.gr.IsHom (dβ i) (β i))

include hbΛ in
theorem reprΛ_eq_zero {q : ℤ} {b : Λ'} (hb : GΛ'.gr.IsHom q b) {κ' : κ} (h : dΛ κ' ≠ q) :
    bΛ.repr b κ' = 0 := by
  classical
  have key : b = bΛ.equivFun.symm (fun j ↦ if dΛ j = q then bΛ.repr b j else 0) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← hb, ← bΛ.sum_repr b, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, GΛ'.gr.proj_of_isHom (hbΛ j)]
    split_ifs <;> simp
  have := congrArg (fun z ↦ bΛ.equivFun z κ') key
  simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at this
  rw [this, if_neg h]

include hπ hbΛ hβ in
theorem act0_isHom {p q : ℤ} {m : ι → ZMod 4} {b : Λ'} (hm : (grF dβ).IsHom p m)
    (hb : GΛ'.gr.IsHom q b) : (grF dβ).IsHom (p + q) (act0 (π := π) (MM := MM) β bΛ m b) := by
  rw [act0_apply]
  refine (grF dβ).isHom_sum _ _ fun i _ ↦ (grF dβ).isHom_sum _ _ fun κ' _ ↦ ?_
  by_cases hi : dβ i = p
  · by_cases hκ : dΛ κ' = q
    · refine (grF dβ).isHom_smul _ (lv_isHom β dβ hβ ?_)
      rw [← hi, ← hκ]
      exact MM.act_hom _ _ _ _ (hβ i) (hπ.deg _ _ (hbΛ κ'))
    · rw [reprΛ_eq_zero bΛ dΛ hbΛ hb hκ, mul_zero, zero_smul]; exact (grF dβ).isHom_zero _
  · rw [(grF_isHom dβ).1 hm i hi, zero_mul, zero_smul]; exact (grF dβ).isHom_zero _

include hπ hbΛ hβ in
theorem defect_isHom {p q r : ℤ} {m : ι → ZMod 4} {a b : Λ'} (hm : (grF dβ).IsHom p m)
    (ha : GΛ'.gr.IsHom q a) (hb : GΛ'.gr.IsHom r b) :
    (grF dβ).IsHom (p + q + r) (defect π β MM bΛ m a b) := by
  rw [defect, sub_eq_add_neg]
  refine (grF dβ).isHom_add (act0_isHom β dβ bΛ hπ dΛ hbΛ hβ
    (act0_isHom β dβ bΛ hπ dΛ hbΛ hβ hm ha) hb) ((grF dβ).isHom_neg ?_)
  rw [add_assoc]
  exact act0_isHom β dβ bΛ hπ dΛ hbΛ hβ hm (GΛ'.mul_hom _ _ _ _ ha hb)

include hβ in
theorem halfF_isHom {p : ℤ} {m : ι → ZMod 4} (hm : (grF dβ).IsHom p m) (h0 : ρF β m = 0) :
    MM.gr.IsHom p (halfF β m) := by
  rw [halfF, Module.Basis.equivFun_symm_apply]
  refine MM.gr.isHom_sum _ _ fun i _ ↦ ?_
  by_cases hi : dβ i = p
  · rw [← hi]; exact MM.gr.isHom_smul _ (hβ i)
  · rw [(grF_isHom dβ).1 hm i hi, show Z4.red (ScalarMeshCategory.half (0 : ZMod 4)) = 0 by decide,
      zero_smul]
    exact MM.gr.isHom_zero _

include hbΛ hβ in
theorem cochainF_good : Good MM MM 2 0 (cochainF (MM := MM) β bΛ hπ) where
  tr a := by simp [cochainF, Bar.tr]
  add a i x y hi := by
    interval_cases i <;> simp [cochainF, Function.update, cbar_add_left, cbar_add_right] <;> abel
  smul a i c x hi := by
    interval_cases i <;> simp [cochainF, Function.update, cbar_smul_left, cbar_smul_right]
  deg a ds p v ha hv := by
    simp only [cochainF, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero,
      LinearMap.neg_apply]
    refine MM.gr.isHom_neg ?_
    obtain ⟨m, hm, rfl⟩ : ∃ m, (grF dβ).IsHom p m ∧ ρF β m = v :=
      ⟨lv β v, lv_isHom β dβ hβ hv, ρF_lv β v⟩
    obtain ⟨x, hx, hx'⟩ := hπ.lift _ _ (ha 0 (by norm_num))
    obtain ⟨y, hy, hy'⟩ := hπ.lift _ _ (ha 1 (by norm_num))
    rw [← hx', ← hy', cbar_spec]
    have := halfF_isHom β dβ hβ (defect_isHom β dβ bΛ hπ dΛ hbΛ hβ hm hx hy)
      (ρF_defect β bΛ hπ _ _ _)
    rwa [add_assoc] at this

theorem cochainF_d : Bar.d (homAct MM MM) 2 (cochainF (MM := MM) β bΛ hπ) = 0 := by
  funext a
  ext v
  rw [Bar.d_two_apply]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, homAct_l, homAct_r, cochainF,
    LinearMap.neg_apply, Pi.zero_apply, LinearMap.zero_apply, map_neg]
  obtain ⟨m, rfl⟩ : ∃ m, ρF β m = v := ⟨lv β v, ρF_lv β v⟩
  obtain ⟨x₀, hx₀⟩ := hπ.surj (a 0)
  obtain ⟨x₁, hx₁⟩ := hπ.surj (a 1)
  obtain ⟨x₂, hx₂⟩ := hπ.surj (a 2)
  have e1 : (Bar.sh a) 0 = π x₁ := by simp [Bar.sh, hx₁]
  have e2 : (Bar.sh a) 1 = π x₂ := by simp [Bar.sh, hx₂]
  have e3 : (Bar.ct 0 a) 0 = π (x₀ * x₁) := by simp [Bar.ct, hx₀, hx₁]
  have e4 : (Bar.ct 0 a) 1 = π x₂ := by simp [Bar.ct, hx₂]
  have e5 : (Bar.ct 1 a) 0 = π x₀ := by simp [Bar.ct, hx₀]
  have e6 : (Bar.ct 1 a) 1 = π (x₁ * x₂) := by simp [Bar.ct, hx₁, hx₂]
  have e7 : (Bar.tr 2 a) 0 = π x₀ := by simp [Bar.tr, hx₀]
  have e8 : (Bar.tr 2 a) 1 = π x₁ := by simp [Bar.tr, hx₁]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, ← hx₀, ← hx₂, ← ρF_act0 β bΛ hπ, cbar_spec, cbar_spec,
    cbar_spec, cbar_spec, ← halfF_act0 β bΛ hπ (ρF_defect β bΛ hπ _ _ _)]
  have hP := defect_pentagon (MM := MM) β bΛ hπ m x₀ x₁ x₂
  have h := congrArg (halfF β) hP
  have r0 := ρF_defect (MM := MM) β bΛ hπ
  rw [halfF_sub β (by rw [map_add, map_sub, r0, r0, r0]; simp)
      (by rw [ρF_act0 β bΛ hπ, r0, map_zero, LinearMap.zero_apply]),
    halfF_add β (by rw [map_sub, r0, r0, sub_self]) (r0 _ _ _),
    halfF_sub β (r0 _ _ _) (r0 _ _ _), halfF_eq β (v := 0) (map_zero _)] at h
  rw [← neg_eq_zero, ← h]
  abel

/-! ### The corrected action -/

variable {β bΛ hπ} in
/-- The corrected action `m ⋆ b = m·b + 2·H(b̄)(m̄)`, for a cochain `H`. -/
def act1 (H : Bar.Cochain Λ (M →ₗ[𝔽₂] M)) (hH : Good MM MM 1 0 H) :
    (ι → ZMod 4) →ₗ[ZMod 4] Λ' →ₗ[ZMod 4] (ι → ZMod 4) :=
  act0 (π := π) (MM := MM) β bΛ + LinearMap.mk₂ (ZMod 4)
    (fun m b ↦ twF β (H (single (π b)) (ρF β m)))
    (fun m m' b ↦ by rw [map_add, map_add, map_add])
    (fun c m b ↦ by rw [ρF_smul, map_smul, twF_smul])
    (fun m b b' ↦ by rw [map_add, hH.single_add, LinearMap.add_apply, map_add])
    (fun c m b ↦ by rw [hπ.smul, hH.single_smul, LinearMap.smul_apply, twF_smul])

theorem act1_apply (H : Bar.Cochain Λ (M →ₗ[𝔽₂] M)) (hH : Good MM MM 1 0 H) (m : ι → ZMod 4)
    (b : Λ') : act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH m b =
      act0 (π := π) (MM := MM) β bΛ m b + twF β (H (single (π b)) (ρF β m)) := rfl

theorem ρF_act1 (H : Bar.Cochain Λ (M →ₗ[𝔽₂] M)) (hH : Good MM MM 1 0 H) (m : ι → ZMod 4)
    (b : Λ') : ρF β (act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH m b) = MM.act (ρF β m) (π b) := by
  rw [act1_apply, map_add, ρF_act0 β bΛ hπ, ρF_twF, add_zero]

/-- **The corrected action is associative** when `dH` is the negated halved defect. -/
theorem act1_assoc (H : Bar.Cochain Λ (M →ₗ[𝔽₂] M)) (hH : Good MM MM 1 0 H)
    (hdH : Bar.d (homAct MM MM) 1 H = cochainF (MM := MM) β bΛ hπ) (m : ι → ZMod 4) (a b : Λ') :
    act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH (act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH m a) b =
      act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH m (a * b) := by
  -- the cochain equation
  have hE : ∀ (v : M) (x y : Λ), H (single y) (MM.act v x) - H (single (x * y)) v +
      MM.act (H (single x) v) y = -cbar (MM := MM) β bΛ hπ x y v := by
    intro v x y
    have h := congrArg (fun G : Bar.Cochain Λ (M →ₗ[𝔽₂] M) ↦ G (Bar.cons x (single y)) v) hdH
    simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l,
      homAct_r, cochainF, LinearMap.neg_apply] at h
    rw [hH.one_eq (Bar.sh _), hH.one_eq (Bar.ct 0 _), hH.one_eq (Bar.tr 1 _)] at h
    simpa [Bar.sh, Bar.ct, Bar.tr, Bar.cons, single] using h
  have hρa : ρF β (act0 (π := π) (MM := MM) β bΛ m a + twF β (H (single (π a)) (ρF β m))) =
      MM.act (ρF β m) (π a) := by rw [map_add, ρF_act0 β bΛ hπ, ρF_twF, add_zero]
  rw [act1_apply, act1_apply, act1_apply, map_add, LinearMap.add_apply, act0_twF β bΛ hπ,
    hρa, ← sub_eq_zero]
  have hD := cbar_spec (MM := MM) β bΛ hπ m a b
  have key := hE (ρF β m) (π a) (π b)
  rw [hD, ← map_mul π] at key
  have h2 := congrArg (twF β) key
  rw [map_add, map_sub, map_neg, twF_halfF β (ρF_defect β bΛ hπ _ _ _)] at h2
  calc _ = defect π β MM bΛ m a b +
        (twF β (H (single (π b)) (MM.act (ρF β m) (π a))) -
          twF β (H (single (π (a * b))) (ρF β m)) +
          twF β (MM.act (H (single (π a)) (ρF β m)) (π b))) := by
          rw [defect]; abel
    _ = 0 := by rw [h2]; abel

/-- **The action of one is the identity**: an idempotent congruent to the identity. -/
theorem act1_one (H : Bar.Cochain Λ (M →ₗ[𝔽₂] M)) (hH : Good MM MM 1 0 H)
    (hdH : Bar.d (homAct MM MM) 1 H = cochainF (MM := MM) β bΛ hπ) (m : ι → ZMod 4) :
    act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH m 1 = m := by
  set E := fun x ↦ act1 (β := β) (bΛ := bΛ) (hπ := hπ) H hH x 1
  have hEE : ∀ x, E (E x) = E x := fun x ↦ by
    simp only [E]; rw [act1_assoc β bΛ hπ H hH hdH, mul_one]
  have hρ : ∀ x, ρF β (E x - x) = 0 := fun x ↦ by
    simp only [E]; rw [map_sub, ρF_act1, map_one, MM.act_one, sub_self]
  obtain ⟨y, hy⟩ := ker_ρF β (hρ m)
  obtain ⟨z, hz⟩ := ker_ρF β (hρ y)
  have hlin : ∀ x x', E (x + x') = E x + E x' := fun x x' ↦ by simp [E, map_add]
  have hsm : ∀ x, E ((2 : ZMod 4) • x) = (2 : ZMod 4) • E x := fun x ↦ by simp [E, map_smul]
  have h1 : E m = m + (2 : ZMod 4) • y := by rw [← hy]; abel
  have h2 : E y = y + (2 : ZMod 4) • z := by rw [← hz]; abel
  have := hEE m
  rw [h1, hlin, hsm, h2, h1, smul_add, smul_smul, Z4.four_eq_zero, zero_smul, add_zero] at this
  have h3 : (2 : ZMod 4) • y = 0 := by
    have := congrArg (· - (m + (2 : ZMod 4) • y)) this
    simp only [sub_self] at this
    rw [← this]; abel
  show E m = m
  rw [h1, h3, add_zero]

include hπ hbΛ hβ in
/-- **Proposition 10.1, the module lifts**: a graded `Λ`-module with a homogeneous basis and
`Ext²_0(M, M) = 0` lifts to a graded `Λ̃`-module structure on `ι → ℤ/4`. -/
theorem exists_liftMod (hExt : ExtVanish MM MM 1 0) :
    ∃ MM' : GMod GΛ' (ι → ZMod 4), IsLift MM' MM π (ρF β) ∧ MM'.gr = grF dβ := by
  obtain ⟨H, hH, hdH⟩ := hExt _ (cochainF_good β dβ bΛ hπ dΛ hbΛ hβ) (cochainF_d β bΛ hπ)
  have hTw : ∀ {r : ℤ} {v : M}, MM.gr.IsHom r v → (grF dβ).IsHom r (twF β v) := fun hv ↦ by
    rw [twF_eq]; exact (grF dβ).isHom_smul _ (lv_isHom β dβ hβ hv)
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
              simpa using this }, ?_, rfl⟩
  exact { smul := ρF_smul β
          act := fun m b ↦ ρF_act1 β bΛ hπ H hH m b
          deg := fun p m hm ↦ ρF_isHom β dβ hβ hm
          lift := fun p m hm ↦ ⟨lv β m, lv_isHom β dβ hβ hm, ρF_lv β m⟩
          ker := fun m h ↦ ker_ρF β h
          ann := fun m h ↦ ann_ρF β h }

end Act

end WLift

end MultiplicativeBasisDeformations
