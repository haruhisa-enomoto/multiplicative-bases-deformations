import MultiplicativeBasisDeformations.Foundations.LinCorners
import MultiplicativeBasisDeformations.Foundations.RayBasis
import MultiplicativeBasisDeformations.Foundations.A0Normed
import MultiplicativeBasisDeformations.Foundations.RayStandard

/-!
# Rays of the fibres of the zero-product family

Proposition 11.3(3) (`binary-families.tex:156–186`), in the form used by Proposition 7.9:
let `B` be an algebra with a linear isomorphism `Ψ : kP → B` carrying a fibre product
`m_c = m + Σ c_z ε_z` to the product of `B`. "Corrections involve only generating nonlocal
inputs. Products with local basis vectors […] are unchanged. Thus the local rings and both
endpoint actions are the same as in `A₀`, and the basis vectors represent exactly the same
endpoint-unit orbits." Hence the images `Ψ b_e` are a complete set of primitive
orthogonal idempotents of `B`, and the images `Ψ b_r` are a ray transversal. When the
coefficients are zero or one, products of these vectors are basis vectors or zero, and by
Corollary 3.3 the transversal is a normed multiplicative basis.

Deviation: the fibre is not formed as a separate algebra; everything is read in `B` through
`Ψ`, which is how Proposition 7.9 uses it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  (hfin : IsRepresentationFinite k (S.P.Lin k)) (c : R → R → k)

local notation:max "⌜" r "⌝" => Sys.rr S r

/-! ### Corrections vanish on local inputs -/

include hfin in
theorem coch_b_local_left {l : R} (hl : S.P.src l = S.P.tgt l) (z : S.P.Lin k) :
    S.coch k c (S.P.b k l) z = 0 := by
  have : S.coch k c (S.P.b k l) = 0 := (S.P.basis k).ext fun v ↦ by
    rw [Mult.basis_apply, coch_b, S.eps_local_left k hfin hl, vecM_zero, smul_zero,
      LinearMap.zero_apply]
  rw [this, LinearMap.zero_apply]

include hfin in
theorem coch_local_left {x : V} {a : S.P.Lin k} (ha : a ∈ S.P.corSp k x x) (z : S.P.Lin k) :
    S.coch k c a z = 0 := by
  induction ha using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, ⟨l1, l2⟩, rfl⟩ := hw
    rw [Mult.basis_apply]; exact S.coch_b_local_left k hfin c (l1.trans l2.symm) z
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add w w' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul t w _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]

include hfin in
theorem coch_b_local_right {l : R} (hl : S.P.src l = S.P.tgt l) (a : S.P.Lin k) :
    S.coch k c a (S.P.b k l) = 0 := by
  have : (S.coch k c).flip (S.P.b k l) = 0 := (S.P.basis k).ext fun v ↦ by
    rw [LinearMap.flip_apply, Mult.basis_apply, coch_b, S.eps_local_right k hfin v hl, vecM_zero,
      smul_zero, LinearMap.zero_apply]
  rw [← LinearMap.flip_apply, this, LinearMap.zero_apply]

include hfin in
theorem coch_local_right {y : V} {z : S.P.Lin k} (hz : z ∈ S.P.corSp k y y) (a : S.P.Lin k) :
    S.coch k c a z = 0 := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, ⟨l1, l2⟩, rfl⟩ := hw
    rw [Mult.basis_apply]; exact S.coch_b_local_right k hfin c (l1.trans l2.symm) a
  | zero => rw [map_zero]
  | add w w' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
  | smul t w _ h => rw [map_smul, h, smul_zero]

/-! ### The transported structure -/

variable {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B] (Ψ : S.P.Lin k ≃ₗ[k] B)
  (hΨ : ∀ a z, Ψ (a * z + S.coch k c a z) = Ψ a * Ψ z)

include hfin hΨ in
theorem Ψ_mul_left {x : V} {a : S.P.Lin k} (ha : a ∈ S.P.corSp k x x) (z : S.P.Lin k) :
    Ψ a * Ψ z = Ψ (a * z) := by
  rw [← hΨ, S.coch_local_left k hfin c ha, add_zero]

include hfin hΨ in
theorem Ψ_mul_right {y : V} {z : S.P.Lin k} (hz : z ∈ S.P.corSp k y y) (a : S.P.Lin k) :
    Ψ a * Ψ z = Ψ (a * z) := by
  rw [← hΨ, S.coch_local_right k hfin c hz, add_zero]

theorem e_mem_corSp (x : V) : S.P.b k (S.P.e x) ∈ S.P.corSp k x x :=
  S.P.b_mem_corSp' k (S.P.src_e x) (S.P.tgt_e x)

include hfin hΨ in
theorem Ψ_one : Ψ 1 = 1 := by
  have h : ∀ z, Ψ 1 * Ψ z = Ψ z := by
    intro z
    rw [← hΨ, one_mul, ← Mult.sum_b_e, map_sum, LinearMap.sum_apply,
      Finset.sum_eq_zero fun x _ ↦ S.coch_local_left k hfin c (S.e_mem_corSp k x) z, add_zero]
  have := h (Ψ.symm 1)
  rwa [Ψ.apply_symm_apply, mul_one] at this

/-- The transported identity vectors. -/
def Eb (x : V) : B := Ψ (S.P.b k (S.P.e x))

include hfin hΨ in
theorem Eb_complete : CompleteOrthogonalIdempotents (S.Eb k Ψ) := by
  have hmul : ∀ x y, S.Eb k Ψ x * S.Eb k Ψ y = if x = y then S.Eb k Ψ x else 0 := by
    intro x y
    rw [Eb, Eb, S.Ψ_mul_left k hfin c Ψ hΨ (S.e_mem_corSp k x), Mult.b_e_mul, S.P.src_e]
    split_ifs with h
    · subst h; rfl
    · exact map_zero Ψ
  refine ⟨⟨fun x ↦ ?_, fun x y hxy ↦ ?_⟩, ?_⟩
  · change _ * _ = _; rw [hmul, if_pos rfl]
  · show S.Eb k Ψ x * S.Eb k Ψ y = 0
    rw [hmul, if_neg hxy]
  · rw [← S.Ψ_one k hfin c Ψ hΨ, ← Mult.sum_b_e, map_sum]; rfl

include hfin hΨ in
/-- The corner of `B` at `x, y` is the image of the corner of `kP`. -/
theorem Eb_mul_mul_Eb (x y : V) (a : S.P.Lin k) :
    S.Eb k Ψ x * Ψ a * S.Eb k Ψ y = Ψ (S.P.b k (S.P.e x) * a * S.P.b k (S.P.e y)) := by
  rw [Eb, Eb, S.Ψ_mul_left k hfin c Ψ hΨ (S.e_mem_corSp k x),
    S.Ψ_mul_right k hfin c Ψ hΨ (S.e_mem_corSp k y)]

include hfin hΨ in
theorem Eb_primitive (x : V) : IsPrimitiveIdempotent (S.Eb k Ψ x) := by
  have hc := S.Eb_complete k hfin c Ψ hΨ
  refine ⟨hc.idem x, fun h ↦ S.P.b_ne_zero k (S.P.e x) (Ψ.injective (by rw [map_zero]; exact h)),
    fun f hf h1 h2 ↦ ?_⟩
  set a := Ψ.symm f
  have hf' : f = Ψ a := (Ψ.apply_symm_apply f).symm
  have hacorner : a ∈ S.P.corSp k x x := by
    have e1 : S.Eb k Ψ x * f * S.Eb k Ψ x = f := by rw [h1, h2]
    rw [hf', S.Eb_mul_mul_Eb k hfin c Ψ hΨ] at e1
    rw [← Ψ.injective e1]
    exact S.P.e_mul_mul_e_mem k x x a
  have haa : a * a = a := by
    apply Ψ.injective
    rw [← S.Ψ_mul_left k hfin c Ψ hΨ hacorner, ← hf']
    exact hf.eq
  rcases S.P.idem_local k hacorner haa with h | h
  · left; rw [hf', h, map_zero]
  · right; rw [hf', h]; rfl

include hfin hΨ in
/-- **The transported identities are a complete set of primitive orthogonal idempotents.** -/
def fibreIdem : PrimitiveIdempotents B where
  m := Fintype.card V
  e i := S.Eb k Ψ ((Fintype.equivFin V).symm i)
  complete := (CompleteOrthogonalIdempotents.equiv (Fintype.equivFin V).symm).2
    (S.Eb_complete k hfin c Ψ hΨ)
  primitive i := S.Eb_primitive k hfin c Ψ hΨ _

include hfin hΨ in
/-- Vertices as indices of the transported idempotents. -/
def fibreIdx : V ≃ Fin (S.fibreIdem k hfin c Ψ hΨ).m := Fintype.equivFin V

local notation "σV" => S.fibreIdx k hfin c Ψ hΨ

include hfin hΨ in
theorem fibre_e (i : Fin (S.fibreIdem k hfin c Ψ hΨ).m) :
    (S.fibreIdem k hfin c Ψ hΨ).e i = Ψ (S.P.b k (S.P.e ((σV).symm i))) := rfl

include hfin hΨ in
theorem fibre_e' (x : V) : (S.fibreIdem k hfin c Ψ hΨ).e (σV x) = Ψ (S.P.b k (S.P.e x)) := by
  rw [fibre_e, Equiv.symm_apply_apply]

include hfin hΨ in
theorem fibre_mem_corner_iff {i j : Fin (S.fibreIdem k hfin c Ψ hΨ).m} {z : B} :
    z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) i j ↔
      Ψ.symm z ∈ S.P.corSp k ((σV).symm i) ((σV).symm j) := by
  rw [PrimitiveIdempotents.mem_corner_iff', fibre_e, fibre_e]
  have e := S.Eb_mul_mul_Eb k hfin c Ψ hΨ ((σV).symm i) ((σV).symm j) (Ψ.symm z)
  rw [Ψ.apply_symm_apply] at e
  unfold Eb at e
  rw [e]
  constructor
  · intro h
    have h' := congrArg Ψ.symm h
    rw [Ψ.symm_apply_apply] at h'
    rw [← h']
    exact S.P.e_mul_mul_e_mem k _ _ _
  · intro h
    rw [S.P.e_mul_of_mem_corSp k h, S.P.mul_e_of_mem_corSp k h, Ψ.apply_symm_apply]

include hfin hΨ in
theorem fibre_isCornerUnit_iff {i : Fin (S.fibreIdem k hfin c Ψ hΨ).m} {u : B} :
    (S.fibreIdem k hfin c Ψ hΨ).IsCornerUnit (k := k) i u ↔
      S.P.IsLocUnit k ((σV).symm i) (Ψ.symm u) := by
  constructor
  · rintro ⟨hu, u', hu', h1, h2⟩
    rw [S.fibre_mem_corner_iff] at hu hu'
    refine ⟨hu, Ψ.symm u', hu', ?_, ?_⟩
    · apply Ψ.injective
      rw [← S.Ψ_mul_left k hfin c Ψ hΨ hu, Ψ.apply_symm_apply, Ψ.apply_symm_apply, h1]; rfl
    · apply Ψ.injective
      rw [← S.Ψ_mul_left k hfin c Ψ hΨ hu', Ψ.apply_symm_apply, Ψ.apply_symm_apply, h2]; rfl
  · rintro ⟨hu, u', hu', h1, h2⟩
    refine ⟨(S.fibre_mem_corner_iff k hfin c Ψ hΨ).2 hu, Ψ u',
      (S.fibre_mem_corner_iff k hfin c Ψ hΨ).2 (by rwa [Ψ.symm_apply_apply]), ?_, ?_⟩
    · rw [← Ψ.apply_symm_apply u, S.Ψ_mul_left k hfin c Ψ hΨ hu, h1]; rfl
    · rw [← Ψ.apply_symm_apply u, S.Ψ_mul_left k hfin c Ψ hΨ hu', h2]; rfl

/-- The transported ray vectors. -/
def βv (r : R) : B := Ψ (S.P.b k r)

include hfin hΨ in
theorem βv_mem_corner (r : R) :
    S.βv k Ψ r ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) (σV (S.P.src r)) (σV (S.P.tgt r)) := by
  rw [S.fibre_mem_corner_iff, βv, Ψ.symm_apply_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  exact S.P.b_mem_corSp k r

theorem βv_ne_zero (r : R) : S.βv k Ψ r ≠ 0 := fun h ↦
  S.P.b_ne_zero k r (Ψ.injective (by rw [map_zero]; exact h))

include hfin hΨ in
/-- **Rays of the transported vectors are ordered by `U`.** -/
theorem inU_of_mem_ray {r s : R}
    (h : S.βv k Ψ r ∈ (S.fibreIdem k hfin c Ψ hΨ).ray (k := k) (σV (S.P.src s)) (σV (S.P.tgt s))
      (S.βv k Ψ s)) : S.InU r s := by
  obtain ⟨u, w, hu, hw, h⟩ := h
  rw [S.fibre_isCornerUnit_iff, Equiv.symm_apply_apply] at hu hw
  have e : S.βv k Ψ r = Ψ (Ψ.symm u * S.P.b k s * Ψ.symm w) := by
    rw [h, βv, ← S.Ψ_mul_right k hfin c Ψ hΨ hw.1, ← S.Ψ_mul_left k hfin c Ψ hΨ hu.1,
      Ψ.apply_symm_apply, Ψ.apply_symm_apply]
  have e' : S.P.b k r = Ψ.symm u * S.P.b k s * Ψ.symm w := Ψ.injective e
  apply S.inU_of_mem_USp k
  rw [e']
  exact S.mul_mem_USp k rfl rfl hu.1 hw.1

include hfin hΨ in
/-- **Every nonzero corner element of `B` lies in the ray of a transported vector.** -/
theorem exists_ray_βv {i j : Fin (S.fibreIdem k hfin c Ψ hΨ).m} {z : B}
    (hz : z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) i j) (hz0 : z ≠ 0) :
    ∃ r, σV (S.P.src r) = i ∧ σV (S.P.tgt r) = j ∧
      z ∈ (S.fibreIdem k hfin c Ψ hΨ).ray (k := k) i j (S.βv k Ψ r) := by
  rw [S.fibre_mem_corner_iff] at hz
  have hz0' : Ψ.symm z ≠ 0 := fun h ↦ hz0 (by rw [← Ψ.apply_symm_apply z, h, map_zero])
  obtain ⟨r, r1, r2, u, w, hu, hw, he⟩ := S.exists_unit_ray k hz hz0'
  refine ⟨r, by rw [r1, Equiv.apply_symm_apply], by rw [r2, Equiv.apply_symm_apply], Ψ u, Ψ w,
    (S.fibre_isCornerUnit_iff k hfin c Ψ hΨ).2 (by rwa [Ψ.symm_apply_apply]),
    (S.fibre_isCornerUnit_iff k hfin c Ψ hΨ).2 (by rwa [Ψ.symm_apply_apply]), ?_⟩
  rw [βv, S.Ψ_mul_left k hfin c Ψ hΨ hu.1, S.Ψ_mul_right k hfin c Ψ hΨ hw.1, ← he,
    Ψ.apply_symm_apply]

/-- The ray of a transported vector. -/
def fibreRay (r : R) : (S.fibreIdem k hfin c Ψ hΨ).NonzeroRay k :=
  ⟨(S.fibreIdem k hfin c Ψ hΨ).ray (k := k) (σV (S.P.src r)) (σV (S.P.tgt r)) (S.βv k Ψ r),
    σV (S.P.src r), σV (S.P.tgt r), S.βv k Ψ r, S.βv_mem_corner k hfin c Ψ hΨ r, S.βv_ne_zero k Ψ r,
    rfl⟩

theorem mem_fibreRay (r : R) : S.βv k Ψ r ∈ (S.fibreRay k hfin c Ψ hΨ r).1 :=
  PrimitiveIdempotents.mem_ray_self _ (S.βv_mem_corner k hfin c Ψ hΨ r)

/-- Two nonzero rays with a common element are equal. -/
theorem _root_.MultiplicativeBasisDeformations.PrimitiveIdempotents.nonzeroRay_eq_of_mem
    {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A] (F : PrimitiveIdempotents A) {ρ ρ' : F.NonzeroRay k} {g : A}
    (h : g ∈ ρ.1) (h' : g ∈ ρ'.1) : ρ = ρ' := by
  obtain ⟨x, y, f, hf, hf0, hρ⟩ := ρ.2
  obtain ⟨x', y', f', hf', hf0', hρ'⟩ := ρ'.2
  rw [hρ] at h
  rw [hρ'] at h'
  have hg := F.ray_subset_corner hf h
  have hg' := F.ray_subset_corner hf' h'
  obtain ⟨rfl, rfl⟩ := F.corner_unique hg hg' (F.ne_zero_of_mem_ray hf hf0 h)
  apply Subtype.ext
  rw [hρ, hρ', ← F.ray_eq_of_mem hf h, ← F.ray_eq_of_mem hf' h']

theorem fibreRay_injective : Function.Injective (S.fibreRay k hfin c Ψ hΨ) := by
  have key : ∀ r s, S.fibreRay k hfin c Ψ hΨ r = S.fibreRay k hfin c Ψ hΨ s → S.InU r s := by
    intro r s h
    have hr := S.mem_fibreRay k hfin c Ψ hΨ r
    rw [h] at hr
    exact S.inU_of_mem_ray k hfin c Ψ hΨ hr
  intro r s h
  exact S.inU_antisymm (key r s h) (key s r h.symm)

theorem fibreRay_surjective : Function.Surjective (S.fibreRay k hfin c Ψ hΨ) := by
  intro ρ
  obtain ⟨x, y, f, hf, hf0, hρ⟩ := ρ.2
  obtain ⟨r, r1, r2, hr⟩ := S.exists_ray_βv k hfin c Ψ hΨ hf hf0
  refine ⟨r, PrimitiveIdempotents.nonzeroRay_eq_of_mem k _ (S.mem_fibreRay k hfin c Ψ hΨ r) ?_⟩
  rw [hρ]
  have hc : S.βv k Ψ r ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) x y := by
    have := S.βv_mem_corner k hfin c Ψ hΨ r; rwa [r1, r2] at this
  rw [PrimitiveIdempotents.ray_eq_of_mem _ hc hr]
  exact PrimitiveIdempotents.mem_ray_self _ hc

/-- **Rays of `B` are the rays of `P`.** -/
def fibreRayEquiv : R ≃ (S.fibreIdem k hfin c Ψ hΨ).NonzeroRay k :=
  Equiv.ofBijective _ ⟨S.fibreRay_injective k hfin c Ψ hΨ, S.fibreRay_surjective k hfin c Ψ hΨ⟩

/-- The transported basis, indexed by the rays of `B`. -/
def fibreBasis : Module.Basis ((S.fibreIdem k hfin c Ψ hΨ).NonzeroRay k) k B :=
  ((S.P.basis k).map Ψ).reindex (S.fibreRayEquiv k hfin c Ψ hΨ)

theorem fibreBasis_apply (ρ : (S.fibreIdem k hfin c Ψ hΨ).NonzeroRay k) :
    S.fibreBasis k hfin c Ψ hΨ ρ = S.βv k Ψ ((S.fibreRayEquiv k hfin c Ψ hΨ).symm ρ) := by
  rw [fibreBasis, Module.Basis.reindex_apply, Module.Basis.map_apply, Mult.basis_apply]; rfl

theorem fibreBasis_ray (r : R) :
    S.fibreBasis k hfin c Ψ hΨ (S.fibreRayEquiv k hfin c Ψ hΨ r) = S.βv k Ψ r := by
  rw [fibreBasis_apply, Equiv.symm_apply_apply]

/-- **The transported basis is a ray transversal.** -/
theorem fibreBasis_isRayTransversal :
    (S.fibreIdem k hfin c Ψ hΨ).IsRayTransversal (S.fibreBasis k hfin c Ψ hΨ) := by
  refine ⟨fun ρ ↦ ?_, fun ρ i hi ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := (S.fibreRayEquiv k hfin c Ψ hΨ).surjective ρ
    rw [fibreBasis_ray]
    exact S.mem_fibreRay k hfin c Ψ hΨ r
  · obtain ⟨r, rfl⟩ := (S.fibreRayEquiv k hfin c Ψ hΨ).surjective ρ
    set x := (σV).symm i
    have hix : (S.fibreIdem k hfin c Ψ hΨ).e i = S.βv k Ψ (S.P.e x) := rfl
    have h1 := S.mem_fibreRay k hfin c Ψ hΨ (S.P.e x)
    rw [← hix] at h1
    have heq := PrimitiveIdempotents.nonzeroRay_eq_of_mem k _ hi h1
    have : r = S.P.e x := S.fibreRay_injective k hfin c Ψ hΨ heq
    rw [fibreBasis_ray, this, hix]

include hΨ in
/-- **Products of transported vectors at binary points are transported vectors or zero.** -/
theorem βv_mul_βv (hc01 : ∀ r s, c r s = 0 ∨ c r s = 1) (r s : R) :
    S.βv k Ψ r * S.βv k Ψ s = 0 ∨ ∃ t, S.βv k Ψ r * S.βv k Ψ s = S.βv k Ψ t := by
  rw [βv, βv, ← hΨ, coch_b, S.b_mul_b k]
  rcases S.rr_mul_rr_cases r s with h | ⟨t, ht⟩
  · rw [h, vecM_zero, zero_add, S.eps_of_mul_eq h]
    rcases hc01 r s with h0 | h1
    · left; rw [h0, zero_smul, map_zero]
    · rw [h1, one_smul]
      rcases S.stem_cases r s with h2 | ⟨t, ht⟩
      · left; rw [h2, vecM_zero, map_zero]
      · right; exact ⟨t, by rw [ht, vecM_rr]; rfl⟩
  · right
    refine ⟨t, ?_⟩
    rw [ht, vecM_rr, S.eps_of_mul_ne (by rw [ht]; exact S.rr_ne t), vecM_zero, smul_zero, add_zero]
    rfl

/-! ### Endpoint subbimodules of a fibre are spanned by rays

The endpoint actions of the fibre are those of `kP` (`Ψ_mul_left`, `Ψ_mul_right`), so an endpoint
subbimodule of `B` pulls back to one of `kP`, which is spanned by rays since `kP` is
representation-finite. No representation-finiteness of `B` is needed. -/

omit [IsAlgClosed k] in
theorem coch_zero_coef : S.coch k (0 : R → R → k) = 0 :=
  (S.P.basis k).ext fun u ↦ (S.P.basis k).ext fun v ↦ by
    rw [Mult.basis_apply, Mult.basis_apply, coch_b, Pi.zero_apply, Pi.zero_apply, zero_smul]; rfl

theorem hΨ₀ : ∀ a z : S.P.Lin k, (LinearEquiv.refl k (S.P.Lin k)) (a * z + S.coch k 0 a z) =
    (LinearEquiv.refl k (S.P.Lin k)) a * (LinearEquiv.refl k (S.P.Lin k)) z := fun a z ↦ by
  rw [coch_zero_coef]; simp

/-- `kP` with its identity vectors and rays, as the fibre at `0`. -/
abbrev idem₀ : PrimitiveIdempotents (S.P.Lin k) :=
  S.fibreIdem k hfin 0 (LinearEquiv.refl k (S.P.Lin k)) (S.hΨ₀ k)

local notation "σ₀" => S.fibreIdx k hfin 0 (LinearEquiv.refl k (S.P.Lin k)) (S.hΨ₀ k)

include hfin hΨ in
theorem fibre_mem_corner_iff₀ {x y : V} {z : S.P.Lin k} :
    Ψ z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) (σV x) (σV y) ↔
      z ∈ (S.idem₀ k hfin).corner (k := k) (σ₀ x) (σ₀ y) := by
  rw [S.fibre_mem_corner_iff, S.fibre_mem_corner_iff k hfin 0 _ (S.hΨ₀ k), Ψ.symm_apply_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rfl

include hfin hΨ in
/-- **Every endpoint subbimodule of a fibre is spanned by the transported rays it contains.** -/
theorem fibre_le_span {x y : V} {N : Submodule k B}
    (hN : (S.fibreIdem k hfin c Ψ hΨ).IsEndpointSubbimodule (σV x) (σV y) N) :
    N ≤ Submodule.span k (S.βv k Ψ '' {r | S.βv k Ψ r ∈ N}) := by
  classical
  set F₀ := S.idem₀ k hfin
  have hcorner : ∀ {z : S.P.Lin k} {x' y'}, z ∈ F₀.corner (k := k) (σ₀ x') (σ₀ y') →
      Ψ z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) (σV x') (σV y') := fun h ↦
    (S.fibre_mem_corner_iff₀ k hfin c Ψ hΨ).2 h
  have hcorner' : ∀ {z : B} {x' y'}, z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) (σV x') (σV y') →
      Ψ.symm z ∈ F₀.corner (k := k) (σ₀ x') (σ₀ y') := fun h ↦
    (S.fibre_mem_corner_iff₀ k hfin c Ψ hΨ).1 (by rwa [Ψ.apply_symm_apply])
  have hloc : ∀ {a : S.P.Lin k} {x'}, a ∈ F₀.corner (k := k) (σ₀ x') (σ₀ x') →
      a ∈ S.P.corSp k x' x' := fun {a x'} ha ↦ by
    have := (S.fibre_mem_corner_iff k hfin c Ψ hΨ).1 (hcorner ha)
    rwa [Ψ.symm_apply_apply, Equiv.symm_apply_apply] at this
  -- the pull-back is an endpoint subbimodule of `kP`
  have hN' : F₀.IsEndpointSubbimodule (σ₀ x) (σ₀ y) (N.comap Ψ.toLinearMap) := by
    refine ⟨fun z hz ↦ ?_, fun a ha z hz ↦ ?_, fun a ha z hz ↦ ?_⟩
    · have := hcorner' (hN.1 hz)
      rwa [LinearEquiv.coe_toLinearMap, Ψ.symm_apply_apply] at this
    · change Ψ (a * z) ∈ N
      rw [← S.Ψ_mul_left k hfin c Ψ hΨ (hloc ha)]
      exact hN.2.1 _ (hcorner ha) _ hz
    · change Ψ (z * a) ∈ N
      rw [← S.Ψ_mul_right k hfin c Ψ hΨ (hloc ha)]
      exact hN.2.2 _ (hcorner ha) _ hz
  have hb₀ := S.fibreBasis_isRayTransversal k hfin 0 _ (S.hΨ₀ k)
  intro n hn
  have h := F₀.le_span_transversal hb₀ hfin _ _ rfl hN' (show Ψ.symm n ∈ N.comap Ψ.toLinearMap by
    simpa using hn)
  have h2 := Submodule.mem_map_of_mem (f := Ψ.toLinearMap) h
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap, Ψ.apply_symm_apply] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
  obtain ⟨r, rfl⟩ := (S.fibreRayEquiv k hfin 0 _ (S.hΨ₀ k)).surjective ρ
  have e := S.fibreBasis_ray k hfin 0 _ (S.hΨ₀ k) r
  simp only [Set.mem_setOf_eq] at hρ
  rw [e] at hρ ⊢
  exact ⟨r, hρ, rfl⟩

/-- A radical power as a two-sided ideal. -/
def radPowIdeal {A : Type u} [Ring A] [Algebra k A] {n : ℕ} (hn : 1 ≤ n) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (algebraRadicalPow k A n) (zero_mem _) (fun hx hy ↦ add_mem hx hy)
    (fun hx ↦ neg_mem hx) (fun {x _} hy ↦ algebraRadicalPow_mul_left hn x hy)
    (fun {_ y} hx ↦ algebraRadicalPow_mul_right hn y hx)

theorem mem_radPowIdeal {A : Type u} [Ring A] [Algebra k A] {n : ℕ} (hn : 1 ≤ n) (a : A) :
    a ∈ radPowIdeal k hn ↔ a ∈ algebraRadicalPow k A n := by
  rw [radPowIdeal, TwoSidedIdeal.mem_mk']; rfl

/-- **Proposition 11.3(3) in `B`**: at binary points the transported rays are a normed
multiplicative basis and a ray transversal. -/
theorem fibreBasis_normed (hc01 : ∀ r s, c r s = 0 ∨ c r s = 1) :
    IsNormedMultiplicativeBasis (S.fibreBasis k hfin c Ψ hΨ) := by
  classical
  set φ := S.fibreRayEquiv k hfin c Ψ hΨ
  have hbφ : ∀ r, S.fibreBasis k hfin c Ψ hΨ (φ r) = S.βv k Ψ r := S.fibreBasis_ray k hfin c Ψ hΨ
  refine ⟨fun ρ ρ' ↦ ?_, ?_, fun n hn ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := φ.surjective ρ
    obtain ⟨s, rfl⟩ := φ.surjective ρ'
    rw [hbφ, hbφ]
    rcases S.βv_mul_βv k c Ψ hΨ hc01 r s with h | ⟨t, ht⟩
    · exact Or.inl h
    · exact Or.inr ⟨φ t, by rw [ht, hbφ]⟩
  · refine ⟨Finset.univ.image fun x ↦ φ (S.P.e x), ?_, ?_⟩
    · let eqv : V ≃ (Finset.univ.image fun x ↦ φ (S.P.e x)) :=
        Equiv.ofBijective (fun x ↦ ⟨φ (S.P.e x), Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
          ⟨fun x y h ↦ by
            have h' := φ.injective (congrArg Subtype.val h)
            rw [← S.P.src_e x, h', S.P.src_e], fun ⟨ρ, hρ⟩ ↦ by
            obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hρ
            exact ⟨x, rfl⟩⟩
      rw [← CompleteOrthogonalIdempotents.equiv eqv]
      have : ((fun i : (Finset.univ.image fun x ↦ φ (S.P.e x)) ↦
          S.fibreBasis k hfin c Ψ hΨ i) ∘ eqv) = S.Eb k Ψ := by
        funext x; exact hbφ (S.P.e x)
      rw [this]
      exact S.Eb_complete k hfin c Ψ hΨ
    · intro ρ hρ
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hρ
      rw [hbφ]
      exact S.Eb_primitive k hfin c Ψ hΨ x
  · ext a
    rw [← mem_radPowIdeal k hn a]
    set I := radPowIdeal (A := B) k hn
    set F := S.fibreIdem k hfin c Ψ hΨ
    constructor
    · intro ha
      have : Submodule.span k (S.fibreBasis k hfin c Ψ hΨ '' {r | S.fibreBasis k hfin c Ψ hΨ r ∈
          algebraRadicalPow k B n}) ≤ PrimitiveIdempotents.idealSubmodule (k := k) I :=
        Submodule.span_le.2 (by rintro _ ⟨r, hr, rfl⟩; exact (mem_radPowIdeal k hn _).2 hr)
      exact this ha
    · intro ha
      rw [F.eq_sum_corners a]
      refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
      obtain ⟨x, rfl⟩ := (σV).surjective x
      obtain ⟨y, rfl⟩ := (σV).surjective y
      have hN : F.IsEndpointSubbimodule (σV x) (σV y)
          (F.corner (k := k) (σV x) (σV y) ⊓ PrimitiveIdempotents.idealSubmodule (k := k) I) :=
        ⟨inf_le_left, fun c hc n hn ↦ ⟨F.corner_mul_corner hc hn.1, I.mul_mem_left _ _ hn.2⟩,
          fun c hc n hn ↦ ⟨F.corner_mul_corner hn.1 hc, I.mul_mem_right _ _ hn.2⟩⟩
      have hmem : F.e (σV x) * a * F.e (σV y) ∈
          F.corner (k := k) (σV x) (σV y) ⊓ PrimitiveIdempotents.idealSubmodule (k := k) I :=
        ⟨F.eAe_mem_corner _ _ a, I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)⟩
      refine Submodule.span_mono ?_ (S.fibre_le_span k hfin c Ψ hΨ hN hmem)
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨S.fibreRayEquiv k hfin c Ψ hΨ r, ?_, S.fibreBasis_ray k hfin c Ψ hΨ r⟩
      show S.fibreBasis k hfin c Ψ hΨ (S.fibreRayEquiv k hfin c Ψ hΨ r) ∈ algebraRadicalPow k B n
      rw [S.fibreBasis_ray]
      exact (mem_radPowIdeal k hn _).1 hr.2

include hfin hΨ in
/-- **`B` has a normed multiplicative basis** (Proposition 11.3(3) with Proposition 7.9). -/
theorem fibre_hasNormedBasis
    (hc01 : ∀ r s, c r s = 0 ∨ c r s = 1) : HasNormedMultiplicativeBasis k B :=
  ⟨_, S.fibreBasis k hfin c Ψ hΨ, S.fibreBasis_normed k hfin c Ψ hΨ hc01⟩

end Sys

end RaySys

end MultiplicativeBasisDeformations
