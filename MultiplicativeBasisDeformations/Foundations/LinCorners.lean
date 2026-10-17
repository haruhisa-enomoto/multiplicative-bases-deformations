import MultiplicativeBasisDeformations.Foundations.IndicatorCocycles

/-!
# Corners of the ray linearization

For `A₀ = kP` in Setting 8.4: the corners `e_x (kP) e_y` are spanned by the rays from `x`
to `y`; the rays of positive degree span a nilpotent subspace; a local corner element with
nonzero identity coefficient is a unit, and the only idempotents of a local corner are `0`
and `e_x`. Every nonzero corner element is `u b_r w` with endpoint units `u, w` and a ray
`r` (the top of its support in the endpoint chain), and `R_x b_s R_y` is spanned by the
rays of `U(s)`. These are the facts behind "the basis vectors represent exactly the same
endpoint-unit orbits" in the proof of Proposition 11.3(3) (`binary-families.tex:160–164`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Tab

variable {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  (P : Tab V R L) (K : Type u) [Field K]

/-- The corner `e_x (kP) e_y`, spanned by the rays from `x` to `y`. -/
def corSp (x y : V) : Submodule K (P.Lin K) :=
  Submodule.span K (P.basis K '' {r | P.src r = x ∧ P.tgt r = y})

/-- The span of the rays of degree at least `d`. -/
def degSp (d : ℤ) : Submodule K (P.Lin K) :=
  Submodule.span K (P.basis K '' {r | d ≤ P.deg (P.wt r)})

theorem mem_corSp_iff {x y : V} {a : P.Lin K} :
    a ∈ P.corSp K x y ↔ ∀ r, (P.basis K).repr a r ≠ 0 → P.src r = x ∧ P.tgt r = y := by
  rw [corSp, Module.Basis.mem_span_image]
  exact ⟨fun h r hr ↦ h (Finsupp.mem_support_iff.2 hr), fun h r hr ↦ h r (Finsupp.mem_support_iff.1 hr)⟩

theorem mem_degSp_iff {d : ℤ} {a : P.Lin K} :
    a ∈ P.degSp K d ↔ ∀ r, (P.basis K).repr a r ≠ 0 → d ≤ P.deg (P.wt r) := by
  rw [degSp, Module.Basis.mem_span_image]
  exact ⟨fun h r hr ↦ h (Finsupp.mem_support_iff.2 hr), fun h r hr ↦ h r (Finsupp.mem_support_iff.1 hr)⟩

theorem b_mem_corSp (r : R) : P.b K r ∈ P.corSp K (P.src r) (P.tgt r) :=
  Submodule.subset_span ⟨r, ⟨rfl, rfl⟩, Mult.basis_apply _ _ r⟩

theorem b_mem_corSp' {r : R} {x y : V} (h1 : P.src r = x) (h2 : P.tgt r = y) :
    P.b K r ∈ P.corSp K x y := h1 ▸ h2 ▸ P.b_mem_corSp K r

theorem b_mem_degSp {r : R} {d : ℤ} (h : d ≤ P.deg (P.wt r)) : P.b K r ∈ P.degSp K d :=
  Submodule.subset_span ⟨r, h, Mult.basis_apply _ _ r⟩

theorem degSp_mono {d d' : ℤ} (h : d ≤ d') : P.degSp K d' ≤ P.degSp K d :=
  Submodule.span_mono (Set.image_mono fun r hr ↦ le_trans h hr)

/-- Degrees add under products. -/
theorem mul_mem_degSp {d d' : ℤ} {a c : P.Lin K} (ha : a ∈ P.degSp K d) (hc : c ∈ P.degSp K d') :
    a * c ∈ P.degSp K (d + d') := by
  have key : ∀ u v, d ≤ P.deg (P.wt u) → d' ≤ P.deg (P.wt v) →
      P.b K u * P.b K v ∈ P.degSp K (d + d') := by
    intro u v hu hv
    rw [Mult.b_mul]
    rcases h : P.mul u v with _ | t
    · exact zero_mem _
    · refine P.b_mem_degSp K ?_
      rw [P.wt_mul u v t h, map_add]; omega
  have hc' : ∀ u, d ≤ P.deg (P.wt u) → P.b K u * c ∈ P.degSp K (d + d') := by
    intro u hu
    induction hc using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, rfl⟩ := hz
      rw [Mult.basis_apply]; exact key u v hu hv
    | zero => rw [mul_zero]; exact zero_mem _
    | add z z' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | smul t z _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, rfl⟩ := hz
    rw [Mult.basis_apply]; exact hc' u hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add z z' _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | smul t z _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ t h

/-- A bound for the degrees of the rays. -/
theorem exists_deg_bound : ∃ D : ℕ, ∀ r, P.deg (P.wt r) ≤ D := by
  classical
  refine ⟨Finset.univ.sup fun r ↦ (P.deg (P.wt r)).toNat, fun r ↦ ?_⟩
  have h1 : (P.deg (P.wt r)).toNat ≤ Finset.univ.sup fun r ↦ (P.deg (P.wt r)).toNat :=
    Finset.le_sup (f := fun r ↦ (P.deg (P.wt r)).toNat) (Finset.mem_univ r)
  have h2 := Int.self_le_toNat (P.deg (P.wt r))
  omega

/-- **Rays of positive degree span a nilpotent subspace.** -/
theorem nilpotent_degSp : ∃ N : ℕ, ∀ n ∈ P.degSp K 1, n ^ N = 0 := by
  obtain ⟨D, hD⟩ := P.exists_deg_bound
  refine ⟨D + 1, fun n hn ↦ ?_⟩
  have hpow : ∀ m : ℕ, n ^ (m + 1) ∈ P.degSp K (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hn
    | succ m ih =>
      rw [pow_succ]
      have := P.mul_mem_degSp K ih hn
      simpa [add_assoc] using this
  have h := hpow D
  rw [P.mem_degSp_iff] at h
  rw [← (P.basis K).repr.injective.eq_iff, map_zero]
  ext r
  by_contra hr
  have h1 := h r hr
  have h2 := hD r
  omega

theorem e_mul_of_mem_corSp {x y : V} {a : P.Lin K} (ha : a ∈ P.corSp K x y) :
    P.b K (P.e x) * a = a := by
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, ⟨h1, -⟩, rfl⟩ := hz
    rw [Mult.basis_apply, Mult.b_e_mul, if_pos h1.symm]
  | zero => rw [mul_zero]
  | add z z' _ _ h1 h2 => rw [mul_add, h1, h2]
  | smul t z _ h => rw [mul_smul_comm, h]

theorem mul_e_of_mem_corSp {x y : V} {a : P.Lin K} (ha : a ∈ P.corSp K x y) :
    a * P.b K (P.e y) = a := by
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, ⟨-, h2⟩, rfl⟩ := hz
    rw [Mult.basis_apply, Mult.b_mul_e, if_pos h2.symm]
  | zero => rw [zero_mul]
  | add z z' _ _ h1 h2 => rw [add_mul, h1, h2]
  | smul t z _ h => rw [smul_mul_assoc, h]

/-- The corner of an element. -/
theorem e_mul_mul_e_mem (x y : V) (a : P.Lin K) :
    P.b K (P.e x) * a * P.b K (P.e y) ∈ P.corSp K x y := by
  have hspan : a ∈ Submodule.span K (Set.range (P.b K)) := by rw [P.span_b K]; trivial
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, rfl⟩ := hz
    rw [Mult.b_e_mul]
    split_ifs with h1
    · rw [Mult.b_mul_e]
      split_ifs with h2
      · exact P.b_mem_corSp' K h1.symm h2.symm
      · exact zero_mem _
    · rw [zero_mul]; exact zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact zero_mem _
  | add z z' _ _ h1 h2 => rw [mul_add, add_mul]; exact add_mem h1 h2
  | smul t z _ h => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ t h

/-- A local corner element is its identity coefficient plus a positive part. -/
theorem local_decomp {x : V} {a : P.Lin K} (ha : a ∈ P.corSp K x x) :
    a - (P.basis K).repr a (P.e x) • P.b K (P.e x) ∈ P.corSp K x x ⊓ P.degSp K 1 := by
  refine ⟨sub_mem ha (Submodule.smul_mem _ _ (P.b_mem_corSp' K (P.src_e x) (P.tgt_e x))), ?_⟩
  show _ ∈ P.degSp K 1
  rw [P.mem_degSp_iff]
  intro r hr
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, ← Mult.basis_apply,
    Module.Basis.repr_self, Finsupp.single_apply] at hr
  by_cases hre : P.e x = r
  · subst hre; simp at hr
  · rw [if_neg hre, smul_zero, sub_zero] at hr
    obtain ⟨h1, -⟩ := (P.mem_corSp_iff K).1 ha r hr
    have hne : r ≠ P.e (P.src r) := by rw [h1]; exact fun h ↦ hre h.symm
    have := P.deg_pos r hne
    omega

theorem repr_e_of_mem_degSp {x : V} {n : P.Lin K} (hn : n ∈ P.degSp K 1) :
    (P.basis K).repr n (P.e x) = 0 := by
  by_contra h
  have := (P.mem_degSp_iff K).1 hn _ h
  rw [P.wt_e, map_zero] at this
  omega

/-- **The only idempotents of a local corner are `0` and `e_x`.** -/
theorem idem_local {x : V} {a : P.Lin K} (ha : a ∈ P.corSp K x x) (hidem : a * a = a) :
    a = 0 ∨ a = P.b K (P.e x) := by
  obtain ⟨N, hN⟩ := P.nilpotent_degSp K
  have hpow : ∀ z : P.Lin K, z * z = z → ∀ m : ℕ, z ^ (m + 1) = z := by
    intro z hz m
    induction m with
    | zero => rw [zero_add, pow_one]
    | succ m ih => rw [pow_succ, ih, hz]
  have hnil : ∀ z ∈ P.degSp K 1, z * z = z → z = 0 := by
    intro z hz hzz
    rw [← hpow z hzz N, pow_succ, hN z hz, zero_mul]
  set c := (P.basis K).repr a (P.e x)
  set E := P.b K (P.e x)
  have hn := P.local_decomp K ha
  set n := a - c • E
  have hEE : E * E = E := by
    rw [Mult.b_e_mul, if_pos (P.src_e x).symm]
  have hEn : E * n = n := P.e_mul_of_mem_corSp K hn.1
  have hnE : n * E = n := P.mul_e_of_mem_corSp K hn.1
  have han : a = c • E + n := by simp [n]
  have hsq : a * a = (c * c) • E + ((2 * c) • n + n * n) := by
    rw [han, add_mul, mul_add, mul_add, smul_mul_smul, hEE, smul_mul_assoc, hEn, mul_smul_comm, hnE]
    rw [two_mul, add_smul]; abel
  have hcc : c * c = c := by
    have h1 := congrArg (fun z ↦ (P.basis K).repr z (P.e x)) hsq
    simp only [hidem, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply] at h1
    have e1 : (P.basis K).repr E (P.e x) = 1 := by
      rw [show E = P.basis K (P.e x) from (Mult.basis_apply _ _ _).symm,
        Module.Basis.repr_self, Finsupp.single_eq_same]
    have e2 := P.repr_e_of_mem_degSp K (x := x) hn.2
    have e3 := P.repr_e_of_mem_degSp K (x := x)
      (P.degSp_mono K (show (1 : ℤ) ≤ 1 + 1 by norm_num) (P.mul_mem_degSp K hn.2 hn.2))
    rw [e1, e2, e3] at h1
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at h1
    have : c = (P.basis K).repr a (P.e x) := rfl
    rw [← this] at h1
    exact h1.symm
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hcc, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hc01 with h | h
  · left
    have ha' : a = n := by rw [han, h, zero_smul, zero_add]
    rw [ha'] at hidem ⊢
    exact hnil n hn.2 hidem
  · right
    have hEa : E * a = a := P.e_mul_of_mem_corSp K ha
    have haE : a * E = a := P.mul_e_of_mem_corSp K ha
    have hz : E - a ∈ P.degSp K 1 := by
      have : E - a = -n := by rw [han, h, one_smul]; abel
      rw [this]; exact neg_mem hn.2
    have hzz : (E - a) * (E - a) = E - a := by
      rw [sub_mul, mul_sub, mul_sub, hEE, hEa, haE, hidem]; abel
    exact (sub_eq_zero.1 (hnil _ hz hzz)).symm

/-- A unit of the local corner at `x`. -/
def IsLocUnit (x : V) (u : P.Lin K) : Prop :=
  u ∈ P.corSp K x x ∧ ∃ u' ∈ P.corSp K x x, u * u' = P.b K (P.e x) ∧ u' * u = P.b K (P.e x)

theorem isLocUnit_e (x : V) : P.IsLocUnit K x (P.b K (P.e x)) := by
  have hE := P.b_mem_corSp' K (P.src_e x) (P.tgt_e x)
  have hEE : P.b K (P.e x) * P.b K (P.e x) = P.b K (P.e x) := by
    rw [Mult.b_e_mul, if_pos (P.src_e x).symm]
  exact ⟨hE, _, hE, hEE, hEE⟩

/-- **A local element with nonzero identity coefficient is a unit.** -/
theorem isLocUnit_of {x : V} {c : K} (hc : c ≠ 0) {n : P.Lin K} (hn : n ∈ P.corSp K x x ⊓ P.degSp K 1) :
    P.IsLocUnit K x (c • P.b K (P.e x) + n) := by
  obtain ⟨N, hN⟩ := P.nilpotent_degSp K
  set E := P.b K (P.e x)
  have hE : E ∈ P.corSp K x x := P.b_mem_corSp' K (P.src_e x) (P.tgt_e x)
  set m := -(c⁻¹ • n)
  have hm : m ∈ P.corSp K x x ⊓ P.degSp K 1 :=
    ⟨neg_mem (Submodule.smul_mem _ _ hn.1), neg_mem (Submodule.smul_mem _ _ hn.2)⟩
  have hEm : E * m = m := P.e_mul_of_mem_corSp K hm.1
  have hmE : m * E = m := P.mul_e_of_mem_corSp K hm.1
  have hEE : E * E = E := by rw [Mult.b_e_mul, if_pos (P.src_e x).symm]
  have hu : c • E + n = c • (E - m) := by
    simp only [m, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
  set w := E + ∑ j ∈ Finset.range N, m ^ (j + 1)
  have hEpow : ∀ j : ℕ, E * m ^ (j + 1) = m ^ (j + 1) := fun j ↦ by rw [pow_succ', ← mul_assoc, hEm]
  have hpowE : ∀ j : ℕ, m ^ (j + 1) * E = m ^ (j + 1) := fun j ↦ by rw [pow_succ, mul_assoc, hmE]
  have htel : ∑ j ∈ Finset.range N, (m ^ (j + 1) - m ^ (j + 1 + 1)) = m - m ^ (N + 1) := by
    rw [Finset.sum_range_sub' (fun j ↦ m ^ (j + 1)) N]; simp
  have hmN : m ^ (N + 1) = 0 := by rw [pow_succ, hN m hm.2, zero_mul]
  have h1 : (E - m) * w = E := by
    have e : (E - m) * w = (E - m) * E + ∑ j ∈ Finset.range N, (E - m) * m ^ (j + 1) := by
      rw [mul_add, Finset.mul_sum]
    rw [e, sub_mul, hEE, hmE, Finset.sum_congr rfl (fun j _ ↦ show (E - m) * m ^ (j + 1) =
      m ^ (j + 1) - m ^ (j + 1 + 1) by rw [sub_mul, hEpow, ← pow_succ']), htel, hmN]; abel
  have h2 : w * (E - m) = E := by
    have e : w * (E - m) = E * (E - m) + ∑ j ∈ Finset.range N, m ^ (j + 1) * (E - m) := by
      rw [add_mul, Finset.sum_mul]
    rw [e, mul_sub, hEE, hEm, Finset.sum_congr rfl (fun j _ ↦ show m ^ (j + 1) * (E - m) =
      m ^ (j + 1) - m ^ (j + 1 + 1) by rw [mul_sub, hpowE, ← pow_succ]), htel, hmN]; abel
  have hw : w ∈ P.corSp K x x :=
    add_mem hE (Submodule.sum_mem _ fun j _ ↦ by
      have := P.e_mul_mul_e_mem K x x (m ^ (j + 1))
      rwa [mul_assoc, hpowE, hEpow] at this)
  rw [hu]
  refine ⟨Submodule.smul_mem _ _ (sub_mem hE hm.1), c⁻¹ • w, Submodule.smul_mem _ _ hw, ?_, ?_⟩
  · rw [smul_mul_smul, mul_inv_cancel₀ hc, one_smul, h1]
  · rw [smul_mul_smul, inv_mul_cancel₀ hc, one_smul, h2]

theorem sum_repr_b (a : P.Lin K) : ∑ s, (P.basis K).repr a s • P.b K s = a := by
  conv_rhs => rw [← (P.basis K).sum_repr a]
  simp only [Mult.basis_apply]

end Tab

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (K : Type u) [Field K]

local notation:max "⌜" r "⌝" => Sys.rr S r

/-- The span of the rays of `U(s)`. -/
def USp (s : R) : Submodule K (S.P.Lin K) :=
  Submodule.span K (S.P.basis K '' {t | S.InU t s})

theorem vecM_mem_degSp {d : ℤ} {x : M S.P.toMult} (hx : x = 0 ∨ ∃ r, x = ⌜r⌝)
    (h : ∀ r, x = ⌜r⌝ → d ≤ S.P.deg (S.P.wt r)) : S.vecM K x ∈ S.P.degSp K d := by
  rcases hx with rfl | ⟨r, rfl⟩
  · exact zero_mem _
  · exact S.P.b_mem_degSp K (h r rfl)

/-- A local power times the identity is a positive local ray unless it is the identity. -/
theorem qpow_e_mem {x : V} (j : ℕ) (hne : S.q x ^ j * ⌜S.P.e x⌝ ≠ ⌜S.P.e x⌝) :
    S.vecM K (S.q x ^ j * ⌜S.P.e x⌝) ∈ S.P.corSp K x x ⊓ S.P.degSp K 1 := by
  rcases S.qpow_cases x j with h | ⟨g, hg, g1, g2, -⟩
  · rw [h, vecM_zero]; exact zero_mem _
  · rw [hg, vecM_rr]
    have hge : g ≠ S.P.e (S.P.src g) := by
      rw [g1]; rintro rfl; exact hne hg
    exact ⟨S.P.b_mem_corSp' K g1 g2, S.P.b_mem_degSp K (by have := S.P.deg_pos g hge; omega)⟩

/-- **Every nonzero corner element is `u b_r w` with endpoint units** (the top ray `r` of its
support in the endpoint chain). -/
theorem exists_unit_ray {x y : V} {a : S.P.Lin K} (ha : a ∈ S.P.corSp K x y) (ha0 : a ≠ 0) :
    ∃ r, S.P.src r = x ∧ S.P.tgt r = y ∧ ∃ u w, S.P.IsLocUnit K x u ∧ S.P.IsLocUnit K y w ∧
      a = u * S.P.b K r * w := by
  classical
  set T := ((S.P.basis K).repr a).support
  have hT : T.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h; apply ha0; rwa [LinearEquiv.map_eq_zero_iff] at h
  obtain ⟨r, hrT, hmin⟩ := T.exists_min_image (fun s ↦ S.P.deg (S.P.wt s)) hT
  have hTc : ∀ s ∈ T, S.P.src s = x ∧ S.P.tgt s = y := fun s hs ↦
    (S.P.mem_corSp_iff K).1 ha s (Finsupp.mem_support_iff.1 hs)
  obtain ⟨r1, r2⟩ := hTc r hrT
  have hU : ∀ s ∈ T, S.InU s r := by
    intro s hs
    obtain ⟨s1, s2⟩ := hTc s hs
    rcases S.inU_total (s := s) (r := r) (s1.trans r1.symm) (s2.trans r2.symm) with h | h
    · exact h
    · have a1 := S.deg_le_of_inU h
      rw [a1.2 (le_antisymm (hmin s hs) a1.1)]
      exact S.inU_refl s
  have hcr : (S.P.basis K).repr a r ≠ 0 := Finsupp.mem_support_iff.1 hrT
  have hsum := S.P.sum_repr_b K a
  rcases S.cyc r with hL | hR
  · -- cyclic at the source
    have hL' : ∀ s ∈ T, ∃ i : ℕ, ⌜s⌝ = S.q x ^ i * ⌜r⌝ := by
      intro s hs
      obtain ⟨i, j, h⟩ := hU s hs
      obtain ⟨i', hi'⟩ := hL i j (by rw [← h]; exact S.rr_ne s)
      exact ⟨i', by rw [h, hi', r1]⟩
    choose! f hf using hL'
    let g : R → M S.P.toMult := fun s ↦ if s = r then ⌜S.P.e x⌝ else S.q x ^ f s * ⌜S.P.e x⌝
    have hg0 : ∀ s, g s = 0 ∨ ∃ t, g s = ⌜t⌝ := by
      intro s
      by_cases hs : s = r
      · right; exact ⟨S.P.e x, by simp [g, hs]⟩
      · simp only [g, if_neg hs]
        rcases S.qpow_cases x (f s) with h | ⟨t, ht, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨t, ht⟩
    have hbs : ∀ s ∈ T, S.P.b K s = S.vecM K (g s) * S.P.b K r := by
      intro s hs
      rw [S.vecM_mul_b K r (hg0 s)]
      by_cases hsr : s = r
      · have e : g s = ⌜S.P.e x⌝ := if_pos hsr
        rw [e, hsr, S.e_mul_rr' r r1, vecM_rr]
      · have e : g s = S.q x ^ f s * ⌜S.P.e x⌝ := if_neg hsr
        rw [e, mul_assoc, S.e_mul_rr' r r1, ← hf s hs, vecM_rr]
    obtain ⟨u, hu_def⟩ : ∃ u, u = ∑ s, (S.P.basis K).repr a s • S.vecM K (g s) := ⟨_, rfl⟩
    have hau : a = u * S.P.b K r * S.P.b K (S.P.e y) := by
      rw [mul_assoc, Mult.b_mul_e, if_pos r2.symm, hu_def, Finset.sum_mul]
      conv_lhs => rw [← hsum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      by_cases hs : s ∈ T
      · rw [hbs s hs, smul_mul_assoc]
      · rw [Finsupp.notMem_support_iff.1 hs, zero_smul, zero_smul, zero_mul]
    have hu : u = (S.P.basis K).repr a r • S.P.b K (S.P.e x) +
        ∑ s ∈ Finset.univ.erase r, (S.P.basis K).repr a s • S.vecM K (g s) := by
      rw [hu_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      congr 1
      rw [show g r = ⌜S.P.e x⌝ from if_pos rfl, vecM_rr]
    have hn : ∑ s ∈ Finset.univ.erase r, (S.P.basis K).repr a s • S.vecM K (g s) ∈
        S.P.corSp K x x ⊓ S.P.degSp K 1 := by
      refine Submodule.sum_mem _ fun s hs ↦ ?_
      have hsr : s ≠ r := Finset.ne_of_mem_erase hs
      by_cases hsT : s ∈ T
      · refine Submodule.smul_mem _ _ ?_
        simp only [g, if_neg hsr]
        refine S.qpow_e_mem K (f s) fun h ↦ hsr ?_
        have := hf s hsT
        rw [← S.e_mul_rr' r r1, ← mul_assoc, h] at this
        exact S.P.rr_injective (this.trans (S.e_mul_rr' r r1))
      · rw [Finsupp.notMem_support_iff.1 hsT, zero_smul]; exact zero_mem _
    refine ⟨r, r1, r2, u, _, ?_, S.P.isLocUnit_e K y, hau⟩
    rw [hu]
    exact S.P.isLocUnit_of K hcr hn
  · -- cyclic at the target
    have hR' : ∀ s ∈ T, ∃ j : ℕ, ⌜s⌝ = ⌜r⌝ * S.q y ^ j := by
      intro s hs
      obtain ⟨i, j, h⟩ := hU s hs
      obtain ⟨j', hj'⟩ := hR i j (by rw [← h]; exact S.rr_ne s)
      exact ⟨j', by rw [h, hj', r2]⟩
    choose! f hf using hR'
    let g : R → M S.P.toMult := fun s ↦ if s = r then ⌜S.P.e y⌝ else S.q y ^ f s * ⌜S.P.e y⌝
    have hg0 : ∀ s, g s = 0 ∨ ∃ t, g s = ⌜t⌝ := by
      intro s
      by_cases hs : s = r
      · right; exact ⟨S.P.e y, by simp [g, hs]⟩
      · simp only [g, if_neg hs]
        rcases S.qpow_cases y (f s) with h | ⟨t, ht, -⟩
        · exact Or.inl h
        · exact Or.inr ⟨t, ht⟩
    have hre : ⌜r⌝ * ⌜S.P.e y⌝ = ⌜r⌝ := by rw [← r2]; exact S.rr_mul_e r
    have hbs : ∀ s ∈ T, S.P.b K s = S.P.b K r * S.vecM K (g s) := by
      intro s hs
      rw [S.b_mul_vecM K r (hg0 s)]
      by_cases hsr : s = r
      · have e : g s = ⌜S.P.e y⌝ := if_pos hsr
        rw [e, hsr, hre, vecM_rr]
      · have e : g s = S.q y ^ f s * ⌜S.P.e y⌝ := if_neg hsr
        rw [e, S.qpow_comm_e, ← mul_assoc, hre, ← hf s hs, vecM_rr]
    obtain ⟨w, hw_def⟩ : ∃ w, w = ∑ s, (S.P.basis K).repr a s • S.vecM K (g s) := ⟨_, rfl⟩
    have haw : a = S.P.b K (S.P.e x) * S.P.b K r * w := by
      rw [Mult.b_e_mul, if_pos r1.symm, hw_def, Finset.mul_sum]
      conv_lhs => rw [← hsum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      by_cases hs : s ∈ T
      · rw [hbs s hs, mul_smul_comm]
      · rw [Finsupp.notMem_support_iff.1 hs, zero_smul, zero_smul, mul_zero]
    have hw : w = (S.P.basis K).repr a r • S.P.b K (S.P.e y) +
        ∑ s ∈ Finset.univ.erase r, (S.P.basis K).repr a s • S.vecM K (g s) := by
      rw [hw_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      congr 1
      rw [show g r = ⌜S.P.e y⌝ from if_pos rfl, vecM_rr]
    have hn : ∑ s ∈ Finset.univ.erase r, (S.P.basis K).repr a s • S.vecM K (g s) ∈
        S.P.corSp K y y ⊓ S.P.degSp K 1 := by
      refine Submodule.sum_mem _ fun s hs ↦ ?_
      have hsr : s ≠ r := Finset.ne_of_mem_erase hs
      by_cases hsT : s ∈ T
      · refine Submodule.smul_mem _ _ ?_
        simp only [g, if_neg hsr]
        refine S.qpow_e_mem K (f s) fun h ↦ hsr ?_
        have := hf s hsT
        rw [← hre, mul_assoc, ← S.qpow_comm_e, h] at this
        exact S.P.rr_injective (this.trans hre)
      · rw [Finsupp.notMem_support_iff.1 hsT, zero_smul]; exact zero_mem _
    refine ⟨r, r1, r2, _, w, S.P.isLocUnit_e K x, ?_, haw⟩
    rw [hw]
    exact S.P.isLocUnit_of K hcr hn

theorem inU_of_mem_USp {r s : R} (h : S.P.b K r ∈ S.USp K s) : S.InU r s := by
  rw [USp, Module.Basis.mem_span_image, ← Mult.basis_apply, Module.Basis.repr_self,
    Finsupp.support_single_ne_zero _ one_ne_zero, Finset.coe_singleton,
    Set.singleton_subset_iff] at h
  exact h

/-- A local ray at `x` is a power of `q_x` times `e_x`. -/
theorem local_eq_qpow {l : R} {x : V} (h1 : S.P.src l = x) (h2 : S.P.tgt l = x) :
    ∃ j : ℕ, ⌜l⌝ = S.q x ^ j * ⌜S.P.e x⌝ := by
  obtain ⟨j, hj⟩ := S.q_pow l (h1.trans h2.symm)
  exact ⟨j, by rw [← h1]; exact hj.symm⟩

/-- **`R_x b_s R_y` is spanned by the rays of `U(s)`.** -/
theorem mul_mem_USp {x y : V} {s : R} (hs1 : S.P.src s = x) (hs2 : S.P.tgt s = y) {u w : S.P.Lin K}
    (hu : u ∈ S.P.corSp K x x) (hw : w ∈ S.P.corSp K y y) : u * S.P.b K s * w ∈ S.USp K s := by
  have key : ∀ l l', S.P.src l = x → S.P.tgt l = x → S.P.src l' = y → S.P.tgt l' = y →
      S.P.b K l * S.P.b K s * S.P.b K l' ∈ S.USp K s := by
    intro l l' l1 l2 l1' l2'
    obtain ⟨j, hj⟩ := S.local_eq_qpow l1 l2
    obtain ⟨j', hj'⟩ := S.local_eq_qpow l1' l2'
    rw [S.b_mul_b K, S.vecM_mul_b K l' (S.rr_mul_rr_cases l s)]
    have a1 : ⌜S.P.e x⌝ * ⌜s⌝ = ⌜s⌝ := S.e_mul_rr' s hs1
    have a2 : ⌜s⌝ * ⌜S.P.e y⌝ = ⌜s⌝ := by rw [← hs2]; exact S.rr_mul_e s
    have e : ⌜l⌝ * ⌜s⌝ * ⌜l'⌝ = S.q (S.P.src s) ^ j * ⌜s⌝ * S.q (S.P.tgt s) ^ j' := by
      rw [hj, hj', S.qpow_comm_e y, hs1, hs2]
      simp only [mul_assoc]
      rw [← mul_assoc ⌜s⌝ ⌜S.P.e y⌝, a2, ← mul_assoc ⌜S.P.e x⌝ ⌜s⌝, a1]
    rw [e]
    rcases S.qpow_mul_rr_mul_qpow s j j' with h | ⟨t, ht, -⟩
    · rw [h, vecM_zero]; exact zero_mem _
    · rw [ht, vecM_rr, ← Mult.basis_apply]
      exact Submodule.subset_span ⟨t, ⟨j, j', ht.symm⟩, rfl⟩
  have hw' : ∀ l, S.P.src l = x → S.P.tgt l = x → S.P.b K l * S.P.b K s * w ∈ S.USp K s := by
    intro l l1 l2
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l', ⟨l1', l2'⟩, rfl⟩ := hz
      rw [Mult.basis_apply]; exact key l l' l1 l2 l1' l2'
    | zero => rw [mul_zero]; exact zero_mem _
    | add z z' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | smul t z _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, ⟨l1, l2⟩, rfl⟩ := hz
    rw [Mult.basis_apply]; exact hw' l l1 l2
  | zero => rw [zero_mul, zero_mul]; exact zero_mem _
  | add z z' _ _ h1 h2 => rw [add_mul, add_mul]; exact add_mem h1 h2
  | smul t z _ h => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ t h

end Sys

end RaySys

end MultiplicativeBasisDeformations
