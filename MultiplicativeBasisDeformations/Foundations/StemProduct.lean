import MultiplicativeBasisDeformations.Foundations.OppositeControls2

/-!
# Proposition 8.12: the stem product

`def:stem-product` and `prop:intrinsic-stem-product` (`local-ray-geometry.tex:96–108,
469–516`): for rays `r : x → y`, `s : y → z`, `r * s = r q_y^n s` for the least `n` with
`r q_y^n s ≠ 0`, and `0` if there is none. In ray terms the endpoint subbimodule `U_r` is the
set of rays `q^i r q^j`, and the product of the sets `U_r U_s` is `U_{r*s}` (`stem_U`). Hence
the stem product is associative (`stem_assoc`), and it is the ray product when the latter is
nonzero (`stem_of_mul_ne`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

open Classical in
/-- **The stem product** (`prop:intrinsic-stem-product`). -/
def stem (r s : R) : M S.P.toMult :=
  if h : ∃ n : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ ≠ 0 then
    ⌜r⌝ * S.q (S.P.tgt r) ^ Nat.find h * ⌜s⌝ else 0

theorem stem_of_mul_ne {r s : R} (h : ⌜r⌝ * ⌜s⌝ ≠ 0) : S.stem r s = ⌜r⌝ * ⌜s⌝ := by
  classical
  have hex : ∃ n : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ ≠ 0 := ⟨0, by simpa using h⟩
  rw [stem, dif_pos hex, (Nat.find_eq_zero hex).2 (by simpa using h)]
  simp

/-- `t` is a product of rays of `U_r` and `U_s`. -/
def InProd (t r s : R) : Prop := ∃ a b, S.InU a r ∧ S.InU b s ∧ ⌜a⌝ * ⌜b⌝ = ⌜t⌝

/-- The degree of a power of a local generator is a nonnegative multiple. -/
theorem deg_χ_nonneg (x : V) : 0 ≤ S.P.deg (S.χ x) := by
  rcases S.q_cases x with h | ⟨g, hg, -⟩
  · rw [S.χ_eq_zero x h, map_zero]
  · rw [χ, hg, wtM_rr]; exact S.P.deg_nonneg g

/-- Expanding a product of elements of `U_r` and `U_s`. -/
theorem inProd_expand {t r s : R} (h : S.InProd t r s) : ∃ i m l : ℕ,
    ⌜t⌝ = S.q (S.P.src r) ^ i * (⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝) * S.q (S.P.tgt s) ^ l := by
  obtain ⟨a, b, ⟨i, j, ha⟩, ⟨k, l, hb⟩, hab⟩ := h
  have hmid : S.P.tgt r = S.P.src s := by
    have h1 := S.src_of_mul_ne (show ⌜a⌝ * ⌜b⌝ ≠ 0 by rw [hab]; exact S.rr_ne t)
    have e1 := (S.inU_endpoints ⟨i, j, ha⟩).2.1
    have e2 := (S.inU_endpoints ⟨k, l, hb⟩).1
    rw [← e1, h1, e2]
  refine ⟨i, j + k, l, ?_⟩
  rw [← hab, ha, hb, hmid, pow_add]
  simp only [mul_assoc]

/-- The degree of a nonzero element. -/
abbrev degM (a : M S.P.toMult) : ℤ := S.P.deg (S.wtM a)

theorem degM_mul {a b : M S.P.toMult} (h : a * b ≠ 0) : S.degM (a * b) = S.degM a + S.degM b := by
  rw [degM, S.wtM_mul _ _ h, map_add]

theorem degM_qpow {x : V} {n : ℕ} (h : S.q x ^ n ≠ 0) : S.degM (S.q x ^ n) = n * S.P.deg (S.χ x) := by
  rw [degM, S.wtM_qpow _ _ h, map_nsmul, nsmul_eq_mul]

theorem degM_qpow_nonneg {x : V} {n : ℕ} (h : S.q x ^ n ≠ 0) : 0 ≤ S.degM (S.q x ^ n) := by
  rw [S.degM_qpow h]; have := S.deg_χ_nonneg x; positivity

theorem degM_rr (r : R) : S.degM ⌜r⌝ = S.P.deg (S.P.wt r) := rfl

/-- **`U_r U_s = U_{r * s}`** (the key step of Proposition 8.12). -/
theorem stem_U (r s : R) : (S.stem r s = 0 ∧ ∀ t, ¬ S.InProd t r s) ∨
    (∃ w, S.stem r s = ⌜w⌝ ∧ ∀ t, S.InProd t r s ↔ S.InU t w) := by
  classical
  by_cases hex : ∃ n : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ ≠ 0
  · right
    set n0 := Nat.find hex with hn0
    have hw0 : ⌜r⌝ * S.q (S.P.tgt r) ^ n0 * ⌜s⌝ ≠ 0 := Nat.find_spec hex
    obtain ⟨w, hw⟩ := S.mul_left_ray (show ⌜r⌝ * (S.q (S.P.tgt r) ^ n0 * ⌜s⌝) ≠ 0 by
      rwa [← mul_assoc])
    rw [← mul_assoc] at hw
    have hst : S.stem r s = ⌜w⌝ := by rw [stem, dif_pos hex, hw]
    have h1 : ⌜r⌝ * S.q (S.P.tgt r) ^ n0 ≠ 0 := fun h0 ↦ hw0 (by rw [h0, zero_mul])
    obtain ⟨u, hu⟩ := S.mul_left_ray h1
    rw [hu] at hw
    have hU : S.InU u r := ⟨0, n0, by rw [← hu, pow_zero, one_mul]⟩
    have hrs : S.P.tgt r = S.P.src s := by
      have := S.src_of_mul_ne (show ⌜u⌝ * ⌜s⌝ ≠ 0 by rw [hw]; exact S.rr_ne w)
      rw [← this, (S.inU_endpoints hU).2.1]
    obtain ⟨w1, w2, -, -⟩ := S.prod_of hw
    have hwsrc : S.P.src w = S.P.src r := by rw [w1, (S.inU_endpoints hU).1]
    -- the degree of `r q^m s`
    have hdeg : ∀ m : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝ ≠ 0 →
        S.degM (⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝) =
          S.P.deg (S.P.wt r) + m * S.P.deg (S.χ (S.P.tgt r)) + S.P.deg (S.P.wt s) := by
      intro m hm
      have hm1 : ⌜r⌝ * S.q (S.P.tgt r) ^ m ≠ 0 := fun h0 ↦ hm (by rw [h0, zero_mul])
      have hm2 : S.q (S.P.tgt r) ^ m ≠ 0 := fun h0 ↦ hm1 (by rw [h0, mul_zero])
      rw [S.degM_mul hm, S.degM_mul hm1, S.degM_qpow hm2]
      rfl
    refine ⟨w, hst, fun t ↦ ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩⟩
    · obtain ⟨i, m, l, e⟩ := S.inProd_expand ht
      have ht0 : S.q (S.P.src r) ^ i * (⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝) *
          S.q (S.P.tgt s) ^ l ≠ 0 := by rw [← e]; exact S.rr_ne t
      have hA : S.q (S.P.src r) ^ i * (⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝) ≠ 0 :=
        fun h0 ↦ ht0 (by rw [h0, zero_mul])
      have hm0 : ⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝ ≠ 0 := fun h0 ↦ hA (by rw [h0, mul_zero])
      have hqi : S.q (S.P.src r) ^ i ≠ 0 := fun h0 ↦ hA (by rw [h0, zero_mul])
      have hql : S.q (S.P.tgt s) ^ l ≠ 0 := fun h0 ↦ ht0 (by rw [h0, mul_zero])
      have hle : n0 ≤ m := Nat.find_min' hex hm0
      have hend : S.P.src t = S.P.src w ∧ S.P.tgt t = S.P.tgt w := by
        obtain ⟨a, b, ha, hb, hab⟩ := ht
        obtain ⟨a1, a2, -, -⟩ := S.prod_of hab
        rw [a1, (S.inU_endpoints ha).1, a2, (S.inU_endpoints hb).2.1, hwsrc, w2]
        exact ⟨rfl, rfl⟩
      rcases S.inU_total hend.1 hend.2 with h | h
      · exact h
      · have hd := S.deg_le_of_inU h
        have hdw : S.P.deg (S.P.wt w) = S.P.deg (S.P.wt r) + n0 * S.P.deg (S.χ (S.P.tgt r)) +
            S.P.deg (S.P.wt s) := by
          rw [← hdeg n0 hw0, ← S.degM_rr, ← hw, ← hu]
        have hdt : S.P.deg (S.P.wt t) = S.degM (S.q (S.P.src r) ^ i) +
            S.degM (⌜r⌝ * S.q (S.P.tgt r) ^ m * ⌜s⌝) + S.degM (S.q (S.P.tgt s) ^ l) := by
          rw [← S.degM_rr, e, S.degM_mul ht0, S.degM_mul hA]
        rw [hdeg m hm0] at hdt
        have := S.degM_qpow_nonneg hqi
        have := S.degM_qpow_nonneg hql
        have := S.deg_χ_nonneg (S.P.tgt r)
        have hmn : (n0 : ℤ) * S.P.deg (S.χ (S.P.tgt r)) ≤ m * S.P.deg (S.χ (S.P.tgt r)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) this
        rw [hd.2 (le_antisymm (by linarith) hd.1)]
        exact S.inU_refl t
    · obtain ⟨i, j, ht'⟩ := ht
      rw [hwsrc, w2, ← hw, ← hu] at ht'
      have ht0 : S.q (S.P.src r) ^ i * (⌜r⌝ * S.q (S.P.tgt r) ^ n0 * ⌜s⌝) *
          S.q (S.P.tgt s) ^ j ≠ 0 := by rw [← ht']; exact S.rr_ne t
      have key : S.q (S.P.src r) ^ i * (⌜r⌝ * S.q (S.P.tgt r) ^ n0 * ⌜s⌝) * S.q (S.P.tgt s) ^ j =
          (S.q (S.P.src r) ^ i * ⌜r⌝) * (S.q (S.P.src s) ^ n0 * (⌜s⌝ * S.q (S.P.tgt s) ^ j)) := by
        rw [hrs]; simp only [mul_assoc]
      have hA : S.q (S.P.src r) ^ i * ⌜r⌝ ≠ 0 := fun h0 ↦ ht0 (by rw [key, h0, zero_mul])
      have hB : S.q (S.P.src s) ^ n0 * (⌜s⌝ * S.q (S.P.tgt s) ^ j) ≠ 0 :=
        fun h0 ↦ ht0 (by rw [key, h0, mul_zero])
      have hB1 : ⌜s⌝ * S.q (S.P.tgt s) ^ j ≠ 0 := fun h0 ↦ hB (by rw [h0, mul_zero])
      obtain ⟨a, ha⟩ := S.mul_right_ray hA
      obtain ⟨s', hs'⟩ := S.mul_left_ray hB1
      rw [hs'] at hB
      obtain ⟨b, hb⟩ := S.mul_right_ray hB
      refine ⟨a, b, ⟨i, 0, by rw [← ha, pow_zero, mul_one]⟩,
        ⟨n0, j, by rw [← hb, ← hs', mul_assoc]⟩, ?_⟩
      rw [ht', key, ha, hs', hb]

  · left
    refine ⟨by rw [stem, dif_neg hex], fun t ht ↦ ?_⟩
    obtain ⟨i, m, l, e⟩ := S.inProd_expand ht
    push Not at hex
    rw [hex m, mul_zero, zero_mul] at e
    exact S.rr_ne t e

/-- Membership in the endpoint subbimodule of an element (zero or a ray). -/
def UM (x : M S.P.toMult) (t : R) : Prop := ∃ w, x = ⌜w⌝ ∧ S.InU t w

theorem stem_cases (r s : R) : S.stem r s = 0 ∨ ∃ w, S.stem r s = ⌜w⌝ := by
  rcases S.stem_U r s with ⟨h, -⟩ | ⟨w, h, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, h⟩

theorem UM_stem (r s t : R) : S.UM (S.stem r s) t ↔ S.InProd t r s := by
  rcases S.stem_U r s with ⟨h, h'⟩ | ⟨w, h, h'⟩
  · rw [h]
    constructor
    · rintro ⟨w, hw, -⟩; exact absurd hw.symm (S.rr_ne w)
    · intro ht; exact absurd ht (h' t)
  · rw [h, h']
    constructor
    · rintro ⟨w', hw', ht⟩; rw [S.rr_inj hw']; exact ht
    · intro ht; exact ⟨w, rfl, ht⟩

/-- Elements with the same endpoint subbimodule are equal. -/
theorem eq_of_UM {x y : M S.P.toMult} (hx : x = 0 ∨ ∃ w, x = ⌜w⌝) (hy : y = 0 ∨ ∃ w, y = ⌜w⌝)
    (h : ∀ t, S.UM x t ↔ S.UM y t) : x = y := by
  rcases hx with rfl | ⟨w, rfl⟩ <;> rcases hy with rfl | ⟨w', rfl⟩
  · rfl
  · obtain ⟨w'', hw'', -⟩ := (h w').2 ⟨w', rfl, S.inU_refl w'⟩
    exact absurd hw''.symm (S.rr_ne w'')
  · obtain ⟨w'', hw'', -⟩ := (h w).1 ⟨w, rfl, S.inU_refl w⟩
    exact absurd hw''.symm (S.rr_ne w'')
  · obtain ⟨a, ha, h1⟩ := (h w).1 ⟨w, rfl, S.inU_refl w⟩
    obtain ⟨b, hb, h2⟩ := (h w').2 ⟨w', rfl, S.inU_refl w'⟩
    rw [← S.rr_inj ha] at h1
    rw [← S.rr_inj hb] at h2
    rw [S.inU_antisymm h1 h2]

open Classical in
/-- The stem product of an element with a ray. -/
def stemL (x : M S.P.toMult) (u : R) : M S.P.toMult :=
  if h : ∃ w, x = ⌜w⌝ then S.stem h.choose u else 0

open Classical in
/-- The stem product of a ray with an element. -/
def stemR (r : R) (y : M S.P.toMult) : M S.P.toMult :=
  if h : ∃ w, y = ⌜w⌝ then S.stem r h.choose else 0

theorem stemL_rr (w u : R) : S.stemL ⌜w⌝ u = S.stem w u := by
  classical
  have h : ∃ w', ⌜w⌝ = ⌜w'⌝ := ⟨w, rfl⟩
  rw [stemL, dif_pos h, S.rr_inj h.choose_spec.symm]

theorem stemR_rr (r w : R) : S.stemR r ⌜w⌝ = S.stem r w := by
  classical
  have h : ∃ w', ⌜w⌝ = ⌜w'⌝ := ⟨w, rfl⟩
  rw [stemR, dif_pos h, S.rr_inj h.choose_spec.symm]

/-- Triple products of the endpoint subbimodules. -/
def InProd3 (t r s u : R) : Prop :=
  ∃ a b c, S.InU a r ∧ S.InU b s ∧ S.InU c u ∧ ⌜a⌝ * ⌜b⌝ * ⌜c⌝ = ⌜t⌝

theorem UM_stemL (r s u t : R) : S.UM (S.stemL (S.stem r s) u) t ↔ S.InProd3 t r s u := by
  rcases S.stem_U r s with ⟨h, h'⟩ | ⟨w, h, h'⟩
  · rw [h]
    have h0 : S.stemL 0 u = 0 := by
      classical
      rw [stemL, dif_neg]
      rintro ⟨w, hw⟩; exact S.rr_ne w hw.symm
    rw [h0]
    constructor
    · rintro ⟨w, hw, -⟩; exact absurd hw.symm (S.rr_ne w)
    · rintro ⟨a, b, c, ha, hb, hc, habc⟩
      have hab : ⌜a⌝ * ⌜b⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← habc, h0, zero_mul])
      obtain ⟨d, hd⟩ := S.ray_of_mul_ne hab
      exact absurd ⟨a, b, ha, hb, hd⟩ (h' d)
  · rw [h, stemL_rr, UM_stem]
    constructor
    · rintro ⟨d, c, hd, hc, hdc⟩
      obtain ⟨a, b, ha, hb, hab⟩ := (h' d).2 hd
      exact ⟨a, b, c, ha, hb, hc, by rw [hab, hdc]⟩
    · rintro ⟨a, b, c, ha, hb, hc, habc⟩
      have hab : ⌜a⌝ * ⌜b⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← habc, h0, zero_mul])
      obtain ⟨d, hd⟩ := S.ray_of_mul_ne hab
      exact ⟨d, c, (h' d).1 ⟨a, b, ha, hb, hd⟩, hc, by rw [← hd, habc]⟩

theorem UM_stemR (r s u t : R) : S.UM (S.stemR r (S.stem s u)) t ↔ S.InProd3 t r s u := by
  rcases S.stem_U s u with ⟨h, h'⟩ | ⟨w, h, h'⟩
  · rw [h]
    have h0 : S.stemR r 0 = 0 := by
      classical
      rw [stemR, dif_neg]
      rintro ⟨w, hw⟩; exact S.rr_ne w hw.symm
    rw [h0]
    constructor
    · rintro ⟨w, hw, -⟩; exact absurd hw.symm (S.rr_ne w)
    · rintro ⟨a, b, c, ha, hb, hc, habc⟩
      have hbc : ⌜b⌝ * ⌜c⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← habc, mul_assoc, h0, mul_zero])
      obtain ⟨d, hd⟩ := S.ray_of_mul_ne hbc
      exact absurd ⟨b, c, hb, hc, hd⟩ (h' d)
  · rw [h, stemR_rr, UM_stem]
    constructor
    · rintro ⟨a, d, ha, hd, had⟩
      obtain ⟨b, c, hb, hc, hbc⟩ := (h' d).2 hd
      exact ⟨a, b, c, ha, hb, hc, by rw [mul_assoc, hbc, had]⟩
    · rintro ⟨a, b, c, ha, hb, hc, habc⟩
      have hbc : ⌜b⌝ * ⌜c⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← habc, mul_assoc, h0, mul_zero])
      obtain ⟨d, hd⟩ := S.ray_of_mul_ne hbc
      exact ⟨a, d, ha, (h' d).1 ⟨b, c, hb, hc, hd⟩, by rw [← hd, ← mul_assoc, habc]⟩

theorem stemL_cases (x : M S.P.toMult) (u : R) : S.stemL x u = 0 ∨ ∃ w, S.stemL x u = ⌜w⌝ := by
  classical
  unfold stemL
  split_ifs
  · exact S.stem_cases _ _
  · exact Or.inl rfl

theorem stemR_cases (r : R) (y : M S.P.toMult) : S.stemR r y = 0 ∨ ∃ w, S.stemR r y = ⌜w⌝ := by
  classical
  unfold stemR
  split_ifs
  · exact S.stem_cases _ _
  · exact Or.inl rfl

/-- **The stem product is associative** (Proposition 8.12). -/
theorem stem_assoc (r s u : R) : S.stemL (S.stem r s) u = S.stemR r (S.stem s u) :=
  S.eq_of_UM (S.stemL_cases _ _) (S.stemR_cases _ _) fun t ↦ by
    rw [UM_stemL, UM_stemR]

end Sys

end RaySys

end MultiplicativeBasisDeformations
