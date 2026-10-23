module

public import MultiplicativeBasisDeformations.Foundations.Successor

/-!
# Primitive cyclic corners (Lemma 8.21)

`def:primitive-return-corner` and `lem:primitive-cyclic-corners`
(`primitive-ray-equations.tex`). Part (1): a generating ray `f : x → y`, `x ≠ y`,
cyclic at both endpoints with `q_x f = f q_y ≠ 0` and `ℓ(q_x)` primitive, has a primitive
reverse whenever `f A₀(y, x) ≠ 0`: the generating ray `h` of `A₀(y, x)` satisfies `fh = q_x`,
`hf = q_y`. A higher least return exponent gives a four-point crown in the faithful projective
support at `x`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

/-- A primitive reverse of `f` (`def:primitive-return-corner`(1)). -/
def PrimRev (f h : R) : Prop :=
  ⌜f⌝ * ⌜h⌝ = S.q (S.P.src f) ∧ ⌜h⌝ * ⌜f⌝ = S.q (S.P.tgt f)

/-- Iterating `q_x f = f q_y`. -/
theorem comm_pow {f : R} (h : S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f)) (n : ℕ) :
    S.q (S.P.src f) ^ n * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.21(1)** (`lem:primitive-cyclic-corners`): the generating reverse is primitive. -/
theorem prim_reverse (hfin : IsRepresentationFinite k (S.P.Lin k)) {f h0 : R}
    (hf : S.IsGen f) (hxy : S.P.src f ≠ S.P.tgt f) (hL : S.CycL f) (hR : S.CycR f)
    (hqf : S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f)) (hqf0 : S.q (S.P.src f) * ⌜f⌝ ≠ 0)
    (hprim : Prim (S.χ (S.P.src f))) (h01 : S.P.src h0 = S.P.tgt f)
    (h02 : S.P.tgt h0 = S.P.src f) (hfh0 : ⌜f⌝ * ⌜h0⌝ ≠ 0) {h : R} (hh : S.IsGen h)
    (hh1 : S.P.src h = S.P.tgt f) (hh2 : S.P.tgt h = S.P.src f) : S.PrimRev f h := by
  set x := S.P.src f with hx
  set y := S.P.tgt f with hy
  have hqx : S.q x ≠ 0 := fun h' ↦ hqf0 (by rw [h', zero_mul])
  have hqy : S.q y ≠ 0 := fun h' ↦ hqf0 (by rw [hqf, h', mul_zero])
  obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases x).resolve_left hqx
  replace hq0 : S.q x = ⌜q0⌝ := hq0
  have hd : 0 < S.P.deg (S.χ x) := S.χ_deg_pos x hqx
  have hdf : 0 < S.P.deg (S.P.wt f) := S.deg_pos_of_ne hxy
  -- every return through `f` is `q_x^b` with `b ≥ a`, where `f h = q_x^a`
  have hret : ∀ v : R, S.P.src v = y → S.P.tgt v = x → ⌜f⌝ * ⌜v⌝ ≠ 0 →
      ∃ i j : ℕ, ⌜f⌝ * ⌜v⌝ = S.q x ^ i * (⌜f⌝ * ⌜h⌝) * S.q x ^ j := by
    intro v v1 v2 hv
    obtain ⟨i, j, hij⟩ := hh v (v1.trans hh1.symm) (v2.trans hh2.symm)
    refine ⟨i, j, ?_⟩
    rw [hij, hh1, hh2, ← mul_assoc, ← mul_assoc, ← S.comm_pow hqf i]
    simp only [mul_assoc]
    rfl
  have hfh : ⌜f⌝ * ⌜h⌝ ≠ 0 := by
    obtain ⟨i, j, e⟩ := hret h0 h01 h02 hfh0
    intro h'; apply hfh0; rw [e, h', mul_zero, zero_mul]
  obtain ⟨t, ht⟩ := S.ray_of_mul_ne hfh
  obtain ⟨t1, t2, -, t4⟩ := S.prod_of ht
  have htloop : S.P.src t = S.P.tgt t := by rw [t1, t2, hh2]
  obtain ⟨a, ha, haw⟩ := S.local_eq t htloop
  rw [t1] at ha haw
  have hdeg : ∀ (r : R) (n : ℕ), ⌜r⌝ = S.q x ^ n * ⌜S.P.e x⌝ → S.P.deg (S.P.wt r) = n * S.P.deg (S.χ x) :=
    fun r n hr ↦ S.deg_wt_qpow_e hr
  have hdh := S.P.deg_nonneg h
  have ha1 : 1 ≤ a := by
    by_contra ha0
    have : a = 0 := by omega
    subst this
    have := congrArg S.P.deg haw
    rw [t4, zero_smul, map_add, map_zero] at this
    omega
  -- minimality of the return exponent
  have hmin : ∀ (v : R) (b : ℕ), S.P.src v = y → S.P.tgt v = x → ⌜f⌝ * ⌜v⌝ ≠ 0 →
      ⌜f⌝ * ⌜v⌝ = S.q x ^ b * ⌜S.P.e x⌝ → a ≤ b := by
    intro v b v1 v2 hv0 hv
    obtain ⟨i, j, e⟩ := hret v v1 v2 hv0
    obtain ⟨u, hu⟩ := S.ray_of_mul_ne hv0
    rw [ht] at e
    have hne : S.q x ^ i * ⌜t⌝ * S.q x ^ j ≠ 0 := by rw [← e]; exact hv0
    have hne1 : S.q x ^ i * ⌜t⌝ ≠ 0 := fun h' ↦ hne (by rw [h', zero_mul])
    have hqi : S.q x ^ i ≠ 0 := fun h' ↦ hne1 (by rw [h', zero_mul])
    have hqj : S.q x ^ j ≠ 0 := fun h' ↦ hne (by rw [h', mul_zero])
    have d1 : S.P.deg (S.P.wt u) = b * S.P.deg (S.χ x) := hdeg u b (hu ▸ hv)
    have d2 : S.P.deg (S.P.wt u) = i * S.P.deg (S.χ x) + a * S.P.deg (S.χ x) +
        j * S.P.deg (S.χ x) := by
      have := congrArg S.wtM (hu.symm.trans e)
      rw [wtM_rr, S.wtM_mul _ _ hne, S.wtM_mul _ _ hne1, S.wtM_qpow _ _ hqi,
        S.wtM_qpow _ _ hqj, wtM_rr, haw] at this
      rw [this]; simp only [map_add, map_nsmul, nsmul_eq_mul]; rfl
    have : ((a : ℕ) : ℤ) * S.P.deg (S.χ x) ≤ b * S.P.deg (S.χ x) := by
      have : (0 : ℤ) ≤ i * S.P.deg (S.χ x) + j * S.P.deg (S.χ x) := by positivity
      linarith
    exact_mod_cast le_of_mul_le_mul_right this hd
  have hdq0 : S.P.deg (S.P.wt q0) = S.P.deg (S.χ x) := by rw [χ, hq0]; rfl
  have hq0e : ⌜q0⌝ = S.q x ^ 1 * ⌜S.P.e x⌝ := by rw [pow_one, S.q_mul_e, hq0]
  have hdv : ∀ v : R, 0 ≤ S.P.deg (S.P.wt v) := fun v ↦ S.P.deg_nonneg v
  have ha2 : a = 1 := by
    by_contra ha2
    have ha2' : 2 ≤ a := by omega
    have hqa1 : S.q x ^ (a - 1) * ⌜S.P.e x⌝ ≠ 0 := by
      intro h'
      apply S.rr_ne t
      rw [← ha, show a = 1 + (a - 1) by omega, pow_add, mul_assoc, h', mul_zero]
    obtain ⟨w, hw, w1, w2, ww⟩ := (S.qpow_cases x (a - 1)).resolve_left hqa1
    have hqa : ⌜t⌝ = ⌜q0⌝ * ⌜w⌝ := by
      rw [← ha, ← hw, ← hq0, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
    have hqf0' : ⌜q0⌝ * ⌜f⌝ ≠ 0 := by rw [← hq0]; exact hqf0
    obtain ⟨qf, hqfr⟩ := S.ray_of_mul_ne hqf0'
    obtain ⟨qf1, qf2, -, qf4⟩ := S.prod_of hqfr
    obtain ⟨qy0, hqy0, qy1, qy2, -⟩ := (S.q_cases y).resolve_left hqy
    replace hqy0 : S.q y = ⌜qy0⌝ := hqy0
    have hfqy : ⌜f⌝ * ⌜qy0⌝ = ⌜qf⌝ := by rw [← hqy0, ← hqf, hq0, hqfr]
    have hdt : S.P.deg (S.P.wt t) = a * S.P.deg (S.χ x) := by
      rw [haw, map_nsmul, nsmul_eq_mul]
    have hdw : S.P.deg (S.P.wt w) = (a - 1 : ℕ) * S.P.deg (S.χ x) := by
      rw [ww, map_nsmul, nsmul_eq_mul]
    have hdqf : S.P.deg (S.P.wt qf) = S.P.deg (S.χ x) + S.P.deg (S.P.wt f) := by
      rw [qf4, map_add, hdq0]
    apply S.P.crown_false k hfin x q0 f t qf ⟨q01, rfl, by rw [t1], by rw [qf1, q01]⟩
    · rw [S.rf_iff]; exact ⟨w, hqa.symm⟩
    · rw [S.rf_iff]; exact ⟨f, hqfr⟩
    · rw [S.rf_iff]; exact ⟨h, ht⟩
    · rw [S.rf_iff]; exact ⟨qy0, hfqy⟩
    · -- `f` is not `q_x v`
      rw [S.rf_iff]; rintro ⟨v, hv⟩
      obtain ⟨-, v2, v3, -⟩ := S.prod_of hv
      exact S.gen_ne_q_mul hf (b := v) (by rw [← v3, q02]) v2.symm 1 le_rfl
        (by rw [← hv, pow_one, ← hq0])
    · -- no return of exponent one
      rw [S.rf_iff]; rintro ⟨v, hv⟩
      obtain ⟨-, v2, v3, -⟩ := S.prod_of hv
      have := hmin v 1 v3.symm (by rw [← v2, q02]) (by rw [hv]; exact S.rr_ne q0)
        (by rw [hv, hq0e])
      omega
    · -- `q_x^a` does not lie below `q_x f`
      rw [S.rf_iff]; rintro ⟨v, hv⟩
      rw [hqa, mul_assoc, ← hqfr] at hv
      have hwv : ⌜w⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne qf (by rw [← hqfr, ← hv, h', mul_zero])
      obtain ⟨z, hz⟩ := S.ray_of_mul_ne hwv
      rw [hz] at hv
      have hzf := S.cancel_left hv (by rw [hv]; exact hqf0')
      subst hzf
      obtain ⟨-, z2, z3, -⟩ := S.prod_of hz
      exact S.gen_ne_q_mul hf (b := v) (by rw [← z3, w2]) z2.symm (a - 1) (by omega)
        (by rw [← hz, ← hw, mul_assoc, S.e_mul_rr' v (by rw [← z3, w2])])
    · -- `q_x f` does not lie below `q_x^a`
      rw [S.rf_iff]; rintro ⟨v, hv⟩
      rw [← hqfr, hqa, mul_assoc] at hv
      have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne t (by rw [hqa, ← hv, h', mul_zero])
      obtain ⟨z, hz⟩ := S.ray_of_mul_ne hfv
      rw [hz] at hv
      have hzw := S.cancel_left hv (by rw [hv, ← hqa]; exact S.rr_ne t)
      subst hzw
      obtain ⟨-, z2, z3, -⟩ := S.prod_of hz
      have := hmin v (a - 1) z3.symm (by rw [← z2, w2]) hfv (by rw [hz, hw])
      omega
    · -- degree
      rw [S.rf_iff]; rintro ⟨v, hv⟩
      have := congrArg S.P.deg (S.prod_of hv).2.2.2
      rw [map_add, hdt, hdq0] at this
      have := hdv v
      have : (2 : ℤ) * S.P.deg (S.χ x) ≤ a * S.P.deg (S.χ x) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast ha2') hd.le
      linarith
    · rw [S.rf_iff]; rintro ⟨v, hv⟩
      obtain ⟨-, v2, v3, -⟩ := S.prod_of hv
      exact S.gen_ne_q_mul hf (b := v) (by rw [← v3, t2, hh2]) v2.symm a (by omega)
        (by rw [← hv, ← ha, mul_assoc, S.e_mul_rr' v (by rw [← v3, t2, hh2])])
    · rw [S.rf_iff]; rintro ⟨v, hv⟩
      have := congrArg S.P.deg (S.prod_of hv).2.2.2
      rw [map_add, hdqf, hdq0] at this
      have := hdv v
      linarith
    · rw [S.rf_iff]; rintro ⟨v, hv⟩
      have := congrArg S.P.deg (S.prod_of hv).2.2.2
      rw [map_add, hdqf] at this
      have := hdv v
      linarith
  subst ha2
  have hfhq : ⌜f⌝ * ⌜h⌝ = S.q x := by rw [ht, ← ha, pow_one, S.q_mul_e]
  have hfhf : ⌜f⌝ * (⌜h⌝ * ⌜f⌝) ≠ 0 := by rw [← mul_assoc, hfhq]; exact hqf0
  have hhf : ⌜h⌝ * ⌜f⌝ ≠ 0 := fun h' ↦ hfhf (by rw [h', mul_zero])
  obtain ⟨s', hs'⟩ := S.ray_of_mul_ne hhf
  obtain ⟨s1, s2, -, s4⟩ := S.prod_of hs'
  have hsloop : S.P.src s' = S.P.tgt s' := by rw [s1, s2, hh1]
  obtain ⟨b, hb, hbw⟩ := S.local_eq s' hsloop
  rw [s1, hh1] at hb hbw
  -- `χ_y = χ_x`
  have hχ : S.χ y = S.χ x := by
    have := congrArg S.wtM hqf
    rw [S.wtM_mul _ _ hqf0, S.wtM_mul _ _ (hqf ▸ hqf0), wtM_rr] at this
    change S.χ x + S.P.wt f = S.P.wt f + S.χ y at this
    rw [add_comm] at this
    exact (add_left_cancel this).symm
  have hb1 : b = 1 := by
    have e1 := congrArg S.P.deg hbw
    have e2 := congrArg S.P.deg t4
    rw [haw, one_smul] at e2
    rw [s4, map_add, hχ, map_nsmul, nsmul_eq_mul] at e1
    rw [map_add] at e2
    have : ((b : ℕ) : ℤ) * S.P.deg (S.χ x) = 1 * S.P.deg (S.χ x) := by linarith
    exact_mod_cast mul_right_cancel₀ hd.ne' this
  subst hb1
  exact ⟨hfhq, by rw [hs', ← hb, pow_one, S.q_mul_e]⟩

/-! ### Return partners and the corner `S_x` -/

/-- A return partner `y` of `x` (`def:primitive-return-corner`(2)). -/
def Partner (x y : V) : Prop :=
  y ≠ x ∧ ∃ f h, S.IsGen f ∧ S.P.src f = x ∧ S.P.tgt f = y ∧ S.PrimRev f h ∧
    S.q x * ⌜f⌝ = ⌜f⌝ * S.q y ∧ S.q x * ⌜f⌝ ≠ 0

/-- Membership in the primitive return corner `S_x`. -/
def InS (x y : V) : Prop := y = x ∨ S.Partner x y

/-- **A factorization `uv = q_x` through `y ≠ x`** (`lem:primitive-cyclic-corners`(3), last
paragraph): `u` is generating with primitive reverse `v`, and `y` is a return partner. -/
theorem partner_of_factor {x y : V} {u v : R} (hu1 : S.P.src u = x) (hu2 : S.P.tgt u = y)
    (hxy : y ≠ x) (huv : ⌜u⌝ * ⌜v⌝ = S.q x) (hq2 : S.q x ^ 2 ≠ 0) (hprim : Prim (S.χ x)) :
    S.IsGen u ∧ S.PrimRev u v ∧ S.q x * ⌜u⌝ = ⌜u⌝ * S.q y ∧ S.q x * ⌜u⌝ ≠ 0 ∧
      S.Partner x y := by
  have hqx : S.q x ≠ 0 := fun h ↦ hq2 (by rw [h, zero_pow two_ne_zero])
  have huv0 : ⌜u⌝ * ⌜v⌝ ≠ 0 := huv ▸ hqx
  obtain ⟨t, ht⟩ := S.ray_of_mul_ne huv0
  obtain ⟨t1, t2, t3, t4⟩ := S.prod_of ht
  have hv2 : S.P.tgt v = x := by
    obtain ⟨q0, hq0, -, q02, -⟩ := (S.q_cases x).resolve_left hqx
    have : t = q0 := S.rr_inj (ht.symm.trans (huv.trans hq0))
    rw [← t2, this, q02]
  have hv1 : S.P.src v = y := by rw [← t3, hu2]
  have hdu : 0 < S.P.deg (S.P.wt u) := S.deg_pos_of_ne (by rw [hu1, hu2]; exact hxy.symm)
  have hdv : 0 < S.P.deg (S.P.wt v) := S.deg_pos_of_ne (by rw [hv1, hv2]; exact hxy)
  have hwt : S.P.wt t = S.χ x := by
    rw [χ, ← huv, ht, wtM_rr]
  -- `vu = q_y`
  have hvuvu : ⌜u⌝ * (⌜v⌝ * ⌜u⌝) * ⌜v⌝ ≠ 0 := by
    rw [← mul_assoc, huv, mul_assoc, huv, ← pow_two]; exact hq2
  have hvu : ⌜v⌝ * ⌜u⌝ ≠ 0 := fun h ↦ hvuvu (by rw [h, mul_zero, zero_mul])
  obtain ⟨w, hw⟩ := S.ray_of_mul_ne hvu
  obtain ⟨w1, w2, -, w4⟩ := S.prod_of hw
  have hwl : S.P.src w = S.P.tgt w := by rw [w1, w2, hv1, hu2]
  obtain ⟨a, ha, haw⟩ := S.local_eq w hwl
  rw [w1, hv1] at ha haw
  have hχ : S.χ x = a • S.χ y := by rw [← hwt, t4, ← haw, w4, add_comm]
  have ha1 : a = 1 := by
    have h1 := hprim a _ hχ
    rcases Nat.lt_or_ge a 1 with h0 | h0
    · exfalso
      have : a = 0 := by omega
      subst this
      have := congrArg S.P.deg haw
      rw [w4, zero_smul, map_zero, map_add] at this
      omega
    · omega
  subst ha1
  rw [one_smul] at hχ
  have hvuq : ⌜v⌝ * ⌜u⌝ = S.q y := by rw [hw, ← ha, pow_one, S.q_mul_e]
  have hqy : S.q x * ⌜u⌝ = ⌜u⌝ * S.q y := by rw [← huv, ← hvuq, mul_assoc]
  have hqu : S.q x * ⌜u⌝ ≠ 0 := by
    intro h; apply hq2; rw [pow_two]; nth_rewrite 2 [← huv]; rw [← mul_assoc, h, zero_mul]
  -- `u` is generating
  have hgen : S.IsGen u := by
    obtain ⟨g, g1, g2, hg⟩ := S.exists_gen u
    obtain ⟨i, j, hij⟩ := hg u g1.symm g2.symm
    have hdg : 0 < S.P.deg (S.P.wt g) := S.deg_pos_of_ne (by rw [g1, g2, hu1, hu2]; exact hxy.symm)
    have hne : S.q (S.P.src g) ^ i * ⌜g⌝ * S.q (S.P.tgt g) ^ j ≠ 0 := hij ▸ S.rr_ne u
    have hne1 : S.q (S.P.src g) ^ i * ⌜g⌝ ≠ 0 := fun h ↦ hne (by rw [h, zero_mul])
    have hqi : S.q (S.P.src g) ^ i ≠ 0 := fun h ↦ hne1 (by rw [h, zero_mul])
    have hqj : S.q (S.P.tgt g) ^ j ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
    have hwu := congrArg S.wtM hij
    rw [wtM_rr, S.wtM_mul _ _ hne, S.wtM_mul _ _ hne1, S.wtM_qpow _ _ hqi, S.wtM_qpow _ _ hqj,
      wtM_rr, g1, g2, hu1, hu2, ← hχ] at hwu
    have hdχ := S.χ_deg_pos x hqx
    have := congrArg S.P.deg t4
    rw [hwt, map_add, hwu] at this
    simp only [map_add, map_nsmul, nsmul_eq_mul] at this
    have hi0 : (0 : ℤ) ≤ i := by positivity
    have hj0 : (0 : ℤ) ≤ j := by positivity
    have hij0 : i = 0 ∧ j = 0 := by
      constructor
      · by_contra hi
        have h1 : (1 : ℤ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
        nlinarith
      · by_contra hj
        have h1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
        nlinarith
    obtain ⟨rfl, rfl⟩ := hij0
    rw [pow_zero, pow_zero, one_mul, mul_one] at hij
    rw [S.rr_inj hij]; exact hg
  refine ⟨hgen, ⟨by rw [huv, hu1], by rw [hvuq, hu2]⟩, hqy, hqu, hxy, u, v, hgen, hu1, hu2,
    ⟨by rw [huv, hu1], by rw [hvuq, hu2]⟩, hqy, hqu⟩

/-! ### Primitive pairs -/

/-- Weights of a primitive pair: `χ_b = ℓ(t) + ℓ(h) = χ_c`. -/
theorem χ_pair {t h : R} (hth : ⌜t⌝ * ⌜h⌝ = S.q (S.P.src t)) (hht : ⌜h⌝ * ⌜t⌝ = S.q (S.P.tgt t))
    (hq : S.q (S.P.src t) ≠ 0) (hq' : S.q (S.P.tgt t) ≠ 0) :
    S.χ (S.P.src t) = S.P.wt t + S.P.wt h ∧ S.χ (S.P.tgt t) = S.P.wt h + S.P.wt t := by
  have h1 : ⌜t⌝ * ⌜h⌝ ≠ 0 := by rw [hth]; exact hq
  obtain ⟨s, hs⟩ := S.ray_of_mul_ne h1
  have hts : S.χ (S.P.src t) = S.P.wt s := by rw [χ, ← hth, hs, wtM_rr]
  have h2 : ⌜h⌝ * ⌜t⌝ ≠ 0 := by rw [hht]; exact hq'
  obtain ⟨s', hs'⟩ := S.ray_of_mul_ne h2
  have hts' : S.χ (S.P.tgt t) = S.P.wt s' := by rw [χ, ← hht, hs', wtM_rr]
  obtain ⟨-, -, -, e4⟩ := S.prod_of hs
  obtain ⟨-, -, -, e4'⟩ := S.prod_of hs'
  exact ⟨hts.trans e4, hts'.trans e4'⟩

/-- **The first ray of a primitive pair between distinct vertices is generating.** -/
theorem gen_of_pair {t h : R} (hbc : S.P.src t ≠ S.P.tgt t)
    (hth : ⌜t⌝ * ⌜h⌝ = S.q (S.P.src t)) (hht : ⌜h⌝ * ⌜t⌝ = S.q (S.P.tgt t))
    (hq : S.q (S.P.src t) ≠ 0) (hq' : S.q (S.P.tgt t) ≠ 0) : S.IsGen t := by
  obtain ⟨hχb, hχc⟩ := S.χ_pair hth hht hq hq'
  have hh1 : S.P.src h = S.P.tgt t := by
    have : ⌜t⌝ * ⌜h⌝ ≠ 0 := by rw [hth]; exact hq
    exact (S.src_of_mul_ne this).symm
  have hh2 : S.P.tgt h = S.P.src t := by
    have : ⌜h⌝ * ⌜t⌝ ≠ 0 := by rw [hht]; exact hq'
    exact S.src_of_mul_ne this
  have hdh : 0 < S.P.deg (S.P.wt h) := S.deg_pos_of_ne (by rw [hh1, hh2]; exact hbc.symm)
  have hχeq : S.χ (S.P.tgt t) = S.χ (S.P.src t) := by rw [hχb, hχc, add_comm]
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen t
  obtain ⟨i, j, hij⟩ := hg t g1.symm g2.symm
  have hne : S.q (S.P.src g) ^ i * ⌜g⌝ * S.q (S.P.tgt g) ^ j ≠ 0 := hij ▸ S.rr_ne t
  have hne1 : S.q (S.P.src g) ^ i * ⌜g⌝ ≠ 0 := fun h ↦ hne (by rw [h, zero_mul])
  have hqi : S.q (S.P.src g) ^ i ≠ 0 := fun h ↦ hne1 (by rw [h, zero_mul])
  have hqj : S.q (S.P.tgt g) ^ j ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
  have hwu := congrArg S.wtM hij
  rw [wtM_rr, S.wtM_mul _ _ hne, S.wtM_mul _ _ hne1, S.wtM_qpow _ _ hqi, S.wtM_qpow _ _ hqj,
    wtM_rr, g1, g2, hχeq] at hwu
  have hdχ := S.χ_deg_pos (S.P.src t) hq
  have hdg := S.P.deg_nonneg g
  have e := congrArg S.P.deg hχb
  rw [map_add, hwu] at e
  simp only [map_add, map_nsmul, nsmul_eq_mul] at e
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hij0 : i = 0 ∧ j = 0 := by
    constructor
    · by_contra hi
      have h1 : (1 : ℤ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
      nlinarith
    · by_contra hj
      have h1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
      nlinarith
  obtain ⟨rfl, rfl⟩ := hij0
  rw [pow_zero, pow_zero, one_mul, mul_one] at hij
  rw [S.rr_inj hij]; exact hg

/-- **A primitive pair gives a return partner** when one local length is at least three
(`lem:primitive-cyclic-corners`(3): "both displayed actions are nonzero: use
`q_b² = t q_c h` or `q_c² = h q_b t`"). -/
theorem partner_of_pair {t h : R} (hbc : S.P.src t ≠ S.P.tgt t)
    (hth : ⌜t⌝ * ⌜h⌝ = S.q (S.P.src t)) (hht : ⌜h⌝ * ⌜t⌝ = S.q (S.P.tgt t))
    (hq : S.q (S.P.src t) ≠ 0) (hq' : S.q (S.P.tgt t) ≠ 0)
    (h3 : S.q (S.P.src t) ^ 2 ≠ 0 ∨ S.q (S.P.tgt t) ^ 2 ≠ 0) :
    S.Partner (S.P.src t) (S.P.tgt t) := by
  have hqt : S.q (S.P.src t) * ⌜t⌝ = ⌜t⌝ * S.q (S.P.tgt t) := by
    rw [← hth, ← hht, mul_assoc]
  have hqt0 : S.q (S.P.src t) * ⌜t⌝ ≠ 0 := by
    rcases h3 with h3 | h3
    · intro h0; apply h3
      rw [pow_two]; nth_rewrite 2 [← hth]; rw [← mul_assoc, h0, zero_mul]
    · intro h0; apply h3
      rw [pow_two, ← hht, mul_assoc, ← mul_assoc ⌜t⌝, hth, ← mul_assoc, mul_assoc, h0, mul_zero]
  exact ⟨fun e ↦ hbc e.symm, t, h, S.gen_of_pair hbc hth hht hq hq', rfl, rfl, ⟨hth, hht⟩,
    hqt, hqt0⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 9.8** (`lem:external-hom-chain`): generating rays out of `x` with surviving
`q_x`-action and targets outside `S_x` are comparable. -/
theorem ext_chain (hfin : IsRepresentationFinite k (S.P.Lin k)) {x : V}
    (hprim : Prim (S.χ x)) (hq2 : S.q x ^ 2 ≠ 0) {f h : R} (hf : S.IsGen f) (hh : S.IsGen h)
    (f1 : S.P.src f = x) (h1 : S.P.src h = x) (hqf : S.q x * ⌜f⌝ ≠ 0) (hqh : S.q x * ⌜h⌝ ≠ 0)
    (hfS : ¬ S.InS x (S.P.tgt f)) (hhS : ¬ S.InS x (S.P.tgt h)) :
    S.P.RF f h ∨ S.P.RF h f := by
  by_contra hc
  obtain ⟨nfh, nhf⟩ := not_or.1 hc
  have hqx : S.q x ≠ 0 := fun h' ↦ hq2 (by rw [h', zero_pow two_ne_zero])
  obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases x).resolve_left hqx
  replace hq0 : S.q x = ⌜q0⌝ := hq0
  have hq00 : ⌜q0⌝ * ⌜q0⌝ ≠ 0 := by rw [← hq0, ← pow_two]; exact hq2
  obtain ⟨q2, hq2r⟩ := S.ray_of_mul_ne hq00
  rw [hq0] at hqf hqh
  obtain ⟨qf, hqfr⟩ := S.ray_of_mul_ne hqf
  obtain ⟨qh, hqhr⟩ := S.ray_of_mul_ne hqh
  have hd0 : 0 < S.P.deg (S.P.wt q0) := S.P.deg_pos q0 (by rw [q01]; exact q03)
  have hfx : S.P.tgt f ≠ x := fun e ↦ hfS (Or.inl e)
  have hhx : S.P.tgt h ≠ x := fun e ↦ hhS (Or.inl e)
  have hdf : 0 < S.P.deg (S.P.wt f) := S.deg_pos_of_ne (by rw [f1]; exact fun e ↦ hfx e.symm)
  have hdh : 0 < S.P.deg (S.P.wt h) := S.deg_pos_of_ne (by rw [h1]; exact fun e ↦ hhx e.symm)
  obtain ⟨a1, -, -, a4⟩ := S.prod_of hq2r
  obtain ⟨b1, -, -, b4⟩ := S.prod_of hqfr
  obtain ⟨c1, -, -, c4⟩ := S.prod_of hqhr
  have ndeg : ∀ a b : R, S.P.deg (S.P.wt b) < S.P.deg (S.P.wt a) → ¬ S.P.RF a b :=
    fun a b hlt hab ↦ absurd (S.rf_deg_le hab) (not_le.2 hlt)
  have hdeg := fun r : R ↦ S.P.deg_nonneg r
  -- leaves are pairwise incomparable
  have nleaf : ∀ {g g' : R} {qg qg' : R}, ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ⌜q0⌝ * ⌜g'⌝ = ⌜qg'⌝ →
      ¬ S.P.RF g g' → ¬ S.P.RF qg qg' := by
    intro g g' qg qg' hg hg' n hr
    rw [S.rf_iff] at hr
    obtain ⟨v, hv⟩ := hr
    rw [← hg, ← hg', mul_assoc] at hv
    have hgv : ⌜g⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne qg' (by rw [← hg', ← hv, h', mul_zero])
    obtain ⟨z, hz⟩ := S.ray_of_mul_ne hgv
    rw [hz] at hv
    exact n ((S.rf_iff _ _).2 ⟨v, by rw [hz, S.cancel_left hv (by rw [hv, hg']; exact S.rr_ne _)]⟩)
  -- `q_x² ≤ q_x g` makes `g` proper
  have nq2 : ∀ {g qg : R}, S.IsGen g → S.P.src g = x → ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ¬ S.P.RF q2 qg := by
    intro g qg hg g1 hgq hr
    rw [S.rf_iff] at hr
    obtain ⟨v, hv⟩ := hr
    rw [← hq2r, ← hgq, mul_assoc] at hv
    have hqv : ⌜q0⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne qg (by rw [← hgq, ← hv, h', mul_zero])
    obtain ⟨z, hz⟩ := S.ray_of_mul_ne hqv
    rw [hz] at hv
    have := S.cancel_left hv (by rw [hv, hgq]; exact S.rr_ne _)
    subst this
    obtain ⟨-, z2, z3, -⟩ := S.prod_of hz
    exact S.gen_ne_q_mul hg (b := v) (by rw [← z3, q02, g1]) z2.symm 1 le_rfl
      (by rw [← hz, pow_one, g1, hq0])
  -- `q_x g ≤ q_x²` puts the target of `g` in `S_x`
  have nqg : ∀ {g qg : R}, S.P.src g = x → S.P.tgt g ≠ x → ¬ S.InS x (S.P.tgt g) →
      ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ¬ S.P.RF qg q2 := by
    intro g qg g1 gx gS hgq hr
    rw [S.rf_iff] at hr
    obtain ⟨v, hv⟩ := hr
    rw [← hq2r, ← hgq, mul_assoc] at hv
    have hgv : ⌜g⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne q2 (by rw [← hq2r, ← hv, h', mul_zero])
    obtain ⟨z, hz⟩ := S.ray_of_mul_ne hgv
    rw [hz] at hv
    have := S.cancel_left hv (by rw [hv]; exact hq00)
    subst this
    exact gS (Or.inr (S.partner_of_factor g1 rfl gx (by rw [hz, ← hq0]) hq2 hprim).2.2.2.2)
  refine S.P.star4_false k hfin x (S.P.e x) q0 q2 qf qh
    ⟨S.P.src_e x, q01, by rw [a1, q01], by rw [b1, q01], by rw [c1, q01]⟩
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [S.rf_iff]; exact ⟨q0, by rw [← q01]; exact S.e_mul_rr q0⟩
  · rw [S.rf_iff]; exact ⟨q0, hq2r⟩
  · rw [S.rf_iff]; exact ⟨f, hqfr⟩
  · rw [S.rf_iff]; exact ⟨h, hqhr⟩
  · exact ndeg _ _ (by rw [S.P.wt_e, map_zero]; exact hd0)
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    refine ⟨⟨ndeg _ _ ?_, ndeg _ _ ?_⟩, ⟨ndeg _ _ ?_, ndeg _ _ ?_⟩, ⟨ndeg _ _ ?_, ndeg _ _ ?_⟩⟩ <;>
      simp only [S.P.wt_e, map_zero, a4, b4, c4, map_add] <;> linarith
  · exact nq2 hf f1 hqfr
  · exact nq2 hh h1 hqhr
  · exact nqg f1 hfx hfS hqfr
  · exact nleaf hqfr hqhr nfh
  · exact nqg h1 hhx hhS hqhr
  · exact nleaf hqhr hqfr nhf

/-- **Lemma 8.21(2), the chain** (`lem:primitive-cyclic-corners`(2)): the generating outgoing
rays of `x` with primitive reverses and surviving equal actions `q_x f = f q_y ≠ 0` are
comparable under factorization ("incomparability would be a crown"). -/
theorem partner_chain (hfin : IsRepresentationFinite k (S.P.Lin k)) {x : V} {f f' h h' : R}
    (hf : S.IsGen f) (hf' : S.IsGen f') (f1 : S.P.src f = x) (f1' : S.P.src f' = x)
    (hfh : S.PrimRev f h) (hfh' : S.PrimRev f' h')
    (hq : S.q x * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f)) (hq0 : S.q x * ⌜f⌝ ≠ 0)
    (hq' : S.q x * ⌜f'⌝ = ⌜f'⌝ * S.q (S.P.tgt f')) (hq0' : S.q x * ⌜f'⌝ ≠ 0) :
    S.P.RF f f' ∨ S.P.RF f' f := by
  by_contra hc
  obtain ⟨n12, n21⟩ := not_or.1 hc
  have hqx : S.q x ≠ 0 := fun h0 ↦ hq0 (by rw [h0, zero_mul])
  obtain ⟨q0, hq0r, q01, q02, q03⟩ := (S.q_cases x).resolve_left hqx
  replace hq0r : S.q x = ⌜q0⌝ := hq0r
  rw [hq0r] at hq hq0 hq' hq0'
  obtain ⟨qf, hqf⟩ := S.ray_of_mul_ne hq0
  obtain ⟨qf', hqf'⟩ := S.ray_of_mul_ne hq0'
  have hd0 : 0 < S.P.deg (S.P.wt q0) := S.P.deg_pos q0 (by rw [q01]; exact q03)
  obtain ⟨a1, -, -, a4⟩ := S.prod_of hqf
  obtain ⟨b1, -, -, b4⟩ := S.prod_of hqf'
  -- `q_x = f h = f' h'`
  have hx : ⌜q0⌝ = ⌜f⌝ * ⌜h⌝ := by rw [← hq0r, ← f1]; exact hfh.1.symm
  have hx' : ⌜q0⌝ = ⌜f'⌝ * ⌜h'⌝ := by rw [← hq0r, ← f1']; exact hfh'.1.symm
  -- the four comparisons of the crown
  have up : ∀ {g g' hg : R} {qg' : R}, ⌜q0⌝ = ⌜g⌝ * ⌜hg⌝ → ⌜q0⌝ * ⌜g'⌝ = ⌜qg'⌝ → S.P.RF g qg' := by
    intro g g' hg qg' hx hqg
    rw [hx, mul_assoc] at hqg
    have hne : ⌜hg⌝ * ⌜g'⌝ ≠ 0 := fun h0 ↦ S.rr_ne qg' (by rw [← hqg, h0, mul_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hne
    rw [ht] at hqg
    exact (S.rf_iff _ _).2 ⟨t, hqg⟩
  -- upper points are not below each other
  have nup : ∀ {g g' qg qg' : R}, ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ⌜q0⌝ * ⌜g'⌝ = ⌜qg'⌝ → ¬ S.P.RF g g' →
      ¬ S.P.RF qg qg' := by
    intro g g' qg qg' hg hg' n hr
    rw [S.rf_iff] at hr
    obtain ⟨v, hv⟩ := hr
    rw [← hg, ← hg', mul_assoc] at hv
    have hgv : ⌜g⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne qg' (by rw [← hg', ← hv, h', mul_zero])
    obtain ⟨z, hz⟩ := S.ray_of_mul_ne hgv
    rw [hz] at hv
    exact n ((S.rf_iff _ _).2 ⟨v, by rw [hz, S.cancel_left hv (by rw [hv, hg']; exact S.rr_ne _)]⟩)
  -- an upper point below a lower point factors a generating ray through `q_x`
  have nlow : ∀ {g g' qg : R}, S.IsGen g' → S.P.src g' = x → ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ →
      ¬ S.P.RF qg g' := by
    intro g g' qg hg' g1' hqg hr
    rw [S.rf_iff] at hr
    obtain ⟨v, hv⟩ := hr
    rw [← hqg, mul_assoc] at hv
    have hgv : ⌜g⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.rr_ne g' (by rw [← hv, h', mul_zero])
    obtain ⟨z, hz⟩ := S.ray_of_mul_ne hgv
    rw [hz] at hv
    obtain ⟨-, z2, z3, -⟩ := S.prod_of hv
    exact S.gen_ne_q_mul hg' (b := z) (by rw [← z3, q02, g1']) z2.symm 1 le_rfl
      (by rw [← hv, pow_one, g1', hq0r])
  have hdeg : ∀ {g qg : R}, ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ¬ S.P.RF qg g := by
    intro g qg hg hr
    have := S.rf_deg_le hr
    obtain ⟨-, -, -, e4⟩ := S.prod_of hg
    rw [e4, map_add] at this
    linarith
  refine S.P.crown_false k hfin x f f' qf qf' ⟨f1, f1', by rw [a1, q01], by rw [b1, q01]⟩
    (up hx hqf) (up hx hqf') (up hx' hqf) (up hx' hqf') n12 n21
    (nup hqf hqf' n12) (nup hqf' hqf n21) (hdeg hqf) (nlow hf' f1' hqf) (nlow hf f1 hqf')
    (hdeg hqf')

omit [IsAlgClosed k] in
/-- **The comparison pair** (`lem:primitive-cyclic-corners`(3)): for partners `b, c` of `a`
with `v = ut`, the rays `t : b → c` and `h = v̄u : c → b` satisfy `th = q_b`, `ht = q_c`. -/
theorem pair_of_rf {a : V} {u u' v v' t : R} (u1 : S.P.src u = a) (v1 : S.P.src v = a)
    (hu : S.PrimRev u u') (hv : S.PrimRev v v')
    (hqu : S.q a * ⌜u⌝ = ⌜u⌝ * S.q (S.P.tgt u)) (hqu0 : S.q a * ⌜u⌝ ≠ 0)
    (hqv : S.q a * ⌜v⌝ = ⌜v⌝ * S.q (S.P.tgt v)) (hqv0 : S.q a * ⌜v⌝ ≠ 0)
    (hut : ⌜u⌝ * ⌜t⌝ = ⌜v⌝) :
    ∃ h, S.P.src t = S.P.tgt u ∧ S.P.tgt t = S.P.tgt v ∧ ⌜t⌝ * ⌜h⌝ = S.q (S.P.tgt u) ∧
      ⌜h⌝ * ⌜t⌝ = S.q (S.P.tgt v) := by
  obtain ⟨-, t2, t3, -⟩ := S.prod_of hut
  have hqa : S.q a ≠ 0 := fun h0 ↦ hqu0 (by rw [h0, zero_mul])
  have hqb : S.q (S.P.tgt u) ≠ 0 := fun h0 ↦ hqu0 (by rw [hqu, h0, mul_zero])
  have hqc : S.q (S.P.tgt v) ≠ 0 := fun h0 ↦ hqv0 (by rw [hqv, h0, mul_zero])
  have hu1 : ⌜u⌝ * ⌜u'⌝ = S.q a := by rw [← u1]; exact hu.1
  have hv1 : ⌜v⌝ * ⌜v'⌝ = S.q a := by rw [← v1]; exact hv.1
  -- `h = v̄ u`
  have hvu : ⌜v'⌝ * ⌜u⌝ ≠ 0 := by
    intro h0; apply hqc; rw [← hv.2, ← hut, ← mul_assoc, h0, zero_mul]
  obtain ⟨h, hh⟩ := S.ray_of_mul_ne hvu
  have hht : ⌜h⌝ * ⌜t⌝ = S.q (S.P.tgt v) := by rw [← hh, mul_assoc, hut]; exact hv.2
  obtain ⟨-, h2, -, -⟩ := S.prod_of hh
  -- `t h` is a nonzero loop at `b`
  have hth0 : ⌜t⌝ * ⌜h⌝ ≠ 0 := by
    have e : S.q a * ⌜u⌝ = ⌜u⌝ * (⌜t⌝ * ⌜h⌝) := by
      rw [← mul_assoc, hut, ← hh, ← mul_assoc, hv1]
    intro h0; apply hqu0; rw [e, h0, mul_zero]
  obtain ⟨w, hw⟩ := S.ray_of_mul_ne hth0
  obtain ⟨w1, w2, -, w4⟩ := S.prod_of hw
  have hwl : S.P.src w = S.P.tgt w := by rw [w1, w2, h2, t3]
  obtain ⟨n, hn, hnw⟩ := S.local_eq w hwl
  -- characters
  have hχb : S.χ a = S.χ (S.P.tgt u) := by
    obtain ⟨e1, e2⟩ := S.χ_pair (t := u) (h := u') (by rw [u1]; exact hu1) hu.2
      (by rw [u1]; exact hqa) hqb
    rw [← u1, e1, e2, add_comm]
  have hχc : S.χ a = S.χ (S.P.tgt v) := by
    obtain ⟨e1, e2⟩ := S.χ_pair (t := v) (h := v') (by rw [v1]; exact hv1) hv.2
      (by rw [v1]; exact hqa) hqc
    rw [← v1, e1, e2, add_comm]
  have hht0 : ⌜h⌝ * ⌜t⌝ ≠ 0 := by rw [hht]; exact hqc
  obtain ⟨s', hs'⟩ := S.ray_of_mul_ne hht0
  have hχc' : S.χ (S.P.tgt v) = S.P.wt h + S.P.wt t := by
    rw [χ, ← hht, hs', wtM_rr]; exact (S.prod_of hs').2.2.2
  rw [w1, ← t3] at hn hnw
  have hd := S.χ_deg_pos (S.P.tgt u) hqb
  have hn1 : n = 1 := by
    have e : (n : ℤ) * S.P.deg (S.χ (S.P.tgt u)) = S.P.deg (S.χ (S.P.tgt u)) := by
      have := congrArg S.P.deg hnw
      rw [w4, map_nsmul, nsmul_eq_mul, map_add] at this
      rw [← this, ← hχb, hχc, hχc', map_add, add_comm]
    have : (n : ℤ) = 1 := by
      have := mul_right_cancel₀ hd.ne' (e.trans (one_mul _).symm)
      exact this
    exact_mod_cast this
  subst hn1
  refine ⟨h, t3.symm, t2.symm, ?_, hht⟩
  rw [hw, ← hn, pow_one, S.q_mul_e]

omit [IsAlgClosed k] in
theorem partners_of_rf {a b c : V} (hbc : b ≠ c)
    (h3 : S.q b ^ 2 ≠ 0 ∨ S.q c ^ 2 ≠ 0) {u v : R} (u1 : S.P.src u = a) (u2 : S.P.tgt u = b)
    (v1 : S.P.src v = a) (v2 : S.P.tgt v = c) {u' v' : R} (hu : S.PrimRev u u')
    (hv : S.PrimRev v v') (hqu : S.q a * ⌜u⌝ = ⌜u⌝ * S.q b) (hqu0 : S.q a * ⌜u⌝ ≠ 0)
    (hqv : S.q a * ⌜v⌝ = ⌜v⌝ * S.q c) (hqv0 : S.q a * ⌜v⌝ ≠ 0) (hr : S.P.RF u v) :
    S.Partner b c ∧ S.Partner c b := by
  obtain ⟨t, ht⟩ := hr
  have hut : ⌜u⌝ * ⌜t⌝ = ⌜v⌝ := S.P.rr_mul_rr_eq_rr.2 ht
  subst u2 v2
  obtain ⟨h, t1, t2, hth, hht⟩ := S.pair_of_rf u1 v1 hu hv hqu hqu0 hqv hqv0 hut
  have hqb : S.q (S.P.tgt u) ≠ 0 := fun h0 ↦ hqu0 (by rw [hqu, h0, mul_zero])
  have hqc : S.q (S.P.tgt v) ≠ 0 := fun h0 ↦ hqv0 (by rw [hqv, h0, mul_zero])
  have hbc' : S.P.src t ≠ S.P.tgt t := by rw [t1, t2]; exact hbc
  have hth' : ⌜t⌝ * ⌜h⌝ = S.q (S.P.src t) := by rw [t1]; exact hth
  have hht' : ⌜h⌝ * ⌜t⌝ = S.q (S.P.tgt t) := by rw [t2]; exact hht
  have hqb' : S.q (S.P.src t) ≠ 0 := by rw [t1]; exact hqb
  have hqc' : S.q (S.P.tgt t) ≠ 0 := by rw [t2]; exact hqc
  have h3' : S.q (S.P.src t) ^ 2 ≠ 0 ∨ S.q (S.P.tgt t) ^ 2 ≠ 0 := by rw [t1, t2]; exact h3
  have h1 : S.P.src h = S.P.tgt t :=
    (S.src_of_mul_ne (show ⌜t⌝ * ⌜h⌝ ≠ 0 by rw [hth']; exact hqb')).symm
  have h2 : S.P.tgt h = S.P.src t := S.src_of_mul_ne (show ⌜h⌝ * ⌜t⌝ ≠ 0 by rw [hht']; exact hqc')
  have hP := S.partner_of_pair hbc' hth' hht' hqb' hqc' h3'
  have hP' := S.partner_of_pair (t := h) (h := t) (by rw [h1, h2]; exact fun e ↦ hbc' e.symm)
    (by rw [h1]; exact hht') (by rw [h2]; exact hth') (by rw [h1]; exact hqc') (by rw [h2]; exact hqb')
    (by rw [h1, h2]; exact h3'.symm)
  rw [t1, t2] at hP
  rw [h1, h2, t1, t2] at hP'
  exact ⟨hP, hP'⟩

/-- **Two partners of `a` are mutual partners** when one has local length at least three
(`lem:primitive-cyclic-corners`(3), first paragraph). -/
theorem partner_comparison (hfin : IsRepresentationFinite k (S.P.Lin k)) {a b c : V}
    (hb : S.Partner a b) (hc : S.Partner a c) (hbc : b ≠ c) (h3 : S.q b ^ 2 ≠ 0 ∨ S.q c ^ 2 ≠ 0) :
    S.Partner b c ∧ S.Partner c b := by
  obtain ⟨-, u, u', hgu, u1, u2, hu, hqu, hqu0⟩ := hb
  obtain ⟨-, v, v', hgv, v1, v2, hv, hqv, hqv0⟩ := hc
  rcases S.partner_chain k hfin hgu hgv u1 v1 hu hv (by rw [u2]; exact hqu) hqu0
    (by rw [v2]; exact hqv) hqv0 with hr | hr
  · exact S.partners_of_rf hbc h3 u1 u2 v1 v2 hu hv hqu hqu0 hqv hqv0 hr
  · exact (S.partners_of_rf (Ne.symm hbc) h3.symm v1 v2 u1 u2 hv hu hqv hqv0 hqu hqu0 hr).symm

omit [IsAlgClosed k] in
/-- **`a` is a partner of its partner `b`** when `N_a ≥ 3` (`q_b ū = ū q_a ≠ 0`). -/
theorem partner_symm {a b : V} (hb : S.Partner a b) (h3 : S.q a ^ 2 ≠ 0) : S.Partner b a := by
  obtain ⟨hba, u, u', -, u1, u2, ⟨hu1, hu2⟩, hqu, hqu0⟩ := hb
  have hqa : S.q a ≠ 0 := fun h0 ↦ hqu0 (by rw [h0, zero_mul])
  have hqb : S.q b ≠ 0 := fun h0 ↦ hqu0 (by rw [hqu, h0, mul_zero])
  rw [u1] at hu1
  rw [u2] at hu2
  have e1 : S.P.src u' = b := by
    rw [← u2]; exact (S.src_of_mul_ne (show ⌜u⌝ * ⌜u'⌝ ≠ 0 by rw [hu1]; exact hqa)).symm
  have e2 : S.P.tgt u' = a := by
    rw [← u1]; exact S.src_of_mul_ne (show ⌜u'⌝ * ⌜u⌝ ≠ 0 by rw [hu2]; exact hqb)
  have hP := S.partner_of_pair (t := u') (h := u) (by rw [e1, e2]; exact hba)
    (by rw [e1]; exact hu2) (by rw [e2]; exact hu1) (by rw [e1]; exact hqb) (by rw [e2]; exact hqa)
    (Or.inr (by rw [e2]; exact h3))
  rwa [e1, e2] at hP

/-- **`V_a ⊆ V_b`** for a partner `b` of `a` with `N_a, N_b ≥ 3`. -/
theorem inS_subset (hfin : IsRepresentationFinite k (S.P.Lin k)) {a b : V} (hb : S.Partner a b)
    (ha3 : S.q a ^ 2 ≠ 0) (hb3 : S.q b ^ 2 ≠ 0) {c : V} (hc : S.InS a c) : S.InS b c := by
  rcases hc with rfl | hc
  · exact Or.inr (S.partner_symm hb ha3)
  · by_cases hbc : b = c
    · exact Or.inl hbc.symm
    · exact Or.inr (S.partner_comparison k hfin hb hc hbc (Or.inl hb3)).1

/-- **`V_a = V_b`** for a partner `b` of `a` with `N_a, N_b ≥ 3`. -/
theorem inS_eq (hfin : IsRepresentationFinite k (S.P.Lin k)) {a b : V} (hb : S.Partner a b)
    (ha3 : S.q a ^ 2 ≠ 0) (hb3 : S.q b ^ 2 ≠ 0) (c : V) : S.InS a c ↔ S.InS b c :=
  ⟨S.inS_subset k hfin hb ha3 hb3, S.inS_subset k hfin (S.partner_symm hb ha3) hb3 ha3⟩

/-- **Lemma 8.21(3)** (`lem:primitive-cyclic-corners`(3)): for vertices `x, x'` with
`N_x, N_{x'} ≥ 3`, the vertex sets `V_x, V_{x'}` of the primitive return corners are disjoint or
equal. (Primitivity is not needed for this part; with it, every nontrivial factorization of
`q_x` passes through `S_x`, `partner_of_factor`.) -/
theorem inS_disjoint_or_eq (hfin : IsRepresentationFinite k (S.P.Lin k)) {x x' : V}
    (hx3 : S.q x ^ 2 ≠ 0) (hx3' : S.q x' ^ 2 ≠ 0) {v : V} (hv : S.InS x v) (hv' : S.InS x' v) :
    ∀ y, S.InS x y ↔ S.InS x' y := by
  rcases hv with rfl | hv
  · rcases hv' with h | hv'
    · subst h; exact fun y ↦ Iff.rfl
    · exact fun y ↦ (S.inS_eq k hfin hv' hx3' hx3 y).symm
  · rcases hv' with rfl | hv'
    · exact S.inS_eq k hfin hv hx3 hx3'
    · by_cases hv3 : S.q v ^ 2 ≠ 0
      · exact fun y ↦ (S.inS_eq k hfin hv hx3 hv3 y).trans (S.inS_eq k hfin hv' hx3' hv3 y).symm
      · by_cases hxx : x = x'
        · subst hxx; exact fun y ↦ Iff.rfl
        · have hP := (S.partner_comparison k hfin (S.partner_symm hv hx3) (S.partner_symm hv' hx3')
            hxx (Or.inl hx3)).1
          exact S.inS_eq k hfin hP hx3 hx3'

omit [IsAlgClosed k] in
theorem loop_of_eq_q {x : V} {t : R} (ht : ⌜t⌝ = S.q x) : S.P.src t = x ∧ S.P.tgt t = x := by
  have hqx : S.q x ≠ 0 := ht ▸ S.rr_ne t
  obtain ⟨q0, hq0, q01, q02, -⟩ := (S.q_cases x).resolve_left hqx
  have : t = q0 := S.rr_inj (ht.trans hq0)
  subst this; exact ⟨q01, q02⟩

omit [IsAlgClosed k] in
/-- Return partners agree for `A₀` and `A₀ᵒᵖ` when `q_x² ≠ 0`. -/
theorem op_partner_iff {x y : V} (hq2 : S.q x ^ 2 ≠ 0) (hprim : Prim (S.χ x)) :
    S.op.Partner x y ↔ S.Partner x y := by
  have hq2' : S.op.q x ^ 2 ≠ 0 := by rw [op_q, ← Tab.toOp_pow]; exact hq2
  have hprim' : Prim (S.op.χ x) := by rw [op_χ]; exact hprim
  constructor
  · rintro ⟨hxy, f, h, -, f1, f2, ⟨hfh, -⟩, -, -⟩
    change S.P.tgt f = x at f1
    change S.P.src f = y at f2
    have hhf : ⌜h⌝ * ⌜f⌝ = S.q x := by
      apply S.P.toOp_injective
      rw [Tab.toOp_mul]; change S.op.rr f * S.op.rr h = S.op.q x; rw [hfh]; change S.op.q (S.P.tgt f) = _; rw [f1]
    have hqx : S.q x ≠ 0 := fun h0 ↦ hq2 (by rw [h0, zero_pow two_ne_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne (hhf ▸ hqx : ⌜h⌝ * ⌜f⌝ ≠ 0)
    obtain ⟨t1, -, t3, -⟩ := S.prod_of ht
    obtain ⟨l1, -⟩ := S.loop_of_eq_q (ht.symm.trans hhf)
    exact (S.partner_of_factor (by rw [← t1, l1]) (by rw [t3, f2]) hxy hhf hq2 hprim).2.2.2.2
  · rintro ⟨hxy, f, h, -, f1, f2, ⟨hfh, -⟩, -, -⟩
    have hhf : S.op.rr h * S.op.rr f = S.op.q x := by
      change S.P.toOp ⌜h⌝ * S.P.toOp ⌜f⌝ = S.P.toOp (S.q x)
      rw [← Tab.toOp_mul, hfh, f1]
    have hqx : S.q x ≠ 0 := fun h0 ↦ hq2 (by rw [h0, zero_pow two_ne_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne (hfh ▸ f1 ▸ hqx : ⌜f⌝ * ⌜h⌝ ≠ 0)
    obtain ⟨-, t2, t3, -⟩ := S.prod_of ht
    obtain ⟨-, l2⟩ := S.loop_of_eq_q (ht.symm.trans (hfh.trans (by rw [f1])))
    exact (S.op.partner_of_factor (u := h) (v := f) (by change S.P.tgt h = x; rw [← t2, l2])
      (by change S.P.src h = y; rw [← t3, f2]) hxy hhf hq2' hprim').2.2.2.2

omit [IsAlgClosed k] in
theorem op_inS_iff {x y : V} (hq2 : S.q x ^ 2 ≠ 0) (hprim : Prim (S.χ x)) :
    S.op.InS x y ↔ S.InS x y := by
  unfold InS; rw [S.op_partner_iff hq2 hprim]

/-- **Lemma 9.8, incoming form.** -/
theorem ext_chain_in (hfin : IsRepresentationFinite k (S.P.Lin k)) {x : V}
    (hprim : Prim (S.χ x)) (hq2 : S.q x ^ 2 ≠ 0) {f h : R} (hf : S.IsGen f) (hh : S.IsGen h)
    (f2 : S.P.tgt f = x) (h2 : S.P.tgt h = x) (hqf : ⌜f⌝ * S.q x ≠ 0) (hqh : ⌜h⌝ * S.q x ≠ 0)
    (hfS : ¬ S.InS x (S.P.src f)) (hhS : ¬ S.InS x (S.P.src h)) :
    S.P.LF f h ∨ S.P.LF h f := by
  have hq2' : S.op.q x ^ 2 ≠ 0 := by rw [op_q, ← Tab.toOp_pow]; exact hq2
  have := S.op.ext_chain k (S.P.op_isRepresentationFinite k hfin) (by rw [op_χ]; exact hprim)
    hq2' ((S.op_isGen_iff f).2 hf) ((S.op_isGen_iff h).2 hh) f2 h2
    (by rw [op_q, op_rr, ← Tab.toOp_mul]; exact hqf) (by rw [op_q, op_rr, ← Tab.toOp_mul]; exact hqh)
    (by rw [S.op_inS_iff hq2 hprim]; exact hfS) (by rw [S.op_inS_iff hq2 hprim]; exact hhS)
  rcases this with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

end Sys

end RaySys

end MultiplicativeBasisDeformations
