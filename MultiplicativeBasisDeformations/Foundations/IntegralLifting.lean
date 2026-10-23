module

public import MultiplicativeBasisDeformations.Foundations.CrownRows

/-!
# Integral lifting of the nonzero-product Leibniz equations (Theorem 9.1(3))

`thm:integral-partial-lifting`(3) and `lem:one-sided-path-coefficients`
(`integral-partial-lifts.tex`). The equations `eq:partial-leibniz-group` are encoded by
`IsSol`: a coefficient `d r` for each ray, zero on unshiftable rays, with
`d t = ε_L d r + ε_R d s` on every nonzero product `rs = t` with shiftable output.

Deviation: only part (3) is used (`cor:zero-supported-coverage`), and it is proved directly:
from a solution modulo two we build an integer solution, by the coefficient formulas of the
proof of Theorem 9.1 — the two-sided part from a lift `ω` of its restriction to the
two-sided rays (the freeness of `W_χ`, from the induction hypothesis, enters only here),
the coefficients of generating one-sided rays by the first-arrow recursion
(`lem:one-sided-path-coefficients`, with paths replaced by unique first arrows), canonical
integer lifts `X_a`, and `Y_b` read off from the rows (Lemma 9.5).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

-- Keep `ZMod 2` on its ring structure: Mathlib's instance making simple nilpotent groups
-- commutative would otherwise give `ZMod 2` a second, non-reducibly-equal additive structure.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

variable (χ : L)

open Classical in
/-- **The nonzero-product Leibniz equations** (`eq:partial-leibniz-group`). -/
def IsSol {M : Type*} [AddCommGroup M] (d : R → M) : Prop :=
  (∀ r, ¬ S.Shift χ r → d r = 0) ∧
    ∀ r s t, ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → S.Shift χ t →
      d t = (if S.EL χ r s t then d r else 0) + (if S.ER χ r s t then d s else 0)

/-! ### The first-arrow recursion -/

open Classical in
/-- A chosen first arrow (an ordinary left divisor) of a nonidentity ray. -/
def fstA (r : R) : R :=
  if h : r ≠ S.P.e (S.P.src r) then (S.exists_OL r h).choose else r

open Classical in
/-- The rest of a ray after its chosen first arrow. -/
def fstRest (r : R) : R :=
  if h : ∃ w, ⌜S.fstA r⌝ * ⌜w⌝ = ⌜r⌝ then h.choose else r

theorem fstA_spec {r : R} (h : r ≠ S.P.e (S.P.src r)) : S.OL r (S.fstA r) := by
  classical
  rw [fstA, dif_pos h]; exact (S.exists_OL r h).choose_spec

theorem fstRest_spec {r : R} (h : r ≠ S.P.e (S.P.src r)) :
    ⌜S.fstA r⌝ * ⌜S.fstRest r⌝ = ⌜r⌝ := by
  classical
  have h' : ∃ w, ⌜S.fstA r⌝ * ⌜w⌝ = ⌜r⌝ := (S.fstA_spec h).2
  rw [fstRest, dif_pos h']; exact h'.choose_spec

open Classical in
/-- The recursion with fuel. -/
def DLf (ω X : R → ℤ) : ℕ → R → ℤ
  | 0, _ => 0
  | n + 1, r => if S.TB χ (S.fstA r) then ω (S.fstA r) + DLf ω X n (S.fstRest r) else X (S.fstA r)

/-- **The coefficient of a generating left-sided ray** (`eq:one-sided-path-coefficients`):
`d_r = [p] + X_a` for the two-sided prefix `p` and the first left-sided arrow `a`. -/
def DL (ω X : R → ℤ) (r : R) : ℤ := S.DLf χ ω X ((S.P.deg (S.P.wt r)).toNat + 1) r

variable {χ}

variable (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem dim2_of_TL {r : R} (hT : S.TL χ r) : S.Dim2 r := by
  left; rw [← S.qh_of_supp χ (S.supp_of_qh hT.2.1)]; exact hT.2.1

/-- The rest after a two-sided first arrow of a generating left-sided ray is generating and
left-sided, of smaller degree. -/
theorem rest_TL (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r a w : R} (hr : S.IsGen r) (hT : S.TL χ r) (ha : S.Ord a)
    (hB : S.TB χ a) (hw : ⌜a⌝ * ⌜w⌝ = ⌜r⌝) :
    S.IsGen w ∧ S.TL χ w ∧ S.P.deg (S.P.wt w) < S.P.deg (S.P.wt r) := by
  have hw0 : w ≠ S.P.e (S.P.src w) := by
    intro he
    have := S.src_of_mul_ne (by rw [hw]; exact S.rr_ne r)
    rw [he, ← this, S.rr_mul_e] at hw
    rw [← S.rr_inj hw] at hT
    exact hB.2.2 hT.2.2
  refine ⟨S.gen_factor k hfin hr (S.dim2_of_TL hT) (a := a) (m := w) (b := S.P.e (S.P.tgt r))
    (by rw [hw, S.rr_mul_e]), ?_, ?_⟩
  · rcases S.table_L hχ hprim ha.1 hw0 hw hT with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd hB.2.2 (by rw [h.2.2]; exact fun h' ↦ h' rfl)
    · exact h
  · rw [(S.prod_of hw).2.2.2, map_add]; have := S.P.deg_pos a ha.1; linarith

variable (ω X : R → ℤ)

omit [IsAlgClosed k] in
open Classical in
theorem DLf_succ (n : ℕ) (r : R) : S.DLf χ ω X (n + 1) r =
    if S.TB χ (S.fstA r) then ω (S.fstA r) + S.DLf χ ω X n (S.fstRest r) else X (S.fstA r) := by
  rw [DLf]

/-- Fuel independence. -/
theorem DLf_eq_DL (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r : R} (hr : S.IsGen r) (hT : S.TL χ r) (n : ℕ)
    (hn : (S.P.deg (S.P.wt r)).toNat + 1 ≤ n) : S.DLf χ ω X n r = S.DL χ ω X r := by
  induction hm : (S.P.deg (S.P.wt r)).toNat using Nat.strong_induction_on generalizing r n with
  | _ m ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt (show 0 < n by omega)
    unfold DL
    rw [zero_add, DLf_succ, hm, DLf_succ]
    split_ifs with hB
    · congr 1
      have hr0 : r ≠ S.P.e (S.P.src r) := hT.1.1
      obtain ⟨g, t, d⟩ := S.rest_TL k hfin hχ hprim hr hT (S.fstA_spec hr0).1 hB (S.fstRest_spec hr0)
      have hd := S.P.deg_nonneg (S.fstRest r)
      have e1 := ih _ (by omega) g t n (by omega) rfl
      have e2 := ih _ (by omega) g t m (by omega) rfl
      rw [e1, e2]
    · rfl

open Classical in
/-- **The first-arrow recursion.** -/
theorem DL_eq (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r a w : R} (hr : S.IsGen r) (hT : S.TL χ r) (ha : S.OL r a)
    (hw : ⌜a⌝ * ⌜w⌝ = ⌜r⌝) :
    S.DL χ ω X r = if S.TB χ a then ω a + S.DL χ ω X w else X a := by
  have hr0 : r ≠ S.P.e (S.P.src r) := hT.1.1
  have hfa : S.fstA r = a := S.unique_first k hfin hχ hprim hr hT (S.fstA_spec hr0) ha
  have hfw : S.fstRest r = w := by
    have := S.fstRest_spec hr0
    rw [hfa] at this
    exact S.cancel_left (this.trans hw.symm) (by rw [this]; exact S.rr_ne r)
  unfold DL
  rw [DLf_succ, hfa, hfw]
  split_ifs with hB
  · congr 1
    obtain ⟨g, t, d⟩ := S.rest_TL k hfin hχ hprim hr hT ha.1 hB hw
    have hd := S.P.deg_nonneg w
    exact S.DLf_eq_DL k ω X hfin hχ hprim g t _ (by omega)
  · rfl

/-- **Lemma 9.4** (`lem:one-sided-path-coefficients`), product equations with generating
left-sided output: `d_t = d_r` for a left-sided first factor, `d_t = d_r + d_s` for a
two-sided one. -/
theorem DL_prod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r u v : R} (hr : S.IsGen r) (hT : S.TL χ r) (huv : ⌜u⌝ * ⌜v⌝ = ⌜r⌝)
    (hu0 : u ≠ S.P.e (S.P.src u)) :
    (S.TL χ u → S.DL χ ω X r = S.DL χ ω X u) ∧
      (S.TB χ u → S.DL χ ω X r = ω u + S.DL χ ω X v) := by
  induction hm : (S.P.deg (S.P.wt r)).toNat using Nat.strong_induction_on generalizing r u v with
  | _ m ih =>
    obtain ⟨r1, -, r3, r4⟩ := S.prod_of huv
    have hug : S.IsGen u := S.gen_factor k hfin hr (S.dim2_of_TL hT) (a := S.P.e (S.P.src u))
      (m := u) (b := v) (by rw [S.e_mul_rr, huv])
    set a := S.fstA u with ha
    have hau : S.OL u a := S.fstA_spec hu0
    have hu' := S.fstRest_spec hu0
    rw [← ha] at hu'
    set u' := S.fstRest u with hu'd
    have hu'v : ⌜u'⌝ * ⌜v⌝ ≠ 0 := by
      intro h0; apply S.rr_ne r; rw [← huv, ← hu', mul_assoc, h0, mul_zero]
    obtain ⟨w', hw'⟩ := S.ray_of_mul_ne hu'v
    have haw' : ⌜a⌝ * ⌜w'⌝ = ⌜r⌝ := by rw [← hw', ← mul_assoc, hu', huv]
    have har : S.OL r a := ⟨hau.1, w', haw'⟩
    have hDLr := S.DL_eq k ω X hfin hχ hprim hr hT har haw'
    have hdv := S.P.deg_nonneg v
    have hda := S.P.deg_pos a hau.1.1
    have hdw' : S.P.deg (S.P.wt w') < S.P.deg (S.P.wt r) := by
      rw [(S.prod_of haw').2.2.2, map_add]; linarith
    constructor
    · intro hTu
      have hDLu := S.DL_eq k ω X hfin hχ hprim hug hTu hau hu'
      rw [hDLr, hDLu]
      split_ifs with hB
      · congr 1
        obtain ⟨g', t', -⟩ := S.rest_TL k hfin hχ hprim hug hTu hau.1 hB hu'
        obtain ⟨gw, tw, -⟩ := S.rest_TL k hfin hχ hprim hr hT hau.1 hB haw'
        exact (ih _ (by have := S.P.deg_nonneg w'; omega) gw tw hw' t'.1.1 rfl).1 t'
      · rfl
    · intro hBu
      have hv0 : v ≠ S.P.e (S.P.src v) := by
        intro he
        have := S.src_of_mul_ne (by rw [huv]; exact S.rr_ne r)
        rw [he, ← this, S.rr_mul_e] at huv
        rw [← S.rr_inj huv] at hT
        exact hBu.2.2 hT.2.2
      have hTv : S.TL χ v := by
        rcases S.table_L hχ hprim hu0 hv0 huv hT with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact absurd hBu.2.2 (by rw [h.2.2]; exact fun h' ↦ h' rfl)
        · exact h
      have hBa : S.TB χ a := S.first_TB hχ hprim hBu hTv huv hT.1 hau
      rw [hDLr, if_pos hBa]
      by_cases hue : u' = S.P.e (S.P.src u')
      · have h1 := S.src_of_mul_ne (by rw [hu']; exact S.rr_ne u)
        have hu'2 := hu'
        rw [hue, ← h1, S.rr_mul_e] at hu'2
        have hau' : a = u := S.rr_inj hu'2
        rw [hue, ← h1, S.e_mul_rr' v (by rw [hau', r3])] at hw'
        have := S.rr_inj hw'
        rw [← this, hau']
      · have hBu' : S.TB χ u' := by
          rcases (S.table_B hχ hprim hau.1.1 hue hu' hBu).1 with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · exact absurd hBa.2.2 (by rw [h.2.2]; exact fun h' ↦ h' rfl)
        obtain ⟨gw, tw, -⟩ := S.rest_TL k hfin hχ hprim hr hT hau.1 hBa haw'
        have := (ih _ (by have := S.P.deg_nonneg w'; omega) gw tw hw' hue rfl).2 hBu'
        rw [this, hω a u' u hBa hBu' hBu hu']; ring

/-! ### Endpoint layers of one-sided rays -/

omit [IsAlgClosed k] in
/-- A left-sided ray is a layer of a generating left-sided ray. -/
theorem layer_TL_exists (hprim : Prim χ) {t : R} (hT : S.TL χ t) :
    ∃ i t0, S.IsGen t0 ∧ S.TL χ t0 ∧ ⌜t⌝ = S.qh χ (S.P.src t) ^ i * ⌜t0⌝ := by
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen t
  have hs := S.supp_of_qh hT.2.1
  have hq : S.qh χ (S.P.src t) = S.q (S.P.src t) := S.qh_of_supp χ hs
  obtain ⟨a, c, hac⟩ := hg t g1.symm g2.symm
  have hqt : S.q (S.P.src t) * ⌜t⌝ ≠ 0 := by rw [← hq]; exact hT.2.1
  have hqg : S.q (S.P.src g) * ⌜g⌝ ≠ 0 := by
    intro h0; apply hqt; rw [hac, ← g1]
    simp only [← mul_assoc]; rw [← pow_succ', pow_succ, mul_assoc _ (S.q (S.P.src g)), h0]
    simp
  obtain ⟨hgL, -⟩ := S.prim_action_gen hg (by rw [g1, hs.2]; exact hprim) hqg
  obtain ⟨i, hi⟩ := hgL t g1.symm g2.symm
  rw [g1, ← hq] at hi
  have hg0 : g ≠ S.P.e (S.P.src g) := by
    intro he; apply S.tl_nonlocal hT
    rw [← g1, ← g2]; nth_rewrite 1 [he]; rw [S.P.tgt_e]
  exact ⟨i, g, hg, S.tl_factor hT hi hg0, hi⟩

omit [IsAlgClosed k] in
/-- Uniqueness of the layer decomposition. -/
theorem layer_TL_unique (hχ : 0 < S.P.deg χ) {t t0 t1 : R} {i j : ℕ} (hT : S.TL χ t)
    (h0 : S.IsGen t0) (h1 : S.IsGen t1) (hi : ⌜t⌝ = S.qh χ (S.P.src t) ^ i * ⌜t0⌝)
    (hj : ⌜t⌝ = S.qh χ (S.P.src t) ^ j * ⌜t1⌝) : i = j ∧ t0 = t1 := by
  have hs := S.supp_of_qh hT.2.1
  rw [S.qh_of_supp χ hs] at hi hj
  obtain ⟨a1, a2⟩ := S.qpow_mul_endpoints hi.symm
  obtain ⟨b1, b2⟩ := S.qpow_mul_endpoints hj.symm
  have := S.gen_unique h0 h1 (by rw [← a1, b1]) (by rw [← a2, b2])
  subst this
  refine ⟨?_, rfl⟩
  have w1 := S.wt_of_eq_qpow_mul (f := t0) (by rw [← a1]; exact hi)
  have w2 := S.wt_of_eq_qpow_mul (f := t0) (by rw [← a1]; exact hj)
  have := congrArg S.P.deg (w1.symm.trans w2)
  simp only [map_add, map_nsmul, nsmul_eq_mul] at this
  have hd := S.χ_deg_pos (S.P.src t0) (by rw [← a1]; exact hs.1)
  have : ((i : ℤ) - j) * S.P.deg (S.χ (S.P.src t0)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · omega
  · linarith

open Classical in
/-- A chosen local generator ray at `x`. -/
def qr (x : V) : R := if h : ∃ g, ⌜g⌝ = S.q x then h.choose else S.P.e x

theorem qr_spec {x : V} (h : S.q x ≠ 0) : ⌜S.qr x⌝ = S.q x := by
  classical
  have h' : ∃ g, ⌜g⌝ = S.q x := by
    obtain ⟨g, hg, -⟩ := (S.q_cases x).resolve_left h; exact ⟨g, hg.symm⟩
  rw [qr, dif_pos h']; exact h'.choose_spec

variable (χ) in
/-- The coefficient of a generating right-sided ray, by the last-arrow recursion. -/
def DR (ω Y : R → ℤ) (r : R) : ℤ := S.op.DL χ ω Y r

variable (χ) in
open Classical in
/-- **The integer coefficients** (`eq:one-sided-path-coefficients`,
`eq:proper-successor-coefficients`): `ω` on two-sided rays, `j[q̂] + d_{r₀}` on layers of
generating one-sided rays, zero on unshiftable rays. -/
def DD (ω X Y : R → ℤ) (t : R) : ℤ :=
  if S.TB χ t then ω t
  else if S.TL χ t then
    (if h : ∃ i : ℕ, ∃ t0, S.IsGen t0 ∧ S.TL χ t0 ∧ ⌜t⌝ = S.qh χ (S.P.src t) ^ i * ⌜t0⌝ then
      (h.choose : ℤ) * ω (S.qr (S.P.src t)) + S.DL χ ω X h.choose_spec.choose else 0)
  else if S.TR χ t then
    (if h : ∃ j : ℕ, ∃ t0, S.IsGen t0 ∧ S.TR χ t0 ∧ ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ j then
      S.DR χ ω Y h.choose_spec.choose + (h.choose : ℤ) * ω (S.qr (S.P.tgt t)) else 0)
  else 0

variable (Y : R → ℤ)

omit [IsAlgClosed k] in
theorem DD_TB {t : R} (h : S.TB χ t) : S.DD χ ω X Y t = ω t := by
  classical
  rw [DD, if_pos h]

omit [IsAlgClosed k] in
theorem DD_unshift {t : R} (h : ¬ S.Shift χ t) : S.DD χ ω X Y t = 0 := by
  classical
  rw [DD, if_neg (fun h' ↦ h h'.1), if_neg (fun h' ↦ h h'.1), if_neg (fun h' ↦ h h'.1)]

omit [IsAlgClosed k] in
theorem DD_TL (hχ : 0 < S.P.deg χ) {t t0 : R} {i : ℕ} (hT : S.TL χ t) (h0 : S.IsGen t0)
    (hi : ⌜t⌝ = S.qh χ (S.P.src t) ^ i * ⌜t0⌝) :
    S.DD χ ω X Y t = (i : ℤ) * ω (S.qr (S.P.src t)) + S.DL χ ω X t0 := by
  classical
  have hnB : ¬ S.TB χ t := fun h ↦ h.2.2 hT.2.2
  have hex : ∃ i : ℕ, ∃ t0, S.IsGen t0 ∧ S.TL χ t0 ∧ ⌜t⌝ = S.qh χ (S.P.src t) ^ i * ⌜t0⌝ := by
    refine ⟨i, t0, h0, ?_, hi⟩
    exact S.tl_factor hT hi (by
      intro he; apply S.tl_nonlocal hT
      have hs := S.supp_of_qh hT.2.1
      obtain ⟨a1, a2⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ hs]; exact hi.symm)
      rw [a1, a2]; nth_rewrite 1 [he]; rw [S.P.tgt_e])
  rw [DD, if_neg hnB, if_pos hT, dif_pos hex]
  obtain ⟨h1, -, h3⟩ := hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := S.layer_TL_unique hχ hT h1 h0 h3 hi
  congr 1
  · rw [e1]
  · rw [e2]

omit [IsAlgClosed k] in
theorem tr_nonlocal {t : R} (hT : S.TR χ t) : S.P.src t ≠ S.P.tgt t :=
  S.op.tl_nonlocal ((S.op_TL t).2 hT)

omit [IsAlgClosed k] in
theorem toOp_qh_pow (x : V) (n : ℕ) : S.P.toOp (S.qh χ x ^ n) = S.op.qh χ x ^ n := by
  rw [Tab.toOp_pow, S.op_qh]

omit [IsAlgClosed k] in
theorem op_layer {t t0 : R} {j : ℕ} (h : ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ j) :
    S.op.rr t = S.op.qh χ (S.op.P.src t) ^ j * S.op.rr t0 := by
  change S.P.toOp ⌜t⌝ = _
  rw [h, Tab.toOp_mul, S.toOp_qh_pow]; rfl

omit [IsAlgClosed k] in
theorem op_layer' {t t0 : R} {j : ℕ} (h : S.op.rr t = S.op.qh χ (S.op.P.src t) ^ j * S.op.rr t0) :
    ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ j := by
  apply S.P.toOp_injective
  rw [Tab.toOp_mul, S.toOp_qh_pow]; exact h

omit [IsAlgClosed k] in
theorem tr_factor {r r0 : R} {i : ℕ} (hT : S.TR χ r) (h : ⌜r⌝ = ⌜r0⌝ * S.qh χ (S.P.tgt r) ^ i)
    (hr0 : r0 ≠ S.P.e (S.P.src r0)) : S.TR χ r0 :=
  (S.op_TL r0).1 (S.op.tl_factor ((S.op_TL r).2 hT) (S.op_layer h)
    (by change r0 ≠ S.P.e (S.P.tgt r0); rwa [S.ne_e_iff_op]))

omit [IsAlgClosed k] in
theorem layer_TR_unique (hχ : 0 < S.P.deg χ) {t t0 t1 : R} {i j : ℕ} (hT : S.TR χ t)
    (h0 : S.IsGen t0) (h1 : S.IsGen t1) (hi : ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ i)
    (hj : ⌜t⌝ = ⌜t1⌝ * S.qh χ (S.P.tgt t) ^ j) : i = j ∧ t0 = t1 :=
  S.op.layer_TL_unique hχ ((S.op_TL t).2 hT) ((S.op_isGen_iff t0).2 h0)
    ((S.op_isGen_iff t1).2 h1) (S.op_layer hi) (S.op_layer hj)

omit [IsAlgClosed k] in
theorem layer_TR_exists (hprim : Prim χ) {t : R} (hT : S.TR χ t) :
    ∃ j t0, S.IsGen t0 ∧ S.TR χ t0 ∧ ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ j := by
  obtain ⟨j, t0, h1, h2, h3⟩ := S.op.layer_TL_exists hprim ((S.op_TL t).2 hT)
  exact ⟨j, t0, (S.op_isGen_iff t0).1 h1, (S.op_TL t0).1 h2, S.op_layer' h3⟩

omit [IsAlgClosed k] in
theorem DD_TR (hχ : 0 < S.P.deg χ) {t t0 : R} {j : ℕ} (hT : S.TR χ t) (h0 : S.IsGen t0)
    (hj : ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ j) :
    S.DD χ ω X Y t = S.DR χ ω Y t0 + (j : ℤ) * ω (S.qr (S.P.tgt t)) := by
  classical
  have hnB : ¬ S.TB χ t := fun h ↦ h.2.1 hT.2.1
  have hnL : ¬ S.TL χ t := fun h ↦ h.2.1 hT.2.1
  have hex : ∃ j : ℕ, ∃ t0, S.IsGen t0 ∧ S.TR χ t0 ∧ ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt t) ^ j := by
    refine ⟨j, t0, h0, S.tr_factor hT hj ?_, hj⟩
    intro he; apply S.tr_nonlocal hT
    have hs := S.supp_of_qh' hT.2.2
    obtain ⟨a1, a2⟩ := S.mul_qpow_endpoints (by rw [← S.qh_of_supp χ hs]; exact hj.symm)
    rw [a1, a2]; nth_rewrite 2 [he]; rw [S.P.tgt_e]
  rw [DD, if_neg hnB, if_neg hnL, if_pos hT, dif_pos hex]
  obtain ⟨h1, -, h3⟩ := hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := S.layer_TR_unique hχ hT h1 h0 h3 hj
  congr 1
  · rw [e2]
  · rw [e1]

omit [IsAlgClosed k] in
theorem op_qr (x : V) : S.op.qr x = S.qr x := by
  by_cases h : S.q x = 0
  · classical
    have h1 : ¬ ∃ g, ⌜g⌝ = S.q x := by rintro ⟨g, hg⟩; exact S.rr_ne g (hg.trans h)
    have h2 : ¬ ∃ g, S.op.rr g = S.op.q x := by
      rintro ⟨g, hg⟩; apply S.rr_ne g; exact S.P.toOp_injective (hg.trans (by rw [op_q, h]))
    rw [qr, dif_neg h2, qr, dif_neg h1]; rfl
  · apply S.rr_inj
    have h' : S.op.q x ≠ 0 := by rw [op_q]; exact h
    have := S.op.qr_spec h'
    apply S.P.toOp_injective
    change S.op.rr (S.op.qr x) = S.P.toOp ⌜S.qr x⌝
    rw [this, S.qr_spec h, op_q]

omit [IsAlgClosed k] in
/-- The coefficients are self-dual under `A₀ ↦ A₀ᵒᵖ`, exchanging `X` and `Y`. -/
theorem op_DD (hχ : 0 < S.P.deg χ) (hprim : Prim χ) (t : R) :
    S.op.DD χ ω Y X t = S.DD χ ω X Y t := by
  by_cases hB : S.TB χ t
  · rw [S.op.DD_TB, S.DD_TB _ _ _ hB]; exact (S.op_TB t).2 hB
  by_cases hL : S.TL χ t
  · obtain ⟨i, t0, h1, -, h3⟩ := S.layer_TL_exists hprim hL
    rw [S.DD_TL _ _ _ hχ hL h1 h3]
    have := S.op.DD_TR ω Y X hχ ((S.op_TR t).2 hL) ((S.op_isGen_iff t0).2 h1) (j := i)
      (by apply S.P.toOp_injective; change S.P.toOp ⌜t⌝ = _
          rw [h3, Tab.toOp_mul, S.toOp_qh_pow]; rfl)
    rw [this, add_comm, S.op_qr]; rfl
  by_cases hR : S.TR χ t
  · obtain ⟨j, t0, h1, -, h3⟩ := S.layer_TR_exists hprim hR
    rw [S.DD_TR _ _ _ hχ hR h1 h3]
    have := S.op.DD_TL ω Y X hχ ((S.op_TL t).2 hR) ((S.op_isGen_iff t0).2 h1) (S.op_layer h3)
    rw [this, add_comm, S.op_qr]; rfl
  · have hs : ¬ S.Shift χ t := by
      intro hs
      rcases S.types_of_shift hχ hprim hs with h | h | h
      · exact hL h
      · exact hR h
      · exact hB h
    rw [S.DD_unshift _ _ _ hs, S.op.DD_unshift _ _ _ (by rwa [S.op_shift])]

/-! ### Two-sided rays -/

omit [IsAlgClosed k] in
/-- A two-sided ray commutes with the local generators. -/
theorem tb_comm {u : R} (hB : S.TB χ u) :
    S.q (S.P.src u) * ⌜u⌝ = ⌜u⌝ * S.q (S.P.tgt u) := by
  obtain ⟨-, e1⟩ := S.shift_of_qh_mul hB.1.1 hB.2.1
  obtain ⟨-, e2⟩ := S.shift_of_mul_qh hB.1.1 hB.2.2
  rw [← S.qh_of_supp χ (S.supp_of_qh hB.2.1), ← S.qh_of_supp χ (S.supp_of_qh' hB.2.2), e1, e2]

omit [IsAlgClosed k] in
/-- The local generator is two-sided when its square survives. -/
theorem qr_TB {x : V} (h2 : S.q x ^ 2 ≠ 0) (hs : S.Supp χ x) : S.TB χ (S.qr x) := by
  have hq : S.q x ≠ 0 := fun h0 ↦ h2 (by rw [h0, zero_pow two_ne_zero])
  have hqr := S.qr_spec hq
  obtain ⟨l1, l2⟩ := S.loop_of_eq_q hqr
  have hqx := S.qh_of_supp χ hs
  have h1 : S.qh χ (S.P.src (S.qr x)) * ⌜S.qr x⌝ ≠ 0 := by
    rw [l1, hqx, hqr, ← pow_two]; exact h2
  have h0 : S.qr x ≠ S.P.e (S.P.src (S.qr x)) := by
    intro he; apply S.P.deg_pos _ (show S.qr x ≠ S.P.e (S.P.src (S.qr x)) from ?_) |>.ne'
    · rw [he, S.P.wt_e, map_zero]
    · intro he'; obtain ⟨g, hg, g1, -, g3⟩ := (S.q_cases x).resolve_left hq
      have := S.rr_inj (hqr.trans hg); subst this; exact g3 (by rw [he', l1])
  exact ⟨(S.shift_of_qh_mul h0 h1).1, h1, by rw [l2, hqx, hqr, ← pow_two]; exact h2⟩

omit [IsAlgClosed k] in
/-- `ω` along local powers of a two-sided ray: `[q̂^n u] = n[q̂] + [u]`. -/
theorem ω_qpow
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {u : R} (hu : S.TB χ u) (n : ℕ) :
    ∀ {t : R}, S.TB χ t → S.q (S.P.src u) ^ n * ⌜u⌝ = ⌜t⌝ →
      ω t = (n : ℤ) * ω (S.qr (S.P.src u)) + ω u := by
  have hs := S.supp_of_qh hu.2.1
  have hqx : S.qh χ (S.P.src u) = S.q (S.P.src u) := S.qh_of_supp χ hs
  induction n with
  | zero => intro t ht h; rw [pow_zero, one_mul] at h; rw [S.rr_inj h]; simp
  | succ n ih =>
    intro t ht h
    have hne : S.q (S.P.src u) ^ n * ⌜u⌝ ≠ 0 := by
      intro h0; apply S.rr_ne t; rw [← h, pow_succ', mul_assoc, h0, mul_zero]
    obtain ⟨t', ht'⟩ := S.mul_right_ray hne
    obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints ht'
    have htt : S.q (S.P.src u) * ⌜t'⌝ = ⌜t⌝ := by rw [← ht', ← mul_assoc, ← pow_succ', h]
    have hqt : S.q (S.P.src u) * ⌜t⌝ ≠ 0 := by
      obtain ⟨t1, -⟩ := S.qpow_mul_endpoints h
      rw [← t1, ← S.qh_of_supp χ (by rw [t1]; exact hs)]; exact ht.2.1
    have hBt' : S.TB χ t' := by
      have h0 : t' ≠ S.P.e (S.P.src t') := by
        apply S.ne_e_of_deg
        rw [S.wt_of_eq_qpow_mul (f := u) ht'.symm, map_add, map_nsmul, nsmul_eq_mul]
        have := S.P.deg_pos u hu.1.1; have := S.deg_χ_nonneg (S.P.src u)
        positivity
      have h1 : S.qh χ (S.P.src t') * ⌜t'⌝ ≠ 0 := by rw [e1, hqx, htt]; exact S.rr_ne t
      have hsz := S.supp_of_qh' hu.2.2
      have h2 : ⌜t'⌝ * S.qh χ (S.P.tgt t') ≠ 0 := by
        rw [e2, S.qh_of_supp χ hsz, ← ht', mul_assoc, ← S.tb_comm hu, ← mul_assoc, ← pow_succ, h]
        exact S.rr_ne t
      exact ⟨(S.shift_of_qh_mul h0 h1).1, h1, h2⟩
    have := ih hBt' ht'
    have hq2 : S.q (S.P.src u) ^ 2 ≠ 0 := by
      intro h0; apply hqt; rw [← htt, ← mul_assoc, ← pow_two, h0, zero_mul]
    have hqr := S.qr_spec (x := S.P.src u) (fun h0 ↦ hq2 (by rw [h0, zero_pow two_ne_zero]))
    rw [hω _ _ _ (S.qr_TB hq2 hs) hBt' ht (by rw [hqr, htt]), this]
    push_cast; ring

/-- **Theorem 9.1, cases 2 and 3**: generating inputs of types `B, L`. -/
theorem eq_BL_gen
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r0 s0 t : R} (hr0 : S.IsGen r0) (hB : S.TB χ r0) (hs0 : S.IsGen s0)
    (hL : S.TL χ s0) (h : ⌜r0⌝ * ⌜s0⌝ = ⌜t⌝) (ht : S.Shift χ t) :
    S.DD χ ω X Y t = ω r0 + S.DL χ ω X s0 := by
  have hTt := S.out_BL hχ hprim hB hL h ht
  obtain ⟨t1, -, t3, -⟩ := S.prod_of h
  by_cases hg : S.IsGen t
  · rw [S.DD_TL _ _ _ hχ hTt hg (i := 0) (by rw [pow_zero, one_mul]), Nat.cast_zero, zero_mul,
      zero_add]
    exact (S.DL_prod k ω X hfin hχ hprim hω hg hTt h hB.1.1).2 hB
  obtain ⟨n, f, hf, hTf, hn⟩ := S.layer_TL_exists hprim hTt
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    rw [pow_zero, one_mul] at hn
    exact hg (by rw [S.rr_inj hn]; exact hf)
  rw [t1] at hn
  obtain ⟨rfl, -, hq3, u, hu1, hu2⟩ := S.BL_proper k hfin hχ hprim hr0 hs0 hB hL h hf hn hn1 ht
  rw [← t1] at hn
  have hsx := S.supp_of_qh hB.2.1
  have hsy := S.supp_of_qh hL.2.1
  have hqx := S.qh_of_supp χ hsx
  have hqy := S.qh_of_supp χ hsy
  rw [t1, hqx, pow_one] at hn
  -- `u f = s₀`
  have huf : ⌜u⌝ * ⌜f⌝ ≠ 0 := by
    intro h0; apply S.rr_ne t; rw [hn, ← hu1, mul_assoc, h0, mul_zero]
  obtain ⟨c, hc⟩ := S.ray_of_mul_ne huf
  have e : ⌜r0⌝ * ⌜c⌝ = ⌜r0⌝ * ⌜s0⌝ := by rw [← hc, ← mul_assoc, hu1, ← hn, h]
  have := S.cancel_left e (by rw [e, h]; exact S.rr_ne t)
  subst this
  -- `u` is two-sided
  have hr0u : ⌜r0⌝ * ⌜u⌝ ≠ 0 := by rw [hu1]; exact hsx.1
  obtain ⟨-, w2, w3, -⟩ := S.prod_of (show ⌜r0⌝ * ⌜u⌝ = ⌜S.qr (S.P.src r0)⌝ by
    rw [hu1, S.qr_spec hsx.1])
  obtain ⟨-, l2⟩ := S.loop_of_eq_q (S.qr_spec hsx.1)
  have u1 : S.P.src u = S.P.tgt r0 := w3.symm
  have u2 : S.P.tgt u = S.P.src r0 := by rw [← w2, l2]
  have hyx : S.P.tgt r0 ≠ S.P.src r0 := fun h' ↦ hB.1.1 (S.gen_loop_e hr0 h'.symm)
  have hcomm : S.q (S.P.tgt r0) * ⌜u⌝ = ⌜u⌝ * S.q (S.P.src r0) := by
    rw [← hu2, mul_assoc, hu1]
  have huq : ⌜u⌝ * S.q (S.P.src r0) ≠ 0 := by
    intro h0; apply hL.2.1
    have : S.qh χ (S.P.src c) * ⌜c⌝ = ⌜u⌝ * S.q (S.P.src r0) * ⌜f⌝ := by
      rw [hqy, ← t3, ← hc, ← mul_assoc, hcomm]
    rw [this, h0, zero_mul]
  have hu0 : u ≠ S.P.e (S.P.src u) := by
    intro he; apply hyx; rw [← u1, ← u2]; nth_rewrite 2 [he]; rw [S.P.tgt_e]
  have hBu : S.TB χ u := by
    have h1 : S.qh χ (S.P.src u) * ⌜u⌝ ≠ 0 := by
      rw [u1, t3, hqy, ← t3, hcomm]; exact huq
    exact ⟨(S.shift_of_qh_mul hu0 h1).1, h1, by rw [u2, hqx]; exact huq⟩
  have hDs := (S.DL_prod k ω X hfin hχ hprim hω hs0 hL hc hu0).2 hBu
  have hq2 : S.q (S.P.src r0) ^ 2 ≠ 0 := by
    intro h0; apply hTt.2.1
    rw [t1, hqx, hn, ← mul_assoc, ← pow_two, h0, zero_mul]
  have hω' := hω r0 u (S.qr (S.P.src r0)) hB hBu (S.qr_TB hq2 hsx) (by rw [hu1, S.qr_spec hsx.1])
  rw [S.DD_TL _ _ _ hχ hTt hf (i := 1) (by rw [t1, hqx, pow_one]; exact hn), hDs, t1, hω']
  push_cast; ring

omit [IsAlgClosed k] in
theorem hω_op
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s) :
    ∀ r s t, S.op.TB χ r → S.op.TB χ s → S.op.TB χ t → S.op.rr r * S.op.rr s = S.op.rr t →
      ω t = ω r + ω s := by
  intro r s t hr hs ht h
  rw [hω s r t ((S.op_TB s).1 hs) ((S.op_TB r).1 hr) ((S.op_TB t).1 ht)
    (S.P.toOp_injective (by rw [Tab.toOp_mul]; exact h)), add_comm]

open Classical in
/-- The last-arrow recursion (the dual of `DL_eq`). -/
theorem DR_eq (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r b w : R} (hr : S.IsGen r) (hT : S.TR χ r) (hb : S.OR r b)
    (hw : ⌜w⌝ * ⌜b⌝ = ⌜r⌝) :
    S.DR χ ω Y r = if S.TB χ b then ω b + S.DR χ ω Y w else Y b := by
  have := S.op.DL_eq k ω Y (S.P.op_isRepresentationFinite k hfin) hχ hprim
    ((S.op_isGen_iff r).2 hr) ((S.op_TL r).2 hT) ((S.op_OL r b).2 hb) (w := w)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw])
  by_cases hB : S.TB χ b
  · rw [if_pos ((S.op_TB b).2 hB)] at this; rw [if_pos hB]; exact this
  · rw [if_neg (fun h ↦ hB ((S.op_TB b).1 h))] at this; rw [if_neg hB]; exact this

/-- **Lemma 9.4, dual**: product equations with generating right-sided output. -/
theorem DR_prod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r u v : R} (hr : S.IsGen r) (hT : S.TR χ r) (huv : ⌜u⌝ * ⌜v⌝ = ⌜r⌝)
    (hv0 : v ≠ S.P.e (S.P.src v)) :
    (S.TR χ v → S.DR χ ω Y r = S.DR χ ω Y v) ∧
      (S.TB χ v → S.DR χ ω Y r = S.DR χ ω Y u + ω v) := by
  have := S.op.DL_prod k ω Y (S.P.op_isRepresentationFinite k hfin) hχ hprim (S.hω_op ω hω)
    ((S.op_isGen_iff r).2 hr) ((S.op_TL r).2 hT) (u := v) (v := u)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, huv])
    (by change v ≠ S.P.e (S.P.tgt v); rwa [S.ne_e_iff_op])
  refine ⟨fun h ↦ this.1 ((S.op_TL v).2 h), fun h ↦ ?_⟩
  have e := this.2 ((S.op_TB v).2 h)
  change S.op.DL χ ω Y r = S.op.DL χ ω Y u + ω v
  rw [e, add_comm]

theorem rest_TR (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r b w : R} (hr : S.IsGen r) (hT : S.TR χ r) (hb : S.Ord b)
    (hB : S.TB χ b) (hw : ⌜w⌝ * ⌜b⌝ = ⌜r⌝) :
    S.IsGen w ∧ S.TR χ w ∧ S.P.deg (S.P.wt w) < S.P.deg (S.P.wt r) := by
  obtain ⟨h1, h2, h3⟩ := S.op.rest_TL k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    ((S.op_isGen_iff r).2 hr) ((S.op_TL r).2 hT) ((S.op_ord b).2 hb) ((S.op_TB b).2 hB)
    (w := w) (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw])
  exact ⟨(S.op_isGen_iff w).1 h1, (S.op_TL w).1 h2, h3⟩

omit [IsAlgClosed k] in
/-- A nonidentity factor `f` of a two-sided `t = q̂^n f` is two-sided. -/
theorem tb_factor {t f : R} {n : ℕ} (hB : S.TB χ t)
    (h : ⌜t⌝ = S.qh χ (S.P.src t) ^ n * ⌜f⌝) (hf0 : f ≠ S.P.e (S.P.src f)) : S.TB χ f := by
  have hsx := S.supp_of_qh hB.2.1
  have hsz := S.supp_of_qh' hB.2.2
  have h' : ⌜t⌝ = S.q (S.P.src t) ^ n * ⌜f⌝ := by rw [← S.qh_of_supp χ hsx]; exact h
  obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints h'.symm
  have h1 : S.qh χ (S.P.src f) * ⌜f⌝ ≠ 0 := by
    intro h0; apply hB.2.1; rw [h, ← mul_assoc, ← pow_succ', pow_succ, mul_assoc, e1, h0, mul_zero]
  have h2 : ⌜f⌝ * S.qh χ (S.P.tgt f) ≠ 0 := by
    intro h0; apply hB.2.2; rw [h, mul_assoc, e2, h0, mul_zero]
  exact ⟨(S.shift_of_qh_mul hf0 h1).1, h1, h2⟩

omit [IsAlgClosed k] in
/-- `ω` along local powers on the right. -/
theorem ω_powq
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {u t : R} (hu : S.TB χ u) (n : ℕ) (ht : S.TB χ t)
    (h : ⌜u⌝ * S.q (S.P.tgt u) ^ n = ⌜t⌝) :
    ω t = ω u + (n : ℤ) * ω (S.qr (S.P.tgt u)) := by
  have := S.op.ω_qpow ω (S.hω_op ω hω) ((S.op_TB u).2 hu) n ((S.op_TB t).2 ht)
    (by change S.P.toOp (S.q (S.P.tgt u)) ^ n * S.P.toOp ⌜u⌝ = S.P.toOp ⌜t⌝
        rw [← Tab.toOp_pow, ← Tab.toOp_mul, h])
  rw [this, S.op_qr, add_comm]; rfl

variable (hRC2 : ∀ a b x, S.NdRow χ a b x → X a + Y b = 2 * ω (S.qr x))

include hRC2 in
/-- The coefficient equation of a nondeep return (`eq:nondeep-coefficient-row`). -/
theorem nondeep_eq (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {x : V} {e l : R} (hN : S.NondeepRet χ x e l) :
    S.DL χ ω X e + S.DR χ ω Y l = 2 * ω (S.qr x) := by
  have hN' := hN
  obtain ⟨he, hl, -, -, -, -, hTe, hTl, -, -⟩ := hN'
  have he0 : e ≠ S.P.e (S.P.src e) := hTe.1.1
  have hl0 : l ≠ S.P.e (S.P.src l) := hTl.1.1
  have ha := S.fstA_spec he0
  obtain ⟨b, hb⟩ := S.exists_OR l hl0
  have hTa := S.nondeep_first_TL k hfin hχ hprim hN ha
  have hTb := S.nondeep_last_TR k hfin hχ hprim hN hb
  obtain ⟨w, hw⟩ := ha.2
  obtain ⟨w', hw'⟩ := hb.2
  rw [S.DL_eq k ω X hfin hχ hprim he hTe ha hw, if_neg (fun h ↦ h.2.2 hTa.2.2),
    S.DR_eq k ω Y hfin hχ hprim hl hTl hb hw', if_neg (fun h ↦ h.2.1 hTb.2.1)]
  exact hRC2 _ _ _ ⟨e, l, hN, S.fstA_spec he0, hb⟩

variable (hRC1 : ∀ a b f, S.CrownRow χ a b f → X a + Y b = ω f)

include hRC1 in
/-- **Theorem 9.1, case 2, crown rows**: generating inputs of types `L, R` with generating
two-sided output (`eq:generating-crown-row`, after stripping two-sided prefixes and
suffixes). -/
theorem crown_eq (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r0 s0 t : R} (hr0 : S.IsGen r0) (hTr : S.TL χ r0) (hs0 : S.IsGen s0) (hTs : S.TR χ s0)
    (h : ⌜r0⌝ * ⌜s0⌝ = ⌜t⌝) (hg : S.IsGen t) (hBt : S.TB χ t) :
    ω t = S.DL χ ω X r0 + S.DR χ ω Y s0 := by
  induction hn : (S.P.deg (S.P.wt r0) + S.P.deg (S.P.wt s0)).toNat using Nat.strong_induction_on
    generalizing r0 s0 t with
  | _ n ih =>
    have hr00 : r0 ≠ S.P.e (S.P.src r0) := hTr.1.1
    have hs00 : s0 ≠ S.P.e (S.P.src s0) := hTs.1.1
    have hdt : S.Dim2 t := Or.inl (by
      rw [← S.qh_of_supp χ (S.supp_of_qh hBt.2.1)]; exact hBt.2.1)
    set a := S.fstA r0 with ha
    have hoa : S.OL r0 a := S.fstA_spec hr00
    have hw0 := S.fstRest_spec hr00
    rw [← ha] at hw0
    set w0 := S.fstRest r0 with hw0d
    have hdr := S.P.deg_nonneg r0
    have hds := S.P.deg_nonneg s0
    by_cases hBa : S.TB χ a
    · -- strip a two-sided first arrow
      obtain ⟨gw, tw, dw⟩ := S.rest_TL k hfin hχ hprim hr0 hTr hoa.1 hBa hw0
      have hws : ⌜w0⌝ * ⌜s0⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← h, ← hw0, mul_assoc, h0, mul_zero])
      obtain ⟨t1, ht1⟩ := S.ray_of_mul_ne hws
      have hat : ⌜a⌝ * ⌜t1⌝ = ⌜t⌝ := by rw [← ht1, ← mul_assoc, hw0, h]
      have ht10 : t1 ≠ S.P.e (S.P.src t1) := by
        apply S.ne_e_of_deg; rw [(S.prod_of ht1).2.2.2, map_add]
        have := S.P.deg_pos s0 hs00; have := S.P.deg_nonneg w0; linarith
      have hBt1 : S.TB χ t1 := by
        rcases (S.table_B hχ hprim hoa.1.1 ht10 hat hBt).1 with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd hBa.2.2 (by rw [h1.2.2]; exact fun h' ↦ h' rfl)
      have hgt1 : S.IsGen t1 := S.gen_factor k hfin hg hdt (a := a) (m := t1)
        (b := S.P.e (S.P.tgt t)) (by rw [hat, S.rr_mul_e])
      have ih1 := ih _ (by have := S.P.deg_nonneg w0; omega) gw tw hs0 hTs ht1 hgt1 hBt1 rfl
      rw [S.DL_eq k ω X hfin hχ hprim hr0 hTr hoa hw0, if_pos hBa, hω a t1 t hBa hBt1 hBt hat,
        ih1]
      ring
    · have hqa : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
        intro h0; apply hTr.2.1
        rw [← hw0, ← mul_assoc, (S.prod_of hw0).1, h0, zero_mul]
      have hTa : S.TL χ a := ⟨(S.shift_of_qh_mul hoa.1.1 hqa).1, hqa,
        by by_contra h'; exact hBa ⟨(S.shift_of_qh_mul hoa.1.1 hqa).1, hqa, h'⟩⟩
      obtain ⟨b, hb⟩ := S.exists_OR s0 hs00
      obtain ⟨w1, hw1⟩ := hb.2
      have hbq : ⌜b⌝ * S.qh χ (S.P.tgt b) ≠ 0 := by
        intro h0; apply hTs.2.2
        rw [← hw1, mul_assoc, (S.prod_of hw1).2.1, h0, mul_zero]
      have hrw : ⌜r0⌝ * ⌜w1⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← h, ← hw1, ← mul_assoc, h0, zero_mul])
      obtain ⟨t2, ht2⟩ := S.ray_of_mul_ne hrw
      have htb : ⌜t2⌝ * ⌜b⌝ = ⌜t⌝ := by rw [← ht2, mul_assoc, hw1, h]
      have ht20 : t2 ≠ S.P.e (S.P.src t2) := by
        apply S.ne_e_of_deg; rw [(S.prod_of ht2).2.2.2, map_add]
        have := S.P.deg_pos r0 hr00; have := S.P.deg_nonneg w1; linarith
      by_cases hBb : S.TB χ b
      · obtain ⟨gw, tw, dw⟩ := S.rest_TR k hfin hχ hprim hs0 hTs hb.1 hBb hw1
        have hBt2 : S.TB χ t2 := by
          rcases (S.table_B hχ hprim ht20 hb.1.1 htb hBt).1 with ⟨h1, -⟩ | ⟨-, h1⟩
          · exact h1
          · exact absurd hBb.2.1 (by rw [h1.2.1]; exact fun h' ↦ h' rfl)
        have hgt2 : S.IsGen t2 := S.gen_factor k hfin hg hdt (a := S.P.e (S.P.src t)) (m := t2)
          (b := b) (by rw [S.e_mul_rr' t2 (by rw [(S.prod_of htb).1]), htb])
        have ih2 := ih _ (by have := S.P.deg_nonneg w1; omega) hr0 hTr gw tw ht2 hgt2 hBt2 rfl
        rw [S.DR_eq k ω Y hfin hχ hprim hs0 hTs hb hw1, if_pos hBb, hω t2 b t hBt2 hBb hBt htb, ih2]
        ring
      · have hTb : S.TR χ b := ⟨(S.shift_of_mul_qh hb.1.1 hbq).1,
          by by_contra h'; exact hBb ⟨(S.shift_of_mul_qh hb.1.1 hbq).1, h', hbq⟩, hbq⟩
        rw [S.DL_eq k ω X hfin hχ hprim hr0 hTr hoa hw0, if_neg hBa,
          S.DR_eq k ω Y hfin hχ hprim hs0 hTs hb hw1, if_neg hBb]
        -- the crown row `(a, b, t)`
        have hws : ⌜w0⌝ * ⌜s0⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← h, ← hw0, mul_assoc, h0, mul_zero])
        obtain ⟨v, hv⟩ := S.ray_of_mul_ne hws
        have hav : ⌜a⌝ * ⌜v⌝ = ⌜t⌝ := by rw [← hv, ← mul_assoc, hw0, h]
        have hw01 : ⌜w0⌝ * ⌜w1⌝ ≠ 0 := fun h0 ↦ S.rr_ne v (by rw [← hv, ← hw1, ← mul_assoc, h0, zero_mul])
        obtain ⟨c, hc⟩ := S.ray_of_mul_ne hw01
        have hv0 : v ≠ S.P.e (S.P.src v) := by
          apply S.ne_e_of_deg; rw [(S.prod_of hv).2.2.2, map_add]
          have := S.P.deg_pos s0 hs00; have := S.P.deg_nonneg w0; linarith
        have hTv : S.TR χ v := by
          rcases (S.table_B hχ hprim hoa.1.1 hv0 hav hBt).1 with ⟨h1, -⟩ | ⟨-, h1⟩
          · exact absurd h1 hBa
          · exact h1
        have hTw : S.TL χ t2 := by
          rcases (S.table_B hχ hprim ht20 hb.1.1 htb hBt).1 with ⟨-, h1⟩ | ⟨h1, -⟩
          · exact absurd h1 hBb
          · exact h1
        refine (hRC1 a b t ⟨hg, hBt, hTa, hTb, v, t2, hav, htb,
          S.gen_factor k hfin hg hdt (a := a) (m := v) (b := S.P.e (S.P.tgt t))
            (by rw [hav, S.rr_mul_e]),
          S.gen_factor k hfin hg hdt (a := S.P.e (S.P.src t)) (m := t2) (b := b)
            (by rw [S.e_mul_rr' t2 (by rw [(S.prod_of htb).1]), htb]),
          hTv, hTw, ⟨hb.1, c, by rw [← hc, mul_assoc, hw1, hv]⟩,
          ⟨hoa.1, c, by rw [← hc, ← mul_assoc, hw0, ht2]⟩⟩).symm

include hRC1 hRC2 in
/-- **Theorem 9.1, cases 2 and 4**: generating inputs of types `L, R` with two-sided output. -/
theorem eq_LR_gen (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r0 s0 t : R} (hr0 : S.IsGen r0) (hTr : S.TL χ r0) (hs0 : S.IsGen s0) (hTs : S.TR χ s0)
    (h : ⌜r0⌝ * ⌜s0⌝ = ⌜t⌝) (hBt : S.TB χ t) :
    ω t = S.DL χ ω X r0 + S.DR χ ω Y s0 := by
  by_cases hg : S.IsGen t
  · exact S.crown_eq k ω X Y hRC1 hfin hχ hprim hω hr0 hTr hs0 hTs h hg hBt
  obtain ⟨t1, t2, -, -⟩ := S.prod_of h
  rcases S.LR_proper k hfin hχ hprim hr0 hs0 hTr hTs h hBt.1 hg with
    ⟨-, hN⟩ | ⟨hzx, f, hf, hft1, hft2, ⟨a, hra, hN⟩ | ⟨b, hsb, hN⟩⟩
  · have hN' := hN
    obtain ⟨-, -, -, -, -, -, hTr', -, hel, hq3⟩ := hN'
    have hsx := S.supp_of_qh hTr'.2.1
    have hqx := S.qh_of_supp χ hsx
    rw [hqx] at hel hq3
    have hq2 : S.q (S.P.src r0) ^ 2 ≠ 0 := fun h0 ↦ hq3 (by rw [pow_succ, h0, zero_mul])
    have hqr := S.qr_spec hsx.1
    have hBq := S.qr_TB hq2 hsx
    rw [hω _ _ _ hBq hBq hBt (by rw [hqr, ← pow_two, ← hel, h]),
      S.nondeep_eq k ω X Y hRC2 hfin hχ hprim hN]
    ring
  · have hsx := S.supp_of_qh hTr.2.1
    have hsz := S.supp_of_qh' hTs.2.2
    rw [← t1] at hft1; rw [← t2] at hft2
    obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ (x := S.P.src t) (by rw [t1]; exact hsx)]; exact hft1.symm)
    have hf0 : f ≠ S.P.e (S.P.src f) := by
      intro he; apply hzx; rw [← t2, e2, ← t1, e1]; nth_rewrite 1 [he]; rw [S.P.tgt_e]
    have hBf := S.tb_factor hBt hft1 hf0
    have hra' : ⌜f⌝ * ⌜a⌝ = ⌜r0⌝ := hra.symm
    have hDL := (S.DL_prod k ω X hfin hχ hprim hω hr0 hTr hra' hf0).2 hBf
    have hωt := S.ω_powq ω hω hBf 2 hBt (by
      rw [← e2, ← S.qh_of_supp χ (x := S.P.tgt t) (by rw [t2]; exact hsz)]; exact hft2.symm)
    have hnd := S.nondeep_eq k ω X Y hRC2 hfin hχ hprim hN
    rw [hωt, hDL, ← e2, t2]
    push_cast; linarith
  · have hsx := S.supp_of_qh hTr.2.1
    rw [← t1] at hft1; rw [← t2] at hft2
    obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ (x := S.P.src t) (by rw [t1]; exact hsx)]; exact hft1.symm)
    have hf0 : f ≠ S.P.e (S.P.src f) := by
      intro he; apply hzx; rw [← t2, e2, ← t1, e1]; nth_rewrite 1 [he]; rw [S.P.tgt_e]
    have hBf := S.tb_factor hBt hft1 hf0
    have hsb' : ⌜b⌝ * ⌜f⌝ = ⌜s0⌝ := hsb.symm
    have hDR := (S.DR_prod k ω Y hfin hχ hprim hω hs0 hTs hsb' hf0).2 hBf
    have hωt := S.ω_qpow ω hω hBf 2 hBt (by
      rw [← e1, ← S.qh_of_supp χ (x := S.P.src t) (by rw [t1]; exact hsx)]; exact hft1.symm)
    have hnd := S.nondeep_eq k ω X Y hRC2 hfin hχ hprim hN
    rw [hωt, hDR, ← e1, t1]
    push_cast; linarith

omit [IsAlgClosed k] in
/-- A two-sided ray is a layer of a generating two-sided ray. -/
theorem layer_TB_exists (hprim : Prim χ) {t : R} (hB : S.TB χ t) (hl : S.P.src t ≠ S.P.tgt t) :
    ∃ i t0, S.IsGen t0 ∧ S.TB χ t0 ∧ ⌜t⌝ = S.qh χ (S.P.src t) ^ i * ⌜t0⌝ := by
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen t
  have hs := S.supp_of_qh hB.2.1
  have hq : S.qh χ (S.P.src t) = S.q (S.P.src t) := S.qh_of_supp χ hs
  obtain ⟨a, c, hac⟩ := hg t g1.symm g2.symm
  have hqt : S.q (S.P.src t) * ⌜t⌝ ≠ 0 := by rw [← hq]; exact hB.2.1
  have hqg : S.q (S.P.src g) * ⌜g⌝ ≠ 0 := by
    intro h0; apply hqt; rw [hac, ← g1]
    simp only [← mul_assoc]; rw [← pow_succ', pow_succ, mul_assoc _ (S.q (S.P.src g)), h0]
    simp
  obtain ⟨hgL, -⟩ := S.prim_action_gen hg (by rw [g1, hs.2]; exact hprim) hqg
  obtain ⟨i, hi⟩ := hgL t g1.symm g2.symm
  rw [g1, ← hq] at hi
  have hg0 : g ≠ S.P.e (S.P.src g) := by
    intro he; apply hl
    rw [← g1, ← g2]; nth_rewrite 2 [he]; rw [S.P.tgt_e]
  exact ⟨i, g, hg, S.tb_factor hB hi hg0, hi⟩

omit [IsAlgClosed k] in
/-- The coefficient of a local power of a left-sided ray. -/
theorem DD_qpow_TL (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {t t' : R} {m : ℕ} (hT : S.TL χ t)
    (hT' : S.TL χ t') (h : ⌜t⌝ = S.qh χ (S.P.src t') ^ m * ⌜t'⌝) :
    S.DD χ ω X Y t = (m : ℤ) * ω (S.qr (S.P.src t')) + S.DD χ ω X Y t' := by
  obtain ⟨l, t0, hg, -, hl⟩ := S.layer_TL_exists hprim hT'
  have hs := S.supp_of_qh hT'.2.1
  obtain ⟨e1, -⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ hs]; exact h.symm)
  rw [S.DD_TL _ _ _ hχ hT' hg hl, S.DD_TL _ _ _ hχ hT hg (i := m + l)
    (by rw [h, hl, ← mul_assoc, ← pow_add, e1]), e1]
  push_cast; ring

omit [IsAlgClosed k] in
/-- `ω` of a local two-sided ray. -/
theorem ω_local
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r : R} {i : ℕ} (hB : S.TB χ r) (hr : ⌜r⌝ = S.q (S.P.src r) ^ i) :
    ω r = (i : ℤ) * ω (S.qr (S.P.src r)) := by
  have hs := S.supp_of_qh hB.2.1
  have hi : 1 ≤ i := by
    by_contra h0; have : i = 0 := by omega
    subst this; rw [pow_zero] at hr; exact S.P.rr_ne_one r hr
  have hq2 : S.q (S.P.src r) ^ 2 ≠ 0 := by
    intro h0; apply hB.2.1
    rw [S.qh_of_supp χ hs, hr, ← pow_succ', show i + 1 = (i - 1) + 2 by omega, pow_add, h0,
      mul_zero]
  have hqr := S.qr_spec hs.1
  obtain ⟨l1, -⟩ := S.loop_of_eq_q hqr
  have := S.ω_qpow ω hω (S.qr_TB hq2 hs) (i - 1) hB (by
    rw [l1, hqr, ← pow_succ, Nat.sub_add_cancel hi, hr])
  rw [this, l1]; push_cast [Nat.cast_sub hi]; ring

/-- **Theorem 9.1, products with left-sided output** (cases 1, 2, 3, 5). -/
theorem eq_TL (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r s t : R} (hr0 : r ≠ S.P.e (S.P.src r)) (hs0 : s ≠ S.P.e (S.P.src s))
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hT : S.TL χ t) :
    (S.TL χ r → S.DD χ ω X Y t = S.DD χ ω X Y r) ∧
      (S.TB χ r → S.DD χ ω X Y t = S.DD χ ω X Y r + S.DD χ ω X Y s) := by
  obtain ⟨t1, -, t3, t4⟩ := S.prod_of h
  constructor
  · intro hTr
    obtain ⟨i, r0, hg, hTr0, hri⟩ := S.layer_TL_exists hprim hTr
    obtain ⟨t0, ht0g, hr0s, ht0⟩ := S.layer_L k hfin hχ hprim hTr hT h hg hri
    have hsr := S.supp_of_qh hTr.2.1
    obtain ⟨a1, -⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ hsr]; exact hri.symm)
    obtain ⟨b1, -, -, b4⟩ := S.prod_of hr0s
    have ht00 : t0 ≠ S.P.e (S.P.src t0) := by
      apply S.ne_e_of_deg; rw [b4, map_add]
      have := S.P.deg_pos r0 hTr0.1.1; have := S.P.deg_nonneg s; linarith
    have hTt0 : S.TL χ t0 := S.tl_factor hT (by rw [t1]; exact ht0) ht00
    rw [S.DD_TL _ _ _ hχ hT ht0g (by rw [t1]; exact ht0), S.DD_TL _ _ _ hχ hTr hg hri, t1,
      (S.DL_prod k ω X hfin hχ hprim hω ht0g hTt0 hr0s hTr0.1.1).1 hTr0]
  · intro hBr
    have hTs : S.TL χ s := by
      rcases S.table_L hχ hprim hr0 hs0 h hT with ⟨h1, -⟩ | ⟨-, h1, -⟩
      · exact absurd h1.2.2 hBr.2.2
      · exact h1
    have hsx := S.supp_of_qh hBr.2.1
    have hqx := S.qh_of_supp χ hsx
    have hsy := S.supp_of_qh hTs.2.1
    have hqy := S.qh_of_supp χ hsy
    have hqt : S.q (S.P.src r) * ⌜t⌝ ≠ 0 := by rw [← hqx, ← t1]; exact hT.2.1
    by_cases hloc : S.P.src r = S.P.tgt r
    · -- a local two-sided first factor
      obtain ⟨n, hn, -⟩ := S.local_eq r hloc
      have hn1 : 1 ≤ n := by
        by_contra h0; have : n = 0 := by omega
        subst this; rw [pow_zero, one_mul] at hn; exact hr0 (S.rr_inj hn).symm
      rw [S.qpow_mul_e hn1] at hn
      rw [S.DD_TB _ _ _ hBr, S.ω_local ω hω hBr hn.symm,
        S.DD_qpow_TL _ _ _ hχ hprim hT hTs (m := n) (by rw [← h, ← hn, hqy, ← t3, ← hloc]), ← t3,
        ← hloc]
    obtain ⟨i, r0, hg, hBr0, hri⟩ := S.layer_TB_exists hprim hBr hloc
    obtain ⟨j, s0, hgs, hTs0, hsj⟩ := S.layer_TL_exists hprim hTs
    rw [hqx] at hri; rw [hqy] at hsj
    obtain ⟨a1, a2⟩ := S.qpow_mul_endpoints hri.symm
    obtain ⟨b1, -⟩ := S.qpow_mul_endpoints hsj.symm
    have hcj := S.comm_pow (S.tb_comm hBr0) j
    rw [← a1, ← a2] at hcj
    have hts : ⌜t⌝ = S.q (S.P.src r) ^ (i + j) * (⌜r0⌝ * ⌜s0⌝) := by
      rw [← h, hri, hsj, ← t3, mul_assoc, ← mul_assoc ⌜r0⌝, ← hcj, pow_add]
      simp only [mul_assoc]
    have hrs0 : ⌜r0⌝ * ⌜s0⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [hts, h0, mul_zero])
    obtain ⟨t', ht'⟩ := S.ray_of_mul_ne hrs0
    rw [ht'] at hts
    obtain ⟨c1, -, -, c4⟩ := S.prod_of ht'
    have ht'0 : t' ≠ S.P.e (S.P.src t') := by
      apply S.ne_e_of_deg; rw [c4, map_add]
      have := S.P.deg_pos s0 hTs0.1.1; have := S.P.deg_nonneg r0; linarith
    have hqt' : S.qh χ (S.P.src t') * ⌜t'⌝ ≠ 0 := by
      rw [c1, ← a1, hqx]; intro h0; apply hqt
      rw [hts, ← mul_assoc, ← pow_succ', pow_succ, mul_assoc, h0, mul_zero]
    have hsh' := (S.shift_of_qh_mul ht'0 hqt').1
    have hBL := S.eq_BL_gen k ω X Y hω hfin hχ hprim hg hBr0 hgs hTs0 ht' hsh'
    have hTt' := S.out_BL hχ hprim hBr0 hTs0 ht' hsh'
    rw [S.DD_qpow_TL _ _ _ hχ hprim hT hTt' (m := i + j) (by rw [c1, ← a1, hqx]; exact hts),
      hBL, S.DD_TB _ _ _ hBr, S.ω_qpow ω hω hBr0 i hBr (by rw [← a1]; exact hri.symm),
      S.DD_TL _ _ _ hχ hTs hgs (i := j) (by rw [hqy]; exact hsj), c1, ← a1]
    -- `j [q̂_y] = j [q̂_x]`
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; push_cast; ring
    · have hq2r : S.q (S.P.src r) ^ 2 * ⌜r0⌝ ≠ 0 := by
        intro h0; apply hqt
        rw [hts, ← ht', ← mul_assoc, ← pow_succ', show i + j + 1 = (i + j - 1) + 2 by omega,
          pow_add, mul_assoc, ← mul_assoc _ ⌜r0⌝, h0]; simp
      have hq2x : S.q (S.P.src r) ^ 2 ≠ 0 := fun h0 ↦ hq2r (by rw [h0, zero_mul])
      have hq2y : S.q (S.P.src s) ^ 2 ≠ 0 := by
        intro h0; apply hTs.2.1
        rw [hqy, hsj, ← mul_assoc, ← pow_succ', show j + 1 = (j - 1) + 2 by omega, pow_add, h0]
        simp
      have hqr0 : S.q (S.P.src r) * ⌜r0⌝ ≠ 0 := fun h0 ↦ hq2r (by rw [pow_two, mul_assoc, h0, mul_zero])
      obtain ⟨m, hm⟩ := S.mul_right_ray hqr0
      have hm1 : ⌜S.qr (S.P.src r)⌝ * ⌜r0⌝ = ⌜m⌝ := by rw [S.qr_spec hsx.1, hm]
      have hcomm := S.tb_comm hBr0
      rw [← a1, ← a2, t3] at hcomm
      have hm2 : ⌜r0⌝ * ⌜S.qr (S.P.src s)⌝ = ⌜m⌝ := by rw [S.qr_spec hsy.1, ← hcomm, hm]
      obtain ⟨m1, m2⟩ := S.qpow_mul_endpoints (n := 1) (by rw [pow_one]; exact hm)
      have hm0 : m ≠ S.P.e (S.P.src m) := by
        apply S.ne_e_of_deg
        rw [(S.prod_of hm1).2.2.2, map_add]
        have := S.P.deg_pos r0 hBr0.1.1
        have := S.P.deg_nonneg (S.qr (S.P.src r)); linarith
      have hBm : S.TB χ m := by
        have h1 : S.qh χ (S.P.src m) * ⌜m⌝ ≠ 0 := by
          rw [m1, ← a1, hqx, ← hm, ← mul_assoc, ← pow_two]; exact hq2r
        have h2 : ⌜m⌝ * S.qh χ (S.P.tgt m) ≠ 0 := by
          have hcj2 := S.comm_pow (S.tb_comm hBr0) 2
          rw [← a1, ← a2, t3] at hcj2
          rw [m2, ← a2, t3, hqy, ← hm2, mul_assoc, S.qr_spec hsy.1, ← pow_two, ← hcj2]
          exact hq2r
        exact ⟨(S.shift_of_qh_mul hm0 h1).1, h1, h2⟩
      have e1 := hω _ _ _ (S.qr_TB hq2x hsx) hBr0 hBm hm1
      have e2 := hω _ _ _ hBr0 (S.qr_TB hq2y hsy) hBm hm2
      have : ω (S.qr (S.P.src s)) = ω (S.qr (S.P.src r)) := by linarith
      rw [this]; push_cast; ring

include hRC1 hRC2 in
/-- **Theorem 9.1, products with two-sided output** (cases 2, 4, 5). -/
theorem eq_TB (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r s t : R} (hr0 : r ≠ S.P.e (S.P.src r)) (hs0 : s ≠ S.P.e (S.P.src s))
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hBt : S.TB χ t) :
    S.DD χ ω X Y t = S.DD χ ω X Y r + S.DD χ ω X Y s := by
  rcases (S.table_B hχ hprim hr0 hs0 h hBt).1 with ⟨hBr, hBs⟩ | ⟨hTr, hTs⟩
  · rw [S.DD_TB _ _ _ hBt, S.DD_TB _ _ _ hBr, S.DD_TB _ _ _ hBs, hω r s t hBr hBs hBt h]
  obtain ⟨t1, t2, t3, -⟩ := S.prod_of h
  obtain ⟨i, r0, hgr, hTr0, hri⟩ := S.layer_TL_exists hprim hTr
  obtain ⟨j, s0, hgs, hTs0, hsj⟩ := S.layer_TR_exists hprim hTs
  have hsx := S.supp_of_qh hTr.2.1
  have hsz := S.supp_of_qh' hTs.2.2
  have hri' := hri; have hsj' := hsj
  rw [S.qh_of_supp χ hsx] at hri'; rw [S.qh_of_supp χ hsz] at hsj'
  obtain ⟨a1, -⟩ := S.qpow_mul_endpoints hri'.symm
  obtain ⟨-, b2⟩ := S.mul_qpow_endpoints hsj'.symm
  have hrs0 : ⌜r⌝ * ⌜s0⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← h, hsj', ← mul_assoc, h0, zero_mul])
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne hrs0
  have hr0s0 : ⌜r0⌝ * ⌜s0⌝ ≠ 0 := fun h0 ↦ hrs0 (by rw [hri', mul_assoc, h0, mul_zero])
  obtain ⟨t', ht'⟩ := S.ray_of_mul_ne hr0s0
  have hut : ⌜u⌝ * S.q (S.P.tgt s) ^ j = ⌜t⌝ := by rw [← hu, mul_assoc, ← hsj', h]
  have hut' : S.q (S.P.src r) ^ i * ⌜t'⌝ = ⌜u⌝ := by rw [← ht', ← mul_assoc, ← hri', hu]
  obtain ⟨u1, u2, -, -⟩ := S.prod_of hu
  obtain ⟨c1, c2, -, c4⟩ := S.prod_of ht'
  have hqt : S.q (S.P.src r) * ⌜t⌝ ≠ 0 := by
    rw [← S.qh_of_supp χ hsx, ← t1]; exact hBt.2.1
  have htq : ⌜t⌝ * S.q (S.P.tgt s) ≠ 0 := by
    rw [← S.qh_of_supp χ hsz, ← t2]; exact hBt.2.2
  -- `u` and `t'` are two-sided
  have hBu : S.TB χ u := by
    have hu0 : u ≠ S.P.e (S.P.src u) := by
      apply S.ne_e_of_deg; rw [(S.prod_of hu).2.2.2, map_add]
      have := S.P.deg_pos r hr0; have := S.P.deg_nonneg s0; linarith
    have h1 : S.qh χ (S.P.src u) * ⌜u⌝ ≠ 0 := by
      rw [u1, S.qh_of_supp χ hsx]; intro h0; apply hqt; rw [← hut, ← mul_assoc, h0, zero_mul]
    have h2 : ⌜u⌝ * S.qh χ (S.P.tgt u) ≠ 0 := by
      rw [u2, ← b2, S.qh_of_supp χ hsz]; intro h0; apply htq
      rw [← hut, mul_assoc, ← pow_succ, pow_succ', ← mul_assoc, h0, zero_mul]
    exact ⟨(S.shift_of_qh_mul hu0 h1).1, h1, h2⟩
  have hBt' : S.TB χ t' := by
    have ht0 : t' ≠ S.P.e (S.P.src t') := by
      apply S.ne_e_of_deg; rw [c4, map_add]
      have := S.P.deg_pos r0 hTr0.1.1; have := S.P.deg_nonneg s0; linarith
    have h1 : S.qh χ (S.P.src t') * ⌜t'⌝ ≠ 0 := by
      rw [c1, ← a1, S.qh_of_supp χ hsx]; intro h0; apply hBu.2.1
      rw [u1, S.qh_of_supp χ hsx, ← hut', ← mul_assoc, ← pow_succ', pow_succ, mul_assoc, h0,
        mul_zero]
    have h2 : ⌜t'⌝ * S.qh χ (S.P.tgt t') ≠ 0 := by
      rw [c2, ← b2, S.qh_of_supp χ hsz]; intro h0; apply hBu.2.2
      rw [u2, ← b2, S.qh_of_supp χ hsz, ← hut', mul_assoc, h0, mul_zero]
    exact ⟨(S.shift_of_qh_mul ht0 h1).1, h1, h2⟩
  have hLR := S.eq_LR_gen k ω X Y hRC2 hRC1 hfin hχ hprim hω hgr hTr0 hgs hTs0 ht' hBt'
  rw [S.DD_TB _ _ _ hBt, S.DD_TL _ _ _ hχ hTr hgr hri, S.DD_TR _ _ _ hχ hTs hgs hsj,
    S.ω_powq ω hω hBu j hBt (by rw [u2, ← b2]; exact hut),
    S.ω_qpow ω hω hBt' i hBu (by rw [c1, ← a1]; exact hut'), hLR, u2, ← b2, c1, ← a1]
  ring

/-- **Theorem 9.1, products with right-sided output** (the dual of `eq_TL`). -/
theorem eq_TR (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s)
    {r s t : R} (hr0 : r ≠ S.P.e (S.P.src r)) (hs0 : s ≠ S.P.e (S.P.src s))
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hT : S.TR χ t) :
    (S.TR χ s → S.DD χ ω X Y t = S.DD χ ω X Y s) ∧
      (S.TB χ s → S.DD χ ω X Y t = S.DD χ ω X Y r + S.DD χ ω X Y s) := by
  have := S.op.eq_TL k ω Y X (S.P.op_isRepresentationFinite k hfin) hχ hprim (S.hω_op ω hω)
    (r := s) (s := r) (t := t)
    (by change s ≠ S.P.e (S.P.tgt s); rwa [S.ne_e_iff_op])
    (by change r ≠ S.P.e (S.P.tgt r); rwa [S.ne_e_iff_op])
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, h]) ((S.op_TL t).2 hT)
  simp only [S.op_DD ω X Y hχ hprim] at this
  refine ⟨fun h1 ↦ this.1 ((S.op_TL s).2 h1), fun h1 ↦ ?_⟩
  rw [this.2 ((S.op_TB s).2 h1), add_comm]

include hRC1 hRC2 in
/-- **The integer coefficients solve all nonzero-product Leibniz equations**
(proof of Theorem 9.1, `α` well defined). -/
theorem isSol_DD (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hω : ∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → ω t = ω r + ω s) :
    S.IsSol χ (S.DD χ ω X Y) := by
  classical
  refine ⟨fun r h ↦ S.DD_unshift ω X Y h, fun r s t h ht ↦ ?_⟩
  obtain ⟨t1, t2, t3, -⟩ := S.prod_of h
  by_cases hr0 : r = S.P.e (S.P.src r)
  · -- an identity first factor
    have hre : ⌜r⌝ = ⌜S.P.e (S.P.src r)⌝ := congrArg _ hr0
    have hsr : S.P.src s = S.P.src r := by
      rw [← t3]; nth_rewrite 1 [hr0]; rw [S.P.tgt_e]
    have hst : s = t := by
      rw [hre, S.e_mul_rr' s hsr] at h
      exact S.rr_inj h
    subst hst
    have hEL : ¬ S.EL χ r s s := fun h' ↦ h'.1.1 hr0
    have hER : S.ER χ r s s := ⟨ht, by
      rw [hre]; exact S.e_mul_rr' _ (by rw [(S.succ_spec χ ht).1, hsr])⟩
    rw [if_neg hEL, if_pos hER, zero_add]
  by_cases hs0 : s = S.P.e (S.P.src s)
  · have hrt : r = t := by
      rw [hs0, ← t3, S.rr_mul_e] at h
      exact S.rr_inj h
    subst hrt
    have hER : ¬ S.ER χ r s r := fun h' ↦ h'.1.1 hs0
    have hEL : S.EL χ r s r := ⟨ht, by
      rw [hs0, ← t3, ← (S.succ_spec χ ht).2.1]; exact S.rr_mul_e _⟩
    rw [if_pos hEL, if_neg hER, add_zero]
  rcases S.types_of_shift hχ hprim ht with hT | hT | hT
  · rcases S.table_L hχ hprim hr0 hs0 h hT with ⟨hTr, hEL, hER⟩ | ⟨hBr, -, hEL, hER⟩
    · rw [if_pos hEL, if_neg hER, add_zero]
      exact (S.eq_TL k ω X Y hfin hχ hprim hω hr0 hs0 h hT).1 hTr
    · rw [if_pos hEL, if_pos hER]
      exact (S.eq_TL k ω X Y hfin hχ hprim hω hr0 hs0 h hT).2 hBr
  · rcases S.table_R hχ hprim hr0 hs0 h hT with ⟨hTs, hER, hEL⟩ | ⟨hBs, -, hEL, hER⟩
    · rw [if_neg hEL, if_pos hER, zero_add]
      exact (S.eq_TR k ω X Y hfin hχ hprim hω hr0 hs0 h hT).1 hTs
    · rw [if_pos hEL, if_pos hER]
      exact (S.eq_TR k ω X Y hfin hχ hprim hω hr0 hs0 h hT).2 hBs
  · obtain ⟨-, hEL, hER⟩ := S.table_B hχ hprim hr0 hs0 h hT
    rw [if_pos hEL, if_pos hER]
    exact S.eq_TB k ω X Y hRC2 hRC1 hfin hχ hprim hω hr0 hs0 h hT

/-! ### Solutions modulo two -/

omit [IsAlgClosed k] in
open Classical in
theorem op_isSol {M : Type*} [AddCommGroup M] {d : R → M} (hd : S.IsSol χ d) :
    S.op.IsSol χ d := by
  refine ⟨fun r h ↦ hd.1 r (fun h' ↦ h ((S.op_shift r).2 h')), fun r s t h ht ↦ ?_⟩
  have ht' := (S.op_shift t).1 ht
  have h' : ⌜s⌝ * ⌜r⌝ = ⌜t⌝ := S.P.toOp_injective (by rw [Tab.toOp_mul]; exact h)
  rw [hd.2 s r t h' ht', add_comm]
  congr 1
  · by_cases hE : S.ER χ s r t
    · rw [if_pos hE, if_pos ((S.op_EL ht').2 hE)]
    · rw [if_neg hE, if_neg (fun h'' ↦ hE ((S.op_EL ht').1 h''))]
  · by_cases hE : S.EL χ s r t
    · rw [if_pos hE, if_pos ((S.op_ER ht').2 hE)]
    · rw [if_neg hE, if_neg (fun h'' ↦ hE ((S.op_ER ht').1 h''))]

omit [IsAlgClosed k] in
open Classical in
/-- The equations of a solution for products with left-sided output. -/
theorem sol_TL (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {M : Type*} [AddCommGroup M] {d : R → M}
    (hd : S.IsSol χ d) {r s t : R} (hr0 : r ≠ S.P.e (S.P.src r)) (hs0 : s ≠ S.P.e (S.P.src s))
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hT : S.TL χ t) :
    (S.TL χ r → d t = d r) ∧ (S.TB χ r → d t = d r + d s) := by
  rw [hd.2 r s t h hT.1]
  rcases S.table_L hχ hprim hr0 hs0 h hT with ⟨hTr, hEL, hER⟩ | ⟨hBr, -, hEL, hER⟩
  · rw [if_pos hEL, if_neg hER, add_zero]
    exact ⟨fun _ ↦ rfl, fun h' ↦ absurd hTr.2.2 h'.2.2⟩
  · rw [if_pos hEL, if_pos hER]
    exact ⟨fun h' ↦ absurd hBr.2.2 (by rw [h'.2.2]; exact fun h'' ↦ h'' rfl), fun _ ↦ rfl⟩

omit [IsAlgClosed k] in
open Classical in
/-- The equations of a solution for products with two-sided output. -/
theorem sol_TB (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {M : Type*} [AddCommGroup M] {d : R → M}
    (hd : S.IsSol χ d) {r s t : R} (hr0 : r ≠ S.P.e (S.P.src r)) (hs0 : s ≠ S.P.e (S.P.src s))
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hB : S.TB χ t) : d t = d r + d s := by
  rw [hd.2 r s t h hB.1]
  obtain ⟨-, hEL, hER⟩ := S.table_B hχ hprim hr0 hs0 h hB
  rw [if_pos hEL, if_pos hER]

/-- The recursion of `DL` computes any solution modulo two. -/
theorem DL_mod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {d : R → ZMod 2} (hd : S.IsSol χ d)
    (hωd : ∀ r, S.TB χ r → (ω r : ZMod 2) = d r) (hXd : ∀ a, (X a : ZMod 2) = d a)
    {r : R} (hr : S.IsGen r) (hT : S.TL χ r) : (S.DL χ ω X r : ZMod 2) = d r := by
  induction hm : (S.P.deg (S.P.wt r)).toNat using Nat.strong_induction_on generalizing r with
  | _ m ih =>
    have hr0 : r ≠ S.P.e (S.P.src r) := hT.1.1
    have ha := S.fstA_spec hr0
    have hw := S.fstRest_spec hr0
    rw [S.DL_eq k ω X hfin hχ hprim hr hT ha hw]
    by_cases hw0 : S.fstRest r = S.P.e (S.P.src (S.fstRest r))
    · -- the ray is an ordinary arrow
      have := S.src_of_mul_ne (by rw [hw]; exact S.rr_ne r)
      rw [hw0, ← this, S.rr_mul_e] at hw
      have har := S.rr_inj hw
      have hnB : ¬ S.TB χ (S.fstA r) := fun h ↦ by rw [har] at h; exact h.2.2 hT.2.2
      rw [if_neg hnB, hXd, har]
    · by_cases hB : S.TB χ (S.fstA r)
      · obtain ⟨g, t, dl⟩ := S.rest_TL k hfin hχ hprim hr hT ha.1 hB hw
        rw [if_pos hB, Int.cast_add, hωd _ hB, ih _ (by have := S.P.deg_nonneg (S.fstRest r); omega)
          g t rfl, (S.sol_TL hχ hprim hd ha.1.1 hw0 hw hT).2 hB]
      · have hTa : S.TL χ (S.fstA r) := by
          have hqa : S.qh χ (S.P.src (S.fstA r)) * ⌜S.fstA r⌝ ≠ 0 := by
            intro h0; apply hT.2.1; rw [← hw, ← mul_assoc, (S.prod_of hw).1, h0, zero_mul]
          exact ⟨(S.shift_of_qh_mul ha.1.1 hqa).1, hqa,
            by by_contra h'; exact hB ⟨(S.shift_of_qh_mul ha.1.1 hqa).1, hqa, h'⟩⟩
        rw [if_neg hB, hXd, (S.sol_TL hχ hprim hd ha.1.1 hw0 hw hT).1 hTa]

omit [IsAlgClosed k] in
/-- A solution along local powers of a left-sided ray: `d(q̂^i t₀) = i d(q̂) + d(t₀)`. -/
theorem sol_layer (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {M : Type*} [AddCommGroup M]
    {d : R → M} (hd : S.IsSol χ d) {t0 : R} (hT0 : S.TL χ t0) (i : ℕ) :
    ∀ {t : R}, S.TL χ t → ⌜t⌝ = S.qh χ (S.P.src t0) ^ i * ⌜t0⌝ →
      d t = i • d (S.qr (S.P.src t0)) + d t0 := by
  have hs := S.supp_of_qh hT0.2.1
  have hqx := S.qh_of_supp χ hs
  induction i with
  | zero => intro t hT h; rw [pow_zero, one_mul] at h; rw [S.rr_inj h]; simp
  | succ i ih =>
    intro t hT h
    rw [hqx] at h
    have hne : S.q (S.P.src t0) ^ i * ⌜t0⌝ ≠ 0 := by
      intro h0; apply S.rr_ne t; rw [h, pow_succ', mul_assoc, h0, mul_zero]
    obtain ⟨t1, ht1⟩ := S.mul_right_ray hne
    obtain ⟨e1, -⟩ := S.qpow_mul_endpoints ht1
    have htt1 : ⌜t⌝ = S.q (S.P.src t0) ^ 1 * ⌜t1⌝ := by rw [h, ← ht1, ← mul_assoc, ← pow_add, add_comm]
    obtain ⟨f1, -⟩ := S.qpow_mul_endpoints htt1.symm
    have ht10 : t1 ≠ S.P.e (S.P.src t1) := by
      apply S.ne_e_of_deg
      rw [S.wt_of_eq_qpow_mul (f := t0) ht1.symm, map_add, map_nsmul, nsmul_eq_mul]
      have := S.P.deg_pos t0 hT0.1.1; have := S.deg_χ_nonneg (S.P.src t0); positivity
    have hTt1 : S.TL χ t1 := S.tl_factor hT (by rw [f1, e1, hqx]; exact htt1) ht10
    have hq2 : S.q (S.P.src t0) ^ 2 ≠ 0 := by
      intro h0; apply hT.2.1
      rw [f1, e1, hqx, htt1, pow_one, ← mul_assoc, ← pow_two, h0, zero_mul]
    have hqr := S.qr_spec hs.1
    have hBq := S.qr_TB hq2 hs
    have hprod : ⌜S.qr (S.P.src t0)⌝ * ⌜t1⌝ = ⌜t⌝ := by rw [hqr, htt1, pow_one]
    have e := (S.sol_TL hχ hprim hd hBq.1.1 ht10 hprod hT).2 hBq
    rw [e, ih hTt1 (by rw [hqx]; exact ht1.symm), succ_nsmul]
    abel

/-- The coefficients reduce to a given solution modulo two on left-sided rays. -/
theorem DD_mod_TL (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {d : R → ZMod 2} (hd : S.IsSol χ d)
    (hωd : ∀ r, S.TB χ r → (ω r : ZMod 2) = d r) (hXd : ∀ a, (X a : ZMod 2) = d a)
    {r : R} (hT : S.TL χ r) : (S.DD χ ω X Y r : ZMod 2) = d r := by
  obtain ⟨i, r0, hg, hT0, hi⟩ := S.layer_TL_exists hprim hT
  have hs := S.supp_of_qh hT.2.1
  obtain ⟨e1, -⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ hs]; exact hi.symm)
  rw [S.DD_TL _ _ _ hχ hT hg hi, S.sol_layer hχ hprim hd hT0 i hT (by rw [← e1]; exact hi),
    ← e1, Int.cast_add, S.DL_mod k ω X hfin hχ hprim hd hωd hXd hg hT0, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; simp
  · have hq2 : S.q (S.P.src r) ^ 2 ≠ 0 := by
      intro h'; apply hT.2.1
      rw [S.qh_of_supp χ hs, hi, S.qh_of_supp χ hs, ← mul_assoc, ← pow_succ',
        show i + 1 = (i - 1) + 2 by omega, pow_add, h', mul_zero, zero_mul]
    rw [Int.cast_mul, hωd _ (S.qr_TB hq2 hs)]; push_cast; ring

/-- **The coefficients reduce to a given solution modulo two** (`βα = id` in the proof of
Theorem 9.1). -/
theorem DD_mod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {d : R → ZMod 2} (hd : S.IsSol χ d)
    (hωd : ∀ r, S.TB χ r → (ω r : ZMod 2) = d r) (hXd : ∀ a, (X a : ZMod 2) = d a)
    (hYd : ∀ b, (Y b : ZMod 2) = d b) (r : R) : (S.DD χ ω X Y r : ZMod 2) = d r := by
  by_cases hB : S.TB χ r
  · rw [S.DD_TB _ _ _ hB, hωd r hB]
  by_cases hL : S.TL χ r
  · exact S.DD_mod_TL k ω X Y hfin hχ hprim hd hωd hXd hL
  by_cases hR : S.TR χ r
  · rw [← S.op_DD ω X Y hχ hprim]
    exact S.op.DD_mod_TL k ω Y X (S.P.op_isRepresentationFinite k hfin) hχ hprim
      (S.op_isSol hd) (fun r h ↦ hωd r ((S.op_TB r).1 h)) hYd ((S.op_TL r).2 hR)
  · have hs : ¬ S.Shift χ r := by
      intro hs
      rcases S.types_of_shift hχ hprim hs with h | h | h
      · exact hL h
      · exact hR h
      · exact hB h
    rw [S.DD_unshift _ _ _ hs, hd.1 r hs, Int.cast_zero]

omit [IsAlgClosed k] in
/-- The equations of a solution for products with right-sided output. -/
theorem sol_TR (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {M : Type*} [AddCommGroup M] {d : R → M}
    (hd : S.IsSol χ d) {r s t : R} (hr0 : r ≠ S.P.e (S.P.src r)) (hs0 : s ≠ S.P.e (S.P.src s))
    (h : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hT : S.TR χ t) (hTs : S.TR χ s) : d t = d s :=
  (S.op.sol_TL hχ hprim (S.op_isSol hd) (r := s) (s := r) (t := t)
    (by change s ≠ S.P.e (S.P.tgt s); rwa [S.ne_e_iff_op])
    (by change r ≠ S.P.e (S.P.tgt r); rwa [S.ne_e_iff_op])
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, h]) ((S.op_TL t).2 hT)).1 ((S.op_TL s).2 hTs)

omit [IsAlgClosed k] in
/-- A crown row holds for every solution. -/
theorem crown_row_sol (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {M : Type*} [AddCommGroup M]
    {d : R → M} (hd : S.IsSol χ d) {a b f : R} (hr : S.CrownRow χ a b f) :
    d f = d a + d b := by
  obtain ⟨-, hBf, hTa, hTb, v, -, hv, -, -, -, hTv, -, ⟨-, w, hw⟩, -⟩ := hr
  rw [S.sol_TB hχ hprim hd hTa.1.1 hTv.1.1 hv hBf]
  congr 1
  by_cases hw0 : w = S.P.e (S.P.src w)
  · have := S.src_of_mul_ne (by rw [hw]; exact S.rr_ne v)
    have h1 : S.P.src b = S.P.src w := by rw [← this]; nth_rewrite 1 [hw0]; rw [S.P.tgt_e]
    rw [hw0, S.e_mul_rr' b h1] at hw
    rw [S.rr_inj hw]
  · exact S.sol_TR hχ hprim hd hw0 hTb.1.1 hw hTv hTb

/-- A nondeep row holds modulo two for every solution. -/
theorem nd_row_sol (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {d : R → ZMod 2} (hd : S.IsSol χ d) {a b : R} {x : V}
    (hr : S.NdRow χ a b x) : d a + d b = 0 := by
  obtain ⟨e, l, hN, ha, hb⟩ := hr
  have hTa := S.nondeep_first_TL k hfin hχ hprim hN ha
  have hTb := S.nondeep_last_TR k hfin hχ hprim hN hb
  obtain ⟨he, hl, e1, e2, l2, -, hTe, hTl, hel, hq3⟩ := hN
  have hde : d e = d a := by
    obtain ⟨-, w, hw⟩ := ha
    by_cases hw0 : w = S.P.e (S.P.src w)
    · have := S.src_of_mul_ne (by rw [hw]; exact S.rr_ne e)
      rw [hw0, ← this, S.rr_mul_e] at hw
      rw [S.rr_inj hw]
    · exact (S.sol_TL hχ hprim hd hTa.1.1 hw0 hw hTe).1 hTa
  have hdl : d l = d b := by
    obtain ⟨-, w, hw⟩ := hb
    by_cases hw0 : w = S.P.e (S.P.src w)
    · have := S.src_of_mul_ne (by rw [hw]; exact S.rr_ne l)
      have h1 : S.P.src b = S.P.src w := by rw [← this]; nth_rewrite 1 [hw0]; rw [S.P.tgt_e]
      rw [hw0, S.e_mul_rr' b h1] at hw
      rw [S.rr_inj hw]
    · exact S.sol_TR hχ hprim hd hw0 hTb.1.1 hw hTl hTb
  have hsx := S.supp_of_qh hTe.2.1
  rw [e1] at hsx
  have hqx : S.qh χ x = S.q x := S.qh_of_supp χ hsx
  rw [hqx] at hel hq3
  have hq2 : S.q x ^ 2 ≠ 0 := fun h0 ↦ hq3 (by rw [pow_succ, h0, zero_mul])
  have hel0 : ⌜e⌝ * ⌜l⌝ ≠ 0 := by rw [hel]; exact hq2
  obtain ⟨q2, hq2r⟩ := S.ray_of_mul_ne hel0
  have hq2x : ⌜q2⌝ = S.q x ^ 2 := hq2r.symm.trans hel
  obtain ⟨p1, p2, -, -⟩ := S.prod_of hq2r
  have hBq2 : S.TB χ q2 := by
    have hq20 : q2 ≠ S.P.e (S.P.src q2) := by
      apply S.ne_e_of_deg
      rw [S.wt_of_eq_qpow hq2x, map_nsmul, nsmul_eq_mul]
      have := S.χ_deg_pos x hsx.1; positivity
    have h1 : S.qh χ (S.P.src q2) * ⌜q2⌝ ≠ 0 := by
      rw [p1, e1, hqx, hq2x, ← pow_succ']; exact hq3
    have h2 : ⌜q2⌝ * S.qh χ (S.P.tgt q2) ≠ 0 := by
      rw [p2, l2, hqx, hq2x, ← pow_succ]; exact hq3
    exact ⟨(S.shift_of_qh_mul hq20 h1).1, h1, h2⟩
  have hBq := S.qr_TB hq2 hsx
  have e3 := S.sol_TB hχ hprim hd hTe.1.1 hTl.1.1 hq2r hBq2
  have e4 := S.sol_TB hχ hprim hd hBq.1.1 hBq.1.1
    (show ⌜S.qr x⌝ * ⌜S.qr x⌝ = ⌜q2⌝ by rw [S.qr_spec hsx.1, ← pow_two, hq2x]) hBq2
  rw [← hde, ← hdl, ← e3, e4]
  exact CharTwo.add_self_eq_zero _

/-! ### The lift -/

/-- The canonical integer lift of the variable `X_a`. -/
def Xc (d : R → ZMod 2) (a : R) : ℤ := ((d a).val : ℤ)

variable (χ) in
open Classical in
/-- The variable `Y_b`, read off from a row containing it (`eq:crown-coefficient-group`). -/
def Yc (ω : R → ℤ) (d : R → ZMod 2) (b : R) : ℤ :=
  if h : ∃ a f, S.CrownRow χ a b f then ω h.choose_spec.choose - Xc d h.choose
  else if h' : ∃ a x, S.NdRow χ a b x then 2 * ω (S.qr h'.choose_spec.choose) - Xc d h'.choose
  else ((d b).val : ℤ)

omit [IsAlgClosed k] in
theorem Xc_mod (d : R → ZMod 2) (a : R) : ((Xc d a : ℤ) : ZMod 2) = d a := by
  rw [Xc, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem rc1 (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ) (hprim : Prim χ)
    {d : R → ZMod 2} (hd : S.IsSol χ d) :
    ∀ a b f, S.CrownRow χ a b f → Xc d a + S.Yc χ ω d b = ω f := by
  classical
  intro a b f hr
  have hex : ∃ a f, S.CrownRow χ a b f := ⟨a, f, hr⟩
  rw [Yc, dif_pos hex]
  have hr' := hex.choose_spec.choose_spec
  have hff := S.crown_row_unique_b k hfin hχ hprim hr' hr
  have e1 := S.crown_row_sol hχ hprim hd hr
  have e2 := S.crown_row_sol hχ hprim hd hr'
  rw [hff] at e2
  have haa : d hex.choose = d a := by
    have := e2.symm.trans e1; exact add_right_cancel this
  rw [hff, Xc, Xc, haa]; ring

theorem rc2 (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ) (hprim : Prim χ)
    {d : R → ZMod 2} (hd : S.IsSol χ d) :
    ∀ a b x, S.NdRow χ a b x → Xc d a + S.Yc χ ω d b = 2 * ω (S.qr x) := by
  classical
  intro a b x hn
  have hnc : ¬ ∃ a f, S.CrownRow χ a b f := by
    rintro ⟨a', f, hr⟩; exact S.crown_nd_disjoint_b k hfin hχ hprim hr hn
  have hex : ∃ a x, S.NdRow χ a b x := ⟨a, x, hn⟩
  rw [Yc, dif_neg hnc, dif_pos hex]
  have hn' := hex.choose_spec.choose_spec
  have tgt_eq : ∀ {a' : R} {x' : V}, S.NdRow χ a' b x' → x' = S.P.tgt b := by
    rintro a' x' ⟨e, l, ⟨-, -, -, -, l2, -⟩, -, ⟨-, w, hw⟩⟩
    rw [← l2, (S.prod_of hw).2.1]
  have hxx : hex.choose_spec.choose = x := (tgt_eq hn').trans (tgt_eq hn).symm
  have e1 := S.nd_row_sol k hfin hχ hprim hd hn
  have e2 := S.nd_row_sol k hfin hχ hprim hd hn'
  have haa : d hex.choose = d a := by
    have := e2.trans e1.symm; exact add_right_cancel this
  rw [hxx, Xc, Xc, haa]; ring

theorem Yc_mod (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {d : R → ZMod 2} (hd : S.IsSol χ d)
    (hωd : ∀ r, S.TB χ r → (ω r : ZMod 2) = d r) (b : R) : ((S.Yc χ ω d b : ℤ) : ZMod 2) = d b := by
  classical
  unfold Yc
  split_ifs with h1 h2
  · have hr := h1.choose_spec.choose_spec
    have e := S.crown_row_sol hχ hprim hd hr
    rw [Int.cast_sub, hωd _ hr.2.1, Xc_mod, e]; ring
  · have e := S.nd_row_sol k hfin hχ hprim hd h2.choose_spec.choose_spec
    rw [Int.cast_sub, Int.cast_mul, Xc_mod, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul,
      zero_sub, ← add_eq_zero_iff_neg_eq.1 e]
  · rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **Theorem 9.1(3)** (`thm:integral-partial-lifting`): every solution modulo two of the
nonzero-product Leibniz equations lifts to an integer solution. The hypothesis `hW` is the
lifting property of `W_χ = W(Q_χ)` (free by Lemma 9.2 and the induction hypothesis of
Prop 8.3). -/
theorem integral_lifting (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hW : ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r)
    {d : R → ZMod 2} (hd : S.IsSol χ d) :
    ∃ D : R → ℤ, S.IsSol χ D ∧ ∀ r, (D r : ZMod 2) = d r := by
  obtain ⟨ω, hω, hωd⟩ := hW d (fun r s t hr hs ht h ↦ S.sol_TB hχ hprim hd hr.1.1 hs.1.1 h ht)
  refine ⟨S.DD χ ω (Xc d) (S.Yc χ ω d), ?_, ?_⟩
  · exact S.isSol_DD k ω (Xc d) (S.Yc χ ω d) (S.rc2 k ω hfin hχ hprim hd)
      (S.rc1 k ω hfin hχ hprim hd) hfin hχ hprim hω
  · exact S.DD_mod k ω (Xc d) (S.Yc χ ω d) hfin hχ hprim hd hωd (Xc_mod d)
      (S.Yc_mod k ω hfin hχ hprim hd hωd)

end Sys

end RaySys

end MultiplicativeBasisDeformations
