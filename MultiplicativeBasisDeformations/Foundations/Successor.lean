module

public import MultiplicativeBasisDeformations.Foundations.GeneratingPaths

/-!
# Section 9: successors and endpoint types

`def:primitive-characters`, `set:fixed-character`, `def:successor-types`
(`primitive-ray-equations.tex`): for a positive primitive character `χ ∈ L`,
`q̂_x = q_x` if `q_x ≠ 0` and `ℓ(q_x) = χ`, and `0` otherwise. A nonidentity ray is
shiftable if a ray with the same endpoints has weight `ℓ(r) + χ` (its successor `r⁺`). The
successor is obtained by one local generator of character `χ` (`succ_by_gen`), which gives the
three endpoint types `L`, `R`, `B`. Also `lem:primitive-action-generation`
(`primitive-ray-equations.tex`).
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

/-- A primitive character: not a proper integer multiple. -/
def Prim (χ : L) : Prop := ∀ (n : ℕ) (η : L), χ = n • η → n ≤ 1

/-! ### Lemma 9.4: primitive action generation -/

/-- **Lemma 9.4** (`lem:primitive-action-generation`): for `f` generating with `ℓ(q_x)`
primitive and `q_x f ≠ 0`, the Hom is cyclic at `x`; if it is also cyclic at `y`, then
`ℓ(q_y) = ℓ(q_x)` and `q_x f = f q_y`. -/
theorem prim_action_gen {f : R} (hf : S.IsGen f) (hprim : Prim (S.χ (S.P.src f)))
    (hqf : S.q (S.P.src f) * ⌜f⌝ ≠ 0) : S.CycL f ∧
      (S.CycR f → S.χ (S.P.tgt f) = S.χ (S.P.src f) ∧
        S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f)) := by
  have key : S.CycR f → S.χ (S.P.tgt f) = S.χ (S.P.src f) ∧
      S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f) := by
    intro hR
    rcases S.src_action_of_cycR hR rfl rfl with h | ⟨a, ha, h⟩
    · exact absurd h hqf
    · have hw := congrArg S.wtM h
      have hne : ⌜f⌝ * S.q (S.P.tgt f) ^ a ≠ 0 := h ▸ hqf
      rw [S.wtM_mul _ _ hqf, S.wtM_mul _ _ hne, S.wtM_qpow _ _
        (fun h0 ↦ hne (by rw [h0, mul_zero])), add_comm] at hw
      have hχ : S.χ (S.P.src f) = a • S.χ (S.P.tgt f) := add_left_cancel hw
      have ha1 : a = 1 := le_antisymm (hprim a _ hχ) ha
      subst ha1
      rw [one_smul] at hχ
      exact ⟨hχ.symm, by rw [h, pow_one]⟩
  refine ⟨?_, key⟩
  rcases S.gen_cyc hf with hL | hR
  · exact hL
  · obtain ⟨-, hqq⟩ := key hR
    have hpow : ∀ j : ℕ, ⌜f⌝ * S.q (S.P.tgt f) ^ j = S.q (S.P.src f) ^ j * ⌜f⌝ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, ← hqq, ← mul_assoc, ← pow_succ]
    intro s h1 h2
    obtain ⟨j, hj⟩ := hR s h1 h2
    exact ⟨j, by rw [hj, hpow]⟩

/-! ### The fixed character -/

section Char

variable (χ : L)

/-- A supporting vertex: its local generator has character `χ`. -/
def Supp (x : V) : Prop := S.q x ≠ 0 ∧ S.χ x = χ

open Classical in
/-- `q̂_x` (`set:fixed-character`). -/
def qh (x : V) : M S.P.toMult := if S.Supp χ x then S.q x else 0

/-- A shiftable ray (`def:successor-types`(2)). -/
def Shift (r : R) : Prop :=
  r ≠ S.P.e (S.P.src r) ∧
    ∃ r', S.P.src r' = S.P.src r ∧ S.P.tgt r' = S.P.tgt r ∧ S.P.wt r' = S.P.wt r + χ

open Classical in
/-- The successor `r⁺`. -/
def succ (r : R) : R :=
  if h : ∃ r', S.P.src r' = S.P.src r ∧ S.P.tgt r' = S.P.tgt r ∧ S.P.wt r' = S.P.wt r + χ
  then h.choose else r

theorem succ_spec {r : R} (h : S.Shift χ r) : S.P.src (S.succ χ r) = S.P.src r ∧
    S.P.tgt (S.succ χ r) = S.P.tgt r ∧ S.P.wt (S.succ χ r) = S.P.wt r + χ := by
  classical
  rw [succ, dif_pos h.2]
  exact h.2.choose_spec

/-- The successor is the only ray with its endpoints and weight. -/
theorem eq_succ {r t : R} (h : S.Shift χ r) (h1 : S.P.src t = S.P.src r)
    (h2 : S.P.tgt t = S.P.tgt r) (h3 : S.P.wt t = S.P.wt r + χ) : t = S.succ χ r := by
  obtain ⟨e1, e2, e3⟩ := S.succ_spec χ h
  exact S.P.sep _ _ (h1.trans e1.symm) (h2.trans e2.symm) (h3.trans e3.symm)

theorem qh_of_supp {x : V} (h : S.Supp χ x) : S.qh χ x = S.q x := by
  classical
  rw [qh, if_pos h]

theorem qh_of_not_supp {x : V} (h : ¬ S.Supp χ x) : S.qh χ x = 0 := by
  classical
  rw [qh, if_neg h]

/-- `q̂_x r` is zero or the successor. -/
theorem qh_mul_cases {r : R} (h : S.Shift χ r) :
    S.qh χ (S.P.src r) * ⌜r⌝ = 0 ∨ S.qh χ (S.P.src r) * ⌜r⌝ = ⌜S.succ χ r⌝ := by
  classical
  by_cases hs : S.Supp χ (S.P.src r)
  · rw [qh_of_supp _ _ hs]
    by_cases h0 : S.q (S.P.src r) * ⌜r⌝ = 0
    · exact Or.inl h0
    · right
      obtain ⟨t, ht⟩ := S.mul_right_ray h0
      have hU : S.InU t r := ⟨1, 0, by rw [← ht, pow_zero, mul_one, pow_one]⟩
      obtain ⟨e1, e2, -⟩ := S.inU_endpoints hU
      rw [ht, S.eq_succ χ h e1 e2 ?_]
      have := congrArg S.wtM ht
      rw [S.wtM_mul _ _ h0, wtM_rr, wtM_rr] at this
      rw [← this, add_comm]
      change S.P.wt r + S.χ (S.P.src r) = _
      rw [hs.2]
  · left; rw [qh_of_not_supp _ _ hs, zero_mul]

/-- `r q̂_y` is zero or the successor. -/
theorem mul_qh_cases {r : R} (h : S.Shift χ r) :
    ⌜r⌝ * S.qh χ (S.P.tgt r) = 0 ∨ ⌜r⌝ * S.qh χ (S.P.tgt r) = ⌜S.succ χ r⌝ := by
  classical
  by_cases hs : S.Supp χ (S.P.tgt r)
  · rw [qh_of_supp _ _ hs]
    by_cases h0 : ⌜r⌝ * S.q (S.P.tgt r) = 0
    · exact Or.inl h0
    · right
      obtain ⟨t, ht⟩ := S.mul_left_ray h0
      have hU : S.InU t r := ⟨0, 1, by rw [← ht, pow_zero, one_mul, pow_one]⟩
      obtain ⟨e1, e2, -⟩ := S.inU_endpoints hU
      rw [ht, S.eq_succ χ h e1 e2 ?_]
      have := congrArg S.wtM ht
      rw [S.wtM_mul _ _ h0, wtM_rr, wtM_rr] at this
      rw [← this]
      change S.P.wt r + S.χ (S.P.tgt r) = _
      rw [hs.2]
  · left; rw [qh_of_not_supp _ _ hs, mul_zero]

variable {χ}

/-- **The successor is obtained by one local generator of character `χ`.** -/
theorem succ_by_gen (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r : R} (h : S.Shift χ r) :
    S.qh χ (S.P.src r) * ⌜r⌝ = ⌜S.succ χ r⌝ ∨ ⌜r⌝ * S.qh χ (S.P.tgt r) = ⌜S.succ χ r⌝ := by
  obtain ⟨e1, e2, e3⟩ := S.succ_spec χ h
  obtain ⟨f, f1, f2, hf⟩ := S.exists_gen r
  rcases S.gen_cyc hf with hL | hR
  · left
    obtain ⟨i, hi⟩ := hL r f1.symm f2.symm
    obtain ⟨i', hi'⟩ := hL (S.succ χ r) (e1.trans f1.symm) (e2.trans f2.symm)
    have w1 := S.wt_of_eq_qpow_mul hi
    have w2 := S.wt_of_eq_qpow_mul hi'
    have hd := S.deg_χ_nonneg (S.P.src f)
    have key : i' • S.χ (S.P.src f) = i • S.χ (S.P.src f) + χ := by
      have := e3
      rw [w1, w2] at this
      rw [← add_right_cancel_iff (a := S.P.wt f)]
      rw [this]; abel
    have hlt : i < i' := by
      have := congrArg S.P.deg key
      simp only [map_add, map_nsmul, nsmul_eq_mul] at this
      by_contra hle
      have : (i' : ℤ) * S.P.deg (S.χ (S.P.src f)) ≤ i * S.P.deg (S.χ (S.P.src f)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast not_lt.1 hle) hd
      linarith
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hn : (n + 1) • S.χ (S.P.src f) = χ := by
      rw [show i + n + 1 = i + (n + 1) by omega, add_nsmul] at key
      exact add_left_cancel key
    have hn1 : n = 0 := by have := hprim (n + 1) _ hn.symm; omega
    subst hn1
    rw [zero_add, one_smul] at hn
    have hq : S.q (S.P.src f) ≠ 0 := by
      intro h0
      apply S.rr_ne (S.succ χ r)
      rw [hi', h0, zero_pow (by omega), zero_mul]
    have hs : S.Supp χ (S.P.src r) := ⟨by rw [← f1]; exact hq, by rw [← f1]; exact hn⟩
    rw [S.qh_of_supp χ hs, hi', hi, ← f1, ← mul_assoc, ← pow_succ', show i + 0 + 1 = i + 1 by omega]
  · right
    obtain ⟨j, hj⟩ := hR r f1.symm f2.symm
    obtain ⟨j', hj'⟩ := hR (S.succ χ r) (e1.trans f1.symm) (e2.trans f2.symm)
    have wt_of : ∀ {t : R} {c : ℕ}, ⌜t⌝ = ⌜f⌝ * S.q (S.P.tgt f) ^ c →
        S.P.wt t = S.P.wt f + c • S.χ (S.P.tgt f) := by
      intro t c ht
      have hne : ⌜f⌝ * S.q (S.P.tgt f) ^ c ≠ 0 := ht ▸ S.rr_ne t
      have := congrArg S.wtM ht
      rw [wtM_rr, S.wtM_mul _ _ hne, S.wtM_qpow _ _ (fun h0 ↦ hne (by rw [h0, mul_zero])),
        wtM_rr] at this
      exact this
    have w1 := wt_of hj
    have w2 := wt_of hj'
    have hd := S.deg_χ_nonneg (S.P.tgt f)
    have key : j' • S.χ (S.P.tgt f) = j • S.χ (S.P.tgt f) + χ := by
      have := e3
      rw [w1, w2, add_assoc] at this
      exact add_left_cancel this
    have hlt : j < j' := by
      have := congrArg S.P.deg key
      simp only [map_add, map_nsmul, nsmul_eq_mul] at this
      by_contra hle
      have : (j' : ℤ) * S.P.deg (S.χ (S.P.tgt f)) ≤ j * S.P.deg (S.χ (S.P.tgt f)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast not_lt.1 hle) hd
      linarith
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hn : (n + 1) • S.χ (S.P.tgt f) = χ := by
      rw [show j + n + 1 = j + (n + 1) by omega, add_nsmul] at key
      exact add_left_cancel key
    have hn1 : n = 0 := by have := hprim (n + 1) _ hn.symm; omega
    subst hn1
    rw [zero_add, one_smul] at hn
    have hq : S.q (S.P.tgt f) ≠ 0 := by
      intro h0
      apply S.rr_ne (S.succ χ r)
      rw [hj', h0, zero_pow (by omega), mul_zero]
    have hs : S.Supp χ (S.P.tgt r) := ⟨by rw [← f2]; exact hq, by rw [← f2]; exact hn⟩
    rw [S.qh_of_supp χ hs, hj', hj, ← f2, mul_assoc, ← pow_succ, show j + 0 + 1 = j + 1 by omega]

variable (χ)

/-- Type `L`: a surviving source action only. -/
def TL (r : R) : Prop :=
  S.Shift χ r ∧ S.qh χ (S.P.src r) * ⌜r⌝ ≠ 0 ∧ ⌜r⌝ * S.qh χ (S.P.tgt r) = 0

/-- Type `R`: a surviving target action only. -/
def TR (r : R) : Prop :=
  S.Shift χ r ∧ S.qh χ (S.P.src r) * ⌜r⌝ = 0 ∧ ⌜r⌝ * S.qh χ (S.P.tgt r) ≠ 0

/-- Type `B`: both actions survive (and agree). -/
def TB (r : R) : Prop :=
  S.Shift χ r ∧ S.qh χ (S.P.src r) * ⌜r⌝ ≠ 0 ∧ ⌜r⌝ * S.qh χ (S.P.tgt r) ≠ 0

/-- Left successor substitution `r⁺ s = t⁺`. -/
def EL (r s t : R) : Prop := S.Shift χ r ∧ ⌜S.succ χ r⌝ * ⌜s⌝ = ⌜S.succ χ t⌝

/-- Right successor substitution `r s⁺ = t⁺`. -/
def ER (r s t : R) : Prop := S.Shift χ s ∧ ⌜r⌝ * ⌜S.succ χ s⌝ = ⌜S.succ χ t⌝

variable {χ}

theorem types_of_shift (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r : R} (h : S.Shift χ r) :
    S.TL χ r ∨ S.TR χ r ∨ S.TB χ r := by
  rcases S.succ_by_gen hχ hprim h with h1 | h1
  · by_cases h2 : ⌜r⌝ * S.qh χ (S.P.tgt r) = 0
    · exact Or.inl ⟨h, by rw [h1]; exact S.rr_ne _, h2⟩
    · exact Or.inr (Or.inr ⟨h, by rw [h1]; exact S.rr_ne _, h2⟩)
  · by_cases h2 : S.qh χ (S.P.src r) * ⌜r⌝ = 0
    · exact Or.inr (Or.inl ⟨h, h2, by rw [h1]; exact S.rr_ne _⟩)
    · exact Or.inr (Or.inr ⟨h, h2, by rw [h1]; exact S.rr_ne _⟩)

/-- A nonzero source action makes a nonidentity ray shiftable, with the action its successor. -/
theorem shift_of_qh_mul {r : R} (hr : r ≠ S.P.e (S.P.src r)) (h : S.qh χ (S.P.src r) * ⌜r⌝ ≠ 0) :
    S.Shift χ r ∧ S.qh χ (S.P.src r) * ⌜r⌝ = ⌜S.succ χ r⌝ := by
  classical
  have hs : S.Supp χ (S.P.src r) := by
    by_contra hs; exact h (by rw [S.qh_of_not_supp χ hs, zero_mul])
  rw [S.qh_of_supp χ hs] at h ⊢
  obtain ⟨t, ht⟩ := S.mul_right_ray h
  have hU : S.InU t r := ⟨1, 0, by rw [← ht, pow_zero, mul_one, pow_one]⟩
  obtain ⟨e1, e2, -⟩ := S.inU_endpoints hU
  have hw : S.P.wt t = S.P.wt r + χ := by
    have := congrArg S.wtM ht
    rw [S.wtM_mul _ _ h, wtM_rr, wtM_rr] at this
    rw [← this, add_comm]
    change S.P.wt r + S.χ (S.P.src r) = _
    rw [hs.2]
  have hsh : S.Shift χ r := ⟨hr, t, e1, e2, hw⟩
  exact ⟨hsh, by rw [ht, S.eq_succ χ hsh e1 e2 hw]⟩

/-- A nonzero target action makes a nonidentity ray shiftable, with the action its successor. -/
theorem shift_of_mul_qh {r : R} (hr : r ≠ S.P.e (S.P.src r)) (h : ⌜r⌝ * S.qh χ (S.P.tgt r) ≠ 0) :
    S.Shift χ r ∧ ⌜r⌝ * S.qh χ (S.P.tgt r) = ⌜S.succ χ r⌝ := by
  classical
  have hs : S.Supp χ (S.P.tgt r) := by
    by_contra hs; exact h (by rw [S.qh_of_not_supp χ hs, mul_zero])
  rw [S.qh_of_supp χ hs] at h ⊢
  obtain ⟨t, ht⟩ := S.mul_left_ray h
  have hU : S.InU t r := ⟨0, 1, by rw [← ht, pow_zero, one_mul, pow_one]⟩
  obtain ⟨e1, e2, -⟩ := S.inU_endpoints hU
  have hw : S.P.wt t = S.P.wt r + χ := by
    have := congrArg S.wtM ht
    rw [S.wtM_mul _ _ h, wtM_rr, wtM_rr] at this
    rw [← this]
    change S.P.wt r + S.χ (S.P.tgt r) = _
    rw [hs.2]
  have hsh : S.Shift χ r := ⟨hr, t, e1, e2, hw⟩
  exact ⟨hsh, by rw [ht, S.eq_succ χ hsh e1 e2 hw]⟩

/-- A nonzero product of nonidentity rays is not an identity. -/
theorem prod_ne_e {r s t : R} (hr : r ≠ S.P.e (S.P.src r)) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) :
    t ≠ S.P.e (S.P.src t) := by
  intro ht
  have h1 := S.P.deg_pos r hr
  have h2 := S.P.deg_nonneg s
  have := congrArg S.P.deg (S.prod_of hrs).2.2.2
  rw [ht, S.P.wt_e, map_zero, map_add] at this
  omega

/-- **Substitutions in a product are zero or the successor of the output.** -/
theorem subst_left {r s t : R} (hr : S.Shift χ r) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) :
    ⌜S.succ χ r⌝ * ⌜s⌝ = 0 ∨ (S.Shift χ t ∧ ⌜S.succ χ r⌝ * ⌜s⌝ = ⌜S.succ χ t⌝) := by
  by_cases h0 : ⌜S.succ χ r⌝ * ⌜s⌝ = 0
  · exact Or.inl h0
  right
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne h0
  obtain ⟨e1, e2, e3⟩ := S.succ_spec χ hr
  obtain ⟨u1, u2, -, u4⟩ := S.prod_of hu
  obtain ⟨t1, t2, -, t4⟩ := S.prod_of hrs
  have ht : S.Shift χ t := ⟨S.prod_ne_e hr.1 hrs, u, by rw [u1, e1, t1], by rw [u2, t2],
    by rw [u4, e3, t4]; abel⟩
  exact ⟨ht, by rw [hu]; exact congrArg _ (S.eq_succ χ (r := t) (t := u) ht
    (by rw [u1, e1, t1]) (by rw [u2, t2]) (by rw [u4, e3, t4]; abel))⟩

theorem subst_right {r s t : R} (hr : r ≠ S.P.e (S.P.src r)) (hs : S.Shift χ s)
    (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) :
    ⌜r⌝ * ⌜S.succ χ s⌝ = 0 ∨ (S.Shift χ t ∧ ⌜r⌝ * ⌜S.succ χ s⌝ = ⌜S.succ χ t⌝) := by
  by_cases h0 : ⌜r⌝ * ⌜S.succ χ s⌝ = 0
  · exact Or.inl h0
  right
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne h0
  obtain ⟨e1, e2, e3⟩ := S.succ_spec χ hs
  obtain ⟨u1, u2, -, u4⟩ := S.prod_of hu
  obtain ⟨t1, t2, -, t4⟩ := S.prod_of hrs
  have ht : S.Shift χ t := ⟨S.prod_ne_e hr hrs, u, by rw [u1, t1], by rw [u2, e2, t2],
    by rw [u4, e3, t4]; abel⟩
  exact ⟨ht, by rw [hu]; exact congrArg _ (S.eq_succ χ (r := t) (t := u) ht
    (by rw [u1, t1]) (by rw [u2, e2, t2]) (by rw [u4, e3, t4]; abel))⟩

/-- **Lemma 9.5, rows with output of type `L`** (`lem:successor-substitutions`). -/
theorem table_L (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r s t : R} (hr : r ≠ S.P.e (S.P.src r)) (hs : s ≠ S.P.e (S.P.src s))
    (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (ht : S.TL χ t) :
    (S.TL χ r ∧ S.EL χ r s t ∧ ¬ S.ER χ r s t) ∨
      (S.TB χ r ∧ S.TL χ s ∧ S.EL χ r s t ∧ S.ER χ r s t) := by
  obtain ⟨hts, ht1, ht2⟩ := ht
  obtain ⟨t1, t2, t3, -⟩ := S.prod_of hrs
  obtain ⟨-, hqt⟩ := S.shift_of_qh_mul hts.1 ht1
  have hqrs : S.qh χ (S.P.src r) * ⌜r⌝ * ⌜s⌝ = S.qh χ (S.P.src t) * ⌜t⌝ := by
    rw [mul_assoc, hrs, t1]
  have hqr : S.qh χ (S.P.src r) * ⌜r⌝ ≠ 0 := fun h0 ↦ ht1 (by rw [← hqrs, h0, zero_mul])
  obtain ⟨hrsh, hqr'⟩ := S.shift_of_qh_mul hr hqr
  have hEL : S.EL χ r s t := ⟨hrsh, by rw [← hqr', hqrs, hqt]⟩
  by_cases hry : ⌜r⌝ * S.qh χ (S.P.tgt r) = 0
  · left
    refine ⟨⟨hrsh, hqr, hry⟩, hEL, fun ⟨hss, hsub⟩ ↦ ?_⟩
    rcases S.succ_by_gen hχ hprim hss with h | h
    · apply S.rr_ne (S.succ χ t)
      rw [← hsub, ← h, ← mul_assoc, ← t3, hry, zero_mul]
    · apply S.rr_ne (S.succ χ t)
      rw [← hsub, ← h, ← mul_assoc, hrs, ← t2, ht2]
  · right
    obtain ⟨-, hry'⟩ := S.shift_of_mul_qh hr hry
    have hqs : S.qh χ (S.P.src s) * ⌜s⌝ ≠ 0 := by
      intro h0
      apply ht1
      rw [← hqrs, hqr', ← hry', mul_assoc, t3, h0, mul_zero]
    obtain ⟨hss, hqs'⟩ := S.shift_of_qh_mul hs hqs
    have hsz : ⌜s⌝ * S.qh χ (S.P.tgt s) = 0 := by
      by_contra hsz
      obtain ⟨-, hsz'⟩ := S.shift_of_mul_qh hs hsz
      apply ht1
      rw [← hqrs, hqr', ← hry', mul_assoc, t3, hqs', ← hsz', ← mul_assoc, hrs, ← t2, ht2]
    refine ⟨⟨hrsh, hqr, hry⟩, ⟨hss, hqs, hsz⟩, hEL, hss, ?_⟩
    rw [← hqs', ← t3, ← mul_assoc, hry', ← hqr', hqrs, hqt]

/-! ### Translation to the opposite system -/

theorem op_supp (x : V) : S.op.Supp χ x ↔ S.Supp χ x := by
  unfold Supp
  rw [op_χ]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h ↦ h1 (by rw [op_q, h]; rfl), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h ↦ h1 h, h2⟩

theorem op_qh (x : V) : S.op.qh χ x = S.P.toOp (S.qh χ x) := by
  classical
  by_cases h : S.Supp χ x
  · rw [S.op.qh_of_supp χ ((S.op_supp x).2 h), S.qh_of_supp χ h]
  · rw [S.op.qh_of_not_supp χ (fun h' ↦ h ((S.op_supp x).1 h')), S.qh_of_not_supp χ h]; rfl

theorem ne_e_iff_op (r : R) : r ≠ S.P.e (S.P.tgt r) ↔ r ≠ S.P.e (S.P.src r) := by
  constructor
  · intro h h'; apply h; rw [h', S.P.tgt_e]
  · intro h h'; apply h; rw [h', S.P.src_e]

theorem op_shift (r : R) : S.op.Shift χ r ↔ S.Shift χ r := by
  unfold Shift
  change (r ≠ S.P.e (S.P.tgt r) ∧ ∃ r', S.P.tgt r' = S.P.tgt r ∧ S.P.src r' = S.P.src r ∧
    S.P.wt r' = S.P.wt r + χ) ↔ _
  rw [S.ne_e_iff_op]
  constructor
  · rintro ⟨h, r', h1, h2, h3⟩; exact ⟨h, r', h2, h1, h3⟩
  · rintro ⟨h, r', h1, h2, h3⟩; exact ⟨h, r', h2, h1, h3⟩

theorem op_succ {r : R} (h : S.Shift χ r) : S.op.succ χ r = S.succ χ r := by
  have h' := (S.op_shift r).2 h
  obtain ⟨e1, e2, e3⟩ := S.op.succ_spec χ h'
  exact S.eq_succ χ h e2 e1 e3

theorem op_TL (r : R) : S.op.TL χ r ↔ S.TR χ r := by
  unfold TL TR
  rw [op_shift]
  change (S.Shift χ r ∧ S.op.qh χ (S.P.tgt r) * S.op.rr r ≠ 0 ∧
    S.op.rr r * S.op.qh χ (S.P.src r) = 0) ↔ _
  rw [op_rr]
  rw [op_qh, op_qh, ← Tab.toOp_mul, ← Tab.toOp_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩

theorem op_TR (r : R) : S.op.TR χ r ↔ S.TL χ r := by
  unfold TL TR
  rw [op_shift]
  change (S.Shift χ r ∧ S.op.qh χ (S.P.tgt r) * S.op.rr r = 0 ∧
    S.op.rr r * S.op.qh χ (S.P.src r) ≠ 0) ↔ _
  rw [op_rr]
  rw [op_qh, op_qh, ← Tab.toOp_mul, ← Tab.toOp_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩

theorem op_TB (r : R) : S.op.TB χ r ↔ S.TB χ r := by
  unfold TB
  rw [op_shift]
  change (S.Shift χ r ∧ S.op.qh χ (S.P.tgt r) * S.op.rr r ≠ 0 ∧
    S.op.rr r * S.op.qh χ (S.P.src r) ≠ 0) ↔ _
  rw [op_rr]
  rw [op_qh, op_qh, ← Tab.toOp_mul, ← Tab.toOp_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩

theorem op_EL {r s t : R} (ht : S.Shift χ t) : S.op.EL χ s r t ↔ S.ER χ r s t := by
  unfold EL ER
  rw [op_shift]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, S.P.toOp_injective ?_⟩
    rw [Tab.toOp_mul]
    change S.op.rr (S.succ χ s) * S.op.rr r = S.op.rr (S.succ χ t)
    rw [← S.op_succ h1, ← S.op_succ ht]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [S.op_succ h1, S.op_succ ht]
    change S.P.toOp ⌜S.succ χ s⌝ * S.P.toOp ⌜r⌝ = S.P.toOp ⌜S.succ χ t⌝
    rw [← Tab.toOp_mul, h2]

theorem op_ER {r s t : R} (ht : S.Shift χ t) : S.op.ER χ s r t ↔ S.EL χ r s t := by
  unfold EL ER
  rw [op_shift]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, S.P.toOp_injective ?_⟩
    rw [Tab.toOp_mul]
    change S.op.rr s * S.op.rr (S.succ χ r) = S.op.rr (S.succ χ t)
    rw [← S.op_succ h1, ← S.op_succ ht]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [S.op_succ h1, S.op_succ ht]
    change S.P.toOp ⌜s⌝ * S.P.toOp ⌜S.succ χ r⌝ = S.P.toOp ⌜S.succ χ t⌝
    rw [← Tab.toOp_mul, h2]

/-- **Lemma 9.5, rows with output of type `R`** (by passing to the opposite system). -/
theorem table_R (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r s t : R}
    (hr : r ≠ S.P.e (S.P.src r)) (hs : s ≠ S.P.e (S.P.src s)) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝)
    (ht : S.TR χ t) :
    (S.TR χ s ∧ S.ER χ r s t ∧ ¬ S.EL χ r s t) ∨
      (S.TB χ s ∧ S.TR χ r ∧ S.EL χ r s t ∧ S.ER χ r s t) := by
  have hts : S.Shift χ t := ht.1
  have hrs' : S.op.rr s * S.op.rr r = S.op.rr t := by
    show S.P.toOp ⌜s⌝ * S.P.toOp ⌜r⌝ = S.P.toOp ⌜t⌝
    rw [← Tab.toOp_mul, hrs]
  rcases S.op.table_L hχ hprim ((S.ne_e_iff_op s).2 hs) ((S.ne_e_iff_op r).2 hr) hrs'
      ((S.op_TL t).2 ht) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · left
    exact ⟨(S.op_TL s).1 h1, (S.op_EL hts).1 h2, fun h ↦ h3 ((S.op_ER hts).2 h)⟩
  · right
    exact ⟨(S.op_TB s).1 h1, (S.op_TL r).1 h2, (S.op_ER hts).1 h4, (S.op_EL hts).1 h3⟩

/-- **Lemma 9.5, rows with output of type `B`.** -/
theorem table_B (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r s t : R}
    (hr : r ≠ S.P.e (S.P.src r)) (hs : s ≠ S.P.e (S.P.src s)) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝)
    (ht : S.TB χ t) :
    ((S.TB χ r ∧ S.TB χ s) ∨ (S.TL χ r ∧ S.TR χ s)) ∧ S.EL χ r s t ∧ S.ER χ r s t := by
  obtain ⟨hts, ht1, ht2⟩ := ht
  obtain ⟨t1, t2, t3, -⟩ := S.prod_of hrs
  obtain ⟨-, hqt⟩ := S.shift_of_qh_mul hts.1 ht1
  obtain ⟨-, htq⟩ := S.shift_of_mul_qh hts.1 ht2
  have hqrs : S.qh χ (S.P.src r) * ⌜r⌝ * ⌜s⌝ = S.qh χ (S.P.src t) * ⌜t⌝ := by
    rw [mul_assoc, hrs, t1]
  have hrsq : ⌜r⌝ * (⌜s⌝ * S.qh χ (S.P.tgt s)) = ⌜t⌝ * S.qh χ (S.P.tgt t) := by
    rw [← mul_assoc, hrs, t2]
  have hqr : S.qh χ (S.P.src r) * ⌜r⌝ ≠ 0 := fun h0 ↦ ht1 (by rw [← hqrs, h0, zero_mul])
  have hsq : ⌜s⌝ * S.qh χ (S.P.tgt s) ≠ 0 := fun h0 ↦ ht2 (by rw [← hrsq, h0, mul_zero])
  obtain ⟨hrsh, hqr'⟩ := S.shift_of_qh_mul hr hqr
  obtain ⟨hssh, hsq'⟩ := S.shift_of_mul_qh hs hsq
  have hEL : S.EL χ r s t := ⟨hrsh, by rw [← hqr', hqrs, hqt]⟩
  have hER : S.ER χ r s t := ⟨hssh, by rw [← hsq', hrsq, htq]⟩
  refine ⟨?_, hEL, hER⟩
  by_cases hry : ⌜r⌝ * S.qh χ (S.P.tgt r) = 0
  · -- `r` has type `L`; then `s` has type `R`
    right
    refine ⟨⟨hrsh, hqr, hry⟩, hssh, ?_, hsq⟩
    by_contra hqs
    obtain ⟨-, hqs'⟩ := S.shift_of_qh_mul hs hqs
    apply ht2
    rw [← hrsq, hsq', ← hqs', ← mul_assoc, ← t3, hry, zero_mul]
  · left
    obtain ⟨-, hry'⟩ := S.shift_of_mul_qh hr hry
    have hqs : S.qh χ (S.P.src s) * ⌜s⌝ ≠ 0 := by
      intro h0
      apply ht1
      rw [← hqrs, hqr', ← hry', mul_assoc, t3, h0, mul_zero]
    exact ⟨⟨hrsh, hqr, hry⟩, ⟨hssh, hqs, hsq⟩⟩

/-- **Lemma 9.5, unshiftable outputs**: no successor substitution survives. -/
theorem table_unshift {r s t : R} (hr : r ≠ S.P.e (S.P.src r)) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝)
    (ht : ¬ S.Shift χ t) :
    (S.Shift χ r → ⌜S.succ χ r⌝ * ⌜s⌝ = 0) ∧ (S.Shift χ s → ⌜r⌝ * ⌜S.succ χ s⌝ = 0) :=
  ⟨fun h ↦ (S.subst_left h hrs).resolve_right fun h' ↦ ht h'.1,
    fun h ↦ (S.subst_right hr h hrs).resolve_right fun h' ↦ ht h'.1⟩

end Char

end Sys

end RaySys

end MultiplicativeBasisDeformations
