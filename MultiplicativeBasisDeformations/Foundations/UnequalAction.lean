module

public import MultiplicativeBasisDeformations.Foundations.RayConfigs

/-!
# Lemma 8.10: unequal endpoint actions

`lem:unequal-endpoint-action` (`local-ray-geometry.tex`): "suppose `A₀(x,y) = R_x f`
has dimension `l`, where `f` is generating. If `f q_y = q_x^a f ≠ 0` with `a ≥ 2`, then
`l = a+1`, and `f q_y` lies in the endpoint socle of `A₀(x,y)`."

Deviation: the paper's seven-point support poset has one commuting relation (`F = 1` in
Lemma 8.8); we use its full subposet without `v₀ = f`, the Euclidean tree `D̃₅` with two
adjacent trivalent vertices (`N = D = 12`), which needs no relation.
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

/-- The table of `D̃₅`: `u₀ < u₁ < u₂ < u₃`, `u₁ < v₁`, `u₂ < v₂` (indices `0..5` are
`u₀ u₁ u₂ u₃ v₁ v₂`). -/
def tD5 : Fin 6 → Fin 6 → Bool := fun i j ↦ match i.val, j.val with
  | 0, _ => true
  | 1, 1 => true | 1, 2 => true | 1, 3 => true | 1, 4 => true | 1, 5 => true
  | 2, 2 => true | 2, 3 => true | 2, 5 => true
  | 3, 3 => true
  | 4, 4 => true
  | 5, 5 => true
  | _, _ => false

theorem tD5_uniq : PosetRep.UniqOK tD5 := by unfold PosetRep.UniqOK; decide

theorem tD5_count : PosetRep.CountOK tD5 ![1, 2, 2, 1, 1, 1] := by
  unfold PosetRep.CountOK; decide

theorem wt_of_eq_qpow_mul {v f : R} {c : ℕ} (h : ⌜v⌝ = S.q (S.P.src f) ^ c * ⌜f⌝) :
    S.P.wt v = c • S.χ (S.P.src f) + S.P.wt f := by
  have h0 : S.q (S.P.src f) ^ c * ⌜f⌝ ≠ 0 := h ▸ S.P.rr_ne_zero v
  have := congrArg S.wtM h
  rwa [wtM_rr, S.wtM_mul _ _ h0, S.wtM_qpow _ _ (fun h' ↦ h0 (by rw [h', zero_mul])),
    wtM_rr] at this

theorem wt_of_eq_qpow_e {v : R} {x : V} {c : ℕ} (h : ⌜v⌝ = S.q x ^ c * ⌜S.P.e x⌝) :
    S.P.wt v = c • S.χ x := by
  rcases S.qpow_cases x c with h0 | ⟨g, hg, -, -, hw⟩
  · rw [h0] at h; exact absurd h (S.P.rr_ne_zero v)
  · rw [hg] at h; obtain rfl := S.P.rr_injective h; exact hw

theorem deg_wt_qpow_e {v : R} {x : V} {c : ℕ} (h : ⌜v⌝ = S.q x ^ c * ⌜S.P.e x⌝) :
    S.P.deg (S.P.wt v) = c * S.P.deg (S.χ x) := by
  rw [S.wt_of_eq_qpow_e h, map_nsmul, nsmul_eq_mul]

theorem deg_wt_qpow_mul {v f : R} {c : ℕ} (h : ⌜v⌝ = S.q (S.P.src f) ^ c * ⌜f⌝) :
    S.P.deg (S.P.wt v) = c * S.P.deg (S.χ (S.P.src f)) + S.P.deg (S.P.wt f) := by
  rw [S.wt_of_eq_qpow_mul h, map_add, map_nsmul, nsmul_eq_mul]

/-- A loop is a power of the local generator; its degree is a multiple of `deg χ`. -/
theorem local_deg (r : R) (h : S.P.src r = S.P.tgt r) : ∃ c : ℕ,
    ⌜r⌝ = S.q (S.P.src r) ^ c * ⌜S.P.e (S.P.src r)⌝ ∧
      S.P.deg (S.P.wt r) = c * S.P.deg (S.χ (S.P.src r)) := by
  obtain ⟨c, hc, hw⟩ := S.local_eq r h
  exact ⟨c, hc.symm, by rw [hw, map_nsmul, nsmul_eq_mul]⟩

/-- The identity is the only ray of degree zero; a generating ray of a loop Hom is `e`. -/
theorem deg_pos_of_ne {f : R} (h : S.P.src f ≠ S.P.tgt f) : 0 < S.P.deg (S.P.wt f) := by
  rcases (S.P.deg_nonneg f).lt_or_eq with h' | h'
  · exact h'
  · exfalso; apply h
    have := S.eq_e_of_deg_zero h'.symm
    rw [this, S.P.tgt_e, S.P.src_e]

/-- The order of the six support points of Lemma 8.10 is `D̃₅`. -/
theorem d5_order {Xr Yr : ℕ → R} {a : ℕ} (ha : 2 ≤ a)
    (XX : ∀ m m', m ≤ a + 1 → m' ≤ a + 1 → (S.P.RF (Xr m) (Xr m') ↔ m ≤ m'))
    (XY : ∀ m m', m ≤ a + 1 → m' ≤ a + 1 → (S.P.RF (Xr m) (Yr m') ↔ m ≤ m'))
    (YX : ∀ m m', 1 ≤ m → m ≤ a → m' ≤ a + 1 → ¬ S.P.RF (Yr m) (Xr m'))
    (YY : ∀ m m', (m = 1 ∧ m' = a ∨ m = a ∧ m' = 1) → ¬ S.P.RF (Yr m) (Yr m')) :
    ∀ i j, tD5 i j = true ↔
      S.P.RF (![Xr 0, Xr 1, Xr a, Xr (a + 1), Yr 1, Yr a] i)
        (![Xr 0, Xr 1, Xr a, Xr (a + 1), Yr 1, Yr a] j) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [tD5, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, true_iff, Bool.false_eq_true, false_iff]
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XY _ _ (by omega) (by omega)).2 (by omega)
  · exact (XY _ _ (by omega) (by omega)).2 (by omega)
  · exact fun h' ↦ absurd ((XX _ _ (by omega) (by omega)).1 h') (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XY _ _ (by omega) (by omega)).2 (by omega)
  · exact (XY _ _ (by omega) (by omega)).2 (by omega)
  · exact fun h' ↦ absurd ((XX _ _ (by omega) (by omega)).1 h') (by omega)
  · exact fun h' ↦ absurd ((XX _ _ (by omega) (by omega)).1 h') (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact fun h' ↦ absurd ((XY _ _ (by omega) (by omega)).1 h') (by omega)
  · exact (XY _ _ (by omega) (by omega)).2 (by omega)
  · exact fun h' ↦ absurd ((XX _ _ (by omega) (by omega)).1 h') (by omega)
  · exact fun h' ↦ absurd ((XX _ _ (by omega) (by omega)).1 h') (by omega)
  · exact fun h' ↦ absurd ((XX _ _ (by omega) (by omega)).1 h') (by omega)
  · exact (XX _ _ (by omega) (by omega)).2 (by omega)
  · exact fun h' ↦ absurd ((XY _ _ (by omega) (by omega)).1 h') (by omega)
  · exact fun h' ↦ absurd ((XY _ _ (by omega) (by omega)).1 h') (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact S.P.rf_refl _
  · exact YY _ _ (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YX _ _ (by omega) (by omega) (by omega)
  · exact YY _ _ (by omega)
  · exact S.P.rf_refl _

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.10** (`lem:unequal-endpoint-action`), length part: `q_x^{a+1} f = 0`, i.e.
`dim A₀(x, y) ≤ a + 1`. -/
theorem unequal_endpoint_action (hfin : IsRepresentationFinite k (S.P.Lin k)) {f : R}
    (hf : S.CycL f) {a : ℕ} (ha : 2 ≤ a)
    (h : ⌜f⌝ * S.q (S.P.tgt f) = S.q (S.P.src f) ^ a * ⌜f⌝) (h0 : ⌜f⌝ * S.q (S.P.tgt f) ≠ 0) :
    S.q (S.P.src f) ^ (a + 1) * ⌜f⌝ = 0 := by
  classical
  set x := S.P.src f with hx
  set y := S.P.tgt f with hy
  have hqa : S.q x ^ a * ⌜f⌝ ≠ 0 := h ▸ h0
  have hqx : S.q x ≠ 0 := fun h' ↦ hqa (by rw [h', zero_pow (by omega), zero_mul])
  set d := S.P.deg (S.χ x) with hd_def
  have hd : 0 < d := S.χ_deg_pos x hqx
  have hfd := S.P.deg_nonneg f
  -- `deg χ_y = a d`
  have hdy : S.P.deg (S.χ y) = a * d := by
    have e1 := congrArg S.wtM h
    rw [S.wtM_mul _ _ h0, S.wtM_mul _ _ hqa, S.wtM_qpow x a (fun h' ↦ hqa (by rw [h', zero_mul])),
      wtM_rr] at e1
    have e2 := congrArg S.P.deg e1
    simp only [map_add, map_nsmul, nsmul_eq_mul] at e2
    change S.P.deg (S.P.wt f) + S.P.deg (S.χ y) = a * d + S.P.deg (S.P.wt f) at e2
    linarith
  -- `x ≠ y`
  have hxy : x ≠ y := by
    intro hxy
    obtain ⟨i, hi⟩ := hf (S.P.e x) (S.P.src_e x) (by rw [S.P.tgt_e, hxy])
    have := S.deg_wt_qpow_mul hi
    rw [S.P.wt_e, map_zero] at this
    have hf0 : S.P.deg (S.P.wt f) = 0 := by
      have : (0 : ℤ) ≤ i * d := by positivity
      linarith
    have hdx := hdy
    rw [← hxy] at hdx
    -- `deg χ_x = a d` with `d = deg χ_x`
    have : (a : ℤ) * d = d := by rw [← hdx]
    nlinarith
  have hfpos : 0 < S.P.deg (S.P.wt f) := S.deg_pos_of_ne hxy
  by_contra h1
  have hb_ne : ∀ b, b ≤ a + 1 → S.q x ^ b * ⌜f⌝ ≠ 0 := fun b hb h' ↦ h1 (by
    rw [show a + 1 = (a + 1 - b) + b by omega, pow_add, mul_assoc, h', mul_zero])
  have hex : ⌜S.P.e x⌝ * ⌜f⌝ = ⌜f⌝ := S.e_mul_rr f
  have hqe_ne : ∀ b, b ≤ a + 1 → S.q x ^ b * ⌜S.P.e x⌝ ≠ 0 := fun b hb h' ↦
    hb_ne b hb (by rw [← hex, ← mul_assoc, h', zero_mul])
  obtain ⟨g0, hg0, hg01, hg02, -⟩ := (S.q_cases x).resolve_left hqx
  replace hg0 : S.q x = ⌜g0⌝ := hg0
  have hg0d : S.P.deg (S.P.wt g0) = d := by rw [hd_def, χ, hg0, wtM_rr]
  -- Step A: no reverse `f h = q_x^b` with `1 ≤ b ≤ a + 1`
  have stepA : ∀ (g : R) (b : ℕ), 1 ≤ b → b ≤ a + 1 →
      ⌜f⌝ * ⌜g⌝ = S.q x ^ b * ⌜S.P.e x⌝ → False := by
    intro g b hb1 hb2 hfg
    have hfgf : ⌜f⌝ * ⌜g⌝ * ⌜f⌝ = S.q x ^ b * ⌜f⌝ := by rw [hfg, mul_assoc, hex]
    have hgf : ⌜g⌝ * ⌜f⌝ ≠ 0 := fun h' ↦ hb_ne b hb2 (by rw [← hfgf, mul_assoc, h', mul_zero])
    have hfg0 : ⌜f⌝ * ⌜g⌝ ≠ 0 := by rw [hfg]; exact hqe_ne b hb2
    have hgsrc : S.P.src g = y := (S.src_of_mul_ne hfg0).symm
    obtain ⟨t, -, ht⟩ := S.P.rr_mul_rr_ne_zero hgf
    obtain ⟨t1, t2, -, t4⟩ := S.prod_of ht
    obtain ⟨m, -, hm⟩ := S.local_deg t (by rw [t1, t2, hgsrc])
    rw [t1, hgsrc, hdy] at hm
    obtain ⟨u, -, hu⟩ := S.P.rr_mul_rr_ne_zero hfg0
    have hdu : S.P.deg (S.P.wt u) = b * d := S.deg_wt_qpow_e (hu.symm.trans hfg)
    have hu4 := (S.prod_of hu).2.2.2
    have key : ((m * a : ℕ) : ℤ) * d = (b : ℤ) * d := by
      have e1 : S.P.deg (S.P.wt t) = S.P.deg (S.P.wt g) + S.P.deg (S.P.wt f) := by
        rw [t4, map_add]
      have e2 : S.P.deg (S.P.wt u) = S.P.deg (S.P.wt f) + S.P.deg (S.P.wt g) := by
        rw [hu4, map_add]
      push_cast; linarith
    have hmab : m * a = b := by exact_mod_cast mul_right_cancel₀ hd.ne' key
    have hm1 : m = 1 := by
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · interval_cases m <;> omega
      · nlinarith
    subst hm1
    have hba : b = a := by omega
    subst hba
    -- `g q_x f` is a loop at `y` of degree `(b + 1) d`
    have e3 : ⌜f⌝ * (⌜g⌝ * ⌜g0⌝ * ⌜f⌝) = S.q x ^ (b + 1) * ⌜f⌝ := by
      rw [← mul_assoc, ← mul_assoc, hfg, ← hg0, mul_assoc (S.q x ^ b), S.e_mul_q, ← pow_succ]
    have hgqf : ⌜g⌝ * ⌜g0⌝ * ⌜f⌝ ≠ 0 := fun h' ↦ hb_ne (b + 1) le_rfl (by
      rw [← e3, h', mul_zero])
    have hgq : ⌜g⌝ * ⌜g0⌝ ≠ 0 := fun h' ↦ hgqf (by rw [h', zero_mul])
    obtain ⟨w, -, hw⟩ := S.P.rr_mul_rr_ne_zero hgq
    rw [hw] at hgqf
    obtain ⟨w', -, hw'⟩ := S.P.rr_mul_rr_ne_zero hgqf
    obtain ⟨w1, -, -, w4⟩ := S.prod_of hw
    obtain ⟨w1', w2', -, w4'⟩ := S.prod_of hw'
    obtain ⟨m', -, hm'⟩ := S.local_deg w' (by rw [w1', w1, w2', hgsrc])
    rw [w1', w1, hgsrc, hdy] at hm'
    have key' : ((m' * b : ℕ) : ℤ) * d = ((b + 1 : ℕ) : ℤ) * d := by
      have e1 : S.P.deg (S.P.wt w') = S.P.deg (S.P.wt g) + d + S.P.deg (S.P.wt f) := by
        rw [w4', w4, map_add, map_add, hg0d]
      have e2 : S.P.deg (S.P.wt u) = S.P.deg (S.P.wt f) + S.P.deg (S.P.wt g) := by
        rw [hu4, map_add]
      push_cast; linarith
    have := mul_right_cancel₀ hd.ne' key'
    have hmb : m' * b = b + 1 := by exact_mod_cast this
    rcases Nat.lt_or_ge m' 2 with hm2 | hm2
    · interval_cases m' <;> omega
    · nlinarith
  -- Step B: the support points `q_x^m` and `q_x^m f`
  have hXex : ∀ m, m ≤ a + 1 → ∃ g, S.q x ^ m * ⌜S.P.e x⌝ = ⌜g⌝ := fun m hm ↦
    S.eq_rr_of_ne _ (hqe_ne m hm) (fun h' ↦ by
      rcases S.qpow_cases x m with h'' | ⟨g, hg, -⟩
      · exact hqe_ne m hm h''
      · rw [hg] at h'; exact S.P.rr_ne_one g h')
  have hYex : ∀ m, m ≤ a + 1 → ∃ g, S.q x ^ m * ⌜f⌝ = ⌜g⌝ := fun m hm ↦ by
    rcases S.qpow_mul_rr_mul_qpow f m 0 with h' | ⟨t, ht, -⟩
    · rw [pow_zero, mul_one] at h'; exact absurd h' (hb_ne m hm)
    · rw [pow_zero, mul_one] at ht; exact ⟨t, ht⟩
  let Xr : ℕ → R := fun m ↦ if hX : ∃ g, S.q x ^ m * ⌜S.P.e x⌝ = ⌜g⌝ then hX.choose else f
  let Yr : ℕ → R := fun m ↦ if hY : ∃ g, S.q x ^ m * ⌜f⌝ = ⌜g⌝ then hY.choose else f
  have hXr : ∀ m, m ≤ a + 1 → ⌜Xr m⌝ = S.q x ^ m * ⌜S.P.e x⌝ := fun m hm ↦ by
    simp only [Xr, dif_pos (hXex m hm)]; exact (hXex m hm).choose_spec.symm
  have hYr : ∀ m, m ≤ a + 1 → ⌜Yr m⌝ = S.q x ^ m * ⌜f⌝ := fun m hm ↦ by
    simp only [Yr, dif_pos (hYex m hm)]; exact (hYex m hm).choose_spec.symm
  have hXd : ∀ m, m ≤ a + 1 → S.P.deg (S.P.wt (Xr m)) = m * d := fun m hm ↦
    S.deg_wt_qpow_e (hXr m hm)
  have hYd : ∀ m, m ≤ a + 1 → S.P.deg (S.P.wt (Yr m)) = m * d + S.P.deg (S.P.wt f) :=
    fun m hm ↦ S.deg_wt_qpow_mul (hYr m hm)
  have hXend : ∀ m, m ≤ a + 1 → S.P.src (Xr m) = x ∧ S.P.tgt (Xr m) = x := fun m hm ↦ by
    rcases S.qpow_cases x m with h' | ⟨g, hg, g1, g2, -⟩
    · exact absurd h' (hqe_ne m hm)
    · rw [← hXr m hm] at hg; obtain rfl := S.P.rr_injective hg; exact ⟨g1, g2⟩
  have hYend : ∀ m, m ≤ a + 1 → S.P.src (Yr m) = x ∧ S.P.tgt (Yr m) = y := fun m hm ↦ by
    rcases S.qpow_mul_rr_mul_qpow f m 0 with h' | ⟨t, ht, t1, t2, -⟩
    · rw [pow_zero, mul_one] at h'; exact absurd h' (hb_ne m hm)
    · rw [pow_zero, mul_one, ← hYr m hm] at ht; obtain rfl := S.P.rr_injective ht; exact ⟨t1, t2⟩
  have hqpow_e : ∀ j, ⌜S.P.e x⌝ * S.q x ^ j = S.q x ^ j * ⌜S.P.e x⌝ := fun j ↦
    (S.qpow_comm_e x j).symm
  -- the four order relations
  have XX : ∀ m m', m ≤ a + 1 → m' ≤ a + 1 → (S.P.RF (Xr m) (Xr m') ↔ m ≤ m') := by
    intro m m' hm hm'
    constructor
    · intro hrf
      have := S.rf_deg_le hrf
      rw [hXd m hm, hXd m' hm'] at this
      by_contra hlt
      have : (m' : ℤ) < m := by exact_mod_cast not_le.1 hlt
      nlinarith
    · intro hle
      rw [S.rf_iff]
      refine ⟨Xr (m' - m), ?_⟩
      rw [hXr m hm, hXr _ (by omega), hXr m' hm', mul_assoc, ← mul_assoc ⌜S.P.e x⌝,
        hqpow_e, mul_assoc]
      rw [show ⌜S.P.e x⌝ * ⌜S.P.e x⌝ = ⌜S.P.e x⌝ by
        have := S.e_mul_rr (S.P.e x); rwa [S.P.src_e] at this]
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  have XY : ∀ m m', m ≤ a + 1 → m' ≤ a + 1 → (S.P.RF (Xr m) (Yr m') ↔ m ≤ m') := by
    intro m m' hm hm'
    constructor
    · intro hrf
      obtain ⟨v, hv⟩ := hrf
      have hv' := S.P.rr_mul_rr_eq_rr.2 hv
      obtain ⟨-, v2, v3, v4⟩ := S.prod_of hv'
      obtain ⟨c, hc⟩ := hf v (by rw [← v3, (hXend m hm).2]) (by rw [← v2, (hYend m' hm').2])
      have hdv := S.deg_wt_qpow_mul hc
      have e1 := congrArg S.P.deg v4
      rw [map_add, hXd m hm, hYd m' hm', hdv] at e1
      by_contra hlt
      have : (m' : ℤ) < m := by exact_mod_cast not_le.1 hlt
      have hc0 : (0 : ℤ) ≤ c := by positivity
      nlinarith
    · intro hle
      rw [S.rf_iff]
      refine ⟨Yr (m' - m), ?_⟩
      rw [hXr m hm, hYr _ (by omega), hYr m' hm', mul_assoc, ← mul_assoc ⌜S.P.e x⌝, hqpow_e,
        mul_assoc, hex, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  have YX : ∀ m m', 1 ≤ m → m ≤ a → m' ≤ a + 1 → ¬ S.P.RF (Yr m) (Xr m') := by
    intro m m' hm1 hm hm' hrf
    obtain ⟨v, hv⟩ := hrf
    have hv' := S.P.rr_mul_rr_eq_rr.2 hv
    obtain ⟨-, v2, v3, v4⟩ := S.prod_of hv'
    have e0 : ⌜Yr m⌝ * ⌜v⌝ = S.q x ^ m * (⌜f⌝ * ⌜v⌝) := by rw [hYr m (by omega), mul_assoc]
    have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ S.P.rr_ne_zero (Xr m') (by rw [← hv', e0, h', mul_zero])
    obtain ⟨w, -, hw⟩ := S.P.rr_mul_rr_ne_zero hfv
    obtain ⟨w1, w2, -, w4⟩ := S.prod_of hw
    have hwloop : S.P.src w = S.P.tgt w := by
      rw [w1, w2, ← v2, (hXend m' hm').2]
    obtain ⟨c, hc, hcd⟩ := S.local_deg w hwloop
    rw [w1] at hc hcd
    have e1 := congrArg S.P.deg v4
    rw [map_add, hXd m' hm', hYd m (by omega)] at e1
    have e2 := congrArg S.P.deg w4
    rw [map_add, hcd] at e2
    have hvd := S.P.deg_nonneg v
    -- `m' = m + c` and `c ≥ 1`
    have hc1 : 1 ≤ c := by
      by_contra hc0
      have : c = 0 := by omega
      subst this
      simp at e2
      linarith
    have hmc : (m' : ℤ) * d = (m + c) * d := by push_cast; linarith
    have hmc' : m' = m + c := by exact_mod_cast mul_right_cancel₀ hd.ne' hmc
    exact stepA v c hc1 (by omega) (by rw [hw]; exact hc)
  have YY : ∀ m m', (m = 1 ∧ m' = a ∨ m = a ∧ m' = 1) → ¬ S.P.RF (Yr m) (Yr m') := by
    intro m m' hmm hrf
    have hm : m ≤ a + 1 := by omega
    have hm' : m' ≤ a + 1 := by omega
    obtain ⟨v, hv⟩ := hrf
    have hv' := S.P.rr_mul_rr_eq_rr.2 hv
    obtain ⟨-, v2, v3, v4⟩ := S.prod_of hv'
    have hvloop : S.P.src v = S.P.tgt v := by rw [← v3, ← v2, (hYend m hm).2, (hYend m' hm').2]
    obtain ⟨c, -, hcd⟩ := S.local_deg v hvloop
    rw [← v3, (hYend m hm).2, hdy] at hcd
    have e1 := congrArg S.P.deg v4
    rw [map_add, hYd m hm, hYd m' hm', hcd] at e1
    have : ((m' : ℕ) : ℤ) * d = ((m + c * a : ℕ) : ℤ) * d := by push_cast; linarith
    have h2 : m' = m + c * a := by exact_mod_cast mul_right_cancel₀ hd.ne' this
    rcases hmm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · omega
      · nlinarith
    · omega
  have hle := S.d5_order ha XX XY YX YY
  have hanti : ∀ i j : Fin 6, tD5 i j = true → tD5 j i = true → i = j := by decide
  set r : Fin 6 → R := ![Xr 0, Xr 1, Xr a, Xr (a + 1), Yr 1, Yr a] with hr_def
  have hinj : Function.Injective r := fun i j hij ↦ hanti i j
    ((hle i j).2 (by rw [hij]; exact S.P.rf_refl _)) ((hle j i).2 (by rw [hij]; exact S.P.rf_refl _))
  refine S.P.projSup_false k hfin x r hinj (fun i ↦ ?_) hle ![1, 2, 2, 1, 1, 1] tD5_uniq tD5_count
  fin_cases i
  · exact (hXend 0 (by omega)).1
  · exact (hXend 1 (by omega)).1
  · exact (hXend a (by omega)).1
  · exact (hXend (a + 1) le_rfl).1
  · exact (hYend 1 (by omega)).1
  · exact (hYend a (by omega)).1

/-- **Lemma 8.10**, socle part: `f q_y` is annihilated by both endpoint radicals. -/
theorem unequal_endpoint_socle (hfin : IsRepresentationFinite k (S.P.Lin k)) {f : R}
    (hf : S.CycL f) {a : ℕ} (ha : 2 ≤ a)
    (h : ⌜f⌝ * S.q (S.P.tgt f) = S.q (S.P.src f) ^ a * ⌜f⌝) (h0 : ⌜f⌝ * S.q (S.P.tgt f) ≠ 0) :
    S.q (S.P.src f) * (⌜f⌝ * S.q (S.P.tgt f)) = 0 ∧
      ⌜f⌝ * S.q (S.P.tgt f) * S.q (S.P.tgt f) = 0 := by
  have hz := S.unequal_endpoint_action k hfin hf ha h h0
  constructor
  · rw [h, ← mul_assoc, ← pow_succ', hz]
  · rw [h, mul_assoc, h, ← mul_assoc, ← pow_add,
      show a + a = (a - 1) + (a + 1) by omega, pow_add, mul_assoc, hz, mul_zero]

end Sys

end RaySys

end MultiplicativeBasisDeformations
