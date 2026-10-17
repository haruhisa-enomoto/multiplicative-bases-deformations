import MultiplicativeBasisDeformations.Foundations.Contours

/-!
# Proper products and external returns (Appendix C.2)

`lem:nondeep-two-object-return` and `prop:proper-ray-products`
(`local-ray-restrictions.tex`, `primitive-ray-equations.tex`).
-/

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

variable (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The opposite form of `prim_action_gen` (Lemma 8.18): a nonzero target action makes the
Hom cyclic at the target. -/
theorem prim_action_gen_op {f : R} (hf : S.IsGen f) (hprim : Prim (S.χ (S.P.tgt f)))
    (hqf : ⌜f⌝ * S.q (S.P.tgt f) ≠ 0) : S.CycR f ∧
      (S.CycL f → S.χ (S.P.src f) = S.χ (S.P.tgt f) ∧
        ⌜f⌝ * S.q (S.P.tgt f) = S.q (S.P.src f) * ⌜f⌝) := by
  have h := S.op.prim_action_gen ((S.op_isGen_iff f).2 hf) (by rw [op_χ]; exact hprim)
    (by rw [op_q, op_rr, ← Tab.toOp_mul]; exact hqf)
  refine ⟨(S.op_cycL_iff f).1 h.1, fun hL ↦ ?_⟩
  obtain ⟨h1, h2⟩ := h.2 ((S.op_cycR_iff f).2 hL)
  refine ⟨by rw [op_χ, op_χ] at h1; exact h1, S.P.toOp_injective ?_⟩
  rw [Tab.toOp_mul, Tab.toOp_mul]; exact h2

/-- **The core of Lemma C.2** (`lem:nondeep-two-object-return`, first paragraph): for an external
return `el = q_b^a` with `q_b^{a+1} ≠ 0`, both Homs are generated only at `b`, and `le = 0`. -/
theorem ret_core (hfin : IsRepresentationFinite k (S.P.Lin k)) {b y : V} {e l : R} {a : ℕ}
    (he : S.IsGen e) (hl : S.IsGen l) (e1 : S.P.src e = b) (e2 : S.P.tgt e = y)
    (l1 : S.P.src l = y) (l2 : S.P.tgt l = b) (hby : y ≠ b) (hel : ⌜e⌝ * ⌜l⌝ = S.q b ^ a)
    (ha : 1 ≤ a) (ha1 : S.q b ^ (a + 1) ≠ 0) (hS : ¬ S.InS b y) (hprim : Prim (S.χ b)) :
    S.CycL e ∧ ¬ S.CycR e ∧ S.CycR l ∧ ¬ S.CycL l ∧ ⌜l⌝ * ⌜e⌝ = 0 := by
  have hqb : S.q b ≠ 0 := fun h0 ↦ ha1 (by rw [h0, zero_pow (by omega)])
  have hqe : S.q b * ⌜e⌝ ≠ 0 := by
    intro h0; apply ha1; rw [pow_succ', ← hel, ← mul_assoc, h0, zero_mul]
  have hlq : ⌜l⌝ * S.q b ≠ 0 := by
    intro h0; apply ha1; rw [pow_succ, ← hel, mul_assoc, h0, mul_zero]
  have hel0 : ⌜e⌝ * ⌜l⌝ ≠ 0 := fun h0 ↦ ha1 (by rw [pow_succ, ← hel, h0, zero_mul])
  obtain ⟨heL, heR⟩ := S.prim_action_gen he (by rw [e1]; exact hprim) (by rw [e1]; exact hqe)
  obtain ⟨hlR, hlL⟩ := S.prim_action_gen_op hl (by rw [l2]; exact hprim) (by rw [l2]; exact hlq)
  -- `e` is not cyclic at `y`
  have nR : ¬ S.CycR e := by
    intro hR
    obtain ⟨-, hc⟩ := heR hR
    have hrev := S.prim_reverse k hfin he (by rw [e1, e2]; exact hby.symm) heL hR hc
      (by rw [e1]; exact hqe) (by rw [e1]; exact hprim) (h0 := l) (by rw [l1, e2])
      (by rw [l2, e1]) hel0 hl (by rw [l1, e2]) (by rw [l2, e1])
    exact hS (Or.inr ⟨hby, e, l, he, e1, e2, hrev, by rw [← e1, ← e2]; exact hc,
      by rw [← e1]; exact (by rw [e1]; exact hqe)⟩)
  -- `l` is not cyclic at `y`
  have nL : ¬ S.CycL l := by
    intro hL
    obtain ⟨hχ, hc⟩ := hlL hL
    rw [l1, l2] at hχ hc
    have hdb := S.χ_deg_pos b hqb
    have hey : ⌜e⌝ * S.q y ≠ 0 := by
      intro h0; apply ha1
      rw [pow_succ, ← hel, mul_assoc, hc, ← mul_assoc, h0, zero_mul]
    obtain ⟨t, ht⟩ := S.mul_left_ray hey
    have ht' : ⌜e⌝ * S.q y ^ 1 = ⌜t⌝ := by rw [pow_one]; exact ht
    obtain ⟨t1, t2⟩ := S.mul_qpow_endpoints ht'
    obtain ⟨i, hi⟩ := heL t t1 t2
    have hw1 := congrArg S.wtM ht
    have hy0 : S.q y ≠ 0 := fun h0 ↦ hey (by rw [h0, mul_zero])
    rw [S.wtM_mul _ _ hey, wtM_rr, wtM_rr] at hw1
    have hw2 := S.wt_of_eq_qpow_mul hi
    rw [e1] at hw2
    have hχy : S.χ y = S.χ b := hχ
    have hi1 : i = 1 := by
      have : S.P.wt e + S.χ y = S.P.wt e + i • S.χ b := by
        rw [add_comm (S.P.wt e) (i • _), ← hw2]; exact hw1
      have := congrArg S.P.deg (add_left_cancel this)
      rw [hχy, map_nsmul, nsmul_eq_mul] at this
      have : ((i : ℤ) - 1) * S.P.deg (S.χ b) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · omega
      · linarith
    subst hi1
    have hR : S.CycR e := by
      have := S.prim_action_gen_op he (by rw [e2, hχy]; exact hprim) (by rw [e2]; exact hey)
      exact this.1
    exact nR hR
  refine ⟨heL, nR, hlR, nL, ?_⟩
  exact S.strong_star k hfin hlR nL heL nR (by rw [l2, e1])
    (by rw [l2, ← pow_two]; exact fun h0 ↦ ha1 (by
      rw [show a + 1 = 2 + (a - 1) by omega, pow_add, h0, zero_mul]))

omit [IsAlgClosed k] in
theorem wt_of_eq_qpow {t : R} {x : V} {n : ℕ} (h : ⌜t⌝ = S.q x ^ n) : S.P.wt t = n • S.χ x := by
  have h0 : S.q x ^ n ≠ 0 := h ▸ S.rr_ne t
  have := congrArg S.wtM h
  rwa [wtM_rr, S.wtM_qpow _ _ h0] at this

/-- **Lemma C.2(1)** (`lem:nondeep-two-object-return`): an external return `el = q_b^a` with
`q_b^{a+1} ≠ 0` has `a = 2`, `N_b = 4` and `le = 0`; both Homs are generated only at `b`. -/
theorem nondeep_return (hfin : IsRepresentationFinite k (S.P.Lin k)) {b y : V} {e l : R} {a : ℕ}
    (he : S.IsGen e) (hl : S.IsGen l) (e1 : S.P.src e = b) (e2 : S.P.tgt e = y)
    (l1 : S.P.src l = y) (l2 : S.P.tgt l = b) (hby : y ≠ b) (hel : ⌜e⌝ * ⌜l⌝ = S.q b ^ a)
    (ha : 1 ≤ a) (ha1 : S.q b ^ (a + 1) ≠ 0) (hS : ¬ S.InS b y) (hprim : Prim (S.χ b)) :
    a = 2 ∧ S.q b ^ 3 ≠ 0 ∧ S.q b ^ 4 = 0 ∧ ⌜l⌝ * ⌜e⌝ = 0 ∧
      S.CycL e ∧ ¬ S.CycR e ∧ S.CycR l ∧ ¬ S.CycL l := by
  obtain ⟨heL, heR, hlR, hlL, hle⟩ :=
    S.ret_core k hfin he hl e1 e2 l1 l2 hby hel ha ha1 hS hprim
  have hqb : S.q b ≠ 0 := fun h0 ↦ ha1 (by rw [h0, zero_pow (by omega)])
  have hdχ := S.χ_deg_pos b hqb
  have hpow : ∀ m, m ≤ a + 1 → S.q b ^ m ≠ 0 := fun m hm h0 ↦
    ha1 (by rw [show a + 1 = m + (a + 1 - m) by omega, pow_add, h0, zero_mul])
  have hwel : S.P.wt e + S.P.wt l = a • S.χ b := by
    have hel0 : ⌜e⌝ * ⌜l⌝ ≠ 0 := by rw [hel]; exact hpow a (by omega)
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hel0
    rw [← (S.prod_of ht).2.2.2]; exact S.wt_of_eq_qpow (ht.symm.trans hel)
  have ha2 : 2 ≤ a := by
    by_contra h
    have : a = 1 := by omega
    subst this
    exact hS (Or.inr (S.partner_of_factor e1 e2 hby (by rw [hel, pow_one])
      (hpow 2 le_rfl) hprim).2.2.2.2)
  have ha3 : a = 2 := by
    by_contra h
    have ha3 : 3 ≤ a := by omega
    obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases b).resolve_left hqb
    replace hq0 : S.q b = ⌜q0⌝ := hq0
    have hq2 : ⌜q0⌝ * ⌜q0⌝ ≠ 0 := by rw [← hq0, ← pow_two]; exact hpow 2 (by omega)
    obtain ⟨q2, hq2r⟩ := S.ray_of_mul_ne hq2
    have hq3 : ⌜q0⌝ * ⌜q2⌝ ≠ 0 := by
      rw [← hq2r, ← hq0, ← pow_two, ← pow_succ']; exact hpow 3 (by omega)
    obtain ⟨q3, hq3r⟩ := S.ray_of_mul_ne hq3
    have h21 : ⌜q2⌝ * ⌜q0⌝ = ⌜q3⌝ := by rw [← hq2r, mul_assoc, hq2r, hq3r]
    have hqe : ⌜q0⌝ * ⌜e⌝ ≠ 0 := by
      intro h0; apply hpow (a + 1) le_rfl
      rw [pow_succ', ← hel, ← mul_assoc, hq0, h0, zero_mul]
    obtain ⟨qe, hqer⟩ := S.ray_of_mul_ne hqe
    have hlq : ⌜l⌝ * ⌜q0⌝ ≠ 0 := by
      intro h0; apply hpow (a + 1) le_rfl
      rw [pow_succ, ← hel, mul_assoc, hq0, h0, mul_zero]
    obtain ⟨lq, hlqr⟩ := S.ray_of_mul_ne hlq
    have w0 : S.P.wt q0 = S.χ b := by rw [S.wt_of_eq_qpow (n := 1) (by rw [pow_one, hq0]), one_smul]
    have w2 : S.P.wt q2 = 2 • S.χ b := S.wt_of_eq_qpow (by rw [← hq2r, ← hq0, pow_two])
    have w3 : S.P.wt q3 = 3 • S.χ b := S.wt_of_eq_qpow (by rw [← hq3r, ← hq2r, ← hq0, pow_succ', pow_two])
    have dq := S.P.deg_pos q0 (by rw [q01]; exact q03)
    have de := S.deg_pos_of_ne (f := e) (by rw [e1, e2]; exact hby.symm)
    have dl := S.deg_pos_of_ne (f := l) (by rw [l1, l2]; exact hby)
    have dwel := congrArg S.P.deg hwel
    rw [map_add, map_nsmul, nsmul_eq_mul] at dwel
    -- weights of the rays of the two Homs
    have wL : ∀ h, S.P.src h = b → S.P.tgt h = y → ∃ u : ℕ,
        S.P.deg (S.P.wt h) = u * S.P.deg (S.χ b) + S.P.deg (S.P.wt e) := by
      intro h h1 h2
      obtain ⟨u, hu⟩ := heL h (by rw [h1, e1]) (by rw [h2, e2])
      refine ⟨u, ?_⟩
      rw [S.wt_of_eq_qpow_mul hu, e1, map_add, map_nsmul, nsmul_eq_mul]
    have wR : ∀ h, S.P.src h = y → S.P.tgt h = b → ∃ u : ℕ,
        S.P.deg (S.P.wt h) = S.P.deg (S.P.wt l) + u * S.P.deg (S.χ b) := by
      intro h h1 h2
      obtain ⟨u, hu⟩ := hlR h (by rw [h1, l1]) (by rw [h2, l2])
      have h0 : ⌜l⌝ * S.q (S.P.tgt l) ^ u ≠ 0 := hu ▸ S.rr_ne h
      have hw := congrArg S.wtM hu
      rw [wtM_rr, S.wtM_mul _ _ h0, wtM_rr, S.wtM_qpow _ _ (fun h' ↦ h0 (by rw [h', mul_zero])),
        l2] at hw
      refine ⟨u, ?_⟩
      rw [hw, map_add, map_nsmul, nsmul_eq_mul]
    refine S.P.q6_false (b := b) (y := y) q01 q02 e1 e2 l1 l2
      (S.P.rr_mul_rr_eq_rr.1 hq2r) (S.P.rr_mul_rr_eq_rr.1 hq3r) (S.P.rr_mul_rr_eq_rr.1 h21)
      (S.P.rr_mul_rr_eq_rr.1 hqer) (S.P.rr_mul_rr_eq_rr.1 hlqr) dq de dl ?_ ?_ ?_ ?_ ?_ ?_ k hfin
    · intro h h1 h2 hm
      exact S.gen_ne_q_mul he (b := h) (by rw [h1, e1]) (by rw [h2, e2]) 1 le_rfl
        (by rw [e1, pow_one, hq0]; exact (S.P.rr_mul_rr_eq_rr.2 hm).symm)
    · intro h h1 h2 hm
      exact hS (Or.inr (S.partner_of_factor e1 e2 hby
        (by rw [S.P.rr_mul_rr_eq_rr.2 hm, hq0]) (hpow 2 (by omega)) hprim).2.2.2.2)
    · intro h h1 h2 hw
      obtain ⟨u, hu⟩ := wR h h1 h2
      have := congrArg S.P.deg hw
      rw [map_add, map_add, hu, w0, w3, map_nsmul, nsmul_eq_mul] at this
      have : ((a : ℤ) + u - 2) * S.P.deg (S.χ b) = 0 := by push_cast at this ⊢; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · omega
      · linarith
    · intro h h1 h2 hw
      exact S.no_below_gen hdχ hl (by rw [h1, l1]) (by rw [h2, l2]) 1 le_rfl
        (by rw [one_smul, ← w0]; rw [w2] at hw; rw [two_nsmul, ← w0] at hw
            exact (add_left_cancel (a := S.P.wt q0) (by rw [← hw]; abel)).symm)
    · intro h h1 h2 hw
      obtain ⟨u, hu⟩ := wL h h1 h2
      have := congrArg S.P.deg hw
      rw [map_add, map_add, hu, w0, w2, map_nsmul, nsmul_eq_mul] at this
      have : ((a : ℤ) + u - 1) * S.P.deg (S.χ b) = 0 := by push_cast at this ⊢; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · omega
      · linarith
    · intro h h1 h2 hw
      obtain ⟨u, hu⟩ := wL h h1 h2
      have := congrArg S.P.deg hw
      rw [map_add, hu, w2, map_nsmul, nsmul_eq_mul] at this
      have : ((a : ℤ) + u - 2) * S.P.deg (S.χ b) = 0 := by push_cast at this ⊢; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · omega
      · linarith
  subst ha3
  refine ⟨rfl, hpow 3 le_rfl, ?_, hle, heL, heR, hlR, hlL⟩
  rw [show 4 = 2 + 2 by rfl, pow_add, ← hel]
  simp only [mul_assoc]
  rw [← mul_assoc ⌜l⌝ ⌜e⌝, hle, zero_mul, mul_zero]

omit [IsAlgClosed k] in
/-- Left cancellation of a local power. -/
theorem cancel_qpow_left {b : V} {u w : R} (j : ℕ) (h : S.q b ^ j * ⌜u⌝ = S.q b ^ j * ⌜w⌝)
    (h0 : S.q b ^ j * ⌜u⌝ ≠ 0) : u = w := by
  induction j generalizing u w with
  | zero => rw [pow_zero, one_mul, one_mul] at h; exact S.rr_inj h
  | succ j ih =>
    have hq : S.q b ≠ 0 := fun h' ↦ h0 (by rw [h', zero_pow (by omega), zero_mul])
    obtain ⟨q0, hq0, -, -, -⟩ := (S.q_cases b).resolve_left hq
    replace hq0 : S.q b = ⌜q0⌝ := hq0
    simp only [pow_succ', mul_assoc] at h h0
    have hu : S.q b ^ j * ⌜u⌝ ≠ 0 := fun h' ↦ h0 (by rw [h', mul_zero])
    have hw : S.q b ^ j * ⌜w⌝ ≠ 0 := fun h' ↦ h0 (by rw [h, h', mul_zero])
    obtain ⟨u', hu'⟩ := S.mul_right_ray hu
    obtain ⟨w', hw'⟩ := S.mul_right_ray hw
    rw [hu', hw', hq0] at h
    rw [hu', hq0] at h0
    exact ih (by rw [hu', hw', S.cancel_left h h0]) hu

omit [IsAlgClosed k] in
theorem qpow_mul_e {x : V} {n : ℕ} (hn : 1 ≤ n) : S.q x ^ n * ⌜S.P.e x⌝ = S.q x ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, pow_succ, mul_assoc, S.q_mul_e]

variable {χ : L}

omit [IsAlgClosed k] in
/-- A left-sided ray is not local. -/
theorem tl_nonlocal {f : R} (hT : S.TL χ f) : S.P.tgt f ≠ S.P.src f := by
  obtain ⟨-, h1, h2⟩ := hT
  have hs := S.supp_of_qh h1
  intro hl
  obtain ⟨j, hj, -⟩ := S.local_eq f hl.symm
  have hq : S.qh χ (S.P.src f) = S.q (S.P.src f) := S.qh_of_supp χ hs
  rw [hq] at h1
  rw [hl, hq] at h2
  have hc : S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.src f) := by
    rw [← hj, ← mul_assoc, ← pow_succ', mul_assoc, S.e_mul_q, ← pow_succ,
      S.qpow_mul_e (by omega)]
  exact h1 (by rw [hc, h2])

omit [IsAlgClosed k] in
/-- A left-sided generating ray leaves the return corner of its source. -/
theorem notInS_of_TL {f : R} (hf : S.IsGen f) (hT : S.TL χ f) :
    S.P.tgt f ≠ S.P.src f ∧ ¬ S.InS (S.P.src f) (S.P.tgt f) := by
  obtain ⟨hsh, h1, h2⟩ := hT
  have hs := S.supp_of_qh h1
  have hloc : S.P.tgt f ≠ S.P.src f := by
    intro hl
    obtain ⟨j, hj, -⟩ := S.local_eq f hl.symm
    have hq : S.qh χ (S.P.src f) = S.q (S.P.src f) := S.qh_of_supp χ hs
    rw [hq] at h1
    rw [hl, hq] at h2
    have hc : S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.src f) := by
      rw [← hj, ← mul_assoc, ← pow_succ', mul_assoc, S.e_mul_q, ← pow_succ,
        S.qpow_mul_e (by omega)]
    exact h1 (by rw [hc, h2])
  refine ⟨hloc, ?_⟩
  rintro (h | ⟨-, g, h', hg, g1, g2, ⟨hgh, hhg⟩, hc, hc0⟩)
  · exact hloc h
  · have := S.gen_unique hg hf (by rw [g1]) g2
    subst this
    have hχ : S.χ (S.P.tgt g) = S.χ (S.P.src g) := by
      have e1 : ⌜g⌝ * ⌜h'⌝ ≠ 0 := by rw [hgh]; exact hs.1
      obtain ⟨t, ht⟩ := S.ray_of_mul_ne e1
      have e2 : ⌜h'⌝ * ⌜g⌝ ≠ 0 := by
        rw [hhg]; intro h0; apply hc0; rw [hc, h0, mul_zero]
      obtain ⟨t', ht'⟩ := S.ray_of_mul_ne e2
      have w1 := S.wt_of_eq_qpow (n := 1) (by rw [pow_one, ← ht, hgh])
      have w2 := S.wt_of_eq_qpow (n := 1) (by rw [pow_one, ← ht', hhg])
      rw [one_smul] at w1 w2
      rw [← w1, ← w2, (S.prod_of ht).2.2.2, (S.prod_of ht').2.2.2, add_comm]
    have hsy : S.Supp χ (S.P.tgt g) := ⟨fun h0 ↦ hc0 (by rw [hc, h0, mul_zero]), hχ.trans hs.2⟩
    rw [S.qh_of_supp χ hsy, ← hc] at h2; exact hc0 h2

omit [IsAlgClosed k] in
/-- Step 2 of the length bound: a reverse product `f h = q_b^m` of a left-sided generating `f`
comes from a generating reverse cyclic at `b`. -/
theorem gen_rev_of_TL (hprim : Prim χ) {f h : R} {m : ℕ} (hf : S.IsGen f) (hT : S.TL χ f)
    (h1 : S.P.src h = S.P.tgt f) (h2 : S.P.tgt h = S.P.src f) (hm : 1 ≤ m)
    (hfh : ⌜f⌝ * ⌜h⌝ = S.q (S.P.src f) ^ m) (hm1 : S.q (S.P.src f) ^ (m + 1) ≠ 0) :
    ∃ l m', S.IsGen l ∧ S.CycR l ∧ S.P.src l = S.P.tgt f ∧ S.P.tgt l = S.P.src f ∧ 1 ≤ m' ∧
      m' ≤ m ∧ ⌜f⌝ * ⌜l⌝ = S.q (S.P.src f) ^ m' := by
  set b := S.P.src f with hb
  set y := S.P.tgt f with hy
  have hT' := hT
  obtain ⟨-, hq1, hq2⟩ := hT'
  have hs := S.supp_of_qh hq1
  have hloc := (S.notInS_of_TL hf hT).1
  have hqb : S.q b ≠ 0 := hs.1
  have hdχ := S.χ_deg_pos b hqb
  have hdf := S.deg_pos_of_ne (f := f) (fun e ↦ hloc e.symm)
  obtain ⟨l, l1, l2, hl⟩ := S.exists_gen h
  rw [h1] at l1; rw [h2] at l2
  have hhq : ⌜h⌝ * S.q b ≠ 0 := by
    intro h0; apply hm1; rw [pow_succ, ← hfh, mul_assoc, h0, mul_zero]
  by_cases hR : S.CycR l
  swap
  · -- generated only at `y`: the action of `q_b` on `h` is a power of `q_y`
    exfalso
    have hL := (S.gen_cyc hl).resolve_right hR
    obtain ⟨i, hi⟩ := hL h (by rw [h1, l1]) (by rw [h2, l2])
    obtain ⟨t, ht⟩ := S.mul_left_ray hhq
    obtain ⟨t1, t2⟩ := S.mul_qpow_endpoints (n := 1) (by rw [pow_one]; exact ht)
    obtain ⟨d, hd⟩ := hL t (by rw [t1, h1, l1]) (by rw [t2, h2, l2])
    rw [l1] at hi hd
    have w1 := S.wt_of_eq_qpow_mul (f := l) (by rw [l1]; exact hi)
    have w2 := S.wt_of_eq_qpow_mul (f := l) (by rw [l1]; exact hd)
    rw [l1] at w1 w2
    have w3 : S.P.wt t = S.P.wt h + S.χ b := by
      have := congrArg S.wtM ht
      rwa [S.wtM_mul _ _ hhq, wtM_rr, wtM_rr, eq_comm] at this
    have hdy := fun n : ℕ ↦ S.nsmul_χ_deg y n
    have key : S.χ b + i • S.χ y = d • S.χ y := by
      have := w3.symm.trans w2
      rw [w1] at this
      have : S.χ b + (i • S.χ y + S.P.wt l) = d • S.χ y + S.P.wt l := by rw [← this]; abel
      have := add_right_cancel (b := S.P.wt l) (by rw [← this]; abel : S.χ b + i • S.χ y + S.P.wt l = d • S.χ y + S.P.wt l)
      exact this
    have hid : i < d := by
      have := congrArg S.P.deg key
      simp only [map_add, map_nsmul, nsmul_eq_mul] at this
      have hy0 := S.deg_χ_nonneg y
      by_contra hc
      have : (d : ℤ) * S.P.deg (S.χ y) ≤ i * S.P.deg (S.χ y) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast not_lt.1 hc) hy0
      linarith
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hid
    have hn : S.χ b = (n + 1) • S.χ y := by
      rw [show i + n + 1 = i + (n + 1) by omega, add_nsmul, add_comm] at key
      exact add_left_cancel key
    have hn0 : n = 0 := by
      have := hprim (n + 1) (S.χ y) (by rw [← hn, hs.2]); omega
    subst hn0
    rw [zero_add, one_smul] at hn
    have hqy : S.q y ≠ 0 := by
      intro h0; apply S.rr_ne t; rw [hd, h0, zero_pow (by omega), zero_mul]
    have hsy : S.Supp χ y := ⟨hqy, hn.symm.trans hs.2⟩
    rw [S.qh_of_supp χ hsy] at hq2
    apply hm1
    rw [pow_succ, ← hfh, mul_assoc, ht, hd, ← mul_assoc, show i + 0 + 1 = i + 1 by omega,
      pow_succ', ← mul_assoc, hq2]
    simp
  · obtain ⟨u, hu⟩ := hR h (by rw [h1, l1]) (by rw [h2, l2])
    rw [l2] at hu
    have hfl : ⌜f⌝ * ⌜l⌝ ≠ 0 := by
      intro h0; apply hm1; rw [pow_succ, ← hfh, hu, ← mul_assoc, h0]; simp
    obtain ⟨v, hv⟩ := S.ray_of_mul_ne hfl
    obtain ⟨v1, v2, -, v4⟩ := S.prod_of hv
    have hvl : S.P.src v = S.P.tgt v := by rw [v1, v2, l2]
    obtain ⟨m', hm', hw⟩ := S.local_eq v hvl
    rw [v1] at hm' hw
    have dl := S.P.deg_nonneg l
    have hm'1 : 1 ≤ m' := by
      by_contra h0
      have : m' = 0 := by omega
      subst this
      rw [zero_smul] at hw
      have := congrArg S.P.deg (v4.symm.trans hw)
      rw [map_add, map_zero] at this; linarith
    -- weights: `m' + u = m`
    have hwm : S.P.wt f + S.P.wt h = m • S.χ b := by
      have hne : ⌜f⌝ * ⌜h⌝ ≠ 0 := by rw [hfh]; intro h0; apply hm1; rw [pow_succ, h0, zero_mul]
      obtain ⟨t, ht⟩ := S.ray_of_mul_ne hne
      rw [← (S.prod_of ht).2.2.2]; exact S.wt_of_eq_qpow (ht.symm.trans hfh)
    have hwh : S.P.wt h = S.P.wt l + u • S.χ b := by
      have h0 : ⌜l⌝ * S.q b ^ u ≠ 0 := hu ▸ S.rr_ne h
      have := congrArg S.wtM hu
      rwa [wtM_rr, S.wtM_mul _ _ h0, wtM_rr, S.wtM_qpow _ _ (fun h' ↦ h0 (by rw [h', mul_zero]))]
        at this
    have hmu : m' + u = m := by
      have e1 := congrArg S.P.deg hwm
      rw [hwh, ← add_assoc, ← v4, hw] at e1
      simp only [map_add, map_nsmul, nsmul_eq_mul] at e1
      have : ((m' : ℤ) + u - m) * S.P.deg (S.χ b) = 0 := by push_cast; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · omega
      · linarith
    exact ⟨l, m', hl, hR, l1, l2, hm'1, by omega, by rw [hv, ← hm', S.qpow_mul_e hm'1]⟩

omit [IsAlgClosed k] in
theorem e_mul_qpow_mul {x : V} {c : R} (hc : S.P.src c = x) (n : ℕ) :
    ⌜S.P.e x⌝ * (S.q x ^ n * ⌜c⌝) = S.q x ^ n * ⌜c⌝ := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [pow_zero, one_mul, S.e_mul_rr' c hc]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, pow_succ', ← mul_assoc, ← mul_assoc, S.e_mul_q]

omit [IsAlgClosed k] in
/-- Positive comparisons in the faithful projective support at `x`. -/
theorem rf_qpow {x : V} {u w c : R} (hc : S.P.src c = x) {i i' : ℕ} (hii : i ≤ i')
    (hu : ⌜u⌝ = S.q x ^ i * ⌜S.P.e x⌝) (hw : ⌜w⌝ = S.q x ^ i' * ⌜c⌝) : S.P.RF u w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hii
  have hne : S.q x ^ d * ⌜c⌝ ≠ 0 := by
    intro h0; apply S.rr_ne w; rw [hw, pow_add, mul_assoc, h0, mul_zero]
  obtain ⟨v, hv⟩ := S.mul_right_ray hne
  refine (S.rf_iff _ _).2 ⟨v, ?_⟩
  rw [hu, ← hv, mul_assoc, S.e_mul_qpow_mul hc, ← mul_assoc, ← pow_add, hw]

omit [IsAlgClosed k] in
theorem tgt_of_qpow_e {u : R} {x : V} {i : ℕ} (hu : ⌜u⌝ = S.q x ^ i * ⌜S.P.e x⌝) :
    S.P.src u = x ∧ S.P.tgt u = x := by
  obtain ⟨h1, h2⟩ := S.qpow_mul_endpoints hu.symm
  rw [S.P.src_e] at h1; rw [S.P.tgt_e] at h2; exact ⟨h1, h2⟩

omit [IsAlgClosed k] in
/-- `Q_i ≤ Y_j` fails for `i > j`: it would make the generating ray proper. -/
theorem not_rf_qpow_gen {x : V} {f u w : R} (hf : S.IsGen f) (f1 : S.P.src f = x) {i j : ℕ}
    (hu : ⌜u⌝ = S.q x ^ i * ⌜S.P.e x⌝) (hw : ⌜w⌝ = S.q x ^ j * ⌜f⌝) (hij : j < i) :
    ¬ S.P.RF u w := by
  rw [S.rf_iff]; rintro ⟨v, hv⟩
  have hv1 : S.P.src v = x := by
    rw [← S.src_of_mul_ne (by rw [hv]; exact S.rr_ne w), (S.tgt_of_qpow_e hu).2]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  rw [hu, mul_assoc, S.e_mul_rr' v hv1, show j + d + 1 = j + (d + 1) by omega, pow_add,
    mul_assoc, hw] at hv
  have hne : S.q x ^ (d + 1) * ⌜v⌝ ≠ 0 := by
    intro h0; apply S.rr_ne w; rw [hw, ← hv, h0, mul_zero]
  obtain ⟨v', hv'⟩ := S.mul_right_ray hne
  rw [hv'] at hv
  have := S.cancel_qpow_left j hv (by rw [hv, ← hw]; exact S.rr_ne w)
  subst this
  obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints hv'
  exact S.gen_ne_q_mul hf (b := v) (by rw [← e1]) (by rw [← e2]) (d + 1) (by omega)
    (by rw [f1]; exact hv'.symm)

omit [IsAlgClosed k] in
theorem not_rf_deg {u w : R} (h : S.P.deg (S.P.wt w) < S.P.deg (S.P.wt u)) : ¬ S.P.RF u w :=
  fun hr ↦ absurd (S.rf_deg_le hr) (not_le.2 h)

/-- **Proposition 8.25(1), length bound** (Steps 1–3 of Appendix C.2): if a left-sided
generating ray `f : b → y` has `q̂_b² f ≠ 0`, then `q̂_b³ = 0`. -/
theorem len_L (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f : R} (hf : S.IsGen f) (hT : S.TL χ f)
    (hq2f : S.qh χ (S.P.src f) ^ 2 * ⌜f⌝ ≠ 0) : S.qh χ (S.P.src f) ^ 3 = 0 := by
  set b := S.P.src f with hb
  set y := S.P.tgt f with hy
  have hT' := hT
  obtain ⟨-, hq1, -⟩ := hT'
  have hs := S.supp_of_qh hq1
  have hqb : S.qh χ b = S.q b := S.qh_of_supp χ hs
  rw [hqb] at hq2f ⊢
  by_contra hq3
  obtain ⟨hyb, hS⟩ := S.notInS_of_TL hf hT
  have hprim' : Prim (S.χ b) := by rw [hs.2]; exact hprim
  have hdχ := S.χ_deg_pos b hs.1
  have hdf := S.deg_pos_of_ne (f := f) (fun e ↦ hyb e.symm)
  have hpow : ∀ m, m ≤ 3 → S.q b ^ m * ⌜S.P.e b⌝ ≠ 0 := by
    intro m hm h0
    apply hq3
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [pow_zero, one_mul] at h0; exact absurd h0 (S.rr_ne _)
    · rw [S.qpow_mul_e h] at h0
      rw [show 3 = m + (3 - m) by omega, pow_add, h0, zero_mul]
  have hpowf : ∀ m, m ≤ 2 → S.q b ^ m * ⌜f⌝ ≠ 0 := by
    intro m hm h0; apply hq2f
    rw [show 2 = (2 - m) + m by omega, pow_add, mul_assoc, h0, mul_zero]
  have rQ : ∀ m, m ≤ 3 → ∃ u, ⌜u⌝ = S.q b ^ m * ⌜S.P.e b⌝ := fun m hm ↦
    (S.mul_right_ray (hpow m hm)).imp fun _ h ↦ h.symm
  have rY : ∀ m, m ≤ 2 → ∃ u, ⌜u⌝ = S.q b ^ m * ⌜f⌝ := fun m hm ↦
    (S.mul_right_ray (hpowf m hm)).imp fun _ h ↦ h.symm
  obtain ⟨Q0, h0⟩ := rQ 0 (by omega)
  obtain ⟨Q1, h1⟩ := rQ 1 (by omega)
  obtain ⟨Q2, h2⟩ := rQ 2 (by omega)
  obtain ⟨Q3, h3⟩ := rQ 3 le_rfl
  obtain ⟨Y1, y1⟩ := rY 1 (by omega)
  obtain ⟨Y2, y2⟩ := rY 2 le_rfl
  have dQ : ∀ {u : R} {m : ℕ}, ⌜u⌝ = S.q b ^ m * ⌜S.P.e b⌝ →
      S.P.deg (S.P.wt u) = m * S.P.deg (S.χ b) := fun h ↦ S.deg_wt_qpow_e h
  have dY : ∀ {u : R} {m : ℕ}, ⌜u⌝ = S.q b ^ m * ⌜f⌝ →
      S.P.deg (S.P.wt u) = m * S.P.deg (S.χ b) + S.P.deg (S.P.wt f) := by
    intro u m h
    rw [S.wt_of_eq_qpow_mul h, map_add, map_nsmul, nsmul_eq_mul]
  -- Step 2: no reverse comparison `Y_j ≤ Q_i`
  have nYQ : ∀ {u w : R} {i j : ℕ}, ⌜u⌝ = S.q b ^ j * ⌜f⌝ → ⌜w⌝ = S.q b ^ i * ⌜S.P.e b⌝ →
      1 ≤ j → j ≤ 2 → i ≤ 3 → ¬ S.P.RF u w := by
    intro u w i j hu hw hj1 hj2 hi3
    by_cases hij : i ≤ j
    · apply S.not_rf_deg
      rw [dQ hw, dY hu]
      have : (i : ℤ) * S.P.deg (S.χ b) ≤ j * S.P.deg (S.χ b) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hdχ.le
      linarith
    rw [S.rf_iff]; rintro ⟨v, hv⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 hij)
    rw [hu, hw, show j + d + 1 = j + (d + 1) by omega, pow_add, mul_assoc, mul_assoc] at hv
    have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ hpow (j + (d + 1)) hi3 (by
      rw [pow_add, mul_assoc, ← hv, h', mul_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hfv
    obtain ⟨s', hs'⟩ := S.mul_right_ray (hpow (d + 1) (by omega))
    rw [ht, hs'] at hv
    have hnz : S.q b ^ j * ⌜t⌝ ≠ 0 := by
      rw [hv, ← hs', ← mul_assoc, ← pow_add]; exact hpow _ hi3
    have := S.cancel_qpow_left j hv hnz
    subst this
    have hfh : ⌜f⌝ * ⌜v⌝ = S.q b ^ (d + 1) := by rw [ht, ← hs', S.qpow_mul_e (by omega)]
    obtain ⟨t1, t2, t3, -⟩ := S.prod_of ht
    obtain ⟨l1', l2'⟩ := S.tgt_of_qpow_e hs'.symm
    obtain ⟨l, m', hl, -, l1, l2, hm1, hm2, hfl⟩ := S.gen_rev_of_TL hprim hf hT (h := v)
      (by rw [← t3]) (by rw [← t2, l2']) (m := d + 1) (by omega) hfh
      (fun h' ↦ hq3 (by rw [show 3 = (d + 2) + (1 - d) by omega, pow_add, h', zero_mul]))
    obtain ⟨-, -, -, hle, -⟩ := S.nondeep_return k hfin hf hl rfl rfl l1 l2 hyb hfl hm1
      (fun h' ↦ hq3 (by rw [show 3 = (m' + 1) + (2 - m') by omega, pow_add, h', zero_mul]))
      hS hprim'
    apply hpowf m' (by omega)
    rw [← hfl, mul_assoc, hle, mul_zero]
  have nY12 : ¬ S.P.RF Y1 Y2 := by
    rw [S.rf_iff]; rintro ⟨v, hv⟩
    rw [y1, y2, mul_assoc, show 2 = 1 + 1 by rfl, pow_add, mul_assoc] at hv
    have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h' ↦ hpowf 2 le_rfl (by
      rw [show 2 = 1 + 1 by rfl, pow_add, mul_assoc, ← hv, h', mul_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hfv
    obtain ⟨t', ht'⟩ := S.mul_right_ray (hpowf 1 (by omega))
    rw [ht, ht'] at hv
    have hnz : S.q b ^ 1 * ⌜t⌝ ≠ 0 := by
      rw [hv, ← ht', ← mul_assoc, ← pow_add]; exact hpowf 2 le_rfl
    have := S.cancel_qpow_left 1 hv hnz
    subst this
    exact S.no_hidden_target hχ hprim hT (by rw [ht, ← ht', pow_one, hqb])
  refine S.P.table_supp_false k hfin Tab.tL6 b ![Q0, Q1, Q2, Q3, Y1, Y2] ![1, 2, 2, 1, 1, 1]
    Tab.tL6_uniq Tab.tL6_count Tab.tL6_anti ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact (S.tgt_of_qpow_e h0).1
    · exact (S.tgt_of_qpow_e h1).1
    · exact (S.tgt_of_qpow_e h2).1
    · exact (S.tgt_of_qpow_e h3).1
    · exact (S.qpow_mul_endpoints y1.symm).1
    · exact (S.qpow_mul_endpoints y2.symm).1
  · have hse := S.P.src_e b
    have p01 := S.rf_qpow hse (by omega) h0 h1
    have p02 := S.rf_qpow hse (by omega) h0 h2
    have p03 := S.rf_qpow hse (by omega) h0 h3
    have p12 := S.rf_qpow hse (by omega) h1 h2
    have p13 := S.rf_qpow hse (by omega) h1 h3
    have p23 := S.rf_qpow hse (by omega) h2 h3
    have p04 := S.rf_qpow (c := f) rfl (by omega) h0 y1
    have p14 := S.rf_qpow (c := f) rfl (by omega) h1 y1
    have p05 := S.rf_qpow (c := f) rfl (by omega) h0 y2
    have p15 := S.rf_qpow (c := f) rfl (by omega) h1 y2
    have p25 := S.rf_qpow (c := f) rfl (by omega) h2 y2
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Tab.tL6] at hij <;>
      first | exact S.P.rf_refl _ | assumption
  · have nQ : ∀ {u w : R} {i j : ℕ}, ⌜u⌝ = S.q b ^ i * ⌜S.P.e b⌝ →
        ⌜w⌝ = S.q b ^ j * ⌜S.P.e b⌝ → j < i → ¬ S.P.RF u w := by
      intro u w i j hu hw hij
      apply S.not_rf_deg
      rw [dQ hu, dQ hw]
      have : (j : ℤ) * S.P.deg (S.χ b) < i * S.P.deg (S.χ b) :=
        mul_lt_mul_of_pos_right (by exact_mod_cast hij) hdχ
      exact this
    have n10 := nQ h1 h0 (by omega)
    have n20 := nQ h2 h0 (by omega)
    have n30 := nQ h3 h0 (by omega)
    have n21 := nQ h2 h1 (by omega)
    have n31 := nQ h3 h1 (by omega)
    have n32 := nQ h3 h2 (by omega)
    have n24 := S.not_rf_qpow_gen hf rfl h2 y1 (by omega)
    have n34 := S.not_rf_qpow_gen hf rfl h3 y1 (by omega)
    have n35 := S.not_rf_qpow_gen hf rfl h3 y2 (by omega)
    have n40 := nYQ y1 h0 le_rfl (by omega) (by omega)
    have n41 := nYQ y1 h1 le_rfl (by omega) (by omega)
    have n42 := nYQ y1 h2 le_rfl (by omega) (by omega)
    have n43 := nYQ y1 h3 le_rfl (by omega) (by omega)
    have n50 := nYQ y2 h0 (by omega) le_rfl (by omega)
    have n51 := nYQ y2 h1 (by omega) le_rfl (by omega)
    have n52 := nYQ y2 h2 (by omega) le_rfl (by omega)
    have n53 := nYQ y2 h3 (by omega) le_rfl (by omega)
    have n54 : ¬ S.P.RF Y2 Y1 := by
      apply S.not_rf_deg; rw [dY y1, dY y2]; push_cast; linarith
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Tab.tL6] at hij <;> assumption
/-- **Proposition 8.25(1), length bound, right-sided form.** -/
theorem len_R (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f : R} (hf : S.IsGen f) (hT : S.TR χ f)
    (hq2f : ⌜f⌝ * S.qh χ (S.P.tgt f) ^ 2 ≠ 0) : S.qh χ (S.P.tgt f) ^ 3 = 0 := by
  have := S.op.len_L k (S.P.op_isRepresentationFinite k hfin) hχ hprim ((S.op_isGen_iff f).2 hf)
    ((S.op_TL f).2 hT) (by
      change S.op.qh χ (S.P.tgt f) ^ 2 * S.P.toOp ⌜f⌝ ≠ 0
      rw [S.op_qh, ← Tab.toOp_pow, ← Tab.toOp_mul]; exact hq2f)
  change S.op.qh χ (S.P.tgt f) ^ 3 = 0 at this
  rw [S.op_qh, ← Tab.toOp_pow] at this
  exact this

/-- Endpoint layer preservation, generating inputs (Appendix C.2): for generating left-sided
`f, h` out of `b`, the product `f v` is never `q̂_b h` with `q̂_b² h ≠ 0`. -/
theorem layer_gen_L (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f h v : R} (hf : S.IsGen f) (hh : S.IsGen h) (hTf : S.TL χ f)
    (hTh : S.TL χ h) (hsrc : S.P.src h = S.P.src f)
    (hv : ⌜f⌝ * ⌜v⌝ = S.qh χ (S.P.src f) * ⌜h⌝)
    (hsh : S.qh χ (S.P.src f) * (S.qh χ (S.P.src f) * ⌜h⌝) ≠ 0) : False := by
  have hTf' := hTf
  obtain ⟨-, hq1, -⟩ := hTf'
  have hs := S.supp_of_qh hq1
  have hqb : S.qh χ (S.P.src f) = S.q (S.P.src f) := S.qh_of_supp χ hs
  have hq2 : S.q (S.P.src f) ^ 2 ≠ 0 := by
    rw [hqb] at hsh; intro h0; apply hsh; rw [← mul_assoc, ← pow_two, h0, zero_mul]
  have hqh : S.qh χ (S.P.src f) * ⌜h⌝ ≠ 0 := fun h0 ↦ hsh (by rw [h0, mul_zero])
  obtain ⟨hfy, hfS⟩ := S.notInS_of_TL hf hTf
  obtain ⟨hhy, hhS⟩ := S.notInS_of_TL hh hTh
  rw [hsrc] at hhS hhy
  rcases S.ext_chain k hfin (by rw [hs.2]; exact hprim) hq2 hf hh rfl hsrc
    (by rw [← hqb]; exact hq1) (by rw [← hqb]; exact hqh) hfS hhS with hc | hc
  · obtain ⟨c, hc⟩ := (S.rf_iff _ _).1 hc
    by_cases hce : c = S.P.e (S.P.src c)
    · have := S.src_of_mul_ne (by rw [hc]; exact S.rr_ne h)
      rw [hce, ← this, S.rr_mul_e] at hc
      have := S.rr_inj hc
      subst this
      exact S.no_hidden_target hχ hprim hTf hv
    · obtain ⟨c1, c2, c3, c4⟩ := S.prod_of hc
      have hTh' := hTh
      obtain ⟨shh, hqh', -⟩ := hTh'
      obtain ⟨-, hsucc⟩ := S.shift_of_qh_mul shh.1 hqh'
      obtain ⟨e1, e2, e3⟩ := S.succ_spec χ shh
      rw [← hsrc, hsucc] at hv
      obtain ⟨v1, v2, v3, v4⟩ := S.prod_of hv
      have hshc : S.Shift χ c := ⟨hce, v, by rw [← v3, c3], by rw [← v2, e2, c2],
        by
          have := v4.symm.trans (e3.trans (by rw [c4]))
          rw [add_assoc] at this; exact add_left_cancel this⟩
      have hvc : v = S.succ χ c := S.eq_succ χ hshc (by rw [← v3, c3]) (by rw [← v2, e2, c2])
        (by have := v4.symm.trans (e3.trans (by rw [c4]))
            rw [add_assoc] at this; exact add_left_cancel this)
      subst hvc
      have hf0 : f ≠ S.P.e (S.P.src f) := hTf.1.1
      rcases S.table_L hχ hprim hf0 hce hc hTh with ⟨-, -, hn⟩ | ⟨hB, -⟩
      · exact hn ⟨hshc, hv⟩
      · exact hB.2.2 hTf.2.2
  · obtain ⟨c, hc⟩ := (S.rf_iff _ _).1 hc
    rw [← hc, mul_assoc] at hv
    have hcv : ⌜c⌝ * ⌜v⌝ ≠ 0 := fun h0 ↦ hqh (by rw [← hv, h0, mul_zero])
    obtain ⟨w, hw⟩ := S.ray_of_mul_ne hcv
    rw [hw] at hv
    exact S.no_hidden_target hχ hprim hTh (by rw [hv, hsrc])

omit [IsAlgClosed k] in
/-- A nonidentity factor `r₀` of a left-sided `r = q̂_b^i r₀` is left-sided. -/
theorem tl_factor {r r0 : R} {i : ℕ} (hT : S.TL χ r)
    (h : ⌜r⌝ = S.qh χ (S.P.src r) ^ i * ⌜r0⌝) (hr0 : r0 ≠ S.P.e (S.P.src r0)) : S.TL χ r0 := by
  obtain ⟨-, h1, h2⟩ := hT
  have hs := S.supp_of_qh h1
  obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ hs]; exact h.symm)
  have hq : S.qh χ (S.P.src r0) * ⌜r0⌝ ≠ 0 := by
    intro h0; apply h1; rw [h, ← mul_assoc, ← pow_succ', pow_succ, mul_assoc, e1, h0, mul_zero]
  obtain ⟨hsh, hs1⟩ := S.shift_of_qh_mul hr0 hq
  refine ⟨hsh, hq, ?_⟩
  by_contra hB
  obtain ⟨-, hs2⟩ := S.shift_of_mul_qh hr0 hB
  have : S.qh χ (S.P.src r) * ⌜r⌝ = ⌜r⌝ * S.qh χ (S.P.tgt r) := by
    rw [h, e1, e2, ← mul_assoc, ← pow_succ', pow_succ, mul_assoc, hs1, mul_assoc, hs2]
  exact h1 (by rw [this, h2])

/-- **Proposition 8.25(1), endpoint layer preservation**: if `r = q̂_b^i r₀` with `r₀`
generating and `rs` are left-sided, then `r₀ s` is generating and `rs = q̂_b^i (r₀ s)`. -/
theorem layer_L (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r s t r0 : R} {i : ℕ} (hTr : S.TL χ r) (hTt : S.TL χ t)
    (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hr0 : S.IsGen r0) (hri : ⌜r⌝ = S.qh χ (S.P.src r) ^ i * ⌜r0⌝) :
    ∃ t0, S.IsGen t0 ∧ ⌜r0⌝ * ⌜s⌝ = ⌜t0⌝ ∧ ⌜t⌝ = S.qh χ (S.P.src r) ^ i * ⌜t0⌝ := by
  have hsr := S.supp_of_qh hTr.2.1
  obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints (by rw [← S.qh_of_supp χ hsr]; exact hri.symm)
  obtain ⟨t1, t2, -, -⟩ := S.prod_of hrs
  have hr0s : ⌜r0⌝ * ⌜s⌝ ≠ 0 := by
    intro h0; apply S.rr_ne t; rw [← hrs, hri, mul_assoc, h0, mul_zero]
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne hr0s
  have htu : ⌜t⌝ = S.qh χ (S.P.src r) ^ i * ⌜u⌝ := by rw [← hrs, hri, mul_assoc, hu]
  obtain ⟨u1, -, -, u4⟩ := S.prod_of hu
  have hnl := S.tl_nonlocal hTr
  have hloc : S.P.tgt r0 ≠ S.P.src r0 := fun h ↦ hnl (by rw [e1, e2, h])
  have hr00 : r0 ≠ S.P.e (S.P.src r0) := fun he ↦ hloc (by
    nth_rewrite 1 [he]; rw [S.P.tgt_e])
  have hTr0 := S.tl_factor hTr hri hr00
  have hu0 : u ≠ S.P.e (S.P.src u) := by
    apply S.ne_e_of_deg; rw [u4, map_add]
    have := S.deg_pos_of_ne (f := r0) (fun e ↦ hloc e.symm)
    have := S.P.deg_nonneg s; linarith
  have hTu : S.TL χ u := S.tl_factor hTt (by rw [htu, t1]) hu0
  refine ⟨u, ?_, hu, htu⟩
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen u
  have hsu := S.supp_of_qh hTu.2.1
  have hqu : S.q (S.P.src u) * ⌜u⌝ ≠ 0 := by rw [← S.qh_of_supp χ hsu]; exact hTu.2.1
  obtain ⟨a, c, hac⟩ := hg u g1.symm g2.symm
  have hqg : S.q (S.P.src g) * ⌜g⌝ ≠ 0 := by
    intro h0; apply hqu; rw [hac, ← g1]
    simp only [← mul_assoc]; rw [← pow_succ', pow_succ, mul_assoc _ (S.q (S.P.src g)), h0]
    simp
  obtain ⟨hgL, -⟩ := S.prim_action_gen hg (by rw [g1, hsu.2]; exact hprim) hqg
  obtain ⟨m, hm⟩ := hgL u g1.symm g2.symm
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; rw [pow_zero, one_mul] at hm; rw [S.rr_inj hm]; exact hg
  · exfalso
    have hqb : S.qh χ (S.P.src g) = S.q (S.P.src g) := by rw [g1]; exact S.qh_of_supp χ hsu
    have hg0 : g ≠ S.P.e (S.P.src g) := by
      intro he; apply S.tl_nonlocal hTu
      rw [← g1, ← g2]; nth_rewrite 1 [he]; rw [S.P.tgt_e]
    have hTg : S.TL χ g := S.tl_factor hTu (by rw [hm, ← hqb, g1]) hg0
    have hqu' : S.q (S.P.src g) ^ (m + 1) * ⌜g⌝ ≠ 0 := by
      rw [pow_succ', mul_assoc, ← hm, g1]; exact hqu
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · have : m = 1 := by omega
      subst this
      have hsg : S.P.src g = S.P.src r0 := by rw [g1, u1]
      apply S.layer_gen_L k hfin hχ hprim hr0 hg hTr0 hTg hsg
      · rw [hu, hm, pow_one, ← hsg, hqb]
      · rw [← hsg, hqb, ← mul_assoc, ← pow_two]; exact hqu'
    · have h3 := S.len_L k hfin hχ hprim hg hTg (by
        rw [hqb]; intro h0; apply hqu'
        rw [show m + 1 = (m - 1) + 2 by omega, pow_add, mul_assoc, h0, mul_zero])
      rw [hqb] at h3
      apply hqu'
      rw [show m + 1 = (m - 2) + 3 by omega, pow_add, h3, mul_zero, zero_mul]

variable (χ) in
/-- **A nondeep external return at `b`** (`def:nondeep-return`). -/
def NondeepRet (b : V) (e l : R) : Prop :=
  S.IsGen e ∧ S.IsGen l ∧ S.P.src e = b ∧ S.P.tgt e = S.P.src l ∧ S.P.tgt l = b ∧
    ¬ S.InS b (S.P.tgt e) ∧ S.TL χ e ∧ S.TR χ l ∧ ⌜e⌝ * ⌜l⌝ = S.qh χ b ^ 2 ∧ S.qh χ b ^ 3 ≠ 0

/-- A generating two-sided ray with a nonzero reverse product reaches the return corner. -/
theorem inS_of_rev (hfin : IsRepresentationFinite k (S.P.Lin k)) (hprim : Prim χ) {f w : R}
    (hf : S.IsGen f) (hB : S.TB χ f) (hc : S.P.tgt f ≠ S.P.src f) (w1 : S.P.src w = S.P.tgt f)
    (w2 : S.P.tgt w = S.P.src f) (hw : ⌜f⌝ * ⌜w⌝ ≠ 0) : S.InS (S.P.src f) (S.P.tgt f) := by
  obtain ⟨hsh, h1, h2⟩ := hB
  have hsb := S.supp_of_qh h1
  have hsc := S.supp_of_qh' h2
  obtain ⟨-, e1⟩ := S.shift_of_qh_mul hsh.1 h1
  obtain ⟨-, e2⟩ := S.shift_of_mul_qh hsh.1 h2
  rw [S.qh_of_supp χ hsb] at h1 e1
  rw [S.qh_of_supp χ hsc] at h2 e2
  have hqf : S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f) := e1.trans e2.symm
  obtain ⟨hL, -⟩ := S.prim_action_gen hf (by rw [hsb.2]; exact hprim) h1
  obtain ⟨hR, -⟩ := S.prim_action_gen_op hf (by rw [hsc.2]; exact hprim) h2
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen w
  have hrev := S.prim_reverse k hfin hf (fun e ↦ hc e.symm) hL hR hqf h1
    (by rw [hsb.2]; exact hprim) w1 w2 hw hg (by rw [g1, w1]) (by rw [g2, w2])
  exact Or.inr ⟨hc, f, g, hf, rfl, rfl, hrev, hqf, h1⟩

/-- **Proposition 8.25(4)** (`prop:proper-ray-products`, Appendix C.2 "absence of external
two-sided action"): at the base of a nondeep external return there is no generating two-sided
ray to a vertex outside the return corner. -/
theorem no_ext_two_sided (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {b : V} {e l f : R} (hN : S.NondeepRet χ b e l) (hf : S.IsGen f)
    (hB : S.TB χ f) (f1 : S.P.src f = b) (hcS : ¬ S.InS b (S.P.tgt f)) : False := by
  obtain ⟨he, hl, e1, e2, l2, hyS, hTe, hTl, hel, hq3⟩ := hN
  have hsb := S.supp_of_qh hTe.2.1
  rw [e1] at hsb
  have hqb : S.qh χ b = S.q b := S.qh_of_supp χ hsb
  rw [hqb] at hel hq3
  have hq2 : S.q b ^ 2 ≠ 0 := fun h0 ↦ hq3 (by rw [pow_succ, h0, zero_mul])
  have hprim' : Prim (S.χ b) := by rw [hsb.2]; exact hprim
  have hcb : S.P.tgt f ≠ b := fun h ↦ hcS (Or.inl h)
  have hyb : S.P.tgt e ≠ b := fun h ↦ hyS (Or.inl h)
  have hqe : S.q b * ⌜e⌝ ≠ 0 := by rw [← hqb, ← e1]; exact hTe.2.1
  have hqf : S.q b * ⌜f⌝ ≠ 0 := by rw [← hqb, ← f1]; exact hB.2.1
  -- no factorization `f v = e`, and no reverse product `f v = q_b²`
  have nrev : ∀ v : R, S.P.src v = S.P.tgt f → S.P.tgt v = b → ⌜f⌝ * ⌜v⌝ ≠ 0 → False := by
    intro v v1 v2 hv
    have hcb' : S.P.tgt f ≠ S.P.src f := by rw [f1]; exact hcb
    have v2' : S.P.tgt v = S.P.src f := by rw [v2, f1]
    have := S.inS_of_rev k hfin hprim hf hB hcb' v1 v2' hv
    rw [f1] at this
    exact hcS this
  have nfe : ¬ S.P.RF f e := by
    rw [S.rf_iff]; rintro ⟨a, ha⟩
    have hal : ⌜a⌝ * ⌜l⌝ ≠ 0 := fun h0 ↦ hq2 (by rw [← hel, ← ha, mul_assoc, h0, mul_zero])
    obtain ⟨al, hal'⟩ := S.ray_of_mul_ne hal
    obtain ⟨a1, -, -, -⟩ := S.prod_of ha
    obtain ⟨-, a2, a3, -⟩ := S.prod_of hal'
    apply nrev al (by rw [S.prod_of hal' |>.1, ← (S.prod_of ha).2.2.1]) (by rw [a2, l2])
    rw [← hal', ← mul_assoc, ha, hel]; exact hq2
  obtain ⟨h, hh⟩ := (S.rf_iff _ _).1 ((S.ext_chain k hfin hprim' hq2 he hf e1 f1 hqe hqf
    hyS hcS).resolve_right nfe)
  have hB' := hB
  obtain ⟨-, -, hfq⟩ := hB'
  have hsc := S.supp_of_qh' hfq
  obtain ⟨-, s1⟩ := S.shift_of_qh_mul hB.1.1 hB.2.1
  obtain ⟨-, s2⟩ := S.shift_of_mul_qh hB.1.1 hfq
  rw [f1, hqb] at s1
  rw [S.qh_of_supp χ hsc] at s2 hfq
  have hcomm : S.q b * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f) := s1.trans s2.symm
  obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases b).resolve_left hsb.1
  replace hq0 : S.q b = ⌜q0⌝ := hq0
  have hq3' : S.q b ^ 3 * ⌜S.P.e b⌝ ≠ 0 := by rw [S.qpow_mul_e (n := 3) (by norm_num)]; exact hq3
  obtain ⟨q3, h3⟩ := S.mul_right_ray hq3'
  rw [S.qpow_mul_e (n := 3) (by norm_num)] at h3
  obtain ⟨qe, hqe'⟩ := S.mul_right_ray hqe
  obtain ⟨qf, hqf'⟩ := S.mul_right_ray hqf
  have hlq : ⌜l⌝ * S.q b ≠ 0 := by
    intro h0; apply hq3; rw [pow_succ, ← hel, mul_assoc, h0, mul_zero]
  obtain ⟨lq, hlq'⟩ := S.mul_left_ray hlq
  have hhq : ⌜h⌝ * S.q (S.P.tgt f) ≠ 0 := by
    intro h0; apply hfq; rw [← hh, mul_assoc, h0, mul_zero]
  obtain ⟨hq, hhq'⟩ := S.mul_left_ray hhq
  have dq := S.P.deg_pos q0 (by rw [q01]; exact q03)
  have de := S.deg_pos_of_ne (f := e) (by rw [e1]; exact fun h ↦ hyb h.symm)
  have hd := fun r : R ↦ S.P.deg_nonneg r
  obtain ⟨c1, -, -, c4⟩ := S.prod_of (show ⌜q0⌝ * ⌜e⌝ = ⌜qe⌝ by rw [← hq0]; exact hqe')
  obtain ⟨d1, -, -, d4⟩ := S.prod_of (show ⌜q0⌝ * ⌜f⌝ = ⌜qf⌝ by rw [← hq0]; exact hqf')
  have w3 : S.P.wt q3 = 3 • S.χ b := S.wt_of_eq_qpow h3.symm
  apply S.P.crown_false k hfin b e qe q3 qf ⟨e1, by rw [c1, q01], (S.tgt_of_qpow_e
    (by rw [S.qpow_mul_e (n := 3) (by norm_num)]; exact h3.symm)).1, by rw [d1, q01]⟩
  · exact (S.rf_iff _ _).2 ⟨lq, by rw [← hlq', ← mul_assoc, hel, ← pow_succ, h3]⟩
  · exact (S.rf_iff _ _).2 ⟨hq, by rw [← hhq', ← mul_assoc, hh, ← hcomm, hqf']⟩
  · exact (S.rf_iff _ _).2 ⟨l, by rw [← hqe', mul_assoc, hel, ← pow_succ', h3]⟩
  · exact (S.rf_iff _ _).2 ⟨h, by rw [← hqe', mul_assoc, hh, hqf']⟩
  · rw [S.rf_iff]; rintro ⟨v, hv⟩
    exact S.no_hidden_target hχ hprim hTe (by rw [hv, ← hqe', e1, hqb])
  · apply S.not_rf_deg; rw [c4, map_add]; linarith
  · exact S.not_rf_qpow_gen hf f1 (by rw [S.qpow_mul_e (n := 3) (by norm_num)]; exact h3.symm)
      (show ⌜qf⌝ = S.q b ^ 1 * ⌜f⌝ by rw [pow_one, hqf']) (by omega)
  · rw [S.rf_iff]; rintro ⟨v, hv⟩
    rw [← hqf', mul_assoc, ← h3, show 3 = 1 + 2 by rfl, pow_add, pow_one] at hv
    have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h0 ↦ hq3 (by
      rw [show 3 = 1 + 2 by rfl, pow_add, pow_one, ← hv, h0, mul_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hfv
    obtain ⟨-, t2, t3, -⟩ := S.prod_of ht
    have hv0 : S.P.src v = S.P.tgt f := t3.symm
    have : S.P.tgt v = b := by
      have hq2' : S.q b ^ 2 * ⌜S.P.e b⌝ ≠ 0 := by rw [S.qpow_mul_e (n := 2) (by norm_num)]; exact hq2
      obtain ⟨s2', hs2'⟩ := S.mul_right_ray hq2'
      rw [S.qpow_mul_e (n := 2) (by norm_num)] at hs2'
      rw [ht, hs2', hq0] at hv
      have := S.cancel_left hv (by rw [hv, ← hs2', ← hq0, ← pow_succ']; exact hq3)
      subst this
      rw [← t2, (S.tgt_of_qpow_e (by rw [S.qpow_mul_e (n := 2) (by norm_num)]; exact hs2'.symm)).2]
    exact nrev v hv0 this hfv
  · exact S.not_rf_qpow_gen he e1 (by rw [S.qpow_mul_e (n := 3) (by norm_num)]; exact h3.symm)
      (show ⌜e⌝ = S.q b ^ 0 * ⌜e⌝ by rw [pow_zero, one_mul]) (by omega)
  · exact S.not_rf_qpow_gen he e1 (by rw [S.qpow_mul_e (n := 3) (by norm_num)]; exact h3.symm)
      (show ⌜qe⌝ = S.q b ^ 1 * ⌜e⌝ by rw [pow_one, hqe']) (by omega)
  · rw [S.rf_iff]; rintro ⟨v, hv⟩
    rw [← hqf', mul_assoc] at hv
    have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h0 ↦ S.rr_ne e (by rw [← hv, h0, mul_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hfv
    rw [ht] at hv
    obtain ⟨t1, t2⟩ := S.qpow_mul_endpoints (n := 1) (by rw [pow_one]; exact hv)
    exact S.gen_ne_q_mul he (b := t) t1.symm t2.symm 1 le_rfl (by rw [e1, pow_one, hv])
  · rw [S.rf_iff]; rintro ⟨v, hv⟩
    rw [← hqf', ← hqe', mul_assoc] at hv
    have hfv : ⌜f⌝ * ⌜v⌝ ≠ 0 := fun h0 ↦ hqe (by rw [← hv, h0, mul_zero])
    obtain ⟨t, ht⟩ := S.ray_of_mul_ne hfv
    rw [ht, hq0] at hv
    have := S.cancel_left hv (by rw [hv, ← hq0]; exact hqe)
    subst this
    exact nfe ((S.rf_iff _ _).2 ⟨v, ht⟩)

/-- **Proposition 8.25(2)** (with `N_x = 3`: `q̂_x² ≠ 0`, `q̂_x³ = 0`): a product of generating rays of types `B, L` with proper
shiftable output `q̂_x^k f` has `k = 1` and `N_x = 3`, and its first factor has a primitive
reverse. -/
theorem BL_proper (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r s t f : R} {n : ℕ} (hr : S.IsGen r) (hs : S.IsGen s) (hBr : S.TB χ r)
    (hLs : S.TL χ s) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hf : S.IsGen f)
    (ht : ⌜t⌝ = S.qh χ (S.P.src r) ^ n * ⌜f⌝) (hn : 1 ≤ n) (hsh : S.Shift χ t) :
    n = 1 ∧ S.qh χ (S.P.src r) ^ 2 ≠ 0 ∧ S.qh χ (S.P.src r) ^ 3 = 0 ∧ ∃ h, S.PrimRev r h := by
  obtain ⟨t1, t2, t3, -⟩ := S.prod_of hrs
  have hr0 : r ≠ S.P.e (S.P.src r) := hBr.1.1
  have hs0 : s ≠ S.P.e (S.P.src s) := hLs.1.1
  -- the output is left-sided
  have hTt : S.TL χ t := by
    rcases S.types_of_shift hχ hprim hsh with h | h | h
    · exact h
    · rcases S.table_R hχ hprim hr0 hs0 hrs h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1.2.2 (by rw [hLs.2.2]; exact fun h ↦ h rfl)
      · exact absurd h1.2.2 (by rw [hLs.2.2]; exact fun h ↦ h rfl)
    · rcases (S.table_B hχ hprim hr0 hs0 hrs h).1 with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact absurd h1.2.2 (by rw [hLs.2.2]; exact fun h ↦ h rfl)
      · exact absurd hBr.2.2 (by rw [h1.2.2]; exact fun h ↦ h rfl)
  have hsx := S.supp_of_qh hBr.2.1
  have hqx : S.qh χ (S.P.src r) = S.q (S.P.src r) := S.qh_of_supp χ hsx
  obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints (by rw [← hqx]; exact ht.symm)
  have hf0 : f ≠ S.P.e (S.P.src f) := by
    intro he; apply S.tl_nonlocal hTt; rw [e1, e2]; nth_rewrite 1 [he]; rw [S.P.tgt_e]
  have hTf : S.TL χ f := S.tl_factor hTt (by rw [ht, t1]) hf0
  have hqt : S.qh χ (S.P.src r) ^ (n + 1) * ⌜f⌝ ≠ 0 := by
    rw [pow_succ', mul_assoc, ← ht, ← t1]; exact hTt.2.1
  have hsf : S.P.src f = S.P.src r := by rw [← e1, t1]
  -- the length bound
  have hq3 : S.qh χ (S.P.src r) ^ 3 = 0 := by
    have := S.len_L k hfin hχ hprim hf hTf (by
      rw [hsf]; intro h0; apply hqt
      rw [show n + 1 = (n - 1) + 2 by omega, pow_add, mul_assoc, h0, mul_zero])
    rwa [hsf] at this
  have hn1 : n = 1 := by
    by_contra h
    apply hqt
    rw [show n + 1 = (n - 2) + 3 by omega, pow_add, hq3, mul_zero, zero_mul]
  subst hn1
  have hq2 : S.qh χ (S.P.src r) ^ 2 ≠ 0 := fun h0 ↦ hqt (by
    rw [show (1 : ℕ) + 1 = 2 from rfl, h0, zero_mul])
  refine ⟨rfl, hq2, hq3, ?_⟩
  -- the middle vertex lies in `S_x`
  set x := S.P.src r with hx
  set y := S.P.tgt r with hy
  have hyx : y ≠ x := by
    intro h
    apply hr0
    exact S.gen_loop_e hr h.symm
  have hq2 : S.q x ^ 2 ≠ 0 := by
    rw [← hqx]; intro h0; apply hqt; rw [h0, zero_mul]
  have hqr : S.q x * ⌜r⌝ ≠ 0 := by rw [← hqx]; exact hBr.2.1
  have hqf : S.q x * ⌜f⌝ ≠ 0 := by
    rw [← hqx]; intro h0; apply hqt; rw [pow_succ, pow_one, mul_assoc, h0, mul_zero]
  obtain ⟨-, hfS⟩ := S.notInS_of_TL hf hTf
  rw [hsf] at hfS
  by_cases hyS : S.InS x y
  · rcases hyS with h | ⟨-, g, h, hg, g1, g2, hrev, -, -⟩
    · exact absurd h hyx
    · have := S.gen_unique hg hr (by rw [g1]) (by rw [g2])
      subst this
      exact ⟨h, hrev⟩
  · exfalso
    have hprim' : Prim (S.χ x) := by rw [hsx.2]; exact hprim
    rcases S.ext_chain k hfin hprim' hq2 hr hf rfl hsf hqr hqf hyS hfS with hc | hc
    · -- `r a = f` gives `s = q_y a`
      obtain ⟨a, ha⟩ := (S.rf_iff _ _).1 hc
      obtain ⟨-, hs1⟩ := S.shift_of_qh_mul hr0 hBr.2.1
      obtain ⟨-, hs2⟩ := S.shift_of_mul_qh hr0 hBr.2.2
      have hcomm : S.q x * ⌜r⌝ = ⌜r⌝ * S.qh χ y := by rw [← hqx, hs1, hs2]
      have e : ⌜r⌝ * ⌜s⌝ = ⌜r⌝ * (S.qh χ y * ⌜a⌝) := by
        rw [hrs, ht, pow_one, hqx, ← ha, ← mul_assoc, hcomm, mul_assoc]
      have hqa : S.qh χ y * ⌜a⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← hrs, e, h0, mul_zero])
      obtain ⟨a', ha'⟩ := S.mul_right_ray hqa
      rw [ha'] at e
      have := S.cancel_left e (by rw [hrs]; exact S.rr_ne t)
      subst this
      have hsy := S.supp_of_qh hqa
      rw [S.qh_of_supp χ hsy] at ha'
      obtain ⟨a1, a2⟩ := S.qpow_mul_endpoints (n := 1) (by rw [pow_one]; exact ha')
      exact S.gen_ne_q_mul hs (b := a) a1.symm a2.symm 1 le_rfl
        (by rw [pow_one, ← t3]; exact ha'.symm)
    · -- `f a = r` gives a hidden target action on `f`
      obtain ⟨a, ha⟩ := (S.rf_iff _ _).1 hc
      have has : ⌜a⌝ * ⌜s⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← hrs, ← ha, mul_assoc, h0, mul_zero])
      obtain ⟨w, hw⟩ := S.ray_of_mul_ne has
      exact S.no_hidden_target hχ hprim hTf (by
        rw [← hw, ← mul_assoc, ha, hrs, ht, pow_one, hsf])

/-- **Proposition 8.25(1), endpoint layer preservation, right-sided form.** -/
theorem layer_R (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r s t s0 : R} {i : ℕ} (hTs : S.TR χ s) (hTt : S.TR χ t)
    (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hs0 : S.IsGen s0) (hsi : ⌜s⌝ = ⌜s0⌝ * S.qh χ (S.P.tgt s) ^ i) :
    ∃ t0, S.IsGen t0 ∧ ⌜r⌝ * ⌜s0⌝ = ⌜t0⌝ ∧ ⌜t⌝ = ⌜t0⌝ * S.qh χ (S.P.tgt s) ^ i := by
  obtain ⟨t0, h1, h2, h3⟩ := S.op.layer_L k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    (r := s) (s := r) (t := t) (r0 := s0) (i := i) ((S.op_TL s).2 hTs) ((S.op_TL t).2 hTt)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hrs]) ((S.op_isGen_iff s0).2 hs0)
    (by change S.P.toOp ⌜s⌝ = S.op.qh χ (S.P.tgt s) ^ i * S.P.toOp ⌜s0⌝
        rw [S.op_qh, ← Tab.toOp_pow, ← Tab.toOp_mul, hsi])
  refine ⟨t0, (S.op_isGen_iff t0).1 h1, S.P.toOp_injective ?_, S.P.toOp_injective ?_⟩
  · rw [Tab.toOp_mul]; exact h2
  · change S.P.toOp ⌜t⌝ = S.P.toOp (⌜t0⌝ * S.qh χ (S.P.tgt s) ^ i)
    rw [Tab.toOp_mul, Tab.toOp_pow, ← S.op_qh]; exact h3

omit [IsAlgClosed k] in
/-- A right-sided generating ray leaves the return corner of its target (when `N ≥ 3`). -/
theorem notInS_of_TR {f : R} (hf : S.IsGen f) (hT : S.TR χ f) (hprim : Prim χ)
    (hq2 : S.q (S.P.tgt f) ^ 2 ≠ 0) :
    S.P.src f ≠ S.P.tgt f ∧ ¬ S.InS (S.P.tgt f) (S.P.src f) := by
  have hsz := S.supp_of_qh' hT.2.2
  obtain ⟨h1, h2⟩ := S.op.notInS_of_TL ((S.op_isGen_iff f).2 hf) ((S.op_TL f).2 hT)
  refine ⟨h1, fun h ↦ h2 ?_⟩
  exact (S.op_inS_iff hq2 (by rw [hsz.2]; exact hprim)).2 h

omit [IsAlgClosed k] in
theorem op_nondeep {b : V} {e l : R} (hN : S.NondeepRet χ b e l) (hprim : Prim χ) :
    S.op.NondeepRet χ b l e := by
  obtain ⟨he, hl, e1, e2, l2, hS, hTe, hTl, hel, hq3⟩ := hN
  have hsb := S.supp_of_qh hTe.2.1
  rw [e1] at hsb
  have hq2 : S.q b ^ 2 ≠ 0 := by
    rw [← S.qh_of_supp χ hsb]; intro h0; apply hq3; rw [pow_succ, h0, zero_mul]
  refine ⟨(S.op_isGen_iff l).2 hl, (S.op_isGen_iff e).2 he, l2, e2.symm, e1, ?_,
    (S.op_TL l).2 hTl, (S.op_TR e).2 hTe, ?_, ?_⟩
  · change ¬ S.op.InS b (S.P.src l)
    rw [S.op_inS_iff hq2 (by rw [hsb.2]; exact hprim), ← e2]; exact hS
  · rw [op_rr, op_rr, ← Tab.toOp_mul, hel, S.op_qh, Tab.toOp_pow]
  · rw [S.op_qh, ← Tab.toOp_pow]; exact hq3

/-- **Proposition 8.25(4), incoming form.** -/
theorem no_ext_two_sided_in (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {b : V} {e l f : R} (hN : S.NondeepRet χ b e l) (hf : S.IsGen f)
    (hB : S.TB χ f) (f2 : S.P.tgt f = b) (hcS : ¬ S.InS b (S.P.src f)) : False := by
  have hN' := hN
  obtain ⟨-, -, e1, -, -, -, hTe, -, -, hq3⟩ := hN'
  have hsb := S.supp_of_qh hTe.2.1
  rw [e1] at hsb
  have hq2 : S.q b ^ 2 ≠ 0 := by
    rw [← S.qh_of_supp χ hsb]; intro h0; apply hq3; rw [pow_succ, h0, zero_mul]
  exact S.op.no_ext_two_sided k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    (S.op_nondeep hN hprim) ((S.op_isGen_iff f).2 hf) ((S.op_TB f).2 hB) f2
    (by rw [S.op_inS_iff hq2 (by rw [hsb.2]; exact hprim)]; exact hcS)

/-- **Proposition 8.25(3)** (`prop:proper-ray-products`): a product of generating rays of
types `L, R` with proper shiftable output has endpoint layer two; it is a nondeep external
return if `x = z`, and otherwise factors through a nondeep return at one endpoint.

Deviation (Appendix C.2, Steps 1–4): with the retraction criterion of Lemma 8.9 the
complementary-path tree needs only the cover factorizations, which hold for `j = 1`
without further hypotheses; so `j = 1` is excluded directly and the quotient `A'` of
Step 4 (with the induction hypothesis) is not used. -/
theorem LR_proper (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r s t : R} (hr : S.IsGen r) (hs : S.IsGen s) (hTr : S.TL χ r)
    (hTs : S.TR χ s) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hsh : S.Shift χ t) (hprop : ¬ S.IsGen t) :
    (S.P.tgt s = S.P.src r ∧ S.NondeepRet χ (S.P.src r) r s) ∨
    (S.P.tgt s ≠ S.P.src r ∧ ∃ f, S.IsGen f ∧ ⌜t⌝ = S.qh χ (S.P.src r) ^ 2 * ⌜f⌝ ∧
      ⌜t⌝ = ⌜f⌝ * S.qh χ (S.P.tgt s) ^ 2 ∧
      ((∃ a, ⌜r⌝ = ⌜f⌝ * ⌜a⌝ ∧ S.NondeepRet χ (S.P.tgt s) a s) ∨
       (∃ b, ⌜s⌝ = ⌜b⌝ * ⌜f⌝ ∧ S.NondeepRet χ (S.P.src r) r b))) := by
  obtain ⟨t1, t2, t3, t4⟩ := S.prod_of hrs
  have hr0 : r ≠ S.P.e (S.P.src r) := hTr.1.1
  have hs0 : s ≠ S.P.e (S.P.src s) := hTs.1.1
  -- the output is two-sided
  have hBt : S.TB χ t := by
    rcases S.types_of_shift hχ hprim hsh with hL | hR | hB
    · exfalso
      obtain ⟨t0, h1, h2, h3⟩ := S.layer_L k hfin hχ hprim (i := 0) hTr hL hrs hr
        (by rw [pow_zero, one_mul])
      rw [pow_zero, one_mul] at h3
      exact hprop (by rw [S.rr_inj h3]; exact h1)
    · exfalso
      obtain ⟨t0, h1, h2, h3⟩ := S.layer_R k hfin hχ hprim (i := 0) hTs hR hrs hs
        (by rw [pow_zero, mul_one])
      rw [pow_zero, mul_one] at h3
      exact hprop (by rw [S.rr_inj h3]; exact h1)
    · exact hB
  set x := S.P.src r with hx
  set y := S.P.tgt r with hy
  set z := S.P.tgt s with hz
  have hsx := S.supp_of_qh hTr.2.1
  have hsz := S.supp_of_qh' hTs.2.2
  have hqx : S.qh χ x = S.q x := S.qh_of_supp χ hsx
  have hqz : S.qh χ z = S.q z := S.qh_of_supp χ hsz
  have hprimx : Prim (S.χ x) := by rw [hsx.2]; exact hprim
  have hprimz : Prim (S.χ z) := by rw [hsz.2]; exact hprim
  have hqt : S.q x * ⌜t⌝ ≠ 0 := by rw [← hqx, ← t1]; exact hBt.2.1
  have htq : ⌜t⌝ * S.q z ≠ 0 := by rw [← hqz, ← t2]; exact hBt.2.2
  -- the generating ray of the output Hom is two-sided
  obtain ⟨f, f1, f2, hf⟩ := S.exists_gen t
  rw [t1] at f1; rw [t2] at f2
  obtain ⟨a0, b0, hab⟩ := hf t (by rw [f1, t1]) (by rw [f2, t2])
  rw [f1, f2] at hab
  have hqf : S.q x * ⌜f⌝ ≠ 0 := by
    intro h0; apply hqt; rw [hab, ← mul_assoc, ← mul_assoc, ← pow_succ', pow_succ, mul_assoc _ _ ⌜f⌝,
      h0]; simp
  have hfq : ⌜f⌝ * S.q z ≠ 0 := by
    intro h0; apply htq
    rw [hab, mul_assoc _ (S.q z ^ b0), ← pow_succ, pow_succ', ← mul_assoc,
      mul_assoc (S.q x ^ a0) ⌜f⌝ (S.q z), h0]; simp
  obtain ⟨hfL, -⟩ := S.prim_action_gen hf (by rw [f1]; exact hprimx) (by rw [f1]; exact hqf)
  obtain ⟨hfR, hfLR⟩ := S.prim_action_gen_op hf (by rw [f2]; exact hprimz) (by rw [f2]; exact hfq)
  obtain ⟨-, hcomm'⟩ := hfLR hfL
  have hcomm : S.q (S.P.src f) * ⌜f⌝ = ⌜f⌝ * S.q (S.P.tgt f) := hcomm'.symm
  obtain ⟨j, hj⟩ := hfL t (by rw [f1, t1]) (by rw [f2, t2])
  rw [f1] at hj hcomm
  rw [f2] at hcomm
  have hj1 : 1 ≤ j := by
    by_contra h0
    have : j = 0 := by omega
    subst this
    rw [pow_zero, one_mul] at hj
    exact hprop (by rw [S.rr_inj hj]; exact hf)
  have hj' : ⌜t⌝ = ⌜f⌝ * S.q z ^ j := by
    rw [hj]; have := S.comm_pow (f := f) (by rw [f1, f2]; exact hcomm) j; rwa [f1, f2] at this
  have hqj1 : S.q x ^ (j + 1) * ⌜f⌝ ≠ 0 := by rw [pow_succ', mul_assoc, ← hj]; exact hqt
  have hfqj1 : ⌜f⌝ * S.q z ^ (j + 1) ≠ 0 := by rw [pow_succ, ← mul_assoc, ← hj']; exact htq
  have hyx : y ≠ x := S.tl_nonlocal hTr
  have hyS : ¬ S.InS x y := (S.notInS_of_TL hr hTr).2
  by_cases hzx : z = x
  · -- a local return
    left
    have hfe : f = S.P.e (S.P.src f) := S.gen_loop_e hf (by rw [f1, f2, hzx])
    rw [f1] at hfe
    have hrsj : ⌜r⌝ * ⌜s⌝ = S.q x ^ j := by rw [hrs, hj, hfe, S.qpow_mul_e hj1]
    have hqj : S.q x ^ (j + 1) ≠ 0 := by
      intro h0; apply hqj1; rw [h0, zero_mul]
    obtain ⟨h2, h3, -, -⟩ := S.nondeep_return k hfin hr hs rfl rfl t3.symm hzx hyx hrsj hj1 hqj
      hyS hprimx
    subst h2
    refine ⟨hzx, hr, hs, rfl, t3, hzx, hyS, hTr, hTs, by rw [hqx]; exact hrsj, by rw [hqx]; exact h3⟩
  right
  refine ⟨hzx, ?_⟩
  have hyz : y ≠ z := fun h ↦ hs0 (S.gen_loop_e hs (t3.symm.trans h))
  have hqx2 : S.q x ^ 2 ≠ 0 := by
    intro h0; apply hqj1; rw [show j + 1 = (j - 1) + 2 by omega, pow_add, h0, mul_zero, zero_mul]
  have hqz2 : S.q z ^ 2 ≠ 0 := by
    intro h0; apply hfqj1; rw [show j + 1 = (j - 1) + 2 by omega, pow_add, h0, mul_zero, mul_zero]
  have hyzS : ¬ S.InS z y := by
    have := (S.notInS_of_TR hs hTs hprim hqz2).2
    rwa [← t3] at this
  have hxz : x ≠ z := fun h ↦ hzx h.symm
  have hqr : S.q x * ⌜r⌝ ≠ 0 := by rw [← hqx]; exact hTr.2.1
  have hsq : ⌜s⌝ * S.q z ≠ 0 := by rw [← hqz]; exact hTs.2.2
  have hfB : S.TB χ f := by
    have hf0 : f ≠ S.P.e (S.P.src f) := fun he ↦ hxz (by
      rw [← f1, ← f2]; nth_rewrite 2 [he]; rw [S.P.tgt_e])
    have h1 : S.qh χ (S.P.src f) * ⌜f⌝ ≠ 0 := by rw [f1, hqx]; exact hqf
    exact ⟨(S.shift_of_qh_mul hf0 h1).1, h1, by rw [f2, hqz]; exact hfq⟩
  -- `z` lies in the return corner of `x`
  have hzS : S.InS x z := by
    by_contra hzS
    rcases S.ext_chain k hfin hprimx hqx2 hr hf rfl f1 hqr hqf hyS (by rw [f2]; exact hzS)
      with hc | hc
    · obtain ⟨a, ha⟩ := (S.rf_iff _ _).1 hc
      obtain ⟨-, a2, a3, -⟩ := S.prod_of ha
      have haq : ⌜a⌝ * S.q z ^ j ≠ 0 := by
        intro h0; apply S.rr_ne t; rw [hj', ← ha, mul_assoc, h0, mul_zero]
      obtain ⟨a', ha'⟩ := S.mul_left_ray haq
      have e : ⌜r⌝ * ⌜s⌝ = ⌜r⌝ * ⌜a'⌝ := by rw [hrs, hj', ← ha, mul_assoc, ha']
      have := S.cancel_left e (by rw [hrs]; exact S.rr_ne t)
      subst this
      exact S.gen_ne_mul_q hs (b := a) (by rw [← a3, ← t3]) (by rw [← a2, f2]) j hj1 ha'.symm
    · obtain ⟨a, ha⟩ := (S.rf_iff _ _).1 hc
      obtain ⟨-, a2, a3, -⟩ := S.prod_of ha
      have hasr : ⌜f⌝ * (⌜a⌝ * ⌜s⌝) = ⌜f⌝ * (S.q z ^ j * ⌜S.P.e z⌝) := by
        rw [← mul_assoc, ha, hrs, hj', S.qpow_mul_e hj1]
      have has0 : ⌜a⌝ * ⌜s⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← hrs, ← ha, mul_assoc, h0, mul_zero])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne has0
      have hz0 : S.q z ^ j * ⌜S.P.e z⌝ ≠ 0 := by
        rw [S.qpow_mul_e hj1]; intro h0; apply htq; rw [hj', h0]; simp
      obtain ⟨d, hd⟩ := S.mul_right_ray hz0
      rw [hc, hd] at hasr
      have := S.cancel_left hasr (by rw [hasr, ← hd, S.qpow_mul_e hj1, ← hj']; exact S.rr_ne t)
      subst this
      have has : ⌜a⌝ * ⌜s⌝ = S.q z ^ j := by rw [hc, ← hd, S.qpow_mul_e hj1]
      have hagen : S.IsGen a := S.gen_factor k hfin hr (Or.inl hqr) (a := f) (m := a)
        (b := S.P.e y) (by rw [ha, S.rr_mul_e])
      have a1 : S.P.src a = z := by rw [← a3, f2]
      have a2' : S.P.tgt a = y := a2.symm
      have hqzj : S.q z ^ (j + 1) ≠ 0 := fun h0 ↦ hfqj1 (by rw [h0, mul_zero])
      obtain ⟨hj2, hq3, -, -, -, haR, -, -⟩ := S.nondeep_return k hfin hagen hs a1 a2' t3.symm rfl
        hyz has hj1 hqzj hyzS hprimz
      subst hj2
      have hTa : S.TL χ a := by
        have hqa : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
          rw [a1, hqz]; intro h0; apply hqzj
          rw [pow_succ', ← has, ← mul_assoc, h0, zero_mul]
        have ha0 : a ≠ S.P.e (S.P.src a) := fun he ↦ hyz (by
          rw [← a2', ← a1]; nth_rewrite 1 [he]; rw [S.P.tgt_e])
        refine ⟨(S.shift_of_qh_mul ha0 hqa).1, hqa, ?_⟩
        by_contra hne
        have hsy := S.supp_of_qh' hne
        rw [S.qh_of_supp χ hsy] at hne
        exact haR (S.prim_action_gen_op hagen (by rw [hsy.2]; exact hprim) hne).1
      have hN : S.NondeepRet χ z a s := ⟨hagen, hs, a1, by rw [a2', t3], rfl,
        by rw [a2']; exact hyzS, hTa, hTs, by rw [hqz]; exact has, by rw [hqz]; exact hq3⟩
      refine S.no_ext_two_sided_in k hfin hχ hprim hN hf hfB f2 ?_
      rw [f1]
      rintro (h | ⟨-, u, w, hu, u1, u2, ⟨huw, hwu⟩, -, -⟩)
      · exact hxz h
      · rw [u1] at huw; rw [u2] at hwu
        have hw : ⌜u⌝ * ⌜w⌝ ≠ 0 := by rw [huw]; exact fun h0 ↦ hqz2 (by rw [pow_two, h0, zero_mul])
        obtain ⟨v, hv⟩ := S.ray_of_mul_ne hw
        obtain ⟨-, v2, v3, -⟩ := S.prod_of hv
        have w1 : S.P.src w = x := by rw [← v3, u2]
        have w2 : S.P.tgt w = z := by
          rw [← v2]; exact (S.loop_of_eq_q (hv.symm.trans huw)).2
        exact hzS (Or.inr (S.partner_of_factor w1 w2 hzx hwu hqx2 hprimx).2.2.2.2)
  -- the generating complement `g : z → x`
  obtain ⟨-, f', h0, hf', f'1, f'2, ⟨hf'h0, -⟩, -, -⟩ := hzS.resolve_left hzx
  have := S.gen_unique hf hf' (by rw [f'1, f1]) (by rw [f'2, f2])
  subst this
  have hne : ⌜f⌝ * ⌜h0⌝ ≠ 0 := by
    rw [hf'h0, f1]; intro h0'; apply hqx2; rw [pow_two, h0', zero_mul]
  obtain ⟨hh01, hh02⟩ : S.P.src h0 = z ∧ S.P.tgt h0 = x := by
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne hne
    obtain ⟨-, c2, c3, -⟩ := S.prod_of hc
    refine ⟨by rw [← c3, f2], ?_⟩
    rw [← c2]; exact (S.loop_of_eq_q (hc.symm.trans (by rw [hf'h0, f1]))).2
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen h0
  rw [hh01] at g1; rw [hh02] at g2
  have hrev := S.prim_reverse k hfin hf (by rw [f1, f2]; exact hxz) hfL hfR
    (by rw [f1, f2]; exact hcomm) (by rw [f1]; exact hqf) (by rw [f1]; exact hprimx)
    (h0 := h0) (by rw [hh01, f2]) (by rw [hh02, f1]) hne hg (by rw [g1, f2]) (by rw [g2, f1])
  obtain ⟨hfg, hgf⟩ := hrev
  rw [f1] at hfg; rw [f2] at hgf
  obtain ⟨qx0, hqx0, qx01, qx02, qx03⟩ := (S.q_cases x).resolve_left hsx.1
  replace hqx0 : S.q x = ⌜qx0⌝ := hqx0
  obtain ⟨qz0, hqz0, qz01, qz02, qz03⟩ := (S.q_cases z).resolve_left hsz.1
  replace hqz0 : S.q z = ⌜qz0⌝ := hqz0
  have hqzj' : S.q z ^ (j + 1) ≠ 0 := fun h0 ↦ hfqj1 (by rw [h0, mul_zero])
  have hqxj' : S.q x ^ (j + 1) ≠ 0 := fun h0 ↦ hqj1 (by rw [h0, zero_mul])
  have hgf' : ⌜g⌝ * ⌜f⌝ = ⌜qz0⌝ := by rw [hgf, hqz0]
  have hfg' : ⌜f⌝ * ⌜g⌝ = ⌜qx0⌝ := by rw [hfg, hqx0]
  have hgq0 : ⌜g⌝ * ⌜qx0⌝ ≠ 0 := by
    intro h0; apply hqz2
    have : S.q z ^ 2 = ⌜g⌝ * ⌜qx0⌝ * ⌜f⌝ := by
      rw [← hfg', ← mul_assoc, hgf', mul_assoc, hgf', ← hqz0, pow_two]
    rw [this, h0, zero_mul]
  obtain ⟨gq, hgq⟩ := S.ray_of_mul_ne hgq0
  have hqg : ⌜qz0⌝ * ⌜g⌝ = ⌜gq⌝ := by rw [← hgf', mul_assoc, hfg', hgq]
  have hgr0 : ⌜g⌝ * ⌜r⌝ ≠ 0 := by
    intro h0; apply hqzj'
    have : S.q z ^ (j + 1) = ⌜g⌝ * ⌜r⌝ * ⌜s⌝ := by
      rw [mul_assoc, hrs, hj', ← mul_assoc, hgf', ← hqz0, ← pow_succ']
    rw [this, h0, zero_mul]
  obtain ⟨gr, hgr⟩ := S.ray_of_mul_ne hgr0
  have hsg0 : ⌜s⌝ * ⌜g⌝ ≠ 0 := by
    intro h0; apply hqxj'
    have : S.q x ^ (j + 1) = ⌜r⌝ * (⌜s⌝ * ⌜g⌝) := by
      rw [← mul_assoc, hrs, hj, mul_assoc, hfg', ← hqx0, ← pow_succ]
    rw [this, h0, mul_zero]
  obtain ⟨sg, hsg⟩ := S.ray_of_mul_ne hsg0
  have dg := S.deg_pos_of_ne (f := g) (by rw [g1, g2]; exact hzx)
  have df := S.deg_pos_of_ne (f := f) (by rw [f1, f2]; exact hxz)
  have dr := S.deg_pos_of_ne (f := r) (fun h ↦ hyx h.symm)
  have ds := S.deg_pos_of_ne (f := s) (by rw [← t3]; exact hyz)
  have hz0 : S.q z ^ j * ⌜S.P.e z⌝ ≠ 0 := by
    rw [S.qpow_mul_e hj1]; intro h0; apply hqzj'; rw [pow_succ, h0, zero_mul]
  obtain ⟨dz, hdz⟩ := S.mul_right_ray hz0
  have hx0 : S.q x ^ j * ⌜S.P.e x⌝ ≠ 0 := by
    rw [S.qpow_mul_e hj1]; intro h0; apply hqxj'; rw [pow_succ, h0, zero_mul]
  obtain ⟨dx, hdx⟩ := S.mul_right_ray hx0
  have hwt : S.P.wt r + S.P.wt s = j • χ + S.P.wt f := by
    rw [← t4, S.wt_of_eq_qpow_mul (f := f) (by rw [f1]; exact hj), f1, hsx.2]
  -- the external returns at the two endpoints
  let ExtX : Prop := ∃ b i, S.IsGen b ∧ S.P.src b = y ∧ S.P.tgt b = x ∧ 1 ≤ i ∧
    ⌜r⌝ * ⌜b⌝ = S.q x ^ i ∧ S.q x ^ (i + 1) ≠ 0
  let ExtZ : Prop := ∃ a i, S.IsGen a ∧ S.P.src a = z ∧ S.P.tgt a = y ∧ 1 ≤ i ∧
    ⌜a⌝ * ⌜s⌝ = S.q z ^ i ∧ S.q z ^ (i + 1) ≠ 0
  -- the complementary-path tree
  have tree : (¬ ExtX ∧ ¬ ExtZ) ∨ j = 1 → False := by
    intro hW
    refine S.P.c6_false (x := x) (y := y) (z := z) g1 g2 f1 f2 rfl rfl t3.symm rfl
      (S.P.rr_mul_rr_eq_rr.1 hgf') (S.P.rr_mul_rr_eq_rr.1 hfg') (S.P.rr_mul_rr_eq_rr.1 hgq)
      (S.P.rr_mul_rr_eq_rr.1 hqg) (S.P.rr_mul_rr_eq_rr.1 hgr) (S.P.rr_mul_rr_eq_rr.1 hsg)
      dg df dr ds ?_ ?_ ?_ ?_ ?_ ?_ k hfin
    · intro h h1 h2 hm
      have hm' : ⌜f⌝ * ⌜h⌝ = ⌜r⌝ := S.P.rr_mul_rr_eq_rr.2 hm
      have e : ⌜f⌝ * (⌜h⌝ * ⌜s⌝) = ⌜f⌝ * ⌜dz⌝ := by
        rw [← mul_assoc, hm', hrs, hj', ← hdz, S.qpow_mul_e hj1]
      have hhs : ⌜h⌝ * ⌜s⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by
        rw [← hrs, ← hm', mul_assoc, h0, mul_zero])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hhs
      rw [hc] at e
      have := S.cancel_left e (by rw [e, ← hdz, S.qpow_mul_e hj1, ← hj']; exact S.rr_ne t)
      subst this
      have hs' : ⌜h⌝ * ⌜s⌝ = S.q z ^ j := by rw [hc, ← hdz, S.qpow_mul_e hj1]
      have hgen := S.gen_factor k hfin hr (Or.inl hqr) (a := f) (m := h) (b := S.P.e y)
        (by rw [hm', S.rr_mul_e])
      rcases hW with ⟨-, hZ⟩ | hj1'
      · exact hZ ⟨h, j, hgen, h1, h2, hj1, hs', hqzj'⟩
      · subst hj1'
        exact hyzS (Or.inr (S.partner_of_factor h1 h2 hyz (by rw [hs', pow_one]) hqz2
          hprimz).2.2.2.2)
    · intro h h1 h2 hw
      exact S.no_below_gen hχ hs (r := h) (by rw [h1]; exact t3) h2 j hj1
        (add_left_cancel (a := S.P.wt r) (by rw [hwt, ← hw]; abel))
    · intro h h1 h2 hm
      exact hyS (Or.inr (S.partner_of_factor rfl rfl hyx
        (by rw [show ⌜r⌝ * ⌜h⌝ = ⌜qx0⌝ from S.P.rr_mul_rr_eq_rr.2 hm, hqx0]) hqx2 hprimx).2.2.2.2)
    · intro h h1 h2 hm
      have hm' : ⌜h⌝ * ⌜f⌝ = ⌜s⌝ := S.P.rr_mul_rr_eq_rr.2 hm
      have e : ⌜r⌝ * ⌜h⌝ * ⌜f⌝ = ⌜dx⌝ * ⌜f⌝ := by
        rw [mul_assoc, hm', hrs, hj, ← hdx, S.qpow_mul_e hj1]
      have hrh : ⌜r⌝ * ⌜h⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by
        rw [← hrs, ← hm', ← mul_assoc, h0, zero_mul])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hrh
      rw [hc] at e
      have := S.cancel_right e (by rw [e, ← hdx, S.qpow_mul_e hj1, ← hj]; exact S.rr_ne t)
      subst this
      have hrh' : ⌜r⌝ * ⌜h⌝ = S.q x ^ j := by rw [hc, ← hdx, S.qpow_mul_e hj1]
      have hgen := S.gen_factor k hfin hs (Or.inr (by rw [← hz]; exact hsq)) (a := S.P.e y)
        (m := h) (b := f) (by rw [S.e_mul_rr' h h1, hm'])
      rcases hW with ⟨hX, -⟩ | hj1'
      · exact hX ⟨h, j, hgen, h1, h2, hj1, hrh', hqxj'⟩
      · subst hj1'
        exact hyS (Or.inr (S.partner_of_factor rfl rfl hyx (by rw [hrh', pow_one]) hqx2
          hprimx).2.2.2.2)
    · intro h h1 h2 hw
      exact S.no_below_gen hχ hr (r := h) h1 h2 j hj1
        (add_right_cancel (b := S.P.wt s) (by rw [hwt, ← hw]; abel))
    · intro h h1 h2 hm
      exact hyzS (Or.inr (S.partner_of_factor h1 h2 hyz
        (by rw [show ⌜h⌝ * ⌜s⌝ = ⌜qz0⌝ from S.P.rr_mul_rr_eq_rr.2 hm, hqz0]) hqz2 hprimz).2.2.2.2)
  have hj2 : 2 ≤ j := by by_contra h; exact tree (Or.inr (by omega))
  have hExt : ExtX ∨ ExtZ := by by_contra h; exact tree (Or.inl (not_or.1 h))
  rcases hExt with ⟨b, i, hb, b1, b2, hi1, hrb, hqi⟩ | ⟨a, i, ha, a1, a2, hi1, has, hqi⟩
  · obtain ⟨hi2, hq3, hq4, -, -, -, -, hbL⟩ := S.nondeep_return k hfin hr hb rfl rfl b1 b2 hyx
      hrb hi1 hqi hyS hprimx
    subst hi2
    obtain rfl : j = 2 := by
      by_contra h; apply hqxj'; rw [show j + 1 = (j + 1 - 4) + 4 by omega, pow_add, hq4, mul_zero]
    have hbf : ⌜b⌝ * ⌜f⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [hj, ← hrb, mul_assoc, h0, mul_zero])
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne hbf
    have e : ⌜r⌝ * ⌜s⌝ = ⌜r⌝ * ⌜c⌝ := by rw [hrs, hj, ← hrb, mul_assoc, hc]
    have := S.cancel_left e (by rw [hrs]; exact S.rr_ne t)
    subst this
    have hb0 : b ≠ S.P.e (S.P.src b) := fun he ↦ hyx (by
      rw [← b2, ← b1]; nth_rewrite 2 [he]; rw [S.P.tgt_e])
    have hbq : ⌜b⌝ * S.qh χ (S.P.tgt b) ≠ 0 := by
      rw [b2, hqx]; intro h0; apply hq3
      rw [pow_succ, ← hrb, mul_assoc, h0, mul_zero]
    have hTb : S.TR χ b := by
      refine ⟨(S.shift_of_mul_qh hb0 hbq).1, ?_, hbq⟩
      by_contra hne
      have hsy := S.supp_of_qh hne
      rw [S.qh_of_supp χ hsy] at hne
      exact hbL (S.prim_action_gen hb (by rw [hsy.2]; exact hprim) hne).1
    exact ⟨f, hf, by rw [hqx]; exact hj, by rw [hqz]; exact hj', Or.inr ⟨b, hc.symm,
      hr, hb, rfl, b1.symm, b2, hyS, hTr, hTb, by rw [hqx]; exact hrb, by rw [hqx]; exact hq3⟩⟩
  · obtain ⟨hi2, hq3, hq4, -, -, haR, -, -⟩ := S.nondeep_return k hfin ha hs a1 a2 t3.symm rfl
      hyz has hi1 hqi hyzS hprimz
    subst hi2
    obtain rfl : j = 2 := by
      by_contra h; apply hqzj'; rw [show j + 1 = (j + 1 - 4) + 4 by omega, pow_add, hq4, mul_zero]
    have hfa : ⌜f⌝ * ⌜a⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [hj', ← has, ← mul_assoc, h0, zero_mul])
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne hfa
    have e : ⌜r⌝ * ⌜s⌝ = ⌜c⌝ * ⌜s⌝ := by rw [hrs, hj', ← has, ← mul_assoc, hc]
    have := S.cancel_right e (by rw [hrs]; exact S.rr_ne t)
    subst this
    have ha0 : a ≠ S.P.e (S.P.src a) := fun he ↦ hyz (by
      rw [← a2, ← a1]; nth_rewrite 1 [he]; rw [S.P.tgt_e])
    have hqa : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
      rw [a1, hqz]; intro h0; apply hq3
      rw [pow_succ', ← has, ← mul_assoc, h0, zero_mul]
    have hTa : S.TL χ a := by
      refine ⟨(S.shift_of_qh_mul ha0 hqa).1, hqa, ?_⟩
      by_contra hne
      have hsy := S.supp_of_qh' hne
      rw [S.qh_of_supp χ hsy] at hne
      exact haR (S.prim_action_gen_op ha (by rw [hsy.2]; exact hprim) hne).1
    exact ⟨f, hf, by rw [hqx]; exact hj, by rw [hqz]; exact hj', Or.inl ⟨a, hc.symm,
      ha, hs, a1, by rw [a2, t3], rfl, by rw [a2]; exact hyzS, hTa, hTs,
      by rw [hqz]; exact has, by rw [hqz]; exact hq3⟩⟩

/-- **Proposition 8.25(2)**, return-corner form (`prop:proper-ray-products`(2)): in
`BL_proper`, the first factor `r : x → y` reaches the primitive return corner, `y ∈ S_x`. -/
theorem BL_proper_inS (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {r s t f : R} {n : ℕ} (hr : S.IsGen r) (hs : S.IsGen s) (hBr : S.TB χ r)
    (hLs : S.TL χ s) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (hf : S.IsGen f)
    (ht : ⌜t⌝ = S.qh χ (S.P.src r) ^ n * ⌜f⌝) (hn : 1 ≤ n) (hsh : S.Shift χ t) :
    S.InS (S.P.src r) (S.P.tgt r) := by
  obtain ⟨-, -, -, h, hrev⟩ := S.BL_proper k hfin hχ hprim hr hs hBr hLs hrs hf ht hn hsh
  by_cases hc : S.P.tgt r = S.P.src r
  · exact Or.inl hc
  · have hq : S.q (S.P.src r) * ⌜r⌝ ≠ 0 := by
      rw [← S.qh_of_supp χ (S.supp_of_qh hBr.2.1)]; exact hBr.2.1
    have hcomm : S.q (S.P.src r) * ⌜r⌝ = ⌜r⌝ * S.q (S.P.tgt r) := by
      obtain ⟨-, e1⟩ := S.shift_of_qh_mul hBr.1.1 hBr.2.1
      obtain ⟨-, e2⟩ := S.shift_of_mul_qh hBr.1.1 hBr.2.2
      rw [← S.qh_of_supp χ (S.supp_of_qh hBr.2.1), ← S.qh_of_supp χ (S.supp_of_qh' hBr.2.2), e1, e2]
    exact Or.inr ⟨hc, r, h, hr, rfl, rfl, hrev, hcomm, hq⟩

/-- **Lemma C.2** (`lem:nondeep-two-object-return`): at a supporting
vertex `b`, generating rays `e : b → y`, `l : y → b` with `y ∉ S_b`, `el = q̂_b^a` and
`q̂_b^{a+1} ≠ 0` have types `L` and `R`, `N_b = 4`, `el = q̂_b²` and `le = 0`. -/
theorem nondeep_return_types (hfin : IsRepresentationFinite k (S.P.Lin k)) (hprim : Prim χ)
    {b y : V} {e l : R} {a : ℕ} (hsupp : S.Supp χ b)
    (he : S.IsGen e) (hl : S.IsGen l) (e1 : S.P.src e = b) (e2 : S.P.tgt e = y)
    (l1 : S.P.src l = y) (l2 : S.P.tgt l = b) (hby : y ≠ b) (hel : ⌜e⌝ * ⌜l⌝ = S.qh χ b ^ a)
    (ha : 1 ≤ a) (ha1 : S.qh χ b ^ (a + 1) ≠ 0) (hS : ¬ S.InS b y) :
    S.TL χ e ∧ S.TR χ l ∧ S.qh χ b ^ 3 ≠ 0 ∧ S.qh χ b ^ 4 = 0 ∧
      ⌜e⌝ * ⌜l⌝ = S.qh χ b ^ 2 ∧ ⌜l⌝ * ⌜e⌝ = 0 := by
  have hqb : S.qh χ b = S.q b := S.qh_of_supp χ hsupp
  rw [hqb] at hel ha1 ⊢
  have hprimb : Prim (S.χ b) := by rw [hsupp.2]; exact hprim
  obtain ⟨ha2, hq3, hq4, hle, heL, heR, hlR, hlL⟩ :=
    S.nondeep_return k hfin he hl e1 e2 l1 l2 hby hel ha ha1 hS hprimb
  subst ha2
  have hqe : S.q b * ⌜e⌝ ≠ 0 := by
    intro h0; apply hq3; rw [pow_succ', ← hel, ← mul_assoc, h0, zero_mul]
  have hlq : ⌜l⌝ * S.q b ≠ 0 := by
    intro h0; apply hq3; rw [pow_succ, ← hel, mul_assoc, h0, mul_zero]
  have he0 : e ≠ S.P.e (S.P.src e) := fun h ↦ hby (by
    have := congrArg S.P.tgt h; rwa [S.P.tgt_e, e2, e1] at this)
  have hl0 : l ≠ S.P.e (S.P.src l) := fun h ↦ hby (by
    have := congrArg S.P.tgt h; rw [S.P.tgt_e, l2, l1] at this; exact this.symm)
  have hqe' : S.qh χ (S.P.src e) * ⌜e⌝ ≠ 0 := by rw [e1, hqb]; exact hqe
  have hlq' : ⌜l⌝ * S.qh χ (S.P.tgt l) ≠ 0 := by rw [l2, hqb]; exact hlq
  refine ⟨⟨(S.shift_of_qh_mul he0 hqe').1, hqe', ?_⟩,
    ⟨(S.shift_of_mul_qh hl0 hlq').1, ?_, hlq'⟩, hq3, hq4, hel, hle⟩
  · by_contra hne
    have hsy := S.supp_of_qh' hne
    rw [S.qh_of_supp χ hsy] at hne
    exact heR (S.prim_action_gen_op he (by rw [hsy.2]; exact hprim) hne).1
  · by_contra hne
    have hsy := S.supp_of_qh hne
    rw [S.qh_of_supp χ hsy] at hne
    exact hlL (S.prim_action_gen hl (by rw [hsy.2]; exact hprim) hne).1

end Sys

end RaySys

end MultiplicativeBasisDeformations
