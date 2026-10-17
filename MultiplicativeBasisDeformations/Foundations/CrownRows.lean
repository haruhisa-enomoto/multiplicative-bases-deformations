import MultiplicativeBasisDeformations.Foundations.ProperProducts

/-!
# Two-sided segments, crown rows and nondeep boundary arrows

`lem:two-sided-factor-paths`, `lem:crown-output-comparison` and
`lem:nondeep-boundary-arrows` (`integral-partial-lifts.tex`), in path-free form: an
ordinary path is recorded by its first (last) arrow, an ordinary left (right) divisor.
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

variable {χ : L}

omit [IsAlgClosed k] in
/-- The output type of a product of a two-sided and a left-sided ray is left-sided. -/
theorem out_BL (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r s t : R} (hr : S.TB χ r)
    (hs : S.TL χ s) (hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝) (ht : S.Shift χ t) : S.TL χ t := by
  have hr0 : r ≠ S.P.e (S.P.src r) := hr.1.1
  have hs0 : s ≠ S.P.e (S.P.src s) := hs.1.1
  rcases S.types_of_shift hχ hprim ht with h | h | h
  · exact h
  · rcases S.table_R hχ hprim hr0 hs0 hrs h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd hs.2.2 h1.2.2
    · exact absurd hs.2.2 h1.2.2
  · rcases (S.table_B hχ hprim hr0 hs0 hrs h).1 with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact absurd hs.2.2 h1.2.2
    · exact absurd h1.2.2 hr.2.2

omit [IsAlgClosed k] in
/-- **Lemma 9.3, first-arrow form** (`lem:two-sided-factor-paths`): if `b` is two-sided and
`bs` is shiftable with `s` left-sided, every ordinary path of `b` starts with a two-sided
arrow. -/
theorem first_TB (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {b s t a : R} (hb : S.TB χ b)
    (hs : S.TL χ s) (hbs : ⌜b⌝ * ⌜s⌝ = ⌜t⌝) (ht : S.Shift χ t) (ha : S.OL b a) : S.TB χ a := by
  obtain ⟨ho, w, hw⟩ := ha
  have hTt := S.out_BL hχ hprim hb hs hbs ht
  obtain ⟨b1, -, -, -⟩ := S.prod_of hw
  have hqa : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
    intro h0; apply hb.2.1; rw [← hw, ← mul_assoc, b1, h0, zero_mul]
  obtain ⟨hsha, hsa⟩ := S.shift_of_qh_mul ho.1 hqa
  by_contra hna
  have haR : ⌜a⌝ * S.qh χ (S.P.tgt a) = 0 := by
    by_contra h; exact hna ⟨hsha, hqa, h⟩
  have hw0 : w ≠ S.P.e (S.P.src w) := by
    intro he
    have := S.src_of_mul_ne (by rw [hw]; exact S.rr_ne b)
    rw [he, ← this, S.rr_mul_e] at hw
    rw [← S.rr_inj hw] at hb
    exact hna hb
  have hTw : S.TR χ w := by
    rcases (S.table_B hχ hprim ho.1 hw0 hw hb).1 with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hna
    · exact h1
  -- the middle action `w q̂ s` survives
  obtain ⟨-, hb1⟩ := S.shift_of_qh_mul hb.1.1 hb.2.1
  obtain ⟨-, hb2⟩ := S.shift_of_mul_qh hb.1.1 hb.2.2
  obtain ⟨t1, -, t3, -⟩ := S.prod_of hbs
  have hmid : ⌜a⌝ * (⌜w⌝ * S.qh χ (S.P.src s) * ⌜s⌝) ≠ 0 := by
    have : S.qh χ (S.P.src t) * ⌜t⌝ = ⌜a⌝ * (⌜w⌝ * S.qh χ (S.P.src s) * ⌜s⌝) := by
      rw [← hbs, t1, ← mul_assoc, hb1, ← hb2, ← t3, ← hw]; simp only [mul_assoc]
    rw [← this]; exact hTt.2.1
  have hwqs : ⌜w⌝ * S.qh χ (S.P.src s) * ⌜s⌝ ≠ 0 := fun h0 ↦ hmid (by rw [h0, mul_zero])
  -- hence `w s = 0`
  have hws : ⌜w⌝ * ⌜s⌝ = 0 := by
    by_contra hws
    obtain ⟨u, hu⟩ := S.ray_of_mul_ne hws
    have hsy := S.supp_of_qh' (show ⌜w⌝ * S.qh χ (S.P.src s) ≠ 0 from
      fun h0 ↦ hwqs (by rw [h0, zero_mul]))
    rw [S.qh_of_supp χ hsy] at hwqs
    obtain ⟨v, hv⟩ := S.mul_left_ray (show ⌜w⌝ * S.q (S.P.src s) ≠ 0 from
      fun h0 ↦ hwqs (by rw [h0, zero_mul]))
    rw [hv] at hwqs
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne hwqs
    obtain ⟨u1, u2, u3, u4⟩ := S.prod_of hu
    obtain ⟨c1, c2, -, c4⟩ := S.prod_of hc
    obtain ⟨v1, v2⟩ := S.mul_qpow_endpoints (n := 1) (by rw [pow_one]; exact hv)
    have hwv : S.P.wt v = S.P.wt w + χ := by
      have := congrArg S.wtM hv
      rw [S.wtM_mul _ _ (by rw [hv]; exact S.rr_ne v), wtM_rr, wtM_rr] at this
      rw [← this, ← hsy.2]; rfl
    have hu0 : u ≠ S.P.e (S.P.src u) := by
      apply S.ne_e_of_deg; rw [u4, map_add]
      have := S.P.deg_pos w hw0; have := S.P.deg_nonneg s; linarith
    have hshu : S.Shift χ u := ⟨hu0, c, by rw [c1, v1, u1], by rw [c2, u2],
      by rw [c4, hwv, u4]; abel⟩
    rcases S.succ_by_gen hχ hprim hshu with h | h
    · apply S.rr_ne (S.succ χ u)
      rw [← h, ← hu, u1, ← mul_assoc, hTw.2.1, zero_mul]
    · apply S.rr_ne (S.succ χ u)
      rw [← h, ← hu, u2, mul_assoc, hs.2.2, mul_zero]
  apply S.rr_ne t
  rw [← hbs, ← hw, mul_assoc, hws, mul_zero]

omit [IsAlgClosed k] in
/-- **Lemma 9.3, last-arrow form** (the dual). -/
theorem last_TB (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r b t a : R} (hb : S.TB χ b)
    (hr : S.TR χ r) (hrb : ⌜r⌝ * ⌜b⌝ = ⌜t⌝) (ht : S.Shift χ t) (ha : S.OR b a) : S.TB χ a :=
  (S.op_TB a).1 (S.op.first_TB hχ hprim ((S.op_TB b).2 hb) ((S.op_TL r).2 hr)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hrb]) ((S.op_shift t).2 ht)
    ((S.op_OL b a).2 ha))

/-- **Lemma 9.6** (`lem:nondeep-boundary-arrows`): the first arrow of the outgoing ray of a
nondeep return is left-sided. -/
theorem nondeep_first_TL (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {x : V} {e l a : R} (hN : S.NondeepRet χ x e l) (ha : S.OL e a) :
    S.TL χ a := by
  obtain ⟨he, hl, e1, e2, l2, hyS, hTe, hTl, hel, hq3⟩ := hN
  obtain ⟨ho, c, hc⟩ := ha
  obtain ⟨c1, c2, c3, -⟩ := S.prod_of hc
  have hsx := S.supp_of_qh hTe.2.1
  rw [e1] at hsx
  have hqx : S.qh χ x = S.q x := S.qh_of_supp χ hsx
  rw [hqx] at hel hq3
  have hqa : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
    intro h0; apply hTe.2.1; rw [← hc, ← mul_assoc, c1, h0, zero_mul]
  obtain ⟨hsha, -⟩ := S.shift_of_qh_mul ho.1 hqa
  by_contra hna
  have hB : S.TB χ a := by
    refine ⟨hsha, hqa, fun h0 ↦ hna ⟨hsha, hqa, h0⟩⟩
  have hd : S.Dim2 e := Or.inl (by rw [← S.qh_of_supp χ (by rw [e1]; exact hsx)]; exact hTe.2.1)
  have hagen : S.IsGen a := S.gen_factor k hfin he hd (a := S.P.e (S.P.src e)) (m := a) (b := c)
    (by rw [S.e_mul_rr' a c1.symm, hc])
  have hcgen : S.IsGen c := S.gen_factor k hfin he hd (a := a) (m := c) (b := S.P.e (S.P.tgt e))
    (by rw [hc, S.rr_mul_e])
  set v := S.P.tgt a with hv
  have hxv : v ≠ x := by
    intro h; apply ho.1
    exact S.no_loop_factor k hfin he hd (a := S.P.e (S.P.src e)) (b := c)
      (by rw [S.e_mul_rr' a c1.symm, hc]) (by rw [← c1, e1, ← h])
  -- `a` is cyclic at both endpoints, with a primitive generating reverse
  obtain ⟨-, h1⟩ := S.shift_of_qh_mul hB.1.1 hB.2.1
  obtain ⟨-, h2⟩ := S.shift_of_mul_qh hB.1.1 hB.2.2
  have hsv := S.supp_of_qh' hB.2.2
  rw [S.qh_of_supp χ hsv] at h2
  rw [← c1, e1, hqx] at h1
  have hcomm : S.q x * ⌜a⌝ = ⌜a⌝ * S.q v := h1.trans h2.symm
  have hqa' : S.q x * ⌜a⌝ ≠ 0 := by rw [h1]; exact S.rr_ne _
  have hprimx : Prim (S.χ x) := by rw [hsx.2]; exact hprim
  obtain ⟨haL, -⟩ := S.prim_action_gen hagen (by rw [← c1, e1]; exact hprimx)
    (by rw [← c1, e1]; exact hqa')
  obtain ⟨haR, -⟩ := S.prim_action_gen_op hagen (by rw [hsv.2]; exact hprim)
    (by rw [← hcomm]; exact hqa')
  have hcl : ⌜c⌝ * ⌜l⌝ ≠ 0 := by
    intro h0; apply hq3; rw [show 3 = 2 + 1 by rfl, pow_succ, ← hel, ← hc, mul_assoc ⌜a⌝, h0]; simp
  obtain ⟨cl, hclr⟩ := S.ray_of_mul_ne hcl
  obtain ⟨cl1, cl2, -, -⟩ := S.prod_of hclr
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen cl
  rw [cl1, ← c3] at g1
  rw [cl2, l2] at g2
  have hacl : ⌜a⌝ * ⌜cl⌝ ≠ 0 := by
    rw [← hclr, ← mul_assoc, hc, hel]; intro h0; apply hq3
    rw [show 3 = 2 + 1 by rfl, pow_succ, h0, zero_mul]
  have hrev := S.prim_reverse k hfin hagen (by rw [← c1, e1]; exact hxv.symm) haL haR
    (by rw [← c1, e1]; exact hcomm) (by rw [← c1, e1]; exact hqa')
    (by rw [← c1, e1]; exact hprimx) (h0 := cl) (by rw [cl1, ← c3])
    (by rw [cl2, l2, ← c1, e1]) hacl hg (by rw [g1]) (by rw [g2, ← c1, e1])
  obtain ⟨hag, hga⟩ := hrev
  rw [← c1, e1] at hag
  have hqvg : S.q v * ⌜g⌝ ≠ 0 := by
    intro h0; apply hacl
    have : ⌜a⌝ * ⌜cl⌝ = ⌜a⌝ * (S.q v * ⌜g⌝) := by
      rw [← hclr, ← mul_assoc, hc, hel, ← mul_assoc, ← hcomm, mul_assoc, hag, pow_two]
    rw [this, h0, mul_zero]
  obtain ⟨w, hw⟩ := S.mul_right_ray hqvg
  have hclw : cl = w := by
    apply S.cancel_left (r := a)
    · rw [← hw, ← hclr, ← mul_assoc, hc, hel, ← mul_assoc, ← hcomm, mul_assoc, hag, pow_two]
    · exact hacl
  subst hclw
  have hc0 : c ≠ S.P.e (S.P.src c) := by
    intro he'
    have := S.src_of_mul_ne (by rw [hc]; exact S.rr_ne e)
    rw [he', ← this, S.rr_mul_e] at hc
    rw [← S.rr_inj hc] at hTe
    exact hna hTe
  have hTc : S.TL χ c := by
    rcases S.table_L hχ hprim ho.1 hc0 hc hTe with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd hB.2.2 (by rw [h.2.2]; exact fun h' ↦ h' rfl)
    · exact h
  have hq2g : S.q v * (S.q v * ⌜g⌝) ≠ 0 := by
    intro h0; apply hq3
    have : S.q x ^ 3 = ⌜a⌝ * (S.q v * (S.q v * ⌜g⌝)) := by
      rw [← mul_assoc, ← hcomm, mul_assoc, ← mul_assoc ⌜a⌝, ← hcomm, mul_assoc, hag,
        pow_succ', pow_two]
    rw [this, h0, mul_zero]
  have hqv : S.qh χ v = S.q v := S.qh_of_supp χ hsv
  have hdv := S.χ_deg_pos v hsv.1
  have hcl0 : cl ≠ S.P.e (S.P.src cl) := by
    apply S.ne_e_of_deg
    rw [(S.prod_of hclr).2.2.2, map_add]
    have := S.P.deg_pos c hc0; have := S.P.deg_nonneg l; linarith
  have hscl : S.P.src cl = v := by rw [cl1, ← c3]
  have hsh : S.Shift χ cl := (S.shift_of_qh_mul hcl0 (by rw [hscl, hqv, ← hw]; exact hq2g)).1
  have hwg : S.P.wt cl = S.χ v + S.P.wt g := by
    have := congrArg S.wtM hw
    rw [S.wtM_mul _ _ hqvg, wtM_rr, wtM_rr] at this
    exact this.symm
  have hprop : ¬ S.IsGen cl := by
    intro hgen
    have := S.gen_unique hgen hg (by rw [hscl, g1]) (by rw [cl2, l2, g2])
    subst this
    have := congrArg S.P.deg hwg
    rw [map_add] at this; linarith
  rcases S.LR_proper k hfin hχ hprim hcgen hl hTc hTl hclr hsh hprop with ⟨h, -⟩ | ⟨-, f, hf, hf2, -⟩
  · exact hxv (by rw [c3, ← h, l2])
  · rw [← c3, hqv] at hf2
    obtain ⟨f1, f2⟩ := S.qpow_mul_endpoints hf2.symm
    have := S.gen_unique hf hg (by rw [← f1, hscl, g1]) (by rw [← f2, cl2, l2, g2])
    subst this
    have h2 := S.wt_of_eq_qpow_mul (f := f) (by rw [← f1, hscl]; exact hf2)
    rw [← f1, hscl] at h2
    have := congrArg S.P.deg (hwg.symm.trans h2)
    simp only [map_add, map_nsmul, nsmul_eq_mul] at this
    push_cast at this
    linarith

/-- **Lemma 9.6, dual**: the last arrow of the incoming ray of a nondeep return is
right-sided. -/
theorem nondeep_last_TR (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {x : V} {e l b : R} (hN : S.NondeepRet χ x e l) (hb : S.OR l b) :
    S.TR χ b :=
  (S.op_TL b).1 (S.op.nondeep_first_TL k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    (S.op_nondeep hN hprim) ((S.op_OL l b).2 hb))

omit [IsAlgClosed k] in
/-- Every nonidentity ray has an ordinary right divisor. -/
theorem exists_OR (f : R) (hf : f ≠ S.P.e (S.P.src f)) : ∃ b, S.OR f b := by
  obtain ⟨b, hb⟩ := S.op.exists_OL f (by
    change f ≠ S.P.e (S.P.tgt f); rwa [S.ne_e_iff_op])
  exact ⟨b, (S.op_OL f b).1 hb⟩

variable (χ) in
/-- A row `X_a + Y_b = [f]` with generating two-sided output (`eq:generating-crown-row`):
`f = a v = w b` with `v` right-sided and `w` left-sided generating, `b` the last arrow of `v`
and `a` the first arrow of `w`. -/
def CrownRow (a b f : R) : Prop :=
  S.IsGen f ∧ S.TB χ f ∧ S.TL χ a ∧ S.TR χ b ∧ ∃ v w, ⌜a⌝ * ⌜v⌝ = ⌜f⌝ ∧ ⌜w⌝ * ⌜b⌝ = ⌜f⌝ ∧
    S.IsGen v ∧ S.IsGen w ∧ S.TR χ v ∧ S.TL χ w ∧ S.OR v b ∧ S.OL w a

variable (χ) in
/-- A row `X_a + Y_b = 2[q̂_x]` of a nondeep return (`eq:nondeep-coefficient-row`). -/
def NdRow (a b : R) (x : V) : Prop :=
  ∃ e l, S.NondeepRet χ x e l ∧ S.OL e a ∧ S.OR l b

omit [IsAlgClosed k] in
theorem op_crownRow {a b f : R} : S.op.CrownRow χ b a f ↔ S.CrownRow χ a b f := by
  unfold CrownRow
  simp only [op_isGen_iff, op_TB, op_TL, op_TR, op_OL, op_OR]
  constructor
  · rintro ⟨h1, h2, h3, h4, v, w, hv, hw, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h1, h2, h4, h3, w, v, S.P.toOp_injective ?_, S.P.toOp_injective ?_,
      h6, h5, h8, h7, h10, h9⟩
    · rw [Tab.toOp_mul]; exact hw
    · rw [Tab.toOp_mul]; exact hv
  · rintro ⟨h1, h2, h3, h4, v, w, hv, hw, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h1, h2, h4, h3, w, v, ?_, ?_, h6, h5, h8, h7, h10, h9⟩
    · rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw]
    · rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hv]

/-- **Lemma 9.5, first part** (`lem:crown-output-comparison`): two two-sided rays whose paths
start with the same ordinary left-sided arrow are comparable by right factorization. -/
theorem crown_compare (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {a f t v w : R} (ha : S.TL χ a) (hoa : S.Ord a) (hf : S.TB χ f)
    (ht : S.TB χ t) (hfa : ⌜a⌝ * ⌜v⌝ = ⌜f⌝) (hta : ⌜a⌝ * ⌜w⌝ = ⌜t⌝) :
    S.P.RF f t ∨ S.P.RF t f := by
  have hsx := S.supp_of_qh ha.2.1
  have hqx : S.qh χ (S.P.src a) = S.q (S.P.src a) := S.qh_of_supp χ hsx
  obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases (S.P.src a)).resolve_left hsx.1
  replace hq0 : S.q (S.P.src a) = ⌜q0⌝ := hq0
  obtain ⟨f1, -, -, -⟩ := S.prod_of hfa
  obtain ⟨t1, -, -, -⟩ := S.prod_of hta
  have hqf : ⌜q0⌝ * ⌜f⌝ ≠ 0 := by rw [← hq0, ← hqx, ← f1]; exact hf.2.1
  have hqt : ⌜q0⌝ * ⌜t⌝ ≠ 0 := by rw [← hq0, ← hqx, ← t1]; exact ht.2.1
  obtain ⟨qf, hqfr⟩ := S.ray_of_mul_ne hqf
  obtain ⟨qt, hqtr⟩ := S.ray_of_mul_ne hqt
  -- the upward comparisons `a ≤ q̂ g`
  have up : ∀ {g u qg : R}, S.TB χ g → ⌜a⌝ * ⌜u⌝ = ⌜g⌝ → ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ →
      S.P.RF a qg := by
    intro g u qg hg hu hqg
    obtain ⟨g1, g2, -, -⟩ := S.prod_of hu
    obtain ⟨-, e1⟩ := S.shift_of_qh_mul hg.1.1 hg.2.1
    obtain ⟨-, e2⟩ := S.shift_of_mul_qh hg.1.1 hg.2.2
    have hc : ⌜q0⌝ * ⌜g⌝ = ⌜g⌝ * S.qh χ (S.P.tgt g) := by rw [← hq0, ← hqx, ← g1, e1, e2]
    have hne : ⌜u⌝ * S.qh χ (S.P.tgt g) ≠ 0 := by
      intro h0; apply S.rr_ne qg; rw [← hqg, hc, ← hu, mul_assoc, h0, mul_zero]
    obtain ⟨u', hu'⟩ := S.mul_left_ray hne
    exact (S.rf_iff _ _).2 ⟨u', by rw [← hu', ← mul_assoc, hu, ← hc, hqg]⟩
  have dq := S.P.deg_pos q0 (by rw [q01]; exact q03)
  have hd := fun r : R ↦ S.P.deg_nonneg r
  obtain ⟨c1, -, -, c4⟩ := S.prod_of hqfr
  obtain ⟨d1, -, -, d4⟩ := S.prod_of hqtr
  -- comparisons of the upper points reduce to comparisons of `f, t`
  have upper : ∀ {g g' qg qg' : R}, ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ⌜q0⌝ * ⌜g'⌝ = ⌜qg'⌝ →
      S.P.RF qg qg' → S.P.RF g g' := by
    intro g g' qg qg' hg hg' hr
    obtain ⟨h, hh⟩ := (S.rf_iff _ _).1 hr
    rw [← hg, ← hg', mul_assoc] at hh
    have hgh : ⌜g⌝ * ⌜h⌝ ≠ 0 := fun h0 ↦ S.rr_ne qg' (by rw [← hg', ← hh, h0, mul_zero])
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne hgh
    rw [hc] at hh
    have := S.cancel_left hh (by rw [hh, hg']; exact S.rr_ne _)
    subst this
    exact (S.rf_iff _ _).2 ⟨h, hc⟩
  -- an upper point is not below `a`
  have nUa : ∀ {g qg : R}, 0 < S.P.deg (S.P.wt g) → ⌜q0⌝ * ⌜g⌝ = ⌜qg⌝ → ¬ S.P.RF qg a := by
    intro g qg hg0 hg hr
    obtain ⟨h, hh⟩ := (S.rf_iff _ _).1 hr
    rw [← hg, mul_assoc] at hh
    have hgh : ⌜g⌝ * ⌜h⌝ ≠ 0 := fun h0 ↦ S.rr_ne a (by rw [← hh, h0, mul_zero])
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne hgh
    rw [hc] at hh
    have dc : 0 < S.P.deg (S.P.wt c) := by
      rw [(S.prod_of hc).2.2.2, map_add]; have := hd h; linarith
    exact hoa.2 q0 c (by rw [q01]; exact q03) (S.ne_e_of_deg dc) hh
  have df := S.P.deg_pos f hf.1.1
  have dt := S.P.deg_pos t ht.1.1
  by_contra hc
  obtain ⟨nft, ntf⟩ := not_or.1 hc
  apply S.P.crown_false k hfin (S.P.src a) q0 a qf qt ⟨q01, rfl, by rw [c1, q01], by rw [d1, q01]⟩
    ((S.rf_iff _ _).2 ⟨f, hqfr⟩) ((S.rf_iff _ _).2 ⟨t, hqtr⟩) (up hf hfa hqfr) (up ht hta hqtr)
  · rw [S.rf_iff]; rintro ⟨h, hh⟩
    by_cases he : h = S.P.e (S.P.src h)
    · have h1 := S.src_of_mul_ne (by rw [hh]; exact S.rr_ne a)
      rw [he, ← h1, S.rr_mul_e] at hh
      have := S.rr_inj hh
      subst this
      exact S.tl_nonlocal ha (by rw [q01, q02])
    · exact hoa.2 q0 h (by rw [q01]; exact q03) he hh
  · rw [S.rf_iff]; rintro ⟨h, hh⟩
    exact S.no_return_one hχ hprim ha (by rw [hh, hq0])
  · exact fun h ↦ nft (upper hqfr hqtr h)
  · exact fun h ↦ ntf (upper hqtr hqfr h)
  · apply S.not_rf_deg; rw [c4, map_add]; linarith
  · exact nUa df hqfr
  · apply S.not_rf_deg; rw [d4, map_add]; linarith
  · exact nUa dt hqtr

/-- One direction of the uniqueness: `f h = t` forces `f = t`. -/
theorem crown_row_step (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {a b b' f t h : R} (hf : S.CrownRow χ a b f) (ht : S.CrownRow χ a b' t)
    (hh : ⌜f⌝ * ⌜h⌝ = ⌜t⌝) : f = t := by
  obtain ⟨-, hBf, -, -, v, -, hv, -, -, -, hTv, -, -, -⟩ := hf
  obtain ⟨hgt, hBt, -, hTb', v', -, hv', -, hgv', -, hTv', -, hb', -⟩ := ht
  by_cases he : h = S.P.e (S.P.src h)
  · have h1 := S.src_of_mul_ne (by rw [hh]; exact S.rr_ne t)
    rw [he, ← h1, S.rr_mul_e] at hh
    exact S.rr_inj hh
  exfalso
  have hB : S.TB χ h := by
    rcases (S.table_B hχ hprim hBf.1.1 he hh hBt).1 with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd hBf.2.2 (by rw [h1.2.2]; exact fun h' ↦ h' rfl)
  have e : ⌜a⌝ * (⌜v⌝ * ⌜h⌝) = ⌜a⌝ * ⌜v'⌝ := by rw [← mul_assoc, hv, hh, hv']
  have hvh : ⌜v⌝ * ⌜h⌝ ≠ 0 := fun h0 ↦ S.rr_ne t (by rw [← hv', ← e, h0, mul_zero])
  obtain ⟨c, hc⟩ := S.ray_of_mul_ne hvh
  rw [hc] at e
  have := S.cancel_left e (by rw [e, hv']; exact S.rr_ne t)
  subst this
  obtain ⟨d, hd⟩ := S.exists_OR h he
  have hdB := S.last_TB hχ hprim hB hTv hc hTv'.1 hd
  obtain ⟨hod, h', hh'⟩ := hd
  have hvh' : ⌜v⌝ * ⌜h'⌝ ≠ 0 := fun h0 ↦ S.rr_ne c (by rw [← hc, ← hh', ← mul_assoc, h0, zero_mul])
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne hvh'
  have hdc : S.OR c d := ⟨hod, u, by rw [← hu, mul_assoc, hh', hc]⟩
  have := S.unique_last k hfin hχ hprim hgv' hTv' hdc hb'
  subst this
  exact hdB.2.1 hTb'.2.1 |> fun h ↦ absurd hTb'.2.1 (by
    intro h'; exact hdB.2.1 (by rw [h']))

/-- **Lemma 9.5** (`lem:crown-output-comparison`, last assertion): crown rows sharing the
variable `X_a` have the same output ray. -/
theorem crown_row_unique_a (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {a b b' f t : R} (hf : S.CrownRow χ a b f) (ht : S.CrownRow χ a b' t) :
    f = t := by
  have hf' := hf
  have ht' := ht
  obtain ⟨-, hBf, hTa, -, v, -, hv, -, -, -, -, -, -, ⟨hoa, -⟩⟩ := hf'
  obtain ⟨-, hBt, -, -, v', -, hv', -⟩ := ht'
  rcases S.crown_compare k hfin hχ hprim hTa hoa hBf hBt hv hv' with h | h
  · obtain ⟨c, hc⟩ := (S.rf_iff _ _).1 h
    exact S.crown_row_step k hfin hχ hprim hf ht hc
  · obtain ⟨c, hc⟩ := (S.rf_iff _ _).1 h
    exact (S.crown_row_step k hfin hχ hprim ht hf hc).symm

/-- **Lemma 9.5, dual**: crown rows sharing `Y_b` have the same output ray. -/
theorem crown_row_unique_b (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {a a' b f t : R} (hf : S.CrownRow χ a b f) (ht : S.CrownRow χ a' b t) :
    f = t :=
  S.op.crown_row_unique_a k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    ((S.op_crownRow).2 hf) ((S.op_crownRow).2 ht)

omit [IsAlgClosed k] in
theorem op_ndRow {a b : R} {x : V} (hprim : Prim χ) (h : S.NdRow χ a b x) :
    S.op.NdRow χ b a x := by
  obtain ⟨e, l, hN, ha, hb⟩ := h
  exact ⟨l, e, S.op_nondeep hN hprim, (S.op_OL l b).2 hb, (S.op_OR e a).2 ha⟩

/-- A generating two-sided ray with a nonzero reverse product has a primitive reverse. -/
theorem prim_rev_of_TB (hfin : IsRepresentationFinite k (S.P.Lin k)) (hprim : Prim χ) {f w : R}
    (hf : S.IsGen f) (hB : S.TB χ f) (w1 : S.P.src w = S.P.tgt f) (w2 : S.P.tgt w = S.P.src f)
    (hw : ⌜f⌝ * ⌜w⌝ ≠ 0) : ∃ g, S.PrimRev f g := by
  have hc : S.P.tgt f ≠ S.P.src f := fun h ↦ hB.1.1 (S.gen_loop_e hf h.symm)
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
  exact ⟨g, S.prim_reverse k hfin hf (fun e ↦ hc e.symm) hL hR hqf h1
    (by rw [hsb.2]; exact hprim) w1 w2 hw hg (by rw [g1, w1]) (by rw [g2, w2])⟩

/-- The variable `X_a` of a nondeep row occurs in no crown row
(`integral-partial-lifts.tex`). -/
theorem crown_nd_disjoint_a (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {a b b' f : R} {x : V} (hf : S.CrownRow χ a b f) (hn : S.NdRow χ a b' x) :
    False := by
  obtain ⟨hgf, hBf, hTa, -, v, -, hv, -, -, -, -, -, -, ⟨hoa, -⟩⟩ := hf
  obtain ⟨e, l, ⟨he, hl, e1, e2, l2, hyS, hTe, hTl, hel, hq3⟩, ⟨-, w, hw⟩, -⟩ := hn
  have hsx := S.supp_of_qh hTe.2.1
  rw [e1] at hsx
  have hqx : S.qh χ x = S.q x := S.qh_of_supp χ hsx
  rw [hqx] at hel hq3
  obtain ⟨a1, -, -, -⟩ := S.prod_of hw
  have hel0 : ⌜e⌝ * ⌜l⌝ ≠ 0 := by
    rw [hel]; intro h0; apply hq3; rw [pow_succ, h0, zero_mul]
  obtain ⟨q2, hq2⟩ := S.ray_of_mul_ne hel0
  have hwl : ⌜a⌝ * (⌜w⌝ * ⌜l⌝) ≠ 0 := by rw [← mul_assoc, hw]; exact hel0
  have hwl' : ⌜w⌝ * ⌜l⌝ ≠ 0 := fun h0 ↦ hwl (by rw [h0, mul_zero])
  obtain ⟨wl, hwlr⟩ := S.ray_of_mul_ne hwl'
  have haq2 : ⌜a⌝ * ⌜wl⌝ = ⌜q2⌝ := by rw [← hwlr, ← mul_assoc, hw, hq2]
  have hq2x : ⌜q2⌝ = S.q x ^ 2 := hq2.symm.trans hel
  obtain ⟨p1, p2, -, -⟩ := S.prod_of hq2
  have hsq2 : S.P.src q2 = x := by rw [p1, e1]
  have htq2 : S.P.tgt q2 = x := by rw [p2, l2]
  have hdχ := S.χ_deg_pos x hsx.1
  have hq20 : q2 ≠ S.P.e (S.P.src q2) := by
    apply S.ne_e_of_deg
    rw [S.wt_of_eq_qpow hq2x, map_nsmul, nsmul_eq_mul]; positivity
  have hq3' : S.qh χ (S.P.src q2) * ⌜q2⌝ ≠ 0 := by
    rw [hsq2, hqx, hq2x, ← pow_succ']; exact hq3
  have hq3'' : ⌜q2⌝ * S.qh χ (S.P.tgt q2) ≠ 0 := by
    rw [htq2, hqx, hq2x, ← pow_succ]; exact hq3
  have hBq2 : S.TB χ q2 := ⟨(S.shift_of_qh_mul hq20 hq3').1, hq3', hq3''⟩
  rcases S.crown_compare k hfin hχ hprim hTa hoa hBf hBq2 hv haq2 with h | h
  · obtain ⟨h', hh'⟩ := (S.rf_iff _ _).1 h
    obtain ⟨g, hfg, -⟩ := S.prim_rev_of_TB k hfin hprim hgf hBf (w := h')
      (by rw [← S.src_of_mul_ne (by rw [hh']; exact S.rr_ne q2)])
      (by rw [← (S.prod_of hh').2.1, htq2, (S.prod_of hv).1, ← a1, e1]) (by rw [hh']; exact S.rr_ne _)
    have hvg : ⌜v⌝ * ⌜g⌝ ≠ 0 := by
      intro h0; apply hsx.1
      rw [show S.q x = S.q (S.P.src f) by rw [(S.prod_of hv).1, ← a1, e1], ← hfg, ← hv,
        mul_assoc, h0, mul_zero]
    obtain ⟨u, hu⟩ := S.ray_of_mul_ne hvg
    exact S.no_return_one hχ hprim hTa (v := u) (by
      rw [← hu, ← mul_assoc, hv, hfg, (S.prod_of hv).1])
  · obtain ⟨h', hh'⟩ := (S.rf_iff _ _).1 h
    obtain ⟨-, k2, k3, -⟩ := S.prod_of hh'
    exact S.gen_ne_q_mul hgf (b := h') (by rw [← k3, htq2, (S.prod_of hv).1, ← a1, e1])
      k2.symm 2 (by omega) (by rw [← hh', hq2x, (S.prod_of hv).1, ← a1, e1])

/-- The variable `Y_b` of a nondeep row occurs in no crown row (the dual). -/
theorem crown_nd_disjoint_b (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {a a' b f : R} {x : V} (hf : S.CrownRow χ a b f) (hn : S.NdRow χ a' b x) :
    False :=
  S.op.crown_nd_disjoint_a k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    ((S.op_crownRow).2 hf) (S.op_ndRow hprim hn)

end Sys

end RaySys

end MultiplicativeBasisDeformations
