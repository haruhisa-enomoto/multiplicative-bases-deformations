import MultiplicativeBasisDeformations.Foundations.CrownRows

/-!
# Lemma 9.3: two-sided factor paths

`integral-partial-lifts.tex` (`lem:two-sided-factor-paths`): "let `b` be a two-sided
ray. If `s` has type `L` and `bs` is nonzero and shiftable, then every ordinary path
representing `b` consists of two-sided arrows. Dually, the same conclusion holds if `r` has
type `R` and `rb` is nonzero and shiftable."

The proof of the first-arrow form (`first_TB`) uses only that the left factor is not an
identity, so every nonidentity left factor of `b` is two-sided (`leftFactor_TB`). For an
ordinary path `a₁ ⋯ aₙ` of `b` (`IsOrdPath`), all prefix products are therefore two-sided;
an arrow `aᵢ` between two two-sided prefixes has both endpoint actions nonzero, since a
two-sided ray commutes with `q̂`, so it is two-sided (`ordPath_TB`). The dual statement
follows by passing to `Sys.op` (`ordPath_TB'`).
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

variable {χ : L}

/-- **Every nonidentity left factor of `b` is two-sided** (the proof of `first_TB`). -/
theorem leftFactor_TB (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {b s t a w : R} (hb : S.TB χ b)
    (hs : S.TL χ s) (hbs : ⌜b⌝ * ⌜s⌝ = ⌜t⌝) (ht : S.Shift χ t) (ha0 : a ≠ S.P.e (S.P.src a))
    (hw : ⌜a⌝ * ⌜w⌝ = ⌜b⌝) : S.TB χ a := by
  have hTt := S.out_BL hχ hprim hb hs hbs ht
  obtain ⟨b1, -, -, -⟩ := S.prod_of hw
  have hqa : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
    intro h0; apply hb.2.1; rw [← hw, ← mul_assoc, b1, h0, zero_mul]
  obtain ⟨hsha, hsa⟩ := S.shift_of_qh_mul ha0 hqa
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
    rcases (S.table_B hχ hprim ha0 hw0 hw hb).1 with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hna
    · exact h1
  obtain ⟨-, hb1⟩ := S.shift_of_qh_mul hb.1.1 hb.2.1
  obtain ⟨-, hb2⟩ := S.shift_of_mul_qh hb.1.1 hb.2.2
  obtain ⟨t1, -, t3, -⟩ := S.prod_of hbs
  have hmid : ⌜a⌝ * (⌜w⌝ * S.qh χ (S.P.src s) * ⌜s⌝) ≠ 0 := by
    have : S.qh χ (S.P.src t) * ⌜t⌝ = ⌜a⌝ * (⌜w⌝ * S.qh χ (S.P.src s) * ⌜s⌝) := by
      rw [← hbs, t1, ← mul_assoc, hb1, ← hb2, ← t3, ← hw]; simp only [mul_assoc]
    rw [← this]; exact hTt.2.1
  have hwqs : ⌜w⌝ * S.qh χ (S.P.src s) * ⌜s⌝ ≠ 0 := fun h0 ↦ hmid (by rw [h0, mul_zero])
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

/-! ### Ordinary paths -/

/-- The product of a sequence of rays. -/
def pathM : List R → M S.P.toMult
  | [] => 1
  | a :: l => ⌜a⌝ * pathM l

theorem pathM_append (l l' : List R) : S.pathM (l ++ l') = S.pathM l * S.pathM l' := by
  induction l with
  | nil => simp [pathM]
  | cons a l ih => simp only [List.cons_append, pathM, ih, mul_assoc]

/-- **An ordinary path of `b`**: a nonempty sequence of ordinary arrows with product `b`. -/
def IsOrdPath (b : R) (l : List R) : Prop := l ≠ [] ∧ (∀ a ∈ l, S.Ord a) ∧ S.pathM l = ⌜b⌝

/-- A nonzero product of a nonempty sequence of nonidentity rays is a nonidentity ray. -/
theorem pathM_ray {l : List R} (hl : l ≠ []) (ho : ∀ a ∈ l, a ≠ S.P.e (S.P.src a))
    (h0 : S.pathM l ≠ 0) : ∃ c, S.pathM l = ⌜c⌝ ∧ c ≠ S.P.e (S.P.src c) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    by_cases hl' : l = []
    · subst hl'
      exact ⟨a, by simp [pathM], ho a (List.mem_cons_self ..)⟩
    · have h0' : S.pathM l ≠ 0 := fun h ↦ h0 (by simp only [pathM, h, mul_zero])
      obtain ⟨c, hc, hc0⟩ := ih hl' (fun b hb ↦ ho b (List.mem_cons_of_mem _ hb)) h0'
      have hac : ⌜a⌝ * ⌜c⌝ ≠ 0 := by simpa only [pathM, hc] using h0
      obtain ⟨d, hd⟩ := S.ray_of_mul_ne hac
      refine ⟨d, by simp only [pathM, hc, hd], ?_⟩
      obtain ⟨-, -, -, d4⟩ := S.prod_of hd
      apply S.ne_e_of_deg
      rw [d4, map_add]
      have := S.P.deg_pos a (ho a (List.mem_cons_self ..))
      have := S.P.deg_pos c hc0
      linarith

/-- **Lemma 9.3** (`lem:two-sided-factor-paths`): if `b` is two-sided and `bs` is nonzero and
shiftable with `s` left-sided, every ordinary path of `b` consists of two-sided arrows. -/
theorem ordPath_TB (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {b s t : R} (hb : S.TB χ b)
    (hs : S.TL χ s) (hbs : ⌜b⌝ * ⌜s⌝ = ⌜t⌝) (ht : S.Shift χ t) {l : List R}
    (hl : S.IsOrdPath b l) : ∀ a ∈ l, S.TB χ a := by
  obtain ⟨-, hord, hprod⟩ := hl
  have hne : ∀ a ∈ l, a ≠ S.P.e (S.P.src a) := fun a ha ↦ (hord a ha).1
  -- prefixes are two-sided
  have hpre : ∀ p q : List R, p ≠ [] → p ++ q = l →
      ∃ c, S.pathM p = ⌜c⌝ ∧ S.TB χ c := by
    intro p q hp hpq
    have hb0 : S.pathM p * S.pathM q = ⌜b⌝ := by rw [← pathM_append, hpq, hprod]
    have hp0 : S.pathM p ≠ 0 := fun h ↦ S.rr_ne b (by rw [← hb0, h, zero_mul])
    obtain ⟨c, hc, hc0⟩ := S.pathM_ray hp (fun a ha ↦ hne a (hpq ▸ List.mem_append_left _ ha)) hp0
    refine ⟨c, hc, ?_⟩
    rcases S.elt_cases (S.pathM q) with hq | hq | ⟨w, hw⟩
    · rw [hc, hq, mul_one] at hb0; rw [S.rr_inj hb0]; exact hb
    · rw [hq, mul_zero] at hb0; exact absurd hb0.symm (S.rr_ne b)
    · rw [hc, hw] at hb0
      exact S.leftFactor_TB hχ hprim hb hs hbs ht hc0 hb0
  intro a ha
  obtain ⟨p, q, rfl⟩ := List.append_of_mem ha
  rcases List.eq_nil_or_concat p with rfl | ⟨p', x, rfl⟩
  · obtain ⟨c, hc, hcB⟩ := hpre [a] q (List.cons_ne_nil _ _) rfl
    simp only [pathM, mul_one] at hc
    rwa [S.rr_inj hc]
  · -- `c' = a₁ ⋯ x` and `c = c' a` are two-sided
    obtain ⟨c', hc', hc'B⟩ := hpre (p' ++ [x]) (a :: q) (by simp) (by simp [List.concat_eq_append])
    obtain ⟨c, hc, hcB⟩ := hpre (p' ++ [x] ++ [a]) q (by simp) (by simp [List.concat_eq_append])
    have hca : ⌜c'⌝ * ⌜a⌝ = ⌜c⌝ := by
      rw [← hc', ← hc, S.pathM_append (p' ++ [x]) [a]]
      simp only [pathM, mul_one]
    obtain ⟨e1, e2, e3, -⟩ := S.prod_of hca
    obtain ⟨-, hq1⟩ := S.shift_of_qh_mul hc'B.1.1 hc'B.2.1
    obtain ⟨-, hq2⟩ := S.shift_of_mul_qh hc'B.1.1 hc'B.2.2
    have hl : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
      intro h0
      apply hcB.2.1
      rw [← hca, e1, ← mul_assoc, hq1, ← hq2, mul_assoc, e3, h0, mul_zero]
    have hr : ⌜a⌝ * S.qh χ (S.P.tgt a) ≠ 0 := by
      intro h0
      apply hcB.2.2
      rw [← hca, e2, mul_assoc, h0, mul_zero]
    exact ⟨(S.shift_of_qh_mul (hne a (by simp)) hl).1, hl, hr⟩

/-- **Every nonidentity right factor of `b` is two-sided** (dual of `leftFactor_TB`). -/
theorem rightFactor_TB (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r b t a w : R} (hb : S.TB χ b)
    (hr : S.TR χ r) (hrb : ⌜r⌝ * ⌜b⌝ = ⌜t⌝) (ht : S.Shift χ t) (ha0 : a ≠ S.P.e (S.P.src a))
    (hw : ⌜w⌝ * ⌜a⌝ = ⌜b⌝) : S.TB χ a :=
  (S.op_TB a).1 (S.op.leftFactor_TB (a := a) (w := w) hχ hprim ((S.op_TB b).2 hb)
    ((S.op_TL r).2 hr)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hrb]) ((S.op_shift t).2 ht)
    (by change a ≠ S.P.e (S.P.tgt a); rw [S.ne_e_iff_op]; exact ha0)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw]))

/-- **Lemma 9.3, the dual**: if `b` is two-sided and `rb` is nonzero and shiftable with `r`
right-sided, every ordinary path of `b` consists of two-sided arrows. -/
theorem ordPath_TB' (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {r b t : R} (hb : S.TB χ b)
    (hr : S.TR χ r) (hrb : ⌜r⌝ * ⌜b⌝ = ⌜t⌝) (ht : S.Shift χ t) {l : List R}
    (hl : S.IsOrdPath b l) : ∀ a ∈ l, S.TB χ a := by
  obtain ⟨-, hord, hprod⟩ := hl
  have hne : ∀ a ∈ l, a ≠ S.P.e (S.P.src a) := fun a ha ↦ (hord a ha).1
  -- suffixes are two-sided
  have hsuf : ∀ p q : List R, q ≠ [] → p ++ q = l →
      ∃ c, S.pathM q = ⌜c⌝ ∧ S.TB χ c := by
    intro p q hq hpq
    have hb0 : S.pathM p * S.pathM q = ⌜b⌝ := by rw [← pathM_append, hpq, hprod]
    have hq0 : S.pathM q ≠ 0 := fun h ↦ S.rr_ne b (by rw [← hb0, h, mul_zero])
    obtain ⟨c, hc, hc0⟩ := S.pathM_ray hq (fun a ha ↦ hne a (hpq ▸ List.mem_append_right _ ha)) hq0
    refine ⟨c, hc, ?_⟩
    rcases S.elt_cases (S.pathM p) with hp | hp | ⟨w, hw⟩
    · rw [hc, hp, one_mul] at hb0; rw [S.rr_inj hb0]; exact hb
    · rw [hp, zero_mul] at hb0; exact absurd hb0.symm (S.rr_ne b)
    · rw [hc, hw] at hb0
      exact S.rightFactor_TB hχ hprim hb hr hrb ht hc0 hb0
  intro a ha
  obtain ⟨p, q, rfl⟩ := List.append_of_mem ha
  rcases q with _ | ⟨y, q'⟩
  · obtain ⟨c, hc, hcB⟩ := hsuf p [a] (List.cons_ne_nil _ _) rfl
    simp only [pathM, mul_one] at hc
    rwa [S.rr_inj hc]
  · obtain ⟨c', hc', hc'B⟩ := hsuf (p ++ [a]) (y :: q') (by simp) (by simp)
    obtain ⟨c, hc, hcB⟩ := hsuf p (a :: y :: q') (by simp) rfl
    have hca : ⌜a⌝ * ⌜c'⌝ = ⌜c⌝ := by
      rw [← hc', ← hc]; rfl
    obtain ⟨e1, e2, -, -⟩ := S.prod_of hca
    obtain ⟨-, hq1⟩ := S.shift_of_qh_mul hc'B.1.1 hc'B.2.1
    obtain ⟨-, hq2⟩ := S.shift_of_mul_qh hc'B.1.1 hc'B.2.2
    obtain ⟨-, -, e3, -⟩ := S.prod_of hca
    have hl : S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
      intro h0
      apply hcB.2.1
      rw [← hca, e1, ← mul_assoc, h0, zero_mul]
    have hr' : ⌜a⌝ * S.qh χ (S.P.tgt a) ≠ 0 := by
      intro h0
      apply hcB.2.2
      rw [← hca, e2, mul_assoc, hq2, ← hq1, ← mul_assoc, ← e3, h0, zero_mul]
    exact ⟨(S.shift_of_qh_mul (hne a (by simp)) hl).1, hl, hr'⟩

end Sys

end RaySys

end MultiplicativeBasisDeformations
