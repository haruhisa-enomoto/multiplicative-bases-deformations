import MultiplicativeBasisDeformations.Foundations.PrimitiveCorners
import MultiplicativeBasisDeformations.Foundations.ContourTrees

/-!
# Ordinary arrows and one-sided generating contours

`def:generating-rays`(3), the path part of `lem:generating-paths`, and
`prop:controlled-contours` (`primitive-ray-equations.tex`, Appendix C.1 in
`local-ray-restrictions.tex`).

An ordinary path for a ray `f` starts with an ordinary left divisor of `f`, and every
ordinary left divisor starts such a path. We prove `prop:controlled-contours` in the form
used by `lem:one-sided-path-coefficients`: a generating ray of type `L` has exactly one
ordinary left divisor (all its ordinary paths start with the same arrow), and dually for
type `R`. The proof is that of Appendix C.1 applied to two paths with distinct first
(respectively last) arrows: the crown and the six-point tree fix their types, and the
six-lift and eight-lift trees exclude the remaining case.
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

/-- An ordinary arrow (`def:generating-rays`(3)). -/
def Ord (a : R) : Prop :=
  a ≠ S.P.e (S.P.src a) ∧
    ∀ r s : R, r ≠ S.P.e (S.P.src r) → s ≠ S.P.e (S.P.src s) → ⌜r⌝ * ⌜s⌝ ≠ ⌜a⌝

/-- An ordinary left divisor: the first arrow of an ordinary path of `f`. -/
def OL (f a : R) : Prop := S.Ord a ∧ ∃ w, ⌜a⌝ * ⌜w⌝ = ⌜f⌝

/-- An ordinary right divisor: the last arrow of an ordinary path of `f`. -/
def OR (f b : R) : Prop := S.Ord b ∧ ∃ w, ⌜w⌝ * ⌜b⌝ = ⌜f⌝

theorem ne_e_of_deg {r : R} (h : 0 < S.P.deg (S.P.wt r)) : r ≠ S.P.e (S.P.src r) := by
  intro h'; rw [h', S.P.wt_e, map_zero] at h; exact lt_irrefl _ h

theorem deg_pos_of_ne_e {r : R} (h : r ≠ S.P.e (S.P.src r)) : 0 < S.P.deg (S.P.wt r) :=
  S.P.deg_pos r h

/-- **Every nonidentity ray has an ordinary left divisor.** -/
theorem exists_OL (f : R) (hf : f ≠ S.P.e (S.P.src f)) : ∃ a, S.OL f a := by
  induction hn : (S.P.deg (S.P.wt f)).toNat using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    by_cases ho : S.Ord f
    · exact ⟨f, ho, S.P.e (S.P.tgt f), S.rr_mul_e f⟩
    · simp only [Ord, not_and, not_forall, not_not] at ho
      obtain ⟨r, s, hr, hs, hrs⟩ := ho hf
      obtain ⟨-, -, -, h4⟩ := S.prod_of hrs
      have hdr := S.P.deg_nonneg r
      have hds := S.P.deg_pos s hs
      obtain ⟨a, ha, w, hw⟩ := ih _ (by
        rw [← hn, h4, map_add]; omega) r hr rfl
      have hws : ⌜w⌝ * ⌜s⌝ ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [← hrs, ← hw, mul_assoc, h0, mul_zero])
      obtain ⟨w', hw'⟩ := S.ray_of_mul_ne hws
      exact ⟨a, ha, w', by rw [← hw', ← mul_assoc, hw, hrs]⟩

/-- Right multiplication by a local power keeps the endpoints of a ray. -/
theorem mul_qpow_endpoints {a a' : R} {x : V} {n : ℕ} (h : ⌜a⌝ * S.q x ^ n = ⌜a'⌝) :
    S.P.src a' = S.P.src a ∧ S.P.tgt a' = S.P.tgt a := by
  induction n generalizing a' with
  | zero => rw [pow_zero, mul_one] at h; rw [S.rr_inj h]; exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hne : ⌜a⌝ * S.q x ^ n * S.q x ≠ 0 := by rw [mul_assoc, ← pow_succ, h]; exact S.rr_ne _
    have hne1 : ⌜a⌝ * S.q x ^ n ≠ 0 := fun h0 ↦ hne (by rw [h0, zero_mul])
    have hqx : S.q x ≠ 0 := fun h0 ↦ hne (by rw [h0, mul_zero])
    obtain ⟨a'', ha''⟩ := S.mul_left_ray hne1
    obtain ⟨q0, hq0, q01, q02, -⟩ := (S.q_cases x).resolve_left hqx
    replace hq0 : S.q x = ⌜q0⌝ := hq0
    have e := ih ha''
    have h2 : ⌜a''⌝ * ⌜q0⌝ = ⌜a'⌝ := by rw [← ha'', ← hq0, mul_assoc, ← pow_succ, h]
    obtain ⟨p1, p2, p3, -⟩ := S.prod_of h2
    exact ⟨p1.trans e.1, by rw [p2, q02, ← q01, ← p3, e.2]⟩

/-- Left multiplication by a local power keeps the endpoints of a ray. -/
theorem qpow_mul_endpoints {b b' : R} {x : V} {n : ℕ} (h : S.q x ^ n * ⌜b⌝ = ⌜b'⌝) :
    S.P.src b' = S.P.src b ∧ S.P.tgt b' = S.P.tgt b := by
  induction n generalizing b' with
  | zero => rw [pow_zero, one_mul] at h; rw [S.rr_inj h]; exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hne : S.q x * (S.q x ^ n * ⌜b⌝) ≠ 0 := by rw [← mul_assoc, ← pow_succ', h]; exact S.rr_ne _
    have hne1 : S.q x ^ n * ⌜b⌝ ≠ 0 := fun h0 ↦ hne (by rw [h0, mul_zero])
    have hqx : S.q x ≠ 0 := fun h0 ↦ hne (by rw [h0, zero_mul])
    obtain ⟨b'', hb''⟩ := S.mul_right_ray hne1
    obtain ⟨q0, hq0, q01, q02, -⟩ := (S.q_cases x).resolve_left hqx
    replace hq0 : S.q x = ⌜q0⌝ := hq0
    have e := ih hb''
    have h2 : ⌜q0⌝ * ⌜b''⌝ = ⌜b'⌝ := by rw [← hb'', ← hq0, ← mul_assoc, ← pow_succ', h]
    obtain ⟨p1, p2, p3, -⟩ := S.prod_of h2
    exact ⟨by rw [p1, q01, ← q02, p3, e.1], p2.trans e.2⟩

/-- A generating local ray is an identity. -/
theorem gen_loop_e {m : R} (hm : S.IsGen m) (hl : S.P.src m = S.P.tgt m) :
    m = S.P.e (S.P.src m) := by
  have hU := hm (S.P.e (S.P.src m)) (S.P.src_e _) (by rw [S.P.tgt_e, hl])
  have := (S.deg_le_of_inU hU).1
  rw [S.P.wt_e, map_zero] at this
  exact S.eq_e_of_deg_zero (le_antisymm this (S.P.deg_nonneg m))

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.14, path part** (`lem:generating-paths`): every factor of a generating ray in
a Hom of dimension at least two is generating. -/
theorem gen_factor (hfin : IsRepresentationFinite k (S.P.Lin k)) {f a m b : R}
    (hf : S.IsGen f) (hd : S.Dim2 f) (h : ⌜a⌝ * ⌜m⌝ * ⌜b⌝ = ⌜f⌝) : S.IsGen m := by
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen m
  obtain ⟨i, j, hij⟩ := hg m g1.symm g2.symm
  have ham : ⌜a⌝ * ⌜m⌝ ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [← h, h0, zero_mul])
  have hmb : ⌜m⌝ * ⌜b⌝ ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [← h, mul_assoc, h0, mul_zero])
  have hta : S.P.tgt a = S.P.src g := by rw [S.src_of_mul_ne ham, g1]
  have hsb : S.P.src b = S.P.tgt g := by rw [← S.src_of_mul_ne hmb, g2]
  rw [hij] at h
  have hi : i = 0 := by
    by_contra hi
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hA : ⌜a⌝ * S.q (S.P.src g) ^ i' ≠ 0 := by
      intro h0; apply S.rr_ne f; rw [← h, pow_succ]; simp only [← mul_assoc]; rw [h0]; simp
    obtain ⟨a', ha'⟩ := S.mul_left_ray hA
    have hB : ⌜g⌝ * (S.q (S.P.tgt g) ^ j * ⌜b⌝) ≠ 0 := by
      intro h0; apply S.rr_ne f; rw [← h, pow_succ]; simp only [mul_assoc] at h0 ⊢; rw [h0]; simp
    obtain ⟨b', hb'⟩ := S.mul_left_ray hB
    have e := S.mul_qpow_endpoints ha'
    apply S.gen_no_rad k hfin hf hd (a := a') (b := b')
    rw [e.2, hta, ← ha', ← hb', ← h, pow_succ]
    simp only [mul_assoc]
  have hj : j = 0 := by
    by_contra hj
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hA : ⌜a⌝ * (S.q (S.P.src g) ^ i * ⌜g⌝ * S.q (S.P.tgt g) ^ j') ≠ 0 := by
      intro h0; apply S.rr_ne f; rw [← h, pow_succ]; simp only [← mul_assoc] at h0 ⊢; rw [h0]; simp
    obtain ⟨a', ha'⟩ := S.mul_left_ray hA
    have e : S.P.tgt a' = S.P.tgt g := by
      subst hi
      rw [pow_zero, one_mul] at ha'
      have hA' : ⌜a⌝ * ⌜g⌝ ≠ 0 := fun h0 ↦ hA (by rw [pow_zero, one_mul, ← mul_assoc, h0, zero_mul])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hA'
      rw [← mul_assoc, hc] at ha'
      rw [(S.mul_qpow_endpoints ha').2, (S.prod_of hc).2.1]
    apply S.gen_no_rad k hfin hf hd (a := a') (b := b)
    rw [e, ← ha', ← h, pow_succ]
    simp only [mul_assoc]
  subst hi hj
  rw [pow_zero, pow_zero, one_mul, mul_one] at hij
  rw [S.rr_inj hij]; exact hg

/-- **Lemma 8.14, vertex-simplicity**: a generating ray in a Hom of dimension at least two has
no local nonidentity factor. -/
theorem no_loop_factor (hfin : IsRepresentationFinite k (S.P.Lin k)) {f a m b : R}
    (hf : S.IsGen f) (hd : S.Dim2 f) (h : ⌜a⌝ * ⌜m⌝ * ⌜b⌝ = ⌜f⌝) (hl : S.P.src m = S.P.tgt m) :
    m = S.P.e (S.P.src m) :=
  S.gen_loop_e (S.gen_factor k hfin hf hd h) hl

omit [IsAlgClosed k] in
/-- No ray lies `n χ` below a generating ray (start of Appendix C.1). -/
theorem no_below_gen {χ : L} (hχ : 0 < S.P.deg χ) {g r : R} (hg : S.IsGen g)
    (h1 : S.P.src r = S.P.src g) (h2 : S.P.tgt r = S.P.tgt g) (n : ℕ) (hn : 1 ≤ n)
    (hw : S.P.wt g = S.P.wt r + n • χ) : False := by
  have := (S.deg_le_of_inU (hg r h1 h2)).1
  rw [hw, map_add, map_nsmul, nsmul_eq_mul] at this
  have : (1 : ℤ) * S.P.deg χ ≤ n * S.P.deg χ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hχ.le
  linarith

/-! ### First arrows of a left-sided generating ray -/

omit [IsAlgClosed k] in
/-- Distinct ordinary arrows are incomparable. -/
theorem ord_not_rf {a1 a2 : R} (h1 : a1 ≠ S.P.e (S.P.src a1)) (h2 : S.Ord a2) (hne : a1 ≠ a2) :
    ¬ S.P.RF a1 a2 := by
  rw [S.rf_iff]; rintro ⟨v, hv⟩
  by_cases hve : v = S.P.e (S.P.src v)
  · apply hne
    have := S.src_of_mul_ne (by rw [hv]; exact S.rr_ne a2)
    rw [hve, ← this, S.rr_mul_e] at hv
    exact S.rr_inj hv
  · exact h2.2 a1 v h1 hve hv

omit [IsAlgClosed k] in
/-- The cofactor of an ordinary left divisor is not an identity when another one exists. -/
theorem ol_cofactor_ne {f a1 a2 w1 : R} (h1 : S.Ord a1) (h2 : S.OL f a2) (hne : a1 ≠ a2)
    (hw1 : ⌜a1⌝ * ⌜w1⌝ = ⌜f⌝) : w1 ≠ S.P.e (S.P.src w1) := by
  intro hw
  have hs := S.src_of_mul_ne (by rw [hw1]; exact S.rr_ne f)
  rw [hw, ← hs, S.rr_mul_e] at hw1
  have hf : a1 = f := S.rr_inj hw1
  subst hf
  obtain ⟨ho2, w2, hw2⟩ := h2
  by_cases hw2e : w2 = S.P.e (S.P.src w2)
  · apply hne
    have hs2 := S.src_of_mul_ne (by rw [hw2]; exact S.rr_ne a1)
    rw [hw2e, ← hs2, S.rr_mul_e] at hw2
    exact (S.rr_inj hw2).symm
  · exact h1.2 a2 w2 ho2.1 hw2e hw2

variable {χ : L}

omit [IsAlgClosed k] in
/-- A supporting source gives `q̂_x = q_x` and `ℓ(q_x) = χ`. -/
theorem supp_of_qh {x : V} {r : R} (h : S.qh χ x * ⌜r⌝ ≠ 0) : S.Supp χ x := by
  classical
  by_contra hs; exact h (by rw [S.qh_of_not_supp χ hs, zero_mul])

omit [IsAlgClosed k] in
theorem supp_of_qh' {x : V} {r : R} (h : ⌜r⌝ * S.qh χ x ≠ 0) : S.Supp χ x := by
  classical
  by_contra hs; exact h (by rw [S.qh_of_not_supp χ hs, mul_zero])

omit [IsAlgClosed k] in
/-- A local ray of character `χ` (primitive, positive) is the local generator. -/
theorem local_eq_q (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {v : R} (hl : S.P.src v = S.P.tgt v)
    (hw : S.P.wt v = χ) : ⌜v⌝ = S.q (S.P.src v) ∧ S.Supp χ (S.P.src v) := by
  obtain ⟨b, hb, hbw⟩ := S.local_eq v hl
  rw [hw] at hbw
  have hb1 : b = 1 := by
    have := hprim b _ hbw
    rcases Nat.lt_or_ge b 1 with h0 | h0
    · have : b = 0 := by omega
      subst this; rw [zero_smul] at hbw; rw [hbw, map_zero] at hχ; exact absurd hχ (lt_irrefl _)
    · omega
  subst hb1
  rw [pow_one, S.q_mul_e] at hb
  rw [one_smul] at hbw
  exact ⟨hb.symm, fun h0 ↦ S.rr_ne v (by rw [← hb, h0]), hbw.symm⟩

omit [IsAlgClosed k] in
/-- A left-sided ray has no target action of character `χ` hidden in its projective support:
`f v = q̂_x f` is impossible. -/
theorem no_hidden_target (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {f v : R} (hT : S.TL χ f)
    (hv : ⌜f⌝ * ⌜v⌝ = S.qh χ (S.P.src f) * ⌜f⌝) : False := by
  obtain ⟨hsh, h1, h2⟩ := hT
  obtain ⟨-, ht⟩ := S.shift_of_qh_mul hsh.1 h1
  obtain ⟨e1, e2, e3⟩ := S.succ_spec χ hsh
  rw [ht] at hv
  obtain ⟨-, v2, v3, v4⟩ := S.prod_of hv
  have hl : S.P.src v = S.P.tgt v := by rw [← v3, ← v2, e2]
  have hw : S.P.wt v = χ := by
    have := v4.symm.trans e3; exact add_left_cancel this
  obtain ⟨hq, hs⟩ := S.local_eq_q hχ hprim hl hw
  apply S.rr_ne (S.succ χ f)
  rw [← hv, ← h2, S.qh_of_supp χ (v3 ▸ hs), v3, hq]

omit [IsAlgClosed k] in
/-- A left-sided ray has no return `a v = q_x`. -/
theorem no_return_one (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {a v : R} (hT : S.TL χ a)
    (hv : ⌜a⌝ * ⌜v⌝ = S.q (S.P.src a)) : False := by
  obtain ⟨-, h1, h2⟩ := hT
  have hs := S.supp_of_qh h1
  rw [S.qh_of_supp χ hs] at h1
  have hava : ⌜a⌝ * (⌜v⌝ * ⌜a⌝) ≠ 0 := by rw [← mul_assoc, hv]; exact h1
  have hva : ⌜v⌝ * ⌜a⌝ ≠ 0 := fun h0 ↦ hava (by rw [h0, mul_zero])
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne hva
  obtain ⟨u1, u2, u3, u4⟩ := S.prod_of hu
  have hav : ⌜a⌝ * ⌜v⌝ ≠ 0 := by rw [hv]; exact fun h0 ↦ h1 (by rw [h0, zero_mul])
  obtain ⟨t, ht⟩ := S.ray_of_mul_ne hav
  obtain ⟨-, -, t3, t4⟩ := S.prod_of ht
  have hl : S.P.src u = S.P.tgt u := by rw [u1, u2, t3]
  have hw : S.P.wt u = χ := by
    rw [u4, add_comm, ← t4, ← hs.2]
    show _ = S.wtM (S.q (S.P.src a)); rw [← hv, ht, wtM_rr]
  obtain ⟨hq, hsu⟩ := S.local_eq_q hχ hprim hl hw
  apply h1
  rw [u1, ← t3] at hq hsu
  rw [← h2, S.qh_of_supp χ hsu, ← hq, ← hu, ← mul_assoc, hv]

omit [IsAlgClosed k] in
/-- A cross comparison `a_i h = q̂_x a_j` between first arrows of a left-sided ray. -/
theorem no_cross (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {f ai wi aj wj h : R}
    (hT : S.TL χ f) (hai : S.TL χ ai) (hai0 : ai ≠ S.P.e (S.P.src ai))
    (hwi0 : wi ≠ S.P.e (S.P.src wi)) (hwi : ⌜ai⌝ * ⌜wi⌝ = ⌜f⌝) (hwj : ⌜aj⌝ * ⌜wj⌝ = ⌜f⌝)
    (hsj : S.P.src aj = S.P.src f) (hh : ⌜ai⌝ * ⌜h⌝ = S.qh χ (S.P.src f) * ⌜aj⌝) : False := by
  have hT' := hT
  obtain ⟨hsh, h1, -⟩ := hT'
  obtain ⟨-, ht⟩ := S.shift_of_qh_mul hsh.1 h1
  obtain ⟨e1, e2, e3⟩ := S.succ_spec χ hsh
  have hm : ⌜ai⌝ * (⌜h⌝ * ⌜wj⌝) = ⌜S.succ χ f⌝ := by
    rw [← mul_assoc, hh, mul_assoc, hwj, ht]
  have hhw : ⌜h⌝ * ⌜wj⌝ ≠ 0 := fun h0 ↦ S.rr_ne (S.succ χ f) (by rw [← hm, h0, mul_zero])
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne hhw
  rw [hu] at hm
  obtain ⟨m1, m2, m3, m4⟩ := S.prod_of hm
  obtain ⟨w1, w2, w3, w4⟩ := S.prod_of hwi
  have hs1 : S.P.src u = S.P.src wi := by rw [← m3, w3]
  have hs2 : S.P.tgt u = S.P.tgt wi := by rw [← m2, e2, w2]
  have hs3 : S.P.wt u = S.P.wt wi + χ := by
    have := m4.symm.trans (e3.trans (by rw [w4]))
    rw [add_assoc] at this; exact add_left_cancel this
  have hshw : S.Shift χ wi := ⟨hwi0, u, hs1, hs2, hs3⟩
  have hER : S.ER χ ai wi f := ⟨hshw, by rw [← S.eq_succ χ hshw hs1 hs2 hs3, hm]⟩
  rcases S.table_L hχ hprim hai0 hwi0 hwi hT with ⟨-, -, hn⟩ | ⟨hB, -⟩
  · exact hn hER
  · exact hB.2.2 hai.2.2

/-- **Two distinct first arrows of a left-sided generating ray** (Appendix C.1, first step):
one is left-sided and the other two-sided. -/
theorem first_arrow_types (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f a1 a2 : R} (hf : S.IsGen f) (hT : S.TL χ f) (h1 : S.OL f a1)
    (h2 : S.OL f a2) (hne : a1 ≠ a2) :
    (S.TL χ a1 ∧ S.TB χ a2) ∨ (S.TB χ a1 ∧ S.TL χ a2) := by
  set x := S.P.src f with hx
  have hT' := hT
  obtain ⟨hsh, hqf, -⟩ := hT'
  have hs := S.supp_of_qh hqf
  have hqx : S.qh χ x = S.q x := S.qh_of_supp χ hs
  have hd : S.Dim2 f := Or.inl (by rw [← hqx]; exact hqf)
  have hqx0 : S.q x ≠ 0 := hs.1
  obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases x).resolve_left hqx0
  replace hq0 : S.q x = ⌜q0⌝ := hq0
  obtain ⟨o1, w1, hw1⟩ := h1
  obtain ⟨o2, w2, hw2⟩ := h2
  have hw10 := S.ol_cofactor_ne o1 ⟨o2, w2, hw2⟩ hne hw1
  have hw20 := S.ol_cofactor_ne o2 ⟨o1, w1, hw1⟩ (Ne.symm hne) hw2
  obtain ⟨s1, -, -, d1⟩ := S.prod_of hw1
  obtain ⟨s2, -, -, d2⟩ := S.prod_of hw2
  -- surviving source actions
  have hqa : ∀ {a w : R}, ⌜a⌝ * ⌜w⌝ = ⌜f⌝ → S.P.src f = S.P.src a →
      S.qh χ (S.P.src a) * ⌜a⌝ ≠ 0 := by
    intro a w h e h0; apply hqf; rw [← h, ← mul_assoc, e, h0, zero_mul]
  have hq1 := hqa hw1 s1
  have hq2 := hqa hw2 s2
  obtain ⟨sh1, hs1⟩ := S.shift_of_qh_mul o1.1 hq1
  obtain ⟨sh2, hs2⟩ := S.shift_of_qh_mul o2.1 hq2
  rw [← s1] at hq1 hs1
  rw [← s2] at hq2 hs2
  -- first arrows are not local
  have hnl : ∀ {a w : R}, S.Ord a → ⌜a⌝ * ⌜w⌝ = ⌜f⌝ → S.P.src a ≠ S.P.tgt a := by
    intro a w ho h hl
    apply ho.1
    exact S.no_loop_factor k hfin hf hd (a := S.P.e (S.P.src a)) (b := w)
      (by rw [S.e_mul_rr, h]) hl
  have hdeg := fun r : R ↦ S.P.deg_nonneg r
  have hdw1 := S.P.deg_pos w1 hw10
  have hdw2 := S.P.deg_pos w2 hw20
  have hdq0 : 0 < S.P.deg (S.P.wt q0) := S.P.deg_pos q0 (by rw [q01]; exact q03)
  have ndeg : ∀ a b : R, S.P.deg (S.P.wt b) < S.P.deg (S.P.wt a) → ¬ S.P.RF a b :=
    fun a b hlt hab ↦ absurd (S.rf_deg_le hab) (not_le.2 hlt)
  by_cases hB1 : ⌜a1⌝ * S.qh χ (S.P.tgt a1) = 0 <;> by_cases hB2 : ⌜a2⌝ * S.qh χ (S.P.tgt a2) = 0
  · -- both left-sided: the six-point tree
    exfalso
    have hL1 : S.TL χ a1 := ⟨sh1, s1 ▸ hq1, hB1⟩
    have hL2 : S.TL χ a2 := ⟨sh2, s2 ▸ hq2, hB2⟩
    rw [hqx, hq0] at hs1 hs2
    obtain ⟨u1, -, -, du1⟩ := S.prod_of hs1
    obtain ⟨u2, -, -, du2⟩ := S.prod_of hs2
    have hq0e : ⌜S.P.e x⌝ * ⌜q0⌝ = ⌜q0⌝ := S.e_mul_rr' q0 q01
    set r : Fin 6 → R := ![S.P.e x, q0, a1, a2, S.succ χ a1, S.succ χ a2] with hr
    have hsrc : ∀ i, S.P.src (r i) = x := by
      intro i; fin_cases i
      · exact S.P.src_e x
      · exact q01
      · exact s1.symm
      · exact s2.symm
      · exact u1.trans q01
      · exact u2.trans q01
    have nret : ∀ {a w v : R}, S.TL χ a → ⌜a⌝ * ⌜w⌝ = ⌜f⌝ → S.P.src f = S.P.src a →
        ⌜a⌝ * ⌜v⌝ ≠ ⌜q0⌝ := by
      intro a w v hL h e hv
      exact S.no_return_one hχ hprim hL (by rw [hv, ← e, ← hq0])
    have nq0a : ∀ {a w : R}, S.Ord a → ⌜a⌝ * ⌜w⌝ = ⌜f⌝ → ¬ S.P.RF q0 a := by
      intro a w ho h
      have hnl' := hnl ho h
      refine S.ord_not_rf (by rw [q01]; exact q03) ho ?_
      rintro rfl; exact hnl' (by rw [q01, q02])
    have ncross : ∀ {ai wi aj wj : R}, S.TL χ ai → S.Ord ai → wi ≠ S.P.e (S.P.src wi) →
        ⌜ai⌝ * ⌜wi⌝ = ⌜f⌝ → ⌜aj⌝ * ⌜wj⌝ = ⌜f⌝ → S.P.src f = S.P.src aj →
        ⌜q0⌝ * ⌜aj⌝ = ⌜S.succ χ aj⌝ → ¬ S.P.RF ai (S.succ χ aj) := by
      intro ai wi aj wj hL ho hw0 hi hj ej hsj hr'
      rw [S.rf_iff] at hr'
      obtain ⟨h, hh⟩ := hr'
      exact S.no_cross hχ hprim hT hL ho.1 hw0 hi hj ej.symm
        (by rw [hh, ← hsj, hqx, hq0])
    have nsa : ∀ {ai aj wj : R}, ai ≠ S.P.e (S.P.src ai) → S.Ord aj → ⌜aj⌝ * ⌜wj⌝ = ⌜f⌝ →
        ⌜q0⌝ * ⌜ai⌝ = ⌜S.succ χ ai⌝ → ¬ S.P.RF (S.succ χ ai) aj := by
      intro ai aj wj hai0 ho hj hsa hr'
      rw [S.rf_iff] at hr'
      obtain ⟨v, hv⟩ := hr'
      rw [← hsa, mul_assoc] at hv
      have hav : ⌜ai⌝ * ⌜v⌝ ≠ 0 := fun h0 ↦ S.rr_ne aj (by rw [← hv, h0, mul_zero])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hav
      rw [hc] at hv
      refine ho.2 q0 c (by rw [q01]; exact q03) ?_ hv
      apply S.ne_e_of_deg
      obtain ⟨-, -, -, h4⟩ := S.prod_of hc
      rw [h4, map_add]
      have := S.P.deg_pos ai hai0
      have := S.P.deg_nonneg v
      linarith
    have nss : ∀ {ai aj : R}, ¬ S.P.RF ai aj → ⌜q0⌝ * ⌜ai⌝ = ⌜S.succ χ ai⌝ →
        ⌜q0⌝ * ⌜aj⌝ = ⌜S.succ χ aj⌝ → ¬ S.P.RF (S.succ χ ai) (S.succ χ aj) := by
      intro ai aj n hi hj hr'
      rw [S.rf_iff] at hr'
      obtain ⟨v, hv⟩ := hr'
      rw [← hi, ← hj, mul_assoc] at hv
      have hav : ⌜ai⌝ * ⌜v⌝ ≠ 0 := fun h0 ↦ S.rr_ne (S.succ χ aj) (by rw [← hj, ← hv, h0, mul_zero])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hav
      rw [hc] at hv
      exact n ((S.rf_iff _ _).2 ⟨v, by rw [hc, S.cancel_left hv (by rw [hv, hj]; exact S.rr_ne _)]⟩)
    have rfe : ∀ {t : R}, S.P.src t = x → S.P.RF (S.P.e x) t :=
      fun {t} h ↦ (S.rf_iff _ _).2 ⟨t, S.e_mul_rr' t h⟩
    have da1 := S.P.deg_pos a1 o1.1
    have da2 := S.P.deg_pos a2 o2.1
    have n12 := S.ord_not_rf o1.1 o2 hne
    have n21 := S.ord_not_rf o2.1 o1 (Ne.symm hne)
    have e0 : S.P.deg (S.P.wt (S.P.e x)) = 0 := by rw [S.P.wt_e, map_zero]
    have m10 : ¬ S.P.RF q0 (S.P.e x) := ndeg _ _ (by rw [e0]; exact hdq0)
    have m20 : ¬ S.P.RF a1 (S.P.e x) := ndeg _ _ (by rw [e0]; exact da1)
    have m30 : ¬ S.P.RF a2 (S.P.e x) := ndeg _ _ (by rw [e0]; exact da2)
    have m40 : ¬ S.P.RF (S.succ χ a1) (S.P.e x) := ndeg _ _ (by rw [e0, du1, map_add]; linarith)
    have m50 : ¬ S.P.RF (S.succ χ a2) (S.P.e x) := ndeg _ _ (by rw [e0, du2, map_add]; linarith)
    have m41 : ¬ S.P.RF (S.succ χ a1) q0 := ndeg _ _ (by rw [du1, map_add]; linarith)
    have m51 : ¬ S.P.RF (S.succ χ a2) q0 := ndeg _ _ (by rw [du2, map_add]; linarith)
    have m42 : ¬ S.P.RF (S.succ χ a1) a1 := ndeg _ _ (by rw [du1, map_add]; linarith)
    have m53 : ¬ S.P.RF (S.succ χ a2) a2 := ndeg _ _ (by rw [du2, map_add]; linarith)
    have m12 := nq0a o1 hw1
    have m13 := nq0a o2 hw2
    have m21 : ¬ S.P.RF a1 q0 := fun h ↦ by
      obtain ⟨v, hv⟩ := (S.rf_iff _ _).1 h; exact nret hL1 hw1 s1 hv
    have m31 : ¬ S.P.RF a2 q0 := fun h ↦ by
      obtain ⟨v, hv⟩ := (S.rf_iff _ _).1 h; exact nret hL2 hw2 s2 hv
    have m24 := ncross hL1 o1 hw10 hw1 hw1 s1 hs1
    have m25 := ncross hL1 o1 hw10 hw1 hw2 s2 hs2
    have m34 := ncross hL2 o2 hw20 hw2 hw1 s1 hs1
    have m35 := ncross hL2 o2 hw20 hw2 hw2 s2 hs2
    have m43 := nsa o1.1 o2 hw2 hs1
    have m52 := nsa o2.1 o1 hw1 hs2
    have m45 := nss n12 hs1 hs2
    have m54 := nss n21 hs2 hs1
    have p01 : S.P.RF (S.P.e x) q0 := rfe q01
    have p02 : S.P.RF (S.P.e x) a1 := rfe s1.symm
    have p03 : S.P.RF (S.P.e x) a2 := rfe s2.symm
    have p04 : S.P.RF (S.P.e x) (S.succ χ a1) := rfe (u1.trans q01)
    have p05 : S.P.RF (S.P.e x) (S.succ χ a2) := rfe (u2.trans q01)
    have p14 : S.P.RF q0 (S.succ χ a1) := (S.rf_iff _ _).2 ⟨a1, hs1⟩
    have p15 : S.P.RF q0 (S.succ χ a2) := (S.rf_iff _ _).2 ⟨a2, hs2⟩
    apply S.P.six_false k hfin x r hsrc
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Tab.tSix] at hij <;> simp [r] <;>
        first | exact S.P.rf_refl _ | assumption
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [Tab.tSix] at hij <;> simp [r] <;> assumption
  · exact Or.inl ⟨⟨sh1, s1 ▸ hq1, hB1⟩, ⟨sh2, s2 ▸ hq2, hB2⟩⟩
  · exact Or.inr ⟨⟨sh1, s1 ▸ hq1, hB1⟩, ⟨sh2, s2 ▸ hq2, hB2⟩⟩
  · -- both two-sided: the four-point crown
    exfalso
    obtain ⟨-, ht1⟩ := S.shift_of_mul_qh o1.1 hB1
    obtain ⟨-, ht2⟩ := S.shift_of_mul_qh o2.1 hB2
    have hqf' : ⌜q0⌝ * ⌜f⌝ ≠ 0 := by rw [← hq0, ← hqx]; exact hqf
    obtain ⟨qf, hqfr⟩ := S.ray_of_mul_ne hqf'
    obtain ⟨c1, -, -, c4⟩ := S.prod_of hqfr
    have up : ∀ {a w : R}, ⌜a⌝ * ⌜w⌝ = ⌜f⌝ → S.qh χ x * ⌜a⌝ = ⌜S.succ χ a⌝ →
        ⌜a⌝ * S.qh χ (S.P.tgt a) = ⌜S.succ χ a⌝ → S.P.RF a qf := by
      intro a w h hl hr'
      have e : ⌜a⌝ * (S.qh χ (S.P.tgt a) * ⌜w⌝) = ⌜qf⌝ := by
        rw [← mul_assoc, hr', ← hl, mul_assoc, h, hqx, hq0, hqfr]
      have hne : S.qh χ (S.P.tgt a) * ⌜w⌝ ≠ 0 := fun h0 ↦ S.rr_ne qf (by rw [← e, h0, mul_zero])
      obtain ⟨v, hv⟩ := S.mul_right_ray hne
      exact (S.rf_iff _ _).2 ⟨v, by rw [← hv, e]⟩
    have dq := S.P.deg_pos a1 o1.1
    have dq' := S.P.deg_pos a2 o2.1
    apply S.P.crown_false k hfin x a1 a2 f qf ⟨s1.symm, s2.symm, rfl, by rw [c1, q01]⟩
      ((S.rf_iff _ _).2 ⟨w1, hw1⟩) (up hw1 hs1 ht1) ((S.rf_iff _ _).2 ⟨w2, hw2⟩) (up hw2 hs2 ht2)
      (S.ord_not_rf o1.1 o2 hne) (S.ord_not_rf o2.1 o1 (Ne.symm hne))
    · intro h
      obtain ⟨v, hv⟩ := (S.rf_iff _ _).1 h
      exact S.no_hidden_target hχ hprim hT (by rw [hv, ← hqfr, ← hq0, ← hqx])
    · exact ndeg _ _ (by rw [c4, map_add]; linarith)
    · exact ndeg _ _ (by rw [d1, map_add]; linarith)
    · exact ndeg _ _ (by rw [d2, map_add]; linarith)
    · exact ndeg _ _ (by rw [c4, d1, map_add, map_add]; linarith)
    · exact ndeg _ _ (by rw [c4, d2, map_add, map_add]; linarith)

/-! ### The opposite system -/

omit [IsAlgClosed k] in
theorem op_ord (a : R) : S.op.Ord a ↔ S.Ord a := by
  unfold Ord
  change (a ≠ S.P.e (S.P.tgt a) ∧ ∀ r s : R, r ≠ S.P.e (S.P.tgt r) → s ≠ S.P.e (S.P.tgt s) →
    S.op.rr r * S.op.rr s ≠ S.op.rr a) ↔ _
  simp only [S.ne_e_iff_op]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun r s hr hs h ↦ h2 s r hs hr ?_⟩
    rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, h]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun r s hr hs h ↦ h2 s r hs hr (S.P.toOp_injective ?_)⟩
    rw [Tab.toOp_mul]; exact h

omit [IsAlgClosed k] in
theorem op_OL (f a : R) : S.op.OL f a ↔ S.OR f a := by
  unfold OL OR
  rw [op_ord]
  constructor
  · rintro ⟨h1, w, hw⟩
    refine ⟨h1, w, S.P.toOp_injective ?_⟩
    rw [Tab.toOp_mul]; exact hw
  · rintro ⟨h1, w, hw⟩
    refine ⟨h1, w, ?_⟩
    rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw]

/-- **Two distinct last arrows of a right-sided generating ray**: one is right-sided and the
other two-sided (the dual of `first_arrow_types`). -/
theorem last_arrow_types (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f b1 b2 : R} (hf : S.IsGen f) (hT : S.TR χ f) (h1 : S.OR f b1)
    (h2 : S.OR f b2) (hne : b1 ≠ b2) :
    (S.TR χ b1 ∧ S.TB χ b2) ∨ (S.TB χ b1 ∧ S.TR χ b2) := by
  rcases S.op.first_arrow_types k (S.P.op_isRepresentationFinite k hfin) hχ hprim
    ((S.op_isGen_iff f).2 hf) ((S.op_TL f).2 hT) ((S.op_OL f b1).2 h1) ((S.op_OL f b2).2 h2)
    hne with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨(S.op_TL b1).1 a, (S.op_TB b2).1 b⟩
  · exact Or.inr ⟨(S.op_TB b1).1 a, (S.op_TL b2).1 b⟩

/-! ### Right-sided rays with two last arrows -/

omit [IsAlgClosed k] in
/-- An ordinary arrow is not a proper left multiple of another ray. -/
theorem ord_not_lf {a b : R} (ha : a ≠ S.P.e (S.P.src a)) (hb : S.Ord b) (hne : a ≠ b) :
    ¬ S.P.LF b a := by
  rw [S.lf_iff]; rintro ⟨v, hv⟩
  by_cases hve : v = S.P.e (S.P.src v)
  · apply hne
    have h0 := S.src_of_mul_ne (by rw [hv]; exact S.rr_ne b)
    rw [hve, S.P.tgt_e] at h0
    rw [hve, h0, S.e_mul_rr] at hv
    exact S.rr_inj hv
  · exact hb.2 v a hve ha hv

omit [IsAlgClosed k] in
theorem op_qh' (x : V) : S.op.qh χ x = S.P.toOp (S.qh χ x) := S.op_qh x

omit [IsAlgClosed k] in
/-- `eq:absent-source-action`: a right-sided ray has no hidden source action. -/
theorem no_hidden_source (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {f v : R} (hT : S.TR χ f)
    (hv : ⌜v⌝ * ⌜f⌝ = ⌜f⌝ * S.qh χ (S.P.tgt f)) : False := by
  apply S.op.no_hidden_target hχ hprim ((S.op_TL f).2 hT) (v := v)
  change S.P.toOp ⌜f⌝ * S.P.toOp ⌜v⌝ = S.op.qh χ (S.P.tgt f) * S.P.toOp ⌜f⌝
  rw [S.op_qh, ← Tab.toOp_mul, ← Tab.toOp_mul, hv]

omit [IsAlgClosed k] in
/-- The cofactor of an ordinary right divisor is not an identity when another one exists. -/
theorem or_cofactor_ne {f b1 b2 w1 : R} (h1 : S.Ord b1) (h2 : S.OR f b2) (hne : b1 ≠ b2)
    (hw1 : ⌜w1⌝ * ⌜b1⌝ = ⌜f⌝) : w1 ≠ S.P.e (S.P.src w1) := by
  have := S.op.ol_cofactor_ne ((S.op_ord b1).2 h1) ((S.op_OL f b2).2 h2) hne (w1 := w1)
    (by rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw1])
  change w1 ≠ S.P.e (S.P.tgt w1) at this
  rwa [S.ne_e_iff_op] at this

/-- **The right-sided case of Appendix C.1**: a right-sided generating ray has no two last
arrows of types `B` and `R`. With a primitive reverse of the two-sided arrow the six-lift
tree occurs; otherwise the eight-lift tree occurs. -/
theorem right_two_last (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f α β : R} (hf : S.IsGen f) (hT : S.TR χ f) (hα : S.OR f α)
    (hβ : S.OR f β) (hne : α ≠ β) (hαB : S.TB χ α) (hβR : S.TR χ β) : False := by
  obtain ⟨oα, γ, hγ⟩ := hα
  obtain ⟨oβ, η, hη⟩ := hβ
  have hγ0 := S.or_cofactor_ne oα ⟨oβ, η, hη⟩ hne hγ
  have hη0 := S.or_cofactor_ne oβ ⟨oα, γ, hγ⟩ (Ne.symm hne) hη
  obtain ⟨g1, g2, g3, g4⟩ := S.prod_of hγ
  obtain ⟨e1, e2, e3, e4⟩ := S.prod_of hη
  set x := S.P.src f with hx
  set z := S.P.tgt f with hz
  set y := S.P.src α with hy
  set t := S.P.src β with ht
  have hT' := hT
  obtain ⟨-, -, hzq⟩ := hT'
  have hsz := S.supp_of_qh' hzq
  have hqz : S.qh χ z = S.q z := S.qh_of_supp χ hsz
  obtain ⟨qz0, hqz0, qz1, qz2, qz3⟩ := (S.q_cases z).resolve_left hsz.1
  replace hqz0 : S.q z = ⌜qz0⌝ := hqz0
  have wqz : S.P.wt qz0 = χ := by
    rw [← hsz.2]; show _ = S.wtM (S.q z); rw [hqz0, wtM_rr]
  obtain ⟨-, hαL, hαR⟩ := hαB
  have hsy := S.supp_of_qh hαL
  obtain ⟨qy0, hqy0, qy1, qy2, qy3⟩ := (S.q_cases y).resolve_left hsy.1
  replace hqy0 : S.q y = ⌜qy0⌝ := hqy0
  have wqy : S.P.wt qy0 = χ := by
    rw [← hsy.2]; show _ = S.wtM (S.q y); rw [hqy0, wtM_rr]
  obtain ⟨-, haqL⟩ := S.shift_of_qh_mul oα.1 hαL
  obtain ⟨-, haqR⟩ := S.shift_of_mul_qh oα.1 hαR
  have α2 : S.P.tgt α = z := g2.symm
  have β2 : S.P.tgt β = z := e2.symm
  rw [S.qh_of_supp χ hsy, hqy0] at haqL
  rw [α2, hqz, hqz0] at haqR
  set aq := S.succ χ α with haq
  obtain ⟨-, -, hβz⟩ := hβR
  rw [β2, hqz, hqz0] at hβz
  obtain ⟨bq, hbq⟩ := S.ray_of_mul_ne hβz
  have hd : S.Dim2 f := Or.inr (by rw [← hqz]; exact hzq)
  have hfq : ⌜f⌝ * ⌜qz0⌝ ≠ 0 := by rw [← hqz0, ← hqz]; exact hzq
  have dγ := S.P.deg_pos γ hγ0
  have dη := S.P.deg_pos η hη0
  have dα := S.P.deg_pos α oα.1
  have dβ := S.P.deg_pos β oβ.1
  have dqy := S.P.deg_pos qy0 (by rw [qy1]; exact qy3)
  have dqz := S.P.deg_pos qz0 (by rw [qz1]; exact qz3)
  have hyz : y ≠ z := by
    intro e
    apply oα.1
    exact S.no_loop_factor k hfin hf hd (a := γ) (b := S.P.e z)
      (by rw [hγ]; exact S.rr_mul_e f) (by rw [α2]; exact e)
  have hne_e : ∀ {h : R}, S.P.src h = y → S.P.tgt h = z → h ≠ S.P.e (S.P.src h) := by
    intro h h1 h2 he; apply hyz; rw [← h1, ← h2]; nth_rewrite 2 [he]; rw [S.P.tgt_e]
  -- `eq:absent-source-action`
  have hab : ∀ u : R, ⌜u⌝ * ⌜f⌝ ≠ ⌜f⌝ * ⌜qz0⌝ := fun u h ↦
    S.no_hidden_source hχ hprim hT (by rw [h, ← hqz0, ← hqz])
  have hab2 : ∀ u w : R, ⌜u⌝ * ⌜w⌝ * ⌜f⌝ ≠ ⌜f⌝ * ⌜qz0⌝ := by
    intro u w h
    have huw : ⌜u⌝ * ⌜w⌝ ≠ 0 := fun h0 ↦ hfq (by rw [← h, h0, zero_mul])
    obtain ⟨c, hc⟩ := S.ray_of_mul_ne huw
    rw [hc] at h; exact hab c h
  have nbelow : ∀ h : R, S.P.src h = x → S.P.tgt h = z →
      S.P.wt h + S.P.wt qz0 = S.P.wt α + S.P.wt γ → False := by
    intro h h1 h2 hw
    exact S.no_below_gen hχ hf h1 h2 1 le_rfl (by rw [g4, one_smul, ← wqz, hw]; abel)
  have X1 : ∀ h, S.P.src h = y → S.P.tgt h = x → S.P.mul h γ ≠ some qy0 := by
    intro h h1 h2 hm
    have hm' := S.P.rr_mul_rr_eq_rr.2 hm
    apply hab2 γ h
    rw [← hγ]; simp only [mul_assoc]
    rw [← mul_assoc ⌜h⌝, hm', haqL, haqR]
  by_cases hrev : ∃ lam, S.PrimRev α lam
  · obtain ⟨lam, hl1, hl2⟩ := hrev
    rw [hqy0] at hl1
    rw [α2, hqz0] at hl2
    obtain ⟨-, l2, l3, -⟩ := S.prod_of hl1
    have l1 : S.P.src lam = z := by rw [← l3, α2]
    have l2' : S.P.tgt lam = y := by rw [← l2, qy2]
    have hζ0 : ⌜β⌝ * ⌜lam⌝ ≠ 0 := by
      intro h0; apply hβz; rw [← hl2, ← mul_assoc, h0, zero_mul]
    obtain ⟨ζ, hζ⟩ := S.ray_of_mul_ne hζ0
    have hbq2 : ⌜ζ⌝ * ⌜α⌝ = ⌜bq⌝ := by rw [← hζ, mul_assoc, hl2, hbq]
    have dl : 0 < S.P.deg (S.P.wt lam) := S.deg_pos_of_ne (by rw [l1, l2']; exact hyz.symm)
    refine S.P.s6_false (x := x) (y := y) (z := z) (t := t) g1.symm g3 rfl α2 l1 l2' rfl β2
      (S.P.rr_mul_rr_eq_rr.1 hγ) (S.P.rr_mul_rr_eq_rr.1 hl1) (S.P.rr_mul_rr_eq_rr.1 hl2)
      (S.P.rr_mul_rr_eq_rr.1 haqR) (S.P.rr_mul_rr_eq_rr.1 haqL) (S.P.rr_mul_rr_eq_rr.1 hζ)
      (S.P.rr_mul_rr_eq_rr.1 hbq) (S.P.rr_mul_rr_eq_rr.1 hbq2) dγ dα dl dβ X1 ?_ ?_ ?_ ?_ ?_
      k hfin
    · intro h h1 h2 hm
      have hm' := S.P.rr_mul_rr_eq_rr.2 hm
      have hhf : ⌜h⌝ * ⌜f⌝ = ⌜qz0⌝ := by rw [← hγ, ← mul_assoc, hm', hl2]
      exact hab2 f h (by rw [mul_assoc, hhf])
    · intro h h1 h2 hm
      have hm' := S.P.rr_mul_rr_eq_rr.2 hm
      have hhf : ⌜h⌝ * ⌜f⌝ = ⌜bq⌝ := by rw [← hγ, ← mul_assoc, hm', hbq2]
      exact hab2 η h (by rw [mul_assoc, hhf, ← hbq, ← mul_assoc, hη])
    · intro h h1 h2 hm
      exact S.ord_not_lf oα.1 oβ hne ((S.lf_iff _ _).2 ⟨h, S.P.rr_mul_rr_eq_rr.2 hm⟩)
    · intro h h1 h2 hw hm
      exact nbelow h h1 h2 hw
    · intro h h1 h2 hm
      exact S.ord_not_lf oβ.1 oα (Ne.symm hne) ((S.lf_iff _ _).2 ⟨h, S.P.rr_mul_rr_eq_rr.2 hm⟩)
  · -- no primitive reverse: the eight-lift tree
    have haq0 : ⌜aq⌝ ≠ 0 := S.rr_ne aq
    -- a reverse factorization through `α` would be primitive
    have rev1 : ∀ h : R, ⌜α⌝ * ⌜h⌝ = ⌜qy0⌝ → False := by
      intro h hm
      have hha : ⌜α⌝ * (⌜h⌝ * ⌜α⌝) ≠ 0 := by rw [← mul_assoc, hm, haqL]; exact haq0
      have hha' : ⌜h⌝ * ⌜α⌝ ≠ 0 := fun h0 ↦ hha (by rw [h0, mul_zero])
      obtain ⟨u, hu⟩ := S.ray_of_mul_ne hha'
      obtain ⟨u1, u2, u3, u4⟩ := S.prod_of hu
      obtain ⟨-, m2, m3, m4⟩ := S.prod_of hm
      have hl : S.P.src u = S.P.tgt u := by rw [u1, u2, ← m3, α2]
      have hw : S.P.wt u = χ := by rw [u4, add_comm, ← m4, wqy]
      obtain ⟨hq, -⟩ := S.local_eq_q hχ hprim hl hw
      exact hrev ⟨h, by rw [hm, hqy0], by rw [α2, hu, hq, u1, ← m3, α2]⟩
    have rev2 : ∀ h : R, ⌜h⌝ * ⌜α⌝ = ⌜qz0⌝ → False := by
      intro h hm
      have hha : ⌜α⌝ * ⌜h⌝ * ⌜α⌝ ≠ 0 := by rw [mul_assoc, hm, haqR]; exact haq0
      have hha' : ⌜α⌝ * ⌜h⌝ ≠ 0 := fun h0 ↦ hha (by rw [h0, zero_mul])
      obtain ⟨u, hu⟩ := S.ray_of_mul_ne hha'
      obtain ⟨u1, u2, u3, u4⟩ := S.prod_of hu
      obtain ⟨m1, -, m3, m4⟩ := S.prod_of hm
      have hl : S.P.src u = S.P.tgt u := by rw [u1, u2, m3]
      have hw : S.P.wt u = χ := by rw [u4, add_comm, ← m4, wqz]
      obtain ⟨hq, -⟩ := S.local_eq_q hχ hprim hl hw
      exact hrev ⟨h, by rw [hu, hq, u1], by rw [hm, α2, hqz0]⟩
    have hγq0 : ⌜γ⌝ * ⌜qy0⌝ ≠ 0 := by
      intro h0; apply hfq; rw [← hγ, mul_assoc, haqR, ← haqL, ← mul_assoc, h0, zero_mul]
    obtain ⟨γq, hγq⟩ := S.ray_of_mul_ne hγq0
    have hγqα : ⌜γq⌝ * ⌜α⌝ = ⌜f⌝ * ⌜qz0⌝ := by
      rw [← hγq, mul_assoc, haqL, ← haqR, ← mul_assoc, hγ]
    have γgen : S.IsGen γ := S.gen_factor k hfin hf hd (a := S.P.e x) (m := γ) (b := α)
      (by rw [S.e_mul_rr' γ g1.symm, hγ])
    -- `β q̂_z = h α` is excluded by a crown in the injective support at `z`
    have Y7 : ∀ h, S.P.src h = t → S.P.tgt h = y → S.P.mul h α ≠ some bq := by
      intro h h1 h2 hm
      have hm' := S.P.rr_mul_rr_eq_rr.2 hm
      obtain ⟨a1, -, -, a4⟩ := S.prod_of haqR
      obtain ⟨b1, b2, -, b4⟩ := S.prod_of hbq
      have ndeg : ∀ a b : R, S.P.deg (S.P.wt a) < S.P.deg (S.P.wt b) → ¬ S.P.op.RF b a :=
        fun a b hlt hab ↦ by
          obtain ⟨v, hv⟩ := (S.lf_iff _ _).1 ((S.op_rf_iff _ _).1 hab)
          have := congrArg S.P.deg (S.prod_of hv).2.2.2
          rw [map_add] at this
          have := S.P.deg_nonneg v
          linarith
      have lfo : ∀ {a b : R}, S.P.op.RF a b → ∃ v, ⌜v⌝ * ⌜a⌝ = ⌜b⌝ :=
        fun hr ↦ (S.lf_iff _ _).1 ((S.op_rf_iff _ _).1 hr)
      refine S.P.op.crown_false k (S.P.op_isRepresentationFinite k hfin) z qz0 α aq bq
        ⟨qz2, α2, by rw [S.P.op_src, (S.prod_of haqR).2.1, qz2], by rw [S.P.op_src, b2, qz2]⟩
        ((S.op_rf_iff _ _).2 ((S.lf_iff _ _).2 ⟨α, haqR⟩))
        ((S.op_rf_iff _ _).2 ((S.lf_iff _ _).2 ⟨β, hbq⟩))
        ((S.op_rf_iff _ _).2 ((S.lf_iff _ _).2 ⟨qy0, haqL⟩))
        ((S.op_rf_iff _ _).2 ((S.lf_iff _ _).2 ⟨h, hm'⟩)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro hr
        obtain ⟨v, hv⟩ := lfo hr
        obtain ⟨v1, -, v3, -⟩ := S.prod_of hv
        exact oα.2 v qz0 (hne_e v1.symm (by rw [v3, qz1])) (by rw [qz1]; exact qz3) hv
      · intro hr
        obtain ⟨v, hv⟩ := lfo hr
        exact rev2 v hv
      · intro hr
        obtain ⟨v, hv⟩ := lfo hr
        rw [← haqR, ← hbq, ← mul_assoc] at hv
        have hva : ⌜v⌝ * ⌜α⌝ ≠ 0 := fun h0 ↦ S.rr_ne bq (by rw [← hbq, ← hv, h0, zero_mul])
        obtain ⟨c, hc⟩ := S.ray_of_mul_ne hva
        rw [hc] at hv
        have := S.cancel_right hv (by rw [hv]; exact hβz)
        subst this
        exact S.ord_not_lf oα.1 oβ hne ((S.lf_iff _ _).2 ⟨v, hc⟩)
      · intro hr
        obtain ⟨v, hv⟩ := lfo hr
        rw [← haqR, ← hbq, ← mul_assoc] at hv
        have hvb : ⌜v⌝ * ⌜β⌝ ≠ 0 := fun h0 ↦ haq0 (by rw [← haqR, ← hv, h0, zero_mul])
        obtain ⟨c, hc⟩ := S.ray_of_mul_ne hvb
        rw [hc] at hv
        have := S.cancel_right hv (by rw [hv, haqR]; exact haq0)
        subst this
        exact S.ord_not_lf oβ.1 oα (Ne.symm hne) ((S.lf_iff _ _).2 ⟨v, hc⟩)
      · exact ndeg _ _ (by rw [a4, map_add]; linarith)
      · exact ndeg _ _ (by rw [a4, map_add]; linarith)
      · exact ndeg _ _ (by rw [b4, map_add]; linarith)
      · intro hr
        obtain ⟨v, hv⟩ := lfo hr
        rw [← hbq, ← mul_assoc] at hv
        have hvb : ⌜v⌝ * ⌜β⌝ ≠ 0 := fun h0 ↦ S.rr_ne α (by rw [← hv, h0, zero_mul])
        obtain ⟨c, hc⟩ := S.ray_of_mul_ne hvb
        rw [hc] at hv
        have dc : 0 < S.P.deg (S.P.wt c) := by
          rw [(S.prod_of hc).2.2.2, map_add]; have := S.P.deg_nonneg v; linarith
        exact oα.2 c qz0 (S.ne_e_of_deg dc) (by rw [qz1]; exact qz3) hv
    refine S.P.s8_false (x := x) (y := y) (z := z) (t := t) g1.symm g3 rfl α2 e1.symm e3 rfl β2
      qy1 qy2 qz1 qz2 (S.P.rr_mul_rr_eq_rr.1 hγq) (S.P.rr_mul_rr_eq_rr.1 hγ)
      (S.P.rr_mul_rr_eq_rr.1 hη) (S.P.rr_mul_rr_eq_rr.1 hbq) dγ dα dη dβ dqy dqz
      ?_ ?_ ?_ ?_ ?_ ?_ Y7 ?_ X1 ?_ ?_ k hfin
    · -- Y1
      intro h h1 h2 hm
      exact oα.2 qy0 h (by rw [qy1]; exact qy3) (hne_e h1 h2) (S.P.rr_mul_rr_eq_rr.2 hm)
    · -- Y2
      intro h h1 h2 hm
      exact rev1 h (S.P.rr_mul_rr_eq_rr.2 hm)
    · -- Y3
      intro h h1 h2 hm
      have hm' := S.P.rr_mul_rr_eq_rr.2 hm
      have e : ⌜γ⌝ * (⌜h⌝ * ⌜β⌝) = ⌜γ⌝ * ⌜α⌝ := by rw [← mul_assoc, hm', hη, hγ]
      have hhb : ⌜h⌝ * ⌜β⌝ ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [← hγ, ← e, h0, mul_zero])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hhb
      rw [hc] at e
      have := S.cancel_left e (by rw [e, hγ]; exact S.rr_ne f)
      subst this
      exact S.ord_not_lf oβ.1 oα (Ne.symm hne) ((S.lf_iff _ _).2 ⟨h, hc⟩)
    · -- Y4
      intro h h1 h2 hm
      have hm' := S.P.rr_mul_rr_eq_rr.2 hm
      have e : ⌜η⌝ * (⌜h⌝ * ⌜α⌝) = ⌜η⌝ * ⌜β⌝ := by rw [← mul_assoc, hm', hγ, hη]
      have hha : ⌜h⌝ * ⌜α⌝ ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [← hη, ← e, h0, mul_zero])
      obtain ⟨c, hc⟩ := S.ray_of_mul_ne hha
      rw [hc] at e
      have := S.cancel_left e (by rw [e, hη]; exact S.rr_ne f)
      subst this
      exact S.ord_not_lf oα.1 oβ hne ((S.lf_iff _ _).2 ⟨h, hc⟩)
    · -- Y5
      intro h h1 h2 hw hm
      exact S.no_below_gen hχ γgen (by rw [h1, g1]) (by rw [h2, g3]) 1 le_rfl
        (by rw [one_smul, ← wqy, ← hw])
    · -- Y6
      intro h h1 h2 hm
      exact rev2 h (S.P.rr_mul_rr_eq_rr.2 hm)
    · -- Y8
      intro h h1 h2 hm
      have hm' := S.P.rr_mul_rr_eq_rr.2 hm
      exact hab h (by rw [← hγ, ← mul_assoc, hm', hγqα, hγ])
    · -- Y10
      intro h h1 h2 hw hm
      exact nbelow h h1 h2 hw
    · -- Y11
      intro h h1 h2 hm
      exact oα.2 h qz0 (hne_e h1 h2) (by rw [qz1]; exact qz3) (S.P.rr_mul_rr_eq_rr.2 hm)

/-- **Proposition 9.10** (`prop:controlled-contours`), right-sided form: all ordinary paths
of a right-sided generating ray end with the same arrow. -/
theorem unique_last (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f b1 b2 : R} (hf : S.IsGen f) (hT : S.TR χ f) (h1 : S.OR f b1)
    (h2 : S.OR f b2) : b1 = b2 := by
  by_contra hne
  rcases S.last_arrow_types k hfin hχ hprim hf hT h1 h2 hne with ⟨a, b⟩ | ⟨a, b⟩
  · exact S.right_two_last k hfin hχ hprim hf hT h2 h1 (Ne.symm hne) b a
  · exact S.right_two_last k hfin hχ hprim hf hT h1 h2 hne a b

omit [IsAlgClosed k] in
theorem op_OR (f a : R) : S.op.OR f a ↔ S.OL f a := by
  unfold OL OR
  rw [op_ord]
  constructor
  · rintro ⟨h1, w, hw⟩
    refine ⟨h1, w, S.P.toOp_injective ?_⟩
    rw [Tab.toOp_mul]; exact hw
  · rintro ⟨h1, w, hw⟩
    refine ⟨h1, w, ?_⟩
    rw [op_rr, op_rr, op_rr, ← Tab.toOp_mul, hw]

/-- **Proposition 9.10**, left-sided form: all ordinary paths of a left-sided generating ray
start with the same arrow. -/
theorem unique_first (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ) {f a1 a2 : R} (hf : S.IsGen f) (hT : S.TL χ f) (h1 : S.OL f a1)
    (h2 : S.OL f a2) : a1 = a2 :=
  S.op.unique_last k (S.P.op_isRepresentationFinite k hfin) hχ hprim ((S.op_isGen_iff f).2 hf)
    ((S.op_TR f).2 hT) ((S.op_OR f a1).2 h1) ((S.op_OR f a2).2 h2)

end Sys

end RaySys

end MultiplicativeBasisDeformations
