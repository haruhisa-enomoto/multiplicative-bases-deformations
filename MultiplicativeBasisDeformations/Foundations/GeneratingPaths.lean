import MultiplicativeBasisDeformations.Foundations.ActiveZero

/-!
# Lemma 8.14: generating rays have no radical factorization

`lem:generating-paths` (`local-ray-geometry.tex`), first assertion: a generating ray
in a Hom of dimension at least two does not factor as `a q_y b` through a nonidentity local
radical.
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

/-- A generating ray is not of the form `q^i g q^j` with `(i, j) ≠ (0, 0)` for a ray `g` of
its Hom. -/
theorem gen_not_inU_strict {f g : R} (hf : S.IsGen f) (h1 : S.P.src g = S.P.src f)
    (h2 : S.P.tgt g = S.P.tgt f) (hU : S.InU f g) : f = g := by
  have hgf := hf g h1 h2
  exact S.inU_antisymm hU hgf

/-- A Hom of dimension at least two: its generating ray is moved by an endpoint radical. -/
def Dim2 (f : R) : Prop := S.q (S.P.src f) * ⌜f⌝ ≠ 0 ∨ ⌜f⌝ * S.q (S.P.tgt f) ≠ 0

/-- Left factorization through a radical of the source. -/
theorem gen_ne_q_mul {f b : R} (hf : S.IsGen f) (hb1 : S.P.src b = S.P.src f)
    (hb2 : S.P.tgt b = S.P.tgt f) (i : ℕ) (hi : 1 ≤ i) :
    ⌜f⌝ ≠ S.q (S.P.src f) ^ i * ⌜b⌝ := by
  intro h
  have hU : S.InU f b := ⟨i, 0, by rw [h, hb1, pow_zero, mul_one]⟩
  have := S.gen_not_inU_strict hf hb1 hb2 hU
  subst this
  have hq : S.q (S.P.src f) ^ i ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [h, h0, zero_mul])
  have hqq : S.q (S.P.src f) ≠ 0 := fun h0 ↦ hq (by rw [h0, zero_pow (by omega)])
  have := congrArg (fun a ↦ S.P.deg (S.wtM a)) h
  change S.P.deg (S.P.wt f) = S.P.deg (S.wtM (S.q (S.P.src f) ^ i * ⌜f⌝)) at this
  rw [S.wtM_mul _ _ (h ▸ S.rr_ne f), S.wtM_qpow _ _ hq, map_add, map_nsmul, nsmul_eq_mul] at this
  have hd := S.χ_deg_pos _ hqq
  have : (0 : ℤ) < i * S.P.deg (S.χ (S.P.src f)) := by positivity
  change S.P.deg (S.P.wt f) = _ + S.P.deg (S.P.wt f) at *
  linarith

/-- Right factorization through a radical of the target. -/
theorem gen_ne_mul_q {f b : R} (hf : S.IsGen f) (hb1 : S.P.src b = S.P.src f)
    (hb2 : S.P.tgt b = S.P.tgt f) (j : ℕ) (hj : 1 ≤ j) :
    ⌜f⌝ ≠ ⌜b⌝ * S.q (S.P.tgt f) ^ j := by
  intro h
  have hU : S.InU f b := ⟨0, j, by rw [h, hb2, pow_zero, one_mul]⟩
  have := S.gen_not_inU_strict hf hb1 hb2 hU
  subst this
  have hq : S.q (S.P.tgt f) ^ j ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [h, h0, mul_zero])
  have hqq : S.q (S.P.tgt f) ≠ 0 := fun h0 ↦ hq (by rw [h0, zero_pow (by omega)])
  have := congrArg (fun a ↦ S.P.deg (S.wtM a)) h
  change S.P.deg (S.P.wt f) = S.P.deg (S.wtM (⌜f⌝ * S.q (S.P.tgt f) ^ j)) at this
  rw [S.wtM_mul _ _ (h ▸ S.rr_ne f), S.wtM_qpow _ _ hq, map_add, map_nsmul, nsmul_eq_mul] at this
  have hd := S.χ_deg_pos _ hqq
  have : (0 : ℤ) < j * S.P.deg (S.χ (S.P.tgt f)) := by positivity
  change S.P.deg (S.P.wt f) = S.P.deg (S.P.wt f) + _ at *
  linarith

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.14**, first assertion (`lem:generating-paths`): a generating ray of a Hom of
dimension at least two has no factorization `a q_y b` through a nonidentity local radical. -/
theorem gen_no_rad (hfin : IsRepresentationFinite k (S.P.Lin k)) {f a b : R} (hf : S.IsGen f)
    (hd : S.Dim2 f) (h : ⌜a⌝ * S.q (S.P.tgt a) * ⌜b⌝ = ⌜f⌝) : False := by
  have hab : ⌜a⌝ * S.q (S.P.tgt a) ≠ 0 := fun h0 ↦ S.rr_ne f (by rw [← h, h0, zero_mul])
  obtain ⟨a', ha'⟩ := S.mul_left_ray hab
  have hmid : S.P.tgt a = S.P.src b := by
    have hU : S.InU a' a := ⟨0, 1, by rw [← ha', pow_zero, one_mul, pow_one]⟩
    rw [← (S.inU_endpoints hU).2.1]
    exact S.src_of_mul_ne (show ⌜a'⌝ * ⌜b⌝ ≠ 0 by rw [← ha', h]; exact S.rr_ne f)
  obtain ⟨f1, f2, -, -⟩ := S.prod_of (show ⌜a'⌝ * ⌜b⌝ = ⌜f⌝ by rw [← ha', h])
  have hU' : S.InU a' a := ⟨0, 1, by rw [← ha', pow_zero, one_mul, pow_one]⟩
  have hfa : S.P.src f = S.P.src a := by rw [f1, (S.inU_endpoints hU').1]
  have hfb : S.P.tgt f = S.P.tgt b := f2
  -- the Hom of `a`
  obtain ⟨ga, ga1, ga2, hga⟩ := S.exists_gen a
  have haL : ¬ S.CycL ga := by
    intro hL
    rcases S.tgt_action_of_cycL hL ga1.symm ga2.symm with h0 | ⟨c, hc, h0⟩
    · exact hab h0
    · have hab' : ⌜a⌝ * ⌜b⌝ ≠ 0 := fun h' ↦ S.rr_ne f (by
        rw [← h, h0, mul_assoc, h', mul_zero])
      obtain ⟨t, ht⟩ := S.ray_of_mul_ne hab'
      obtain ⟨t1, t2, -, -⟩ := S.prod_of ht
      apply S.gen_ne_q_mul hf (b := t) (by rw [t1, hfa]) (by rw [t2, hfb]) c hc
      rw [← h, h0, mul_assoc, ht, hfa]
  have haR : S.CycR ga := (S.gen_cyc hga).resolve_left haL
  -- the Hom of `b`
  obtain ⟨gb, gb1, gb2, hgb⟩ := S.exists_gen b
  have hbR : ¬ S.CycR gb := by
    intro hR
    rcases S.src_action_of_cycR hR gb1.symm gb2.symm with h0 | ⟨c, hc, h0⟩
    · exact S.rr_ne f (by rw [← h, mul_assoc, hmid, h0, mul_zero])
    · have hab' : ⌜a⌝ * ⌜b⌝ ≠ 0 := fun h' ↦ S.rr_ne f (by
        rw [← h, mul_assoc, hmid, h0, ← mul_assoc, h', zero_mul])
      obtain ⟨t, ht⟩ := S.ray_of_mul_ne hab'
      obtain ⟨t1, t2, -, -⟩ := S.prod_of ht
      apply S.gen_ne_mul_q hf (b := t) (by rw [t1, hfa]) (by rw [t2, hfb]) c hc
      rw [← h, mul_assoc, hmid, h0, ← mul_assoc, ht, hfb]
  have hbL : S.CycL gb := (S.gen_cyc hgb).resolve_right hbR
  -- both Homs are generated only at the middle
  obtain ⟨i, hi⟩ := haR a ga1.symm ga2.symm
  obtain ⟨j, hj⟩ := hbL b gb1.symm gb2.symm
  have hg : S.P.tgt ga = S.P.src gb := by rw [ga2, hmid, gb1]
  have key : ⌜f⌝ = ⌜ga⌝ * S.q (S.P.tgt ga) ^ (i + 1 + j) * ⌜gb⌝ := by
    rw [← h, hi, hj, ← ga2, ← hg, pow_add, pow_add, pow_one]
    simp only [mul_assoc]
  by_cases hij : 2 ≤ i + 1 + j
  · exact S.rr_ne f (by rw [key, S.opposite_controls_high k hfin haR haL hbL hbR hg _ hij])
  · have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    have e1 := S.opposite_controls_src k hfin haR haL hbL hbR hg 1
    have e2 := S.opposite_controls_tgt k hfin haR haL hbL hbR hg 1
    have hga' : S.P.src ga = S.P.src f := by rw [ga1, ← hfa]
    have hgb' : S.P.tgt gb = S.P.tgt f := by rw [gb2, ← hfb]
    rw [show (0 : ℕ) + 1 + 0 = 1 from rfl] at key
    rw [← key, hga'] at e1
    rw [← key, hgb'] at e2
    rcases hd with hd | hd
    · exact hd e1
    · exact hd e2

end Sys

end RaySys

end MultiplicativeBasisDeformations
