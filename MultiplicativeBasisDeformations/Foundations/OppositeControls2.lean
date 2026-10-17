import MultiplicativeBasisDeformations.Foundations.OppositeControls
import MultiplicativeBasisDeformations.Foundations.BoundConfigs

/-!
# Lemma 8.11, Case 2 and the statement

Case 2 of `lem:opposite-controls` (`local-ray-geometry.tex:396–451`): `fg = 0` with
`f q², q² g ≠ 0` is excluded by the seven-object category with arrows
`u → c → d`, `u → u'`, `l → c → r`, `l_d → d` and the relation `l → c → r = 0`
(dimensions `3` at `c`, `2` at `u, d`, `1` elsewhere: `N = 22`, `D = 21`, `F = 1`).
Indices `0..6` are `u' u c d l r l_d`.
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

open PosetRep

/-- The table of the seven-object category. -/
def t7 : Fin 7 → Fin 7 → Bool := fun i j ↦
  i == j || (i.val == 1 && (j.val == 0 || j.val == 2 || j.val == 3 || j.val == 5)) ||
    (i.val == 2 && (j.val == 3 || j.val == 5)) || (i.val == 4 && (j.val == 2 || j.val == 3 || j.val == 5)) ||
    (i.val == 6 && j.val == 3)

instance : Fact (Ax t7) := ⟨by unfold Ax; decide⟩

theorem t7_uniq : UniqOK t7 := by unfold UniqOK; decide

theorem t7_count : ∑ i, (![1, 2, 3, 2, 1, 1, 1] : Fin 7 → ℕ) i ^ 2 +
    (![1, 2, 3, 2, 1, 1, 1] : Fin 7 → ℕ) 5 * (![1, 2, 3, 2, 1, 1, 1] : Fin 7 → ℕ) 4 ≤
      ∑ i, ∑ j, if covB t7 i j then (![1, 2, 3, 2, 1, 1, 1] : Fin 7 → ℕ) i *
        (![1, 2, 3, 2, 1, 1, 1] : Fin 7 → ℕ) j else 0 := by decide

theorem t7_cov42 : covB t7 4 2 = true := by decide

theorem t7_cov25 : covB t7 2 5 = true := by decide

section C2Conf

variable {b c a : V} {f g q0 fq q2 qg : R}
  (f1 : S.P.src f = b) (f2 : S.P.tgt f = c) (g1 : S.P.src g = c) (g2 : S.P.tgt g = a)
  (q01 : S.P.src q0 = c) (q02 : S.P.tgt q0 = c)
  (hfq : S.P.mul f q0 = some fq) (hq2 : S.P.mul q0 q0 = some q2)
  (hqg : S.P.mul q0 g = some qg) (hfg : S.P.mul f g = none)
  (hdf : 0 < S.P.deg (S.P.wt f)) (hdg : 0 < S.P.deg (S.P.wt g))
  (hdq : 0 < S.P.deg (S.P.wt q0))
  (X1 : ∀ h, S.P.src h = a → S.P.tgt h = c → S.P.mul g h ≠ some q0)
  (X2 : ∀ h, S.P.src h = a → S.P.tgt h = c → S.P.mul g h ≠ some q2)
  (X3 : ∀ h, S.P.src h = a → S.P.tgt h = a → S.P.mul g h ≠ some qg)
  (X4 : ∀ h, S.P.src h = c → S.P.tgt h = a → S.P.mul q0 h ≠ some g)
  (X5 : ∀ h, S.P.src h = c → S.P.tgt h = b → S.P.mul h f ≠ some q0)
  (X6 : ∀ h, S.P.src h = c → S.P.tgt h = b → S.P.mul h f ≠ some q2)
  (X7 : ∀ h, S.P.src h = b → S.P.tgt h = b → S.P.mul h f ≠ some fq)
  (X8 : ∀ h, S.P.src h = b → S.P.tgt h = c → S.P.mul h q0 ≠ some f)

/-- The objects. -/
def c2V (b c a : V) : Fin 7 → V := ![a, c, c, c, b, a, b]

/-- The weights. -/
def c2G (f g q0 : R) : Fin 7 → L :=
  ![S.P.wt g - S.P.wt q0, -S.P.wt q0, 0, S.P.wt q0, -S.P.wt f, S.P.wt g, S.P.wt q0 - S.P.wt f]

/-- The rays. -/
def c2ρ (b c a : V) (f g q0 fq q2 qg : R) : Fin 7 → Fin 7 → R :=
  ![![S.P.e a, S.P.e a, S.P.e a, S.P.e a, S.P.e a, S.P.e a, S.P.e a],
    ![g, S.P.e c, q0, q2, S.P.e a, qg, S.P.e a],
    ![S.P.e a, S.P.e a, S.P.e c, q0, S.P.e a, g, S.P.e a],
    ![S.P.e a, S.P.e a, S.P.e a, S.P.e c, S.P.e a, S.P.e a, S.P.e a],
    ![S.P.e a, S.P.e a, f, fq, S.P.e b, S.P.e a, S.P.e a],
    ![S.P.e a, S.P.e a, S.P.e a, S.P.e a, S.P.e a, S.P.e a, S.P.e a],
    ![S.P.e a, S.P.e a, S.P.e a, f, S.P.e a, S.P.e a, S.P.e b]]

set_option maxHeartbeats 1000000 in
include f1 g1 q01 hfq hq2 hqg in
theorem c2_src : ∀ i j, t7 i j = true → ¬ Tab.ZT t7 4 5 i j →
    S.P.src (S.c2ρ b c a f g q0 fq q2 qg i j) = c2V b c a i := by
  have e1 := S.P.mul_src _ _ _ hfq
  have e2 := S.P.mul_src _ _ _ hq2
  have e3 := S.P.mul_src _ _ _ hqg
  intro i j hij hz
  fin_cases i <;> fin_cases j <;> simp [t7] at hij hz <;>
    simp [c2V, c2ρ, S.P.src_e, e1, e2, e3, f1, g1, q01]

set_option maxHeartbeats 1000000 in
include f2 g2 q02 hfq hq2 hqg in
theorem c2_tgt : ∀ i j, t7 i j = true → ¬ Tab.ZT t7 4 5 i j →
    S.P.tgt (S.c2ρ b c a f g q0 fq q2 qg i j) = c2V b c a j := by
  have e1 := S.P.mul_tgt _ _ _ hfq
  have e2 := S.P.mul_tgt _ _ _ hq2
  have e3 := S.P.mul_tgt _ _ _ hqg
  intro i j hij hz
  fin_cases i <;> fin_cases j <;> simp [t7] at hij hz <;>
    simp [c2V, c2ρ, S.P.tgt_e, e1, e2, e3, f2, g2, q02]

set_option maxHeartbeats 1000000 in
include hfq hq2 hqg in
theorem c2_wt : ∀ i j, t7 i j = true → ¬ Tab.ZT t7 4 5 i j →
    S.P.wt (S.c2ρ b c a f g q0 fq q2 qg i j) = S.c2G f g q0 j - S.c2G f g q0 i := by
  have e1 := S.P.wt_mul _ _ _ hfq
  have e2 := S.P.wt_mul _ _ _ hq2
  have e3 := S.P.wt_mul _ _ _ hqg
  intro i j hij hz
  fin_cases i <;> fin_cases j <;> simp [t7] at hij hz <;>
    simp [c2G, c2ρ, S.P.wt_e, e1, e2, e3] <;> abel

theorem c2_e : ∀ i, S.c2ρ b c a f g q0 fq q2 qg i i = S.P.e (c2V b c a i) := by
  intro i; fin_cases i <;> rfl

set_option maxHeartbeats 2000000 in
include hfq hq2 hqg in
theorem c2_mul : ∀ i j l, t7 i j = true → t7 j l = true → i ≠ j → j ≠ l →
    ¬ Tab.ZT t7 4 5 i l →
    S.P.mul (S.c2ρ b c a f g q0 fq q2 qg i j) (S.c2ρ b c a f g q0 fq q2 qg j l) =
      some (S.c2ρ b c a f g q0 fq q2 qg i l) := by
  intro i j l h1 h2 h3 h4 hz
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [t7, Tab.ZT] at h1 h2 h3 h4 hz <;>
    simp [c2ρ, hfq, hq2, hqg]

set_option maxHeartbeats 2000000 in
include hfg in
theorem c2_mulZ : ∀ i j l, t7 i j = true → t7 j l = true → ¬ Tab.ZT t7 4 5 i j →
    ¬ Tab.ZT t7 4 5 j l → Tab.ZT t7 4 5 i l →
    S.P.mul (S.c2ρ b c a f g q0 fq q2 qg i j) (S.c2ρ b c a f g q0 fq q2 qg j l) = none := by
  intro i j l h1 h2 h3 h4 hz
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [t7, Tab.ZT] at h1 h2 h3 h4 hz <;>
    simp [c2ρ, hfg]

set_option maxHeartbeats 4000000 in
include hdf hdg hdq X1 X2 X3 X4 X5 X6 X7 X8 in
theorem c2_retL : ∀ i j l (h : R), covB t7 i j = true → t7 i l = true →
    ¬ Tab.ZT t7 4 5 i l → S.P.src h = c2V b c a j → S.P.tgt h = c2V b c a l →
    S.P.wt h = S.c2G f g q0 l - S.c2G f g q0 j →
    S.P.mul (S.c2ρ b c a f g q0 fq q2 qg i j) h = some (S.c2ρ b c a f g q0 fq q2 qg i l) →
    t7 j l = true := by
  intro i j l h hcv hil hz h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hil (by decide)
    | exact (hz (by decide)).elim
    | skip
  all_goals simp [c2V, c2G, c2ρ] at h1 h2 h3 hm
  all_goals first
    | exact (X1 h h1 h2 hm).elim
    | exact (X2 h h1 h2 hm).elim
    | exact (X3 h h1 h2 hm).elim
    | exact (X4 h h1 h2 hm).elim
    | exact (X5 h h1 h2 hm).elim
    | exact (X6 h h1 h2 hm).elim
    | exact (X7 h h1 h2 hm).elim
    | exact (X8 h h1 h2 hm).elim
    | (exfalso; have hd := S.P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)
    | skip

set_option maxHeartbeats 4000000 in
include hdf hdg hdq X1 X2 X3 X4 X5 X6 X7 X8 in
theorem c2_retR : ∀ i j l (h : R), covB t7 i j = true → t7 l j = true →
    ¬ Tab.ZT t7 4 5 l j → S.P.src h = c2V b c a l → S.P.tgt h = c2V b c a i →
    S.P.wt h = S.c2G f g q0 i - S.c2G f g q0 l →
    S.P.mul h (S.c2ρ b c a f g q0 fq q2 qg i j) = some (S.c2ρ b c a f g q0 fq q2 qg l j) →
    t7 l i = true := by
  intro i j l h hcv hlj hz h1 h2 h3 hm
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | decide
    | exact absurd hcv (by decide)
    | exact absurd hlj (by decide)
    | exact (hz (by decide)).elim
    | skip
  all_goals simp [c2V, c2G, c2ρ] at h1 h2 h3 hm
  all_goals first
    | exact (X1 h h1 h2 hm).elim
    | exact (X2 h h1 h2 hm).elim
    | exact (X3 h h1 h2 hm).elim
    | exact (X4 h h1 h2 hm).elim
    | exact (X5 h h1 h2 hm).elim
    | exact (X6 h h1 h2 hm).elim
    | exact (X7 h h1 h2 hm).elim
    | exact (X8 h h1 h2 hm).elim
    | (exfalso; have hd := S.P.deg_nonneg h; rw [h3] at hd
       simp only [map_sub, map_neg, map_add, map_zero] at hd; linarith)
    | skip

variable (k : Type u) [Field k] [IsAlgClosed k]

include f1 f2 g1 g2 q01 q02 hfq hq2 hqg hfg hdf hdg hdq X1 X2 X3 X4 X5 X6 X7 X8 in
/-- **The seven-object category of Case 2 is excluded.** -/
theorem c2_false (hfin : IsRepresentationFinite k (S.P.Lin k)) : False :=
  S.P.bound_false k hfin t7_uniq t7_cov42 t7_cov25 ![1, 2, 3, 2, 1, 1, 1] ⟨0, by decide⟩ t7_count
    (Tab.ConfZ.ofTable S.P 4 5 (c2V b c a) (S.c2G f g q0) (S.c2ρ b c a f g q0 fq q2 qg)
      (S.c2_src f1 g1 q01 hfq hq2 hqg) (S.c2_tgt f2 g2 q02 hfq hq2 hqg)
      (S.c2_wt hfq hq2 hqg) S.c2_e (S.c2_mul hfq hq2 hqg) (S.c2_mulZ hfg)
      (S.c2_retL hdf hdg hdq X1 X2 X3 X4 X5 X6 X7 X8)
      (S.c2_retR hdf hdg hdq X1 X2 X3 X4 X5 X6 X7 X8))

end C2Conf

section Lemma89

variable {g : R} (hgL : S.CycL g) (hgR : ¬ S.CycR g)

include hgL hgR in
/-- `g q_a^j ∈ R_c q² g` for `j ≥ 1`. -/
theorem rad_tgt_pow_mul_of_cycL (j : ℕ) (hj : 1 ≤ j) : ⌜g⌝ * S.q (S.P.tgt g) ^ j = 0 ∨
    ∃ m, 2 ≤ m ∧ ⌜g⌝ * S.q (S.P.tgt g) ^ j = S.q (S.P.src g) ^ m * ⌜g⌝ := by
  rcases S.op.rad_src_pow_mul_of_cycR (S.op_hyp_of_cycL hgL hgR).1 (S.op_hyp_of_cycL hgL hgR).2
    j hj with h | ⟨m, hm, h⟩
  · left
    apply S.P.toOp_injective
    rw [Tab.toOp_mul, Tab.toOp_pow]
    exact h
  · right
    refine ⟨m, hm, S.P.toOp_injective ?_⟩
    rw [Tab.toOp_mul, Tab.toOp_mul, Tab.toOp_pow, Tab.toOp_pow]
    exact h

end Lemma89

/-- A loop equal to `q^m e` and to `q` forces `m = 1`. -/
theorem eq_one_of_qpow {x : V} {q0 : R} (hq0 : S.q x = ⌜q0⌝)
    (hdq : 0 < S.P.deg (S.P.wt q0)) {m : ℕ} {t : R} (ht : ⌜t⌝ = S.q x ^ m * ⌜S.P.e x⌝)
    (ht' : S.P.wt t = S.P.wt q0) : m = 1 := by
  have := S.deg_wt_qpow_e ht
  rw [ht', show S.χ x = S.P.wt q0 by rw [χ, hq0]; rfl] at this
  have : ((1 : ℕ) : ℤ) * S.P.deg (S.P.wt q0) = m * S.P.deg (S.P.wt q0) := by push_cast; linarith
  exact_mod_cast (mul_right_cancel₀ hdq.ne' this).symm

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.11(1)** (`lem:opposite-controls`): for generating `f : b → c`, `g : c → a`
whose Homs are cyclic at `c` but not at the other endpoints, `f q² = 0` or `q² g = 0`. -/
theorem opposite_controls (hfin : IsRepresentationFinite k (S.P.Lin k)) {f g : R}
    (hfR : S.CycR f) (hfL : ¬ S.CycL f) (hgL : S.CycL g) (hgR : ¬ S.CycR g)
    (hfg : S.P.tgt f = S.P.src g) :
    ⌜f⌝ * S.q (S.P.tgt f) ^ 2 = 0 ∨ S.q (S.P.tgt f) ^ 2 * ⌜g⌝ = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hfq2, hq2g⟩ := hcon
  have hq2 : S.q (S.P.tgt f) * S.q (S.P.tgt f) ≠ 0 := by
    rw [← sq]; exact fun h0 ↦ hfq2 (by rw [h0, mul_zero])
  have hfg0 := S.strong_star k hfin hfR hfL hgL hgR hfg hq2
  have hqc : S.q (S.P.tgt f) ≠ 0 := fun h0 ↦ hq2 (by rw [h0, zero_mul])
  obtain ⟨q0, hq0, q01, q02, q03⟩ := (S.q_cases (S.P.tgt f)).resolve_left hqc
  replace hq0 : S.q (S.P.tgt f) = ⌜q0⌝ := hq0
  have hdq : 0 < S.P.deg (S.P.wt q0) := S.P.deg_pos q0 (by rw [q01]; exact q03)
  have hdf : 0 < S.P.deg (S.P.wt f) := S.deg_pos_of_ne (S.src_ne_tgt_of_cycR hfR hfL)
  have hdg : 0 < S.P.deg (S.P.wt g) := S.deg_pos_of_ne (S.src_ne_tgt_of_cycL hgL hgR)
  have hfq := S.mul_q_ne_of_cycR hfR hfL
  rw [hq0] at hfq hq2 hfq2 hq2g
  have hqg : ⌜q0⌝ * ⌜g⌝ ≠ 0 := fun h0 ↦ hq2g (by rw [sq, mul_assoc, h0, mul_zero])
  obtain ⟨fq, hfqr⟩ := S.ray_of_mul_ne hfq
  obtain ⟨q2, hq2r⟩ := S.ray_of_mul_ne hq2
  obtain ⟨qg, hqgr⟩ := S.ray_of_mul_ne hqg
  have hχ : S.χ (S.P.tgt f) = S.P.wt q0 := by rw [χ, hq0]; rfl
  have wq2 : S.P.wt q2 = S.P.wt q0 + S.P.wt q0 := (S.prod_of hq2r).2.2.2
  have wqg : S.P.wt qg = S.P.wt q0 + S.P.wt g := (S.prod_of hqgr).2.2.2
  have wfq : S.P.wt fq = S.P.wt f + S.P.wt q0 := (S.prod_of hfqr).2.2.2
  refine S.c2_false (b := S.P.src f) (c := S.P.tgt f) (a := S.P.tgt g) rfl rfl hfg.symm rfl
    q01 q02 (S.P.rr_mul_rr_eq_rr.1 hfqr) (S.P.rr_mul_rr_eq_rr.1 hq2r)
    (S.P.rr_mul_rr_eq_rr.1 hqgr) (S.P.rr_mul_rr_eq_zero.1 hfg0) hdf hdg hdq
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k hfin
  · -- X1: `g h ≠ q`
    intro h h1 h2 hm
    have hm' : ⌜g⌝ * ⌜h⌝ = ⌜q0⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    obtain ⟨m, hm2, e⟩ := S.rev_mul_of_cycL hgL hgR h (by rw [hm']; exact S.rr_ne q0)
      (by rw [h2, hfg])
    rw [hm', ← hfg] at e
    have := S.eq_one_of_qpow hq0 hdq e rfl
    omega
  · -- X2: `g h ≠ q²`
    intro h h1 h2 hm
    have hm' : ⌜g⌝ * ⌜h⌝ = ⌜q2⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    apply hfq2
    rw [sq, hq2r, ← hm', ← mul_assoc, hfg0, zero_mul]
  · -- X3: `g h ≠ q g` for a loop `h` at `a`
    intro h h1 h2 hm
    have hm' : ⌜g⌝ * ⌜h⌝ = ⌜qg⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    obtain ⟨j, hj, -⟩ := S.local_eq h (h1.trans h2.symm)
    rw [h1] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, one_mul] at hj
      rw [← hj, S.rr_mul_e g] at hm'
      have := congrArg S.P.deg (congrArg S.wtM hm')
      simp only [wtM_rr, wqg, map_add] at this
      linarith
    · have e1 : ⌜g⌝ * ⌜h⌝ = ⌜g⌝ * S.q (S.P.tgt g) ^ j := by
        rw [← hj, S.qpow_comm_e, ← mul_assoc, S.rr_mul_e]
      rcases S.rad_tgt_pow_mul_of_cycL hgL hgR j hj0 with h0 | ⟨m, hm2, h0⟩
      · rw [e1, h0] at hm'; exact S.rr_ne qg hm'.symm
      · rw [e1, h0, ← hfg, hq0] at hm'
        rw [← hqgr] at hm'
        have hne : ⌜q0⌝ ^ m * ⌜g⌝ ≠ 0 := by rw [hm']; exact hqg
        have := congrArg S.P.deg (congrArg S.wtM hm')
        rw [S.wtM_mul _ _ hne, S.wtM_mul _ _ hqg,
          S.wtM_pow _ _ (fun h0 ↦ hne (by rw [h0, zero_mul]))] at this
        simp only [wtM_rr, map_add, map_nsmul, nsmul_eq_mul] at this
        have : (1 : ℤ) * S.P.deg (S.P.wt q0) = m * S.P.deg (S.P.wt q0) := by linarith
        have := mul_right_cancel₀ hdq.ne' this
        omega
  · -- X4: `q h ≠ g`
    intro h h1 h2 hm
    obtain ⟨j, hj⟩ := hgL h (by rw [h1, hfg]) h2
    have := S.deg_wt_qpow_mul hj
    rw [← hfg, hχ] at this
    have hm' := S.P.wt_mul _ _ _ hm
    have : (0 : ℤ) ≤ j * S.P.deg (S.P.wt q0) := by positivity
    have := congrArg S.P.deg hm'
    rw [map_add] at this
    linarith
  · -- X5: `h f ≠ q`
    intro h h1 h2 hm
    have hm' : ⌜h⌝ * ⌜f⌝ = ⌜q0⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    obtain ⟨m, hm2, e⟩ := S.rev_mul_of_cycR hfR hfL h (by rw [hm']; exact S.rr_ne q0) h1
    rw [hm'] at e
    have := S.eq_one_of_qpow hq0 hdq e rfl
    omega
  · -- X6: `h f ≠ q²`
    intro h h1 h2 hm
    have hm' : ⌜h⌝ * ⌜f⌝ = ⌜q2⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    apply hq2g
    rw [sq, hq2r, ← hm', mul_assoc, hfg0, mul_zero]
  · -- X7: `h f ≠ f q` for a loop `h` at `b`
    intro h h1 h2 hm
    have hm' : ⌜h⌝ * ⌜f⌝ = ⌜fq⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    obtain ⟨j, hj, -⟩ := S.local_eq h (h1.trans h2.symm)
    rw [h1] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, one_mul] at hj
      rw [← hj, S.e_mul_rr f] at hm'
      have := congrArg S.P.deg (congrArg S.wtM hm')
      simp only [wtM_rr, wfq, map_add] at this
      linarith
    · have e1 : ⌜h⌝ * ⌜f⌝ = S.q (S.P.src f) ^ j * ⌜f⌝ := by
        rw [← hj, mul_assoc, S.e_mul_rr]
      rcases S.rad_src_pow_mul_of_cycR hfR hfL j hj0 with h0 | ⟨m, hm2, h0⟩
      · rw [e1, h0] at hm'; exact S.rr_ne fq hm'.symm
      · rw [e1, h0, hq0] at hm'
        rw [← hfqr] at hm'
        have hne : ⌜f⌝ * ⌜q0⌝ ^ m ≠ 0 := by rw [hm']; exact hfq
        have := congrArg S.P.deg (congrArg S.wtM hm')
        rw [S.wtM_mul _ _ hne, S.wtM_mul _ _ hfq,
          S.wtM_pow _ _ (fun h0 ↦ hne (by rw [h0, mul_zero]))] at this
        simp only [wtM_rr, map_add, map_nsmul, nsmul_eq_mul] at this
        have : (1 : ℤ) * S.P.deg (S.P.wt q0) = m * S.P.deg (S.P.wt q0) := by linarith
        have := mul_right_cancel₀ hdq.ne' this
        omega
  · -- X8: `h q ≠ f`
    intro h h1 h2 hm
    obtain ⟨j, hj⟩ := hfR h h1 h2
    have hm' := S.P.wt_mul _ _ _ hm
    have e2 := congrArg (fun a ↦ S.P.deg (S.wtM a)) hj
    change S.P.deg (S.P.wt h) = S.P.deg (S.wtM (⌜f⌝ * S.q (S.P.tgt f) ^ j)) at e2
    rw [S.wtM_mul _ _ (hj ▸ S.rr_ne h), S.wtM_qpow _ _ (fun h0 ↦ S.rr_ne h
      (by rw [hj, h0, mul_zero])), wtM_rr, hχ, map_add, map_nsmul, nsmul_eq_mul] at e2
    have := congrArg S.P.deg hm'
    rw [map_add] at this
    have : (0 : ℤ) ≤ j * S.P.deg (S.P.wt q0) := by positivity
    linarith

/-- **Lemma 8.11(2)**, first part: `f q^n g = 0` for `n ≥ 2`. -/
theorem opposite_controls_high (hfin : IsRepresentationFinite k (S.P.Lin k)) {f g : R}
    (hfR : S.CycR f) (hfL : ¬ S.CycL f) (hgL : S.CycL g) (hgR : ¬ S.CycR g)
    (hfg : S.P.tgt f = S.P.src g) (n : ℕ) (hn : 2 ≤ n) :
    ⌜f⌝ * S.q (S.P.tgt f) ^ n * ⌜g⌝ = 0 := by
  rcases S.opposite_controls k hfin hfR hfL hgL hgR hfg with h | h
  · rw [show n = 2 + (n - 2) by omega, pow_add, ← mul_assoc, h, zero_mul, zero_mul]
  · rw [show n = (n - 2) + 2 by omega, pow_add, mul_assoc, mul_assoc, h, mul_zero, mul_zero]

/-- **Lemma 8.11(2)**, socle part: the source radical kills `f q^n g`. -/
theorem opposite_controls_src (hfin : IsRepresentationFinite k (S.P.Lin k)) {f g : R}
    (hfR : S.CycR f) (hfL : ¬ S.CycL f) (hgL : S.CycL g) (hgR : ¬ S.CycR g)
    (hfg : S.P.tgt f = S.P.src g) (n : ℕ) :
    S.q (S.P.src f) * (⌜f⌝ * S.q (S.P.tgt f) ^ n * ⌜g⌝) = 0 := by
  rw [← mul_assoc, ← mul_assoc]
  rcases S.rad_src_mul_of_cycR hfR hfL with h | ⟨m, hm, h⟩
  · rw [h, zero_mul, zero_mul]
  · rw [h, mul_assoc ⌜f⌝, ← pow_add]
    exact S.opposite_controls_high k hfin hfR hfL hgL hgR hfg _ (by omega)

/-- **Lemma 8.11(2)**, socle part: the target radical kills `f q^n g`. -/
theorem opposite_controls_tgt (hfin : IsRepresentationFinite k (S.P.Lin k)) {f g : R}
    (hfR : S.CycR f) (hfL : ¬ S.CycL f) (hgL : S.CycL g) (hgR : ¬ S.CycR g)
    (hfg : S.P.tgt f = S.P.src g) (n : ℕ) :
    ⌜f⌝ * S.q (S.P.tgt f) ^ n * ⌜g⌝ * S.q (S.P.tgt g) = 0 := by
  rw [mul_assoc]
  rcases S.rad_tgt_mul_of_cycL hgL hgR with h | ⟨m, hm, h⟩
  · rw [h, mul_zero]
  · rw [h, ← mul_assoc, mul_assoc ⌜f⌝, ← hfg, ← pow_add]
    exact S.opposite_controls_high k hfin hfR hfL hgL hgR hfg _ (by omega)

end Sys

end RaySys

end MultiplicativeBasisDeformations
