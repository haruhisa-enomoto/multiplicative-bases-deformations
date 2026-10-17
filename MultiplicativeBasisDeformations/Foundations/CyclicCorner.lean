import MultiplicativeBasisDeformations.Foundations.PrimitiveCorners
import MultiplicativeBasisDeformations.Foundations.ProperProducts

/-!
# Lemma 8.21(2): the primitive return corner is cyclic Nakayama

`primitive-ray-equations.tex` (`lem:primitive-cyclic-corners`(2)): "the full corner
`S_x` … is a cyclic Nakayama algebra. … List them as `y_1, …, y_t`. The comparison maps satisfy
`f_i h_{ij} = f_j`, `h_{ij} h_j = h_i`, `h_{ji} = h_j f_i`. … Hence the full corner is generated
by the cycle `x → y_1 → ⋯ → y_t → x`. Every simple forward or wraparound path is a generating
ray, and full cycles are the local generators. All rays are these paths times powers of a full
cycle; the only relations are zero paths."

We list the return partners `y_1, …, y_t` of `x` by the degrees of their generating rays
`f_i : x → y_i` (a chain under factorization, `partner_chain`), take the cycle arrows
`x → y_1 → ⋯ → y_t → x` (`f_1`, the comparison maps, the reverse `h_t`), and show: full cycles
are the local generators, consecutive paths between distinct vertices of `S_x` are its
generating rays (by degrees), and every nonidentity ray of `S_x` is a consecutive path
(`cyclicNakayama`). Consecutive products are `cpath a i ℓ = a_i a_{i+1} ⋯ a_{i+ℓ-1}`.
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

/-! ### Consecutive products -/

/-- `a_i a_{i+1} ⋯ a_{i+ℓ-1}`. -/
def cpath (a : ℕ → R) (i ℓ : ℕ) : M S.P.toMult := ((List.range ℓ).map fun j ↦ ⌜a (i + j)⌝).prod

theorem cpath_zero (a : ℕ → R) (i : ℕ) : S.cpath a i 0 = 1 := rfl

theorem cpath_succ (a : ℕ → R) (i ℓ : ℕ) : S.cpath a i (ℓ + 1) = S.cpath a i ℓ * ⌜a (i + ℓ)⌝ := by
  simp [cpath, List.range_succ, List.prod_append]

theorem cpath_one (a : ℕ → R) (i : ℕ) : S.cpath a i 1 = ⌜a i⌝ := by
  rw [cpath_succ, cpath_zero, one_mul, add_zero]

theorem cpath_add (a : ℕ → R) (i ℓ ℓ' : ℕ) :
    S.cpath a i (ℓ + ℓ') = S.cpath a i ℓ * S.cpath a (i + ℓ) ℓ' := by
  induction ℓ' with
  | zero => rw [add_zero, cpath_zero, mul_one]
  | succ ℓ' ih => rw [← add_assoc, cpath_succ, ih, cpath_succ, mul_assoc, add_assoc]

theorem cpath_const (g : R) (i ℓ : ℕ) : S.cpath (fun _ ↦ g) i ℓ = ⌜g⌝ ^ ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [cpath_succ, ih, pow_succ]

/-! ### Generating rays -/

/-- A ray of the degree of a generating ray with the same endpoints is that ray. -/
theorem eq_gen_of_deg {c g : R} (hg : S.IsGen g) (h1 : S.P.src c = S.P.src g)
    (h2 : S.P.tgt c = S.P.tgt g) (hd : S.P.deg (S.P.wt c) ≤ S.P.deg (S.P.wt g)) : c = g := by
  have hU := hg c h1 h2
  exact (S.deg_le_of_inU hU).2 (le_antisymm hd (S.deg_le_of_inU hU).1)

theorem deg_le_gen {c g : R} (hg : S.IsGen g) (h1 : S.P.src c = S.P.src g)
    (h2 : S.P.tgt c = S.P.tgt g) : S.P.deg (S.P.wt g) ≤ S.P.deg (S.P.wt c) :=
  (S.deg_le_of_inU (hg c h1 h2)).1

theorem isGen_of_deg {c : R} (h : ∀ s, S.P.src s = S.P.src c → S.P.tgt s = S.P.tgt c →
    S.P.deg (S.P.wt c) ≤ S.P.deg (S.P.wt s)) : S.IsGen c := by
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen c
  rw [S.eq_gen_of_deg hg g1.symm g2.symm (by have := h g g1 g2; exact this)]
  exact hg

/-- A strict factorization between rays with distinct targets raises the degree. -/
theorem rf_deg_lt {f f' : R} (hr : S.P.RF f f') (ht : S.P.tgt f ≠ S.P.tgt f') :
    S.P.deg (S.P.wt f) < S.P.deg (S.P.wt f') := by
  obtain ⟨v, hv⟩ := hr
  have hv' : ⌜f⌝ * ⌜v⌝ = ⌜f'⌝ := S.P.rr_mul_rr_eq_rr.2 hv
  obtain ⟨-, e2, e3, e4⟩ := S.prod_of hv'
  have hv0 : v ≠ S.P.e (S.P.src v) := by
    intro he; apply ht; rw [e2, e3, he, S.P.tgt_e, S.P.src_e]
  have := S.P.deg_pos v hv0
  rw [e4, map_add]; linarith

/-! ### The cycle of an ordered list of partners -/

section Cycle

variable {x : V} {t : ℕ} (ht : 1 ≤ t) {y : ℕ → V} {F H c : ℕ → R}
  (hF : ∀ i < t, S.IsGen (F i) ∧ S.P.src (F i) = x ∧ S.P.tgt (F i) = y i ∧ S.PrimRev (F i) (H i) ∧
    S.q x * S.rr (F i) = S.rr (F i) * S.q (y i) ∧ S.q x * S.rr (F i) ≠ 0)
  (hc : ∀ i, i + 1 < t → S.rr (F i) * S.rr (c i) = S.rr (F (i + 1)))

/-- The vertices of the cycle: `σ 0 = x`, `σ (i+1) = y_i`, with period `t + 1`. -/
def cv (x : V) (t : ℕ) (y : ℕ → V) (m : ℕ) : V := if m % (t + 1) = 0 then x else y (m % (t + 1) - 1)

/-- The arrows of the cycle: `a_0 = f_1`, `a_i = c_i` (the comparison maps), `a_t = h_t`. -/
def ca (t : ℕ) (F H c : ℕ → R) (m : ℕ) : R :=
  if m % (t + 1) = 0 then F 0 else if m % (t + 1) = t then H (t - 1) else c (m % (t + 1) - 1)

theorem cv_period (m : ℕ) : cv x t y (m + (t + 1)) = cv x t y m := by
  simp [cv, Nat.add_mod_right]

theorem cv_period' (j n : ℕ) : cv x t y (j + n * (t + 1)) = cv x t y j := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_mul, one_mul, ← add_assoc, cv_period, ih]

theorem ca_period (m : ℕ) : ca t F H c (m + (t + 1)) = ca t F H c m := by
  simp [ca, Nat.add_mod_right]

theorem cpath_period (i ℓ : ℕ) :
    S.cpath (ca t F H c) (i + (t + 1)) ℓ = S.cpath (ca t F H c) i ℓ := by
  unfold cpath
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  rw [add_right_comm, ca_period]

theorem cpath_period' (i n ℓ : ℕ) :
    S.cpath (ca t F H c) (i + n * (t + 1)) ℓ = S.cpath (ca t F H c) i ℓ := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_mul, one_mul, ← add_assoc, cpath_period, ih]

include hF in
theorem F_src_tgt_H {i : ℕ} (hi : i < t) : S.P.src (H i) = y i ∧ S.P.tgt (H i) = x := by
  obtain ⟨-, f1, f2, ⟨h1, h2⟩, hq, hq0⟩ := hF i hi
  have hqx : S.q x ≠ 0 := fun h0 ↦ hq0 (by rw [h0, zero_mul])
  have hqy : S.q (y i) ≠ 0 := fun h0 ↦ hq0 (by rw [hq, h0, mul_zero])
  rw [f1] at h1
  rw [f2] at h2
  refine ⟨?_, ?_⟩
  · rw [← f2]; exact (S.src_of_mul_ne (show ⌜F i⌝ * ⌜H i⌝ ≠ 0 by rw [h1]; exact hqx)).symm
  · rw [← f1]; exact S.src_of_mul_ne (show ⌜H i⌝ * ⌜F i⌝ ≠ 0 by rw [h2]; exact hqy)

include ht hF hc in
/-- The arrows join consecutive vertices. -/
theorem ca_ends (m : ℕ) : S.P.src (ca t F H c m) = cv x t y m ∧
    S.P.tgt (ca t F H c m) = cv x t y (m + 1) := by
  have hm := Nat.mod_lt m (show 0 < t + 1 by omega)
  set m' := m % (t + 1) with hm'
  have hsucc : (m + 1) % (t + 1) = if m' = t then 0 else m' + 1 := by
    rw [Nat.add_mod, ← hm']
    split_ifs with h
    · rw [h, Nat.one_mod_eq_one.2 (by omega)]; simp
    · rw [Nat.one_mod_eq_one.2 (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold ca cv
  rw [hsucc, ← hm']
  by_cases h0 : m' = 0
  · obtain ⟨-, f1, f2, -⟩ := hF 0 (by omega)
    have ht0 : ¬ (0 = t) := by omega
    simp only [h0, if_true, ht0, if_false]
    exact ⟨f1, by simp [f2]⟩
  · by_cases htt : m' = t
    · obtain ⟨h1, h2⟩ := S.F_src_tgt_H hF (i := t - 1) (by omega)
      have ht0 : ¬ t = 0 := by omega
      simp only [htt, ht0, if_false, if_true]
      exact ⟨h1, h2⟩
    · simp only [h0, htt, if_false]
      have hc' := hc (m' - 1) (by omega)
      obtain ⟨-, e2, e3, -⟩ := S.prod_of hc'
      obtain ⟨-, -, fa, -⟩ := hF (m' - 1) (by omega)
      obtain ⟨-, -, fb, -⟩ := hF (m' - 1 + 1) (by omega)
      have hne : m' + 1 ≠ 0 := by omega
      simp only [hne, if_false]
      refine ⟨by rw [← e3, fa], by rw [← e2, fb]; congr 1; omega⟩

include ht hc in
/-- **The forward paths from `x` are the `f_i`.** -/
theorem cpath_forward : ∀ j, 1 ≤ j → j ≤ t → S.cpath (ca t F H c) 0 j = S.rr (F (j - 1)) := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
      intro _ hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [S.cpath_one]; simp [ca]
      · rw [S.cpath_succ, ih hj0 (by omega), zero_add]
        have hca : ca t F H c j = c (j - 1) := by
          have hjm : j % (t + 1) = j := Nat.mod_eq_of_lt (by omega)
          simp only [ca, hjm]
          rw [if_neg (by omega), if_neg (by omega)]
        rw [hca, hc (j - 1) (by omega), show j - 1 + 1 = j + 1 - 1 by omega]

include ht hF hc in
/-- **The full cycle at `x` is `q_x`.** -/
theorem cpath_full_zero : S.cpath (ca t F H c) 0 (t + 1) = S.q x := by
  rw [S.cpath_succ, S.cpath_forward ht hc t ht le_rfl, zero_add]
  have hca : ca t F H c t = H (t - 1) := by
    have htm : t % (t + 1) = t := Nat.mod_eq_of_lt (by omega)
    simp only [ca, htm]
    rw [if_neg (by omega), if_true]
  rw [hca]
  obtain ⟨-, f1, -, ⟨h1, -⟩, -⟩ := hF (t - 1) (by omega)
  rw [h1, f1]

include ht hF hc in
/-- **The backward paths to `x` are the reverses `h_i`.** -/
theorem cpath_back (hy : ∀ i < t, y i ≠ x) {i : ℕ} (hi1 : 1 ≤ i) (hit : i ≤ t) :
    S.cpath (ca t F H c) i (t + 1 - i) = S.rr (H (i - 1)) := by
  have e := S.cpath_full_zero ht hF hc
  rw [show t + 1 = i + (t + 1 - i) by omega, S.cpath_add, zero_add,
    S.cpath_forward ht hc i hi1 hit] at e
  obtain ⟨-, f1, f2, ⟨h1, -⟩, hq, hq0⟩ := hF (i - 1) (by omega)
  have hqx : S.q x ≠ 0 := fun h0 ↦ hq0 (by rw [h0, zero_mul])
  rw [f1] at h1
  rw [← h1] at e
  have hne : S.rr (F (i - 1)) * S.cpath (ca t F H c) i (t + 1 - i) ≠ 0 := by rw [e, h1]; exact hqx
  rcases S.elt_cases (S.cpath (ca t F H c) i (t + 1 - i)) with h | h | ⟨r, hr⟩
  · exfalso
    rw [h, mul_one] at e
    have hH := congrArg S.wtM e
    have hne' : S.rr (F (i - 1)) * S.rr (H (i - 1)) ≠ 0 := by rw [h1]; exact hqx
    rw [S.wtM_mul _ _ hne', wtM_rr, wtM_rr] at hH
    obtain ⟨hs, ht'⟩ := S.F_src_tgt_H hF (i := i - 1) (by omega)
    have hHne : H (i - 1) ≠ S.P.e (S.P.src (H (i - 1))) := by
      intro he
      apply hy (i - 1) (by omega)
      rw [← hs, ← ht', he, S.P.tgt_e, S.P.src_e]
    have := S.P.deg_pos (H (i - 1)) hHne
    have := congrArg S.P.deg hH
    rw [map_add] at this
    linarith
  · exact absurd (by rw [h, mul_zero]) hne
  · rw [hr] at e hne ⊢
    rw [S.cancel_left e hne]

include ht hF hc in
/-- **Full cycles are the local generators.** -/
theorem cpath_full (hy : ∀ i < t, y i ≠ x) (i : ℕ) :
    S.cpath (ca t F H c) i (t + 1) = S.q (cv x t y i) := by
  have hi := Nat.mod_lt i (show 0 < t + 1 by omega)
  have hdiv := Nat.mod_add_div i (t + 1)
  rw [← hdiv, mul_comm, S.cpath_period', show cv x t y (i % (t + 1) + i / (t + 1) * (t + 1)) =
    cv x t y (i % (t + 1)) by simp [cv, Nat.add_mul_mod_self_right]]
  set i' := i % (t + 1)
  rcases Nat.eq_zero_or_pos i' with h0 | h0
  · rw [h0, S.cpath_full_zero ht hF hc]; simp [cv]
  · rw [show t + 1 = (t + 1 - i') + i' by omega, S.cpath_add, S.cpath_back ht hF hc hy h0 (by omega),
      show i' + (t + 1 - i') = 0 + (t + 1) by omega, S.cpath_period, S.cpath_forward ht hc i' h0 (by omega)]
    obtain ⟨-, -, f2, ⟨-, h2⟩, -⟩ := hF (i' - 1) (by omega)
    rw [h2, f2]
    simp only [cv, Nat.mod_eq_of_lt hi]
    rw [if_neg (by omega)]

theorem cv_zero : cv x t y 0 = x := by simp [cv]

theorem cv_succ {i : ℕ} (hi : i < t) : cv x t y (i + 1) = y i := by
  simp only [cv, Nat.mod_eq_of_lt (show i + 1 < t + 1 by omega)]
  rw [if_neg (by omega)]; rfl

theorem cv_cases (m : ℕ) : cv x t y m = x ∨ ∃ i < t, cv x t y m = y i := by
  unfold cv
  split_ifs with h
  · exact Or.inl rfl
  · have := Nat.mod_lt m (show 0 < t + 1 by omega)
    exact Or.inr ⟨m % (t + 1) - 1, by omega, rfl⟩

include hF in
theorem χ_y {i : ℕ} (hi : i < t) : S.χ (y i) = S.χ x ∧ S.q (y i) ≠ 0 := by
  obtain ⟨-, f1, f2, ⟨h1, h2⟩, hq, hq0⟩ := hF i hi
  have hqx : S.q x ≠ 0 := fun h0 ↦ hq0 (by rw [h0, zero_mul])
  have hqy : S.q (y i) ≠ 0 := fun h0 ↦ hq0 (by rw [hq, h0, mul_zero])
  obtain ⟨e1, e2⟩ := S.χ_pair (t := F i) (h := H i) h1 h2 (by rw [f1]; exact hqx)
    (by rw [f2]; exact hqy)
  rw [f1] at e1
  rw [f2] at e2
  exact ⟨by rw [e1, e2, add_comm], hqy⟩

include hF in
theorem χ_cv (hqx : S.q x ≠ 0) (m : ℕ) : S.χ (cv x t y m) = S.χ x ∧ S.q (cv x t y m) ≠ 0 := by
  rcases cv_cases (x := x) (t := t) (y := y) m with h | ⟨i, hi, h⟩
  · rw [h]; exact ⟨rfl, hqx⟩
  · rw [h]; exact S.χ_y hF hi

include ht hF hc in
theorem cpath_pow (hy : ∀ i < t, y i ≠ x) (i n : ℕ) :
    S.cpath (ca t F H c) i (n * (t + 1)) = S.q (cv x t y i) ^ n := by
  induction n with
  | zero => simp [S.cpath_zero]
  | succ n ih =>
      rw [add_mul, one_mul, S.cpath_add, ih, S.cpath_period' (t := t), pow_succ,
        S.cpath_full ht hF hc hy]

include ht hF hc in
/-- **A nonzero consecutive path is a ray** from `σ_i` to `σ_{i+ℓ}`. -/
theorem cpath_ray : ∀ (i ℓ : ℕ), 1 ≤ ℓ → S.cpath (ca t F H c) i ℓ ≠ 0 →
    ∃ r, S.cpath (ca t F H c) i ℓ = S.rr r ∧ S.P.src r = cv x t y i ∧
      S.P.tgt r = cv x t y (i + ℓ) := by
  intro i ℓ
  induction ℓ with
  | zero => intro h; omega
  | succ ℓ ih =>
      intro _ h0
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
      · rw [S.cpath_one]
        exact ⟨ca t F H c i, rfl, (S.ca_ends ht hF hc i).1, (S.ca_ends ht hF hc i).2⟩
      · rw [S.cpath_succ] at h0 ⊢
        have h1 : S.cpath (ca t F H c) i ℓ ≠ 0 := fun h ↦ h0 (by rw [h, zero_mul])
        obtain ⟨r, hr, r1, r2⟩ := ih hℓ h1
        rw [hr] at h0 ⊢
        obtain ⟨u, hu⟩ := S.ray_of_mul_ne h0
        obtain ⟨u1, u2, -, -⟩ := S.prod_of hu
        refine ⟨u, hu, by rw [u1, r1], ?_⟩
        rw [u2, (S.ca_ends ht hF hc (i + ℓ)).2, add_assoc]

include ht hF hc in
/-- Consecutive paths of length at most `t + 1` are nonzero (they divide a full cycle). -/
theorem cpath_ne_zero (hy : ∀ i < t, y i ≠ x) (hqx : S.q x ≠ 0) {i ℓ : ℕ} (hℓ : ℓ ≤ t + 1) :
    S.cpath (ca t F H c) i ℓ ≠ 0 := by
  intro h0
  apply (S.χ_cv hF hqx i).2
  rw [← S.cpath_full ht hF hc hy, show t + 1 = ℓ + (t + 1 - ℓ) by omega, S.cpath_add, h0, zero_mul]

theorem deg_InU {r g : R} {χ₀ : L} (hU : S.InU r g) (h1 : S.χ (S.P.src g) = χ₀)
    (h2 : S.χ (S.P.tgt g) = χ₀) (hd0 : 0 ≤ S.P.deg χ₀)
    (hlt : S.P.deg (S.P.wt g) < S.P.deg (S.P.wt r)) :
    S.P.deg (S.P.wt g) + S.P.deg χ₀ ≤ S.P.deg (S.P.wt r) := by
  obtain ⟨-, -, a, b, hw, -, -⟩ := S.inU_endpoints hU
  rw [h1, h2] at hw
  have e := congrArg S.P.deg hw
  simp only [map_add, map_nsmul, nsmul_eq_mul] at e
  rw [e] at hlt ⊢
  have ha : (0 : ℤ) ≤ a := by positivity
  have hb : (0 : ℤ) ≤ b := by positivity
  rcases Nat.eq_zero_or_pos a with rfl | ha'
  · rcases Nat.eq_zero_or_pos b with rfl | hb'
    · simp at hlt
    · have : (1 : ℤ) ≤ b := by exact_mod_cast hb'
      nlinarith
  · have : (1 : ℤ) ≤ a := by exact_mod_cast ha'
    nlinarith

include ht hF hc in
/-- **Consecutive paths between distinct vertices are generating rays** ("every simple forward
or wraparound path is a generating ray"). -/
theorem cpath_gen (hy : ∀ i < t, y i ≠ x) (hyinj : ∀ i j, i < t → j < t → y i = y j → i = j)
    (hmono : ∀ i j, i < t → j < t → i < j → S.P.deg (S.P.wt (F i)) < S.P.deg (S.P.wt (F j)))
    (hqx : S.q x ≠ 0) {i ℓ : ℕ} (hi : i < t + 1) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ t) {r : R}
    (hr : S.cpath (ca t F H c) i ℓ = S.rr r) : S.IsGen r := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · -- forward from `x`
    rw [S.cpath_forward ht hc ℓ hℓ1 hℓ] at hr
    rw [← S.rr_inj hr]; exact (hF (ℓ - 1) (by omega)).1
  by_cases hback : i + ℓ = t + 1
  · -- back to `x`
    have := S.cpath_back ht hF hc hy hi1 (by omega)
    rw [show t + 1 - i = ℓ by omega, hr] at this
    rw [S.rr_inj this]
    obtain ⟨-, f1, f2, ⟨h1, h2⟩, hq, hq0⟩ := hF (i - 1) (by omega)
    obtain ⟨hs, ht'⟩ := S.F_src_tgt_H hF (i := i - 1) (by omega)
    have hqy : S.q (y (i - 1)) ≠ 0 := fun h0 ↦ hq0 (by rw [hq, h0, mul_zero])
    exact S.gen_of_pair (t := H (i - 1)) (h := F (i - 1)) (by rw [hs, ht']; exact hy _ (by omega))
      (by rw [hs, ← f2]; exact h2) (by rw [ht', ← f1]; exact h1) (by rw [hs]; exact hqy)
      (by rw [ht']; exact hqx)
  -- the general case: compare with the generating ray of the Hom
  obtain ⟨g, g1, g2, hg⟩ := S.exists_gen r
  have hU : S.InU r g := hg r g1.symm g2.symm
  obtain ⟨p, q, hpq⟩ := hU
  obtain ⟨-, f1, f2, -, hq, hq0⟩ := hF (i - 1) (by omega)
  have hrs : S.P.src r = cv x t y i := by
    obtain ⟨r', hr', r1, -⟩ := S.cpath_ray ht hF hc i ℓ hℓ1 (by rw [hr]; exact S.rr_ne r)
    rw [S.rr_inj (hr.symm.trans hr')]; exact r1
  have hrt : S.P.tgt r = cv x t y (i + ℓ) := by
    obtain ⟨r', hr', -, r2⟩ := S.cpath_ray ht hF hc i ℓ hℓ1 (by rw [hr]; exact S.rr_ne r)
    rw [S.rr_inj (hr.symm.trans hr')]; exact r2
  have hcvi : cv x t y i = y (i - 1) := by
    rw [show i = (i - 1) + 1 by omega, cv_succ (by omega)]; rfl
  -- `F_{i-1} r = cpath 0 (i + ℓ)`
  have hFr : S.rr (F (i - 1)) * S.rr r = S.cpath (ca t F H c) 0 (i + ℓ) := by
    rw [S.cpath_add, ← hr, S.cpath_forward ht hc i hi1 (by omega), zero_add]
  have hq' : S.q (S.P.src (F (i - 1))) * S.rr (F (i - 1)) =
      S.rr (F (i - 1)) * S.q (S.P.tgt (F (i - 1))) := by rw [f1, f2]; exact hq
  -- `F_{i-1} g ≠ 0`
  have hFr0 : S.rr (F (i - 1)) * S.rr r ≠ 0 := by
    rw [hFr]
    by_cases hw : i + ℓ ≤ t
    · rw [S.cpath_forward ht hc (i + ℓ) (by omega) hw]; exact S.rr_ne _
    · rw [show i + ℓ = (t + 1) + (i + ℓ - (t + 1)) by omega, S.cpath_add,
        S.cpath_full_zero ht hF hc, show 0 + (t + 1) = 0 + (t + 1) from rfl,
        S.cpath_period, S.cpath_forward ht hc _ (by omega) (by omega)]
      obtain ⟨-, f1', -, -, -, hq0'⟩ := hF (i + ℓ - (t + 1) - 1) (by omega)
      exact hq0'
  have hFg : S.rr (F (i - 1)) * S.rr g ≠ 0 := by
    intro h0; apply hFr0
    rw [hpq, ← mul_assoc, ← mul_assoc, g1, hrs, hcvi, ← f2, ← S.comm_pow hq' p, f1,
      mul_assoc (S.q x ^ p), h0, mul_zero, zero_mul]
  obtain ⟨s, hs⟩ := S.ray_of_mul_ne hFg
  obtain ⟨s1, s2, -, s4⟩ := S.prod_of hs
  obtain ⟨u, hu⟩ := S.ray_of_mul_ne hFr0
  obtain ⟨-, -, -, e4⟩ := S.prod_of hu
  have hgs : S.P.src g = cv x t y i := by rw [g1, hrs]
  have hgt : S.P.tgt g = cv x t y (i + ℓ) := by rw [g2, hrt]
  have hdχ := S.χ_deg_pos x hqx
  refine S.eq_gen_of_deg hg g1.symm g2.symm ?_ ▸ hg
  by_cases hw : i + ℓ ≤ t
  · -- no wrap: `F_{i-1} r = F_{i+ℓ-1}`
    have hFj := S.cpath_forward (H := H) ht hc (i + ℓ) (by omega) hw
    rw [← hFr, hu] at hFj
    have huj := S.rr_inj hFj
    obtain ⟨hgj, fj1, fj2, -⟩ := hF (i + ℓ - 1) (by omega)
    have hle := S.deg_le_gen hgj (c := s) (by rw [s1, f1, fj1])
      (by rw [s2, hgt, fj2, show i + ℓ = (i + ℓ - 1) + 1 by omega, cv_succ (by omega)]; rfl)
    rw [← huj, e4, map_add, s4, map_add] at hle
    linarith
  · -- wrap: `F_{i-1} r = q_x F_{j-1}`
    set j := i + ℓ - (t + 1) with hj
    have hj1 : 1 ≤ j := by omega
    have hji : j < i := by omega
    have hcp : S.cpath (ca t F H c) 0 (i + ℓ) = S.q x * S.rr (F (j - 1)) := by
      rw [show i + ℓ = (t + 1) + j by omega, S.cpath_add, S.cpath_full_zero ht hF hc,
        show 0 + (t + 1) = 0 + (t + 1) from rfl, S.cpath_period, S.cpath_forward ht hc j hj1 (by omega)]
    obtain ⟨q0, hq0r, -, -, -⟩ := (S.q_cases x).resolve_left hqx
    replace hq0r : S.q x = S.rr q0 := hq0r
    have hux : S.rr u = S.rr q0 * S.rr (F (j - 1)) := by rw [← hu, hFr, hcp, hq0r]
    obtain ⟨-, -, -, e4'⟩ := S.prod_of hux.symm
    have hχx : S.P.wt q0 = S.χ x := by rw [χ, hq0r, wtM_rr]
    obtain ⟨hgj, fj1, fj2, -⟩ := hF (j - 1) (by omega)
    by_contra hlt
    push Not at hlt
    have hU' : S.InU r g := hg r g1.symm g2.symm
    have h3 := S.deg_InU hU' (χ₀ := S.χ x) (by rw [hgs]; exact (S.χ_cv hF hqx i).1)
      (by rw [hgt]; exact (S.χ_cv hF hqx (i + ℓ)).1) hdχ.le hlt
    have htj : S.P.tgt s = S.P.tgt (F (j - 1)) := by
      rw [s2, hgt, fj2, show i + ℓ = j + (t + 1) by omega, cv_period,
        show j = (j - 1) + 1 by omega, cv_succ (by omega)]
      rfl
    have hsj : s = F (j - 1) := by
      refine S.eq_gen_of_deg hgj (by rw [s1, f1, fj1]) htj ?_
      have e1 := congrArg S.P.deg e4
      have e2 := congrArg S.P.deg e4'
      rw [map_add] at e1
      rw [map_add, hχx] at e2
      rw [s4, map_add]
      linarith
    have hrf : S.P.RF (F (i - 1)) (F (j - 1)) := (S.rf_iff _ _).2 ⟨g, by rw [hs, hsj]⟩
    have hlt1 := S.rf_deg_lt hrf (by
      rw [f2, fj2]; intro he
      have := hyinj (i - 1) (j - 1) (by omega) (by omega) he
      omega)
    have hlt2 := hmono (j - 1) (i - 1) (by omega) (by omega) (by omega)
    linarith

include ht hF hc in
/-- **Every nonidentity ray between vertices of the cycle is a consecutive path.** -/
theorem ray_eq_cpath (hy : ∀ i < t, y i ≠ x) (hyinj : ∀ i j, i < t → j < t → y i = y j → i = j)
    (hmono : ∀ i j, i < t → j < t → i < j → S.P.deg (S.P.wt (F i)) < S.P.deg (S.P.wt (F j)))
    (hqx : S.q x ≠ 0) {r : R} {i j : ℕ} (hi : i < t + 1) (hj : j < t + 1)
    (hsrc : S.P.src r = cv x t y i) (htgt : S.P.tgt r = cv x t y j)
    (hr0 : r ≠ S.P.e (S.P.src r)) :
    ∃ m ℓ, 1 ≤ ℓ ∧ S.rr r = S.cpath (ca t F H c) m ℓ := by
  by_cases hij : i = j
  · -- a loop: a positive power of the local generator
    subst hij
    obtain ⟨p, hp, -⟩ := S.local_eq r (by rw [hsrc, htgt])
    have hp1 : 1 ≤ p := by
      by_contra h0
      have : p = 0 := by omega
      subst this
      rw [pow_zero, one_mul] at hp
      exact hr0 (S.rr_inj hp).symm
    refine ⟨i, p * (t + 1), by nlinarith, ?_⟩
    rw [← hp, S.qpow_mul_e hp1, hsrc, S.cpath_pow ht hF hc hy]
  · -- the consecutive path from `σ_i` to `σ_j`
    set ℓ₀ := if i < j then j - i else j + (t + 1) - i with hℓ₀
    have hℓ1 : 1 ≤ ℓ₀ := by rw [hℓ₀]; split_ifs <;> omega
    have hℓt : ℓ₀ ≤ t := by rw [hℓ₀]; split_ifs <;> omega
    have hend : ∃ n, i + ℓ₀ = j + n * (t + 1) := by
      rw [hℓ₀]; split_ifs with h
      · exact ⟨0, by omega⟩
      · exact ⟨1, by omega⟩
    obtain ⟨n₀, hn₀⟩ := hend
    obtain ⟨cr, hcr, c1, c2⟩ := S.cpath_ray ht hF hc i ℓ₀ hℓ1
      (S.cpath_ne_zero ht hF hc hy hqx (by omega))
    have hcgen := S.cpath_gen ht hF hc hy hyinj hmono hqx hi hℓ1 hℓt hcr
    have hc2 : S.P.tgt cr = cv x t y j := by
      rw [c2, hn₀, cv_period']
    obtain ⟨p, q, hpq⟩ := hcgen r (by rw [hsrc, c1]) (by rw [htgt, hc2])
    refine ⟨i, p * (t + 1) + ℓ₀ + q * (t + 1), by omega, ?_⟩
    rw [hpq, c1, hc2, ← S.cpath_pow ht hF hc hy, ← S.cpath_pow ht hF hc hy, ← hcr,
      S.cpath_add, S.cpath_add, add_comm i (p * (t + 1)), ← add_assoc,
      add_comm (p * (t + 1)) i, S.cpath_period', add_assoc i, add_comm (p * (t + 1)) ℓ₀,
      ← add_assoc i, hn₀, add_assoc j, ← add_mul, S.cpath_period']

end Cycle

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Lemma 8.21(2)** (`lem:primitive-cyclic-corners`(2)): the primitive return corner `S_x` is
a cyclic Nakayama algebra. Its vertices are `σ_0 = x, σ_1, …, σ_t` (the return partners, in the
order of the chain of their generating rays), the arrows `a_i : σ_i → σ_{i+1}` (indices mod
`t + 1`) form a cycle, each full cycle is the local generator, and every nonidentity ray
between vertices of `S_x` is a consecutive path `a_m a_{m+1} ⋯ a_{m+ℓ-1}`; products of rays
are thus concatenations, and the only relations are zero paths. -/
theorem cyclicNakayama (hfin : IsRepresentationFinite k (S.P.Lin k)) {x : V} (hqx : S.q x ≠ 0) :
    ∃ (n : ℕ) (σ : ℕ → V) (a : ℕ → R),
      σ 0 = x ∧ (∀ m, σ (m + (n + 1)) = σ m) ∧ Set.InjOn σ (Set.Iio (n + 1)) ∧
      (∀ v, S.InS x v ↔ ∃ i < n + 1, σ i = v) ∧
      (∀ m, S.P.src (a m) = σ m ∧ S.P.tgt (a m) = σ (m + 1)) ∧
      (∀ i, S.cpath a i (n + 1) = S.q (σ i)) ∧
      ∀ r : R, S.InS x (S.P.src r) → S.InS x (S.P.tgt r) → r ≠ S.P.e (S.P.src r) →
        ∃ m ℓ, 1 ≤ ℓ ∧ S.rr r = S.cpath a m ℓ := by
  classical
  obtain ⟨q0, hq0r, q01, q02, q03⟩ := (S.q_cases x).resolve_left hqx
  replace hq0r : S.q x = S.rr q0 := hq0r
  set P := Finset.univ.filter (S.Partner x) with hPdef
  by_cases hP : P = ∅
  · -- no partners: the local algebra `k[q_x]`
    have hnoP : ∀ v, ¬ S.Partner x v := fun v hv ↦ by
      have : v ∈ P := by simp [P, hv]
      rw [hP] at this; simp at this
    refine ⟨0, fun _ ↦ x, fun _ ↦ q0, rfl, fun _ ↦ rfl, fun i hi j hj _ ↦ by
      simp only [Set.mem_Iio] at hi hj; omega, fun v ↦ ⟨fun h ↦ ?_, fun ⟨i, _, h⟩ ↦ Or.inl h.symm⟩,
      fun _ ↦ ⟨q01, q02⟩, fun _ ↦ by rw [cpath_const, pow_one, hq0r], fun r hr1 hr2 hr0 ↦ ?_⟩
    · rcases h with h | h
      · exact ⟨0, by omega, h.symm⟩
      · exact absurd h (hnoP v)
    · have h1 : S.P.src r = x := hr1.resolve_right (hnoP _)
      have h2 : S.P.tgt r = x := hr2.resolve_right (hnoP _)
      obtain ⟨p, hp, -⟩ := S.local_eq r (by rw [h1, h2])
      have hp1 : 1 ≤ p := by
        by_contra h0
        have : p = 0 := by omega
        subst this
        rw [pow_zero, one_mul] at hp
        exact hr0 (S.rr_inj hp).symm
      exact ⟨0, p, hp1, by rw [← hp, S.qpow_mul_e hp1, h1, hq0r, cpath_const]⟩
  -- the partners, with their data
  have hd : ∀ v, S.Partner x v → ∃ f h, S.IsGen f ∧ S.P.src f = x ∧ S.P.tgt f = v ∧
      S.PrimRev f h ∧ S.q x * S.rr f = S.rr f * S.q v ∧ S.q x * S.rr f ≠ 0 := fun v hv ↦ hv.2
  have : Nonempty R := ⟨q0⟩
  choose! fp hp hfp using hd
  set κ : V → ℤ := fun v ↦ S.P.deg (S.P.wt (fp v)) with hκ
  have hchain : ∀ v ∈ P, ∀ v' ∈ P, v ≠ v' → (κ v < κ v' ↔ S.P.RF (fp v) (fp v')) := by
    intro v hv v' hv' hne
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    obtain ⟨g1, f1, f2, r1, q1, q1'⟩ := hfp v hv
    obtain ⟨g2, f1', f2', r2, q2, q2'⟩ := hfp v' hv'
    have hc := S.partner_chain k hfin g1 g2 f1 f1' r1 r2 (by rw [f2]; exact q1) q1'
      (by rw [f2']; exact q2) q2'
    constructor
    · intro hlt
      rcases hc with h | h
      · exact h
      · exact absurd (S.rf_deg_lt h (by rw [f2, f2']; exact Ne.symm hne)) (not_lt.2 hlt.le)
    · intro h; exact S.rf_deg_lt h (by rw [f2, f2']; exact hne)
  have hκinj : Set.InjOn κ P := by
    intro v hv v' hv' he
    by_contra hne
    rcases lt_trichotomy (κ v) (κ v') with h | h | h
    · exact absurd he h.ne
    · simp only [P, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hv'
      obtain ⟨g1, f1, f2, r1, q1, q1'⟩ := hfp v hv
      obtain ⟨g2, f1', f2', r2, q2, q2'⟩ := hfp v' hv'
      have hc := S.partner_chain k hfin g1 g2 f1 f1' r1 r2 (by rw [f2]; exact q1) q1'
        (by rw [f2']; exact q2) q2'
      rcases hc with h' | h'
      · exact absurd h (S.rf_deg_lt h' (by rw [f2, f2']; exact hne)).ne
      · exact absurd h.symm (S.rf_deg_lt h' (by rw [f2, f2']; exact Ne.symm hne)).ne
    · exact absurd he h.ne'
  set t := P.card with htdef
  have ht : 1 ≤ t := by
    rw [htdef]; exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hP)
  set K := P.image κ with hK
  have hKc : K.card = t := Finset.card_image_of_injOn hκinj
  set emb := K.orderEmbOfFin hKc
  have hyex : ∀ i : Fin t, ∃ v ∈ P, κ v = emb i := fun i ↦ by
    have := K.orderEmbOfFin_mem hKc i
    obtain ⟨v, hv, he⟩ := Finset.mem_image.1 this
    exact ⟨v, hv, he⟩
  choose yv hyvP hyvκ using hyex
  set y : ℕ → V := fun i ↦ if h : i < t then yv ⟨i, h⟩ else x with hy
  have hyP : ∀ i < t, y i ∈ P := fun i hi ↦ by simp only [y, dif_pos hi]; exact hyvP _
  have hyκ : ∀ i (hi : i < t), κ (y i) = emb ⟨i, hi⟩ := fun i hi ↦ by
    simp only [y, dif_pos hi]; exact hyvκ _
  have hyPar : ∀ i < t, S.Partner x (y i) := fun i hi ↦ by
    have := hyP i hi; simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  set F : ℕ → R := fun i ↦ fp (y i)
  set H : ℕ → R := fun i ↦ hp (y i)
  have hF : ∀ i < t, S.IsGen (F i) ∧ S.P.src (F i) = x ∧ S.P.tgt (F i) = y i ∧
      S.PrimRev (F i) (H i) ∧ S.q x * S.rr (F i) = S.rr (F i) * S.q (y i) ∧
      S.q x * S.rr (F i) ≠ 0 := fun i hi ↦ hfp (y i) (hyPar i hi)
  have hmono : ∀ i j, i < t → j < t → i < j → S.P.deg (S.P.wt (F i)) < S.P.deg (S.P.wt (F j)) := by
    intro i j hi hj hij
    change κ (y i) < κ (y j)
    rw [hyκ i hi, hyκ j hj]
    exact emb.strictMono (Fin.mk_lt_mk.2 hij)
  have hyinj : ∀ i j, i < t → j < t → y i = y j → i = j := by
    intro i j hi hj he
    have := congrArg κ he
    rw [hyκ i hi, hyκ j hj] at this
    exact Fin.mk.inj_iff.1 (emb.injective this)
  have hyx : ∀ i < t, y i ≠ x := fun i hi ↦ (hyPar i hi).1
  have hcex : ∀ i, i + 1 < t → ∃ c, S.rr (F i) * S.rr c = S.rr (F (i + 1)) := by
    intro i hi
    have hr := (hchain (y i) (hyP i (by omega)) (y (i + 1)) (hyP (i + 1) hi)
      (fun he ↦ by have := hyinj i (i + 1) (by omega) hi he; omega)).1
      (hmono i (i + 1) (by omega) hi (by omega))
    obtain ⟨c, hc⟩ := hr
    exact ⟨c, S.P.rr_mul_rr_eq_rr.2 hc⟩
  set c : ℕ → R := fun i ↦ if h : i + 1 < t then Classical.choose (hcex i h) else q0
  have hc : ∀ i, i + 1 < t → S.rr (F i) * S.rr (c i) = S.rr (F (i + 1)) := fun i hi ↦ by
    simp only [c, dif_pos hi]; exact Classical.choose_spec (hcex i hi)
  have hcv : ∀ v, S.InS x v ↔ ∃ i < t + 1, cv x t y i = v := by
    intro v
    constructor
    · rintro (rfl | hv)
      · exact ⟨0, by omega, cv_zero⟩
      · have hvP : v ∈ P := by simp [P, hv]
        obtain ⟨i, hi⟩ : ∃ i : Fin t, emb i = κ v := by
          have : κ v ∈ (K : Set ℤ) := Finset.mem_coe.2 (Finset.mem_image_of_mem κ hvP)
          rw [← Finset.range_orderEmbOfFin K hKc] at this
          obtain ⟨i, hi⟩ := Set.mem_range.1 this
          exact ⟨i, hi⟩
        refine ⟨i + 1, by omega, ?_⟩
        rw [cv_succ i.2]
        apply hκinj (hyP i i.2) hvP
        rw [hyκ i i.2, ← hi]
    · rintro ⟨i, hi, rfl⟩
      rcases cv_cases (x := x) (t := t) (y := y) i with h | ⟨j, hj, h⟩
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr (hyPar j hj)
  refine ⟨t, cv x t y, ca t F H c, cv_zero, cv_period, ?_, hcv, S.ca_ends ht hF hc,
    S.cpath_full ht hF hc hyx, fun r hr1 hr2 hr0 ↦ ?_⟩
  · intro i hi j hj he
    simp only [Set.mem_Iio] at hi hj
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · rw [cv_zero, show j = (j - 1) + 1 by omega, cv_succ (by omega)] at he
      exact absurd he.symm (hyx _ (by omega))
    · rw [cv_zero, show i = (i - 1) + 1 by omega, cv_succ (by omega)] at he
      exact absurd he (hyx _ (by omega))
    · rw [show i = (i - 1) + 1 by omega, show j = (j - 1) + 1 by omega, cv_succ (by omega),
        cv_succ (by omega)] at he
      have := hyinj _ _ (by omega) (by omega) he
      omega
  · obtain ⟨i, hi, hie⟩ := (hcv _).1 hr1
    obtain ⟨j, hj, hje⟩ := (hcv _).1 hr2
    exact S.ray_eq_cpath ht hF hc hyx hyinj hmono hqx hi hj hie.symm hje.symm hr0

end Sys

end RaySys

end MultiplicativeBasisDeformations
