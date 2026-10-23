module

public import MultiplicativeBasisDeformations.Foundations.TraceTypesAD

/-!
# Type `D` traces in every characteristic (Appendix B)

`characteristic-two-mesh-calculations.tex`: "In word degree `j < N` the
alternating words `w_j, w'_j`, starting with `x, y`, span; in degree `N` they satisfy
`w_N + w'_N = 0`. Multiplying this relation by `x` and `y` shows that both
alternating words of degree `N + 1` are zero. … In the ordinary trace, the
one-letter classes vanish …. An odd alternating word of length at least three
rotates to a word containing a square. For even `j`, rotation identifies `w_j` and
`w'_j`. … If `ι` interchanges the two short arms, twisted rotation turns an even
alternating word into a word containing a square, while in odd degree the two
alternating words become equal."

We record this without assumptions on the characteristic: every positive trace is
an integer multiple of the trace of the alternating word `altE` starting with `x`;
that trace vanishes in odd degree for the trivial twist, in even degree for the
interchange, and in degree above `N = L c + 2`, where `c` is the long arm.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

open TraceData

section Alt

variable {S : Type*} [Ring S] (p q : S)

/-- The alternating word of length `n` starting with `p`. -/
def altE (n : ℕ) : S := if Even n then (p * q) ^ (n / 2) else (p * q) ^ (n / 2) * p

theorem altE_even (r : ℕ) : altE p q (2 * r) = (p * q) ^ r := by
  rw [altE, if_pos (even_two_mul r), Nat.mul_div_cancel_left r two_pos]

theorem altE_odd (r : ℕ) : altE p q (2 * r + 1) = (p * q) ^ r * p := by
  rw [altE, if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one r)]
  congr 2; omega

theorem altE_succ_even (r : ℕ) : altE p q (2 * r + 1) = altE p q (2 * r) * p := by
  rw [altE_odd, altE_even]

theorem altE_succ_odd (r : ℕ) : altE p q (2 * r + 2) = altE p q (2 * r + 1) * q := by
  rw [show 2 * r + 2 = 2 * (r + 1) by ring, altE_even, altE_odd, pow_succ, mul_assoc]

theorem altE_eq_zero_of_le (n : ℕ) (hn : altE p q n = 0) : ∀ n', n ≤ n' → altE p q n' = 0 := by
  intro n' hn'
  induction n' with
  | zero => obtain rfl : n = 0 := by omega
            exact hn
  | succ n' ih =>
      rcases Nat.eq_or_lt_of_le hn' with h | h
      · rw [← h]; exact hn
      · have ih' := ih (by omega)
        rcases Nat.even_or_odd n' with ⟨r, hr⟩ | ⟨r, hr⟩
        · rw [show n' + 1 = 2 * r + 1 by omega, altE_succ_even, show 2 * r = n' by omega, ih',
            zero_mul]
        · rw [show n' + 1 = 2 * r + 2 by omega, altE_succ_odd, show 2 * r + 1 = n' by omega, ih',
            zero_mul]

variable {p q} (hp : p * p = 0) (hq : q * q = 0)

include hp hq in
/-- **Alternating words above the nilpotency degree vanish**: if `(p + q)^N = 0`,
then `altE (N + 1) = 0`. -/
theorem altE_zero_of_pow {N : ℕ} (hN : 1 ≤ N) (hpow : (p + q) ^ N = 0) :
    ∀ n, N + 1 ≤ n → altE p q n = 0 := by
  apply altE_eq_zero_of_le p q (N + 1)
  rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- `N = 2r`: `(pq)^r + (qp)^r = 0`, multiply by `p` on the left
    have hr1 : 1 ≤ r := by omega
    rw [show N = 2 * r by omega, add_sq_pow p q hp hq r hr1] at hpow
    have h1 : p * (p * q) ^ r = 0 := by
      obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [pow_succ', ← mul_assoc, ← mul_assoc, hp, zero_mul, zero_mul]
    rw [show N + 1 = 2 * r + 1 by omega, altE_odd]
    -- `p (qp)^r = (pq)^r p`
    have e : p * (q * p) ^ r = (p * q) ^ r * p := q_mul_pq_pow q p r
    have hh := congrArg (p * ·) hpow
    simp only [mul_add, mul_zero, h1, zero_add] at hh
    rwa [e] at hh
  · -- `N = 2r + 1`: `(pq)^r p + (qp)^r q = 0`, multiply by `p` on the left
    rw [show N = 2 * r + 1 by omega, add_sq_pow_succ p q hp hq r] at hpow
    have hh := congrArg (p * ·) hpow
    simp only [mul_add, mul_zero] at hh
    have h1 : p * ((p * q) ^ r * p) = 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr'
      · simp [hp]
      · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [pow_succ', ← mul_assoc, ← mul_assoc, ← mul_assoc, hp]; simp
    rw [h1, zero_add, ← mul_assoc, q_mul_pq_pow q p r, mul_assoc, ← pow_succ] at hh
    rw [show N + 1 = 2 * (r + 1) by omega, altE_even]
    exact hh

end Alt

variable {M : Type*} [AddCommGroup M]

section D

variable {L : Fin 3 → ℕ} (D : TraceData L M) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
  (hbc : b ≠ c) (hLa : L a = 0) (hLb : L b = 0)

include hLa in
theorem xa_sq : x L a * x L a = 0 := by have := x_pow L a; rwa [hLa, zero_add, sq] at this

include hLb in
theorem xb_sq : x L b * x L b = 0 := by have := x_pow L b; rwa [hLb, zero_add, sq] at this

include hab hac hbc in
theorem xc_eq : x L c = -(x L a + x L b) := by
  have := sum_x L
  rw [sum_fin_three _ hab hac hbc] at this
  exact eq_neg_of_add_eq_zero_right this

include hab hac hbc hLa hLb in
/-- **Alternating words vanish above degree `N = L c + 2`.** -/
theorem altE_zero (n : ℕ) (hn : L c + 3 ≤ n) : altE (x L a) (x L b) n = 0 := by
  have hpow : (x L a + x L b) ^ (L c + 2) = 0 := by
    have h := x_pow L c
    rw [xc_eq hab hac hbc] at h
    rcases (L c + 2).even_or_odd with he | ho
    · rwa [he.neg_pow] at h
    · rwa [ho.neg_pow, neg_eq_zero] at h
  exact altE_zero_of_pow (xa_sq hLa) (xb_sq hLb) (by omega) hpow n (by omega)

include hab hac hbc hLa hLb in
/-- **Every positive trace is a multiple of the trace of the alternating word.** -/
theorem trace_D_span (hθ : (D.θ a = a ∧ D.θ b = b) ∨ (D.θ a = b ∧ D.θ b = a))
    {w : List (Fin 3)} (hw : w ≠ []) :
    ∃ z : ℤ, D.tr w = z • D.trR (altE (x L a) (x L b) w.length) := by
  set p := x L a
  set q := x L b
  have hp : p * p = 0 := xa_sq hLa
  have hq : q * q = 0 := xb_sq hLb
  have rot : ∀ g h : R L, D.trR (g * h) = D.trR (h * D.twR g) := D.trR_rotate
  have tp : D.twR p = x L (D.θ a) := D.twR_x a
  have tq : D.twR q = x L (D.θ b) := D.twR_x b
  have hn : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  have hgen : ∀ g ∈ altW p q w.length, ∃ z : ℤ, D.trR g = z • D.trR (altE p q w.length) := by
    intro g hg
    unfold altW at hg
    split_ifs at hg with he
    · obtain ⟨r, hr⟩ := he
      rw [show w.length / 2 = r by omega] at hg
      have hr1 : 1 ≤ r := by omega
      rw [show w.length = 2 * r by omega, altE_even]
      rcases hg with rfl | rfl
      · exact ⟨1, (one_smul _ _).symm⟩
      · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have e2 : (q * p) ^ (r + 1) = q * (p * (q * p) ^ r) := by rw [pow_succ']; noncomm_ring
        rcases hθ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · refine ⟨1, ?_⟩
          rw [one_smul, e2, rot, tq, hb, q_mul_pq_pow q p r, mul_assoc, ← pow_succ]
        · refine ⟨0, ?_⟩
          rw [zero_smul, e2, rot, tq, hb, q_mul_pq_pow, mul_assoc, hp, mul_zero, map_zero]
    · obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.1 he
      rw [show w.length / 2 = r by omega] at hg
      rw [show w.length = 2 * r + 1 by omega, altE_odd]
      rcases hg with rfl | rfl
      · exact ⟨1, (one_smul _ _).symm⟩
      · rcases hθ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · refine ⟨0, ?_⟩
          rw [zero_smul]
          rcases Nat.eq_zero_or_pos r with rfl | hr'
          · simpa using D.trR_fixed b hb 1 le_rfl
          obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          rw [pow_succ', mul_assoc, mul_assoc, rot, tq, hb, mul_assoc, mul_assoc, hq,
            mul_zero, mul_zero, map_zero]
        · refine ⟨1, ?_⟩
          rw [one_smul]
          have := rot ((p * q) ^ r * p) 1
          have e : D.twR ((p * q) ^ r * p) = (q * p) ^ r * q := by
            rw [map_mul, map_pow, map_mul, tp, tq, ha, hb]
          rw [mul_one, one_mul, e] at this
          exact this.symm
  rw [← D.trR_word]
  have key : ∀ y ∈ AddSubgroup.closure (altW p q w.length),
      ∃ z : ℤ, D.trR y = z • D.trR (altE p q w.length) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem g hg => exact hgen g hg
    | zero => exact ⟨0, by simp⟩
    | add g g' _ _ h h' =>
        obtain ⟨z, hz⟩ := h; obtain ⟨z', hz'⟩ := h'
        exact ⟨z + z', by rw [map_add, hz, hz', add_smul]⟩
    | neg g _ h =>
        obtain ⟨z, hz⟩ := h
        exact ⟨-z, by rw [map_neg, hz, neg_smul]⟩
  exact key _ (prod_mem_alt hab hac hbc hp hq (xc_eq hab hac hbc) w)

include hLa hLb in
/-- With the trivial twist on the short arms, odd alternating words have zero trace. -/
theorem trace_altE_odd (ha : D.θ a = a) (hb : D.θ b = b) (r : ℕ) :
    D.trR (altE (x L a) (x L b) (2 * r + 1)) = 0 := by
  rw [altE_odd]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa using D.trR_fixed a ha 1 le_rfl
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ', mul_assoc, mul_assoc, D.trR_rotate, D.twR_x, ha, mul_assoc, mul_assoc,
    xa_sq hLa, mul_zero, mul_zero, map_zero]

include hLb in
/-- With the short-arm interchange, even alternating words have zero trace. -/
theorem trace_altE_even (ha : D.θ a = b) (r : ℕ) (hr : 1 ≤ r) :
    D.trR (altE (x L a) (x L b) (2 * r)) = 0 := by
  rw [altE_even]
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [show (x L a * x L b) ^ (r + 1) = x L a * (x L b * (x L a * x L b) ^ r) by
      rw [pow_succ']; noncomm_ring, D.trR_rotate, D.twR_x, ha, q_mul_pq_pow, mul_assoc, xb_sq hLb,
    mul_zero, map_zero]

end D

end TraceAlg

end MultiplicativeBasisDeformations
