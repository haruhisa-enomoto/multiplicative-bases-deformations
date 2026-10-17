import MultiplicativeBasisDeformations.Foundations.TraceE78
import MultiplicativeBasisDeformations.Foundations.StarCase

/-!
# Twisted traces killed by two (Lemma B.2, the trace calculations)

`characteristic-two-mesh-calculations.tex` (proof of `lem:integral-mesh-cokernels`),
over an arbitrary coefficient group (no division by two):

* type `D`: "In either case the fixed long-arm power gives `0 = [(-x-y)^j] = ±2[w_j]`.
  Thus every possible retained type-`D` trace quotient is killed by two." (`trace_D_two`,
  `trace_D_any_two`);
* the reflection of `E₆`: "`[ξ₆] = [(xyx²)y] = -[x²yx²] = -[ξ₆]`" (`trace_E6r_two`);
* `E₇`, `E₈`: the candidate classes `[yx³]`, `[(yx³)²]`, `[(yx³)(yx⁴)²]` of word degrees
  `4, 8, 14` are killed by two (`trace_E78_two`), by the identities of Lemma A.6 without
  its final division.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

open TraceData

variable {M : Type*} [AddCommGroup M]

/-! ### Type `D` -/

/-- **Type `D`**: with short arms `a, b` and long arm `c` fixed by the twist, every positive
trace is killed by two. -/
theorem trace_D_two {L : Fin 3 → ℕ} (D : TraceData L M)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hLa : L a = 0) (hLb : L b = 0)
    (hθc : D.θ c = c) (hθ : (D.θ a = a ∧ D.θ b = b) ∨ (D.θ a = b ∧ D.θ b = a))
    {w : List (Fin 3)} (hw : w ≠ []) : D.tr w + D.tr w = 0 := by
  set p := x L a
  set q := x L b
  have hp : p * p = 0 := by have := x_pow L a; rwa [hLa, zero_add, sq] at this
  have hq : q * q = 0 := by have := x_pow L b; rwa [hLb, zero_add, sq] at this
  have hz : x L c = -(p + q) := by
    have := sum_x L
    rw [sum_fin_three _ hab hac hbc] at this
    exact eq_neg_of_add_eq_zero_right this
  have hzpow : ∀ n, 1 ≤ n → D.trR ((p + q) ^ n) = 0 := by
    intro n hn
    have := D.trR_fixed c hθc n hn
    rw [hz] at this
    rcases n.even_or_odd with he | ho
    · rwa [he.neg_pow] at this
    · rwa [ho.neg_pow, map_neg, neg_eq_zero] at this
  have rot : ∀ g h : R L, D.trR (g * h) = D.trR (h * D.twR g) := D.trR_rotate
  have tp : D.twR p = x L (D.θ a) := D.twR_x a
  have tq : D.twR q = x L (D.θ b) := D.twR_x b
  have heven : ∀ r, 1 ≤ r → D.trR ((p * q) ^ r) + D.trR ((p * q) ^ r) = 0 ∧
      D.trR ((q * p) ^ r) + D.trR ((q * p) ^ r) = 0 := by
    intro r hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have e1 : (p * q) ^ (r + 1) = p * (q * (p * q) ^ r) := by rw [pow_succ']; noncomm_ring
    have e2 : (q * p) ^ (r + 1) = q * (p * (q * p) ^ r) := by rw [pow_succ']; noncomm_ring
    rcases hθ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h1 : D.trR ((p * q) ^ (r + 1)) = D.trR ((q * p) ^ (r + 1)) := by
        rw [e1, rot, tp, ha]
        congr 1
        rw [q_mul_pq_pow p q r, mul_assoc, ← pow_succ]
      have hsum := hzpow (2 * (r + 1)) (by omega)
      rw [add_sq_pow p q hp hq (r + 1) (by omega), map_add] at hsum
      refine ⟨?_, ?_⟩
      · nth_rewrite 2 [h1]; exact hsum
      · nth_rewrite 1 [← h1]; exact hsum
    · constructor
      · rw [e1, rot, tp, ha, q_mul_pq_pow, mul_assoc, hq, mul_zero, map_zero, add_zero]
      · rw [e2, rot, tq, hb, q_mul_pq_pow, mul_assoc, hp, mul_zero, map_zero, add_zero]
  have hodd : ∀ r, D.trR ((p * q) ^ r * p) + D.trR ((p * q) ^ r * p) = 0 ∧
      D.trR ((q * p) ^ r * q) + D.trR ((q * p) ^ r * q) = 0 := by
    intro r
    rcases hθ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [pow_zero, one_mul]
        have h1 := D.trR_fixed a ha 1 le_rfl
        have h2 := D.trR_fixed b hb 1 le_rfl
        rw [pow_one] at h1 h2
        exact ⟨by rw [h1, add_zero], by rw [h2, add_zero]⟩
      obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      constructor
      · rw [pow_succ', mul_assoc, mul_assoc, rot, tp, ha, mul_assoc, mul_assoc, hp,
          mul_zero, mul_zero, map_zero, add_zero]
      · rw [pow_succ', mul_assoc, mul_assoc, rot, tq, hb, mul_assoc, mul_assoc, hq,
          mul_zero, mul_zero, map_zero, add_zero]
    · have h1 : D.trR ((p * q) ^ r * p) = D.trR ((q * p) ^ r * q) := by
        have := rot ((p * q) ^ r * p) 1
        have e : D.twR ((p * q) ^ r * p) = (q * p) ^ r * q := by
          rw [map_mul, map_pow, map_mul, tp, tq, ha, hb]
        rw [mul_one, one_mul, e] at this
        exact this
      have hsum := hzpow (2 * r + 1) (by omega)
      rw [add_sq_pow_succ p q hp hq r, map_add] at hsum
      refine ⟨?_, ?_⟩
      · nth_rewrite 2 [h1]; exact hsum
      · nth_rewrite 1 [← h1]; exact hsum
  have hvan : ∀ n, 1 ≤ n → ∀ g ∈ altW p q n, D.trR g + D.trR g = 0 := by
    intro n hn g hg
    unfold altW at hg
    split_ifs at hg with he
    · obtain ⟨r, rfl⟩ := he
      rw [show (r + r) / 2 = r by omega] at hg
      rcases hg with rfl | rfl
      · exact (heven r (by omega)).1
      · exact (heven r (by omega)).2
    · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.1 he
      rw [show (2 * r + 1) / 2 = r by omega] at hg
      rcases hg with rfl | rfl
      · exact (hodd r).1
      · exact (hodd r).2
  rw [← D.trR_word]
  have hn : 1 ≤ w.length := List.length_pos_of_ne_nil hw
  have key : ∀ y ∈ AddSubgroup.closure (altW p q w.length), D.trR y + D.trR y = 0 := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem g hg => exact hvan _ hn g hg
    | zero => simp
    | add g g' _ _ h h' => rw [map_add]; rw [show D.trR g + D.trR g' + (D.trR g + D.trR g') =
        (D.trR g + D.trR g) + (D.trR g' + D.trR g') by abel, h, h', add_zero]
    | neg g _ h => rw [map_neg, ← neg_add, h, neg_zero]
  exact key _ (prod_mem_alt hab hac hbc hp hq hz w)

/-- **Type `D` with any twist preserving the arm lengths**: all traces of length at least two
are killed by two. -/
theorem trace_D_any_two {L : Fin 3 → ℕ} (D : TraceData L M) {a b c : Fin 3} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hLa : L a = 0) (hLb : L b = 0) {w : List (Fin 3)}
    (hw : 2 ≤ w.length) : D.tr w + D.tr w = 0 := by
  have hne : w ≠ [] := by rintro rfl; simp at hw
  have hθL := D.hL
  by_cases hLc : L c = 0
  · have hall : ∀ i, L i = 0 := fun i ↦ by
      rcases fin_three_cases hab hac hbc i with rfl | rfl | rfl <;> assumption
    by_cases hfix : ∃ e, D.θ e = e
    · obtain ⟨e, he⟩ := hfix
      obtain ⟨a', b', ha'b', ha'e, hb'e, hcov⟩ : ∃ a' b' : Fin 3, a' ≠ b' ∧ a' ≠ e ∧ b' ≠ e ∧
          ∀ i, i = a' ∨ i = b' ∨ i = e := by
        fin_cases e
        · exact ⟨1, 2, by decide, by decide, by decide, fun i ↦ by fin_cases i <;> simp⟩
        · exact ⟨0, 2, by decide, by decide, by decide, fun i ↦ by fin_cases i <;> simp⟩
        · exact ⟨0, 1, by decide, by decide, by decide, fun i ↦ by fin_cases i <;> simp⟩
      refine trace_D_two D ha'b' ha'e hb'e (hall a') (hall b') he ?_ hne
      have ha' : D.θ a' ≠ e := fun h ↦ ha'e (D.θ.injective (h.trans he.symm))
      have hb' : D.θ b' ≠ e := fun h ↦ hb'e (D.θ.injective (h.trans he.symm))
      rcases hcov (D.θ a') with h1 | h1 | h1
      · left; refine ⟨h1, ?_⟩
        rcases hcov (D.θ b') with h3 | h3 | h3
        · exact absurd (D.θ.injective (h3.trans h1.symm)) (Ne.symm ha'b')
        · exact h3
        · exact absurd h3 hb'
      · right; refine ⟨h1, ?_⟩
        rcases hcov (D.θ b') with h3 | h3 | h3
        · exact h3
        · exact absurd (D.θ.injective (h3.trans h1.symm)) (Ne.symm ha'b')
        · exact absurd h3 hb'
      · exact absurd h1 ha'
    · push_neg at hfix
      rw [trace_D4_cycle hall D hfix hw, add_zero]
  · have hθc : D.θ c = c := by
      rcases fin_three_cases hab hac hbc (D.θ c) with h | h | h
      · exact absurd ((hθL c).symm.trans (h ▸ hLa)) hLc
      · exact absurd ((hθL c).symm.trans (h ▸ hLb)) hLc
      · exact h
    have ha : D.θ a ≠ c := fun h ↦ hac (D.θ.injective (h.trans hθc.symm))
    have hb : D.θ b ≠ c := fun h ↦ hbc (D.θ.injective (h.trans hθc.symm))
    refine trace_D_two D hab hac hbc hLa hLb hθc ?_ hne
    rcases fin_three_cases hab hac hbc (D.θ a) with h1 | h1 | h1
    · left; refine ⟨h1, ?_⟩
      rcases fin_three_cases hab hac hbc (D.θ b) with h3 | h3 | h3
      · exact absurd (D.θ.injective (h3.trans h1.symm)) (Ne.symm hab)
      · exact h3
      · exact absurd h3 hb
    · right; refine ⟨h1, ?_⟩
      rcases fin_three_cases hab hac hbc (D.θ b) with h3 | h3 | h3
      · exact h3
      · exact absurd (D.θ.injective (h3.trans h1.symm)) (Ne.symm hab)
      · exact absurd h3 hb
    · exact absurd h1 ha

/-! ### The corner identities of the types `E` -/

section Corner

variable {S : Type*} [Ring S] {x y : S} (hy3 : y ^ 3 = 0)
  (hd1 : y * y + y * x + x * y + x * x = 0)

include hy3 hd1 in
theorem e_d2 : y * x * y - x * y * x - x ^ 3 = 0 := by
  have e : y * x * y - x * y * x - x ^ 3 =
      y * (y * y + y * x + x * y + x * x) - (y * y + y * x + x * y + x * x) * x - y ^ 3 := by
    noncomm_ring
  rw [e, hd1, hy3]; simp

include hy3 hd1 in
theorem e_d3 : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y +
    2 * x ^ 4 = 0 := by
  have e : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4 =
      (y * y + y * x + x * y + x * x) * x * y - x * (y * x * y - x * y * x - x ^ 3) -
        y * (y * x * y - x * y * x - x ^ 3) - (y * x * y - x * y * x - x ^ 3) * x := by
    noncomm_ring
  rw [e, hd1, e_d2 hy3 hd1]; simp

include hy3 hd1 in
theorem e_F (hx5 : x ^ 5 = 0) : y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y -
    x ^ 2 * y * x ^ 3 - x ^ 3 * y * x ^ 2 = 0 := by
  have e : y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
      x ^ 3 * y * x ^ 2 =
      -((y * x * y - x * y * x - x ^ 3) * x ^ 2 * y -
        y * x * (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4) +
        (y * x * y - x * y * x - x ^ 3) * x ^ 3 +
        (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4) * x ^ 2) -
      x ^ 5 * y + x ^ 5 * x - y * x ^ 5 := by noncomm_ring
  rw [e, e_d2 hy3 hd1, e_d3 hy3 hd1, hx5]; simp

end Corner

/-! ### The types `E` -/

section E

variable {L : Fin 3 → ℕ} (D : TraceData L M) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
  (hbc : b ≠ c) (hLa : L a = 0) (hLb : L b = 1)

include hab hac hbc hLa in
theorem e_hd1 : x L b * x L b + x L b * x L c + x L c * x L b + x L c * x L c = 0 := by
  have hs := sum_x L
  rw [sum_fin_three _ hab hac hbc] at hs
  have hz : x L a = -(x L c + x L b) := by rw [eq_neg_iff_add_eq_zero, ← hs]; abel
  have := x_pow L a
  rw [hLa, zero_add, hz, neg_sq, sq] at this
  rw [← this]; noncomm_ring

include hLb in
theorem e_hy3 : x L b ^ 3 = 0 := by have := x_pow L b; rwa [hLb] at this

include hab hac hbc hLa hLb in
/-- **The reflection of `E₆`**: `[x²yx²] = -[x²yx²]`. -/
theorem trace_E6r_two (hLc : L c = 1) (hθc : D.θ c = b) :
    D.tr [c, c, b, c, c] + D.tr [c, c, b, c, c] = 0 := by
  set X := x L c
  set Y := x L b
  have hX3 : X ^ 3 = 0 := by have := x_pow L c; rwa [hLc] at this
  have hd3 := e_d3 (e_hy3 hLb) (e_hd1 hab hac hbc hLa)
  have hX4 : X ^ 4 = 0 := by rw [show 4 = 3 + 1 from rfl, pow_add, hX3, zero_mul]
  have hd3' : Y * X ^ 2 * Y + X * Y * X ^ 2 + X ^ 2 * Y * X = 0 := by
    rw [← hd3, hX3, hX4]; noncomm_ring
  have hyx2y : Y * X ^ 2 * Y = -(X * Y * X ^ 2) - X ^ 2 * Y * X := by
    rw [← sub_eq_zero, ← hd3']; noncomm_ring
  have hw : D.tr [c, c, b, c, c] = D.trR (X ^ 2 * Y * X ^ 2) := by
    rw [← D.trR_word]; simp [X, Y, sq, mul_assoc]
  have hrot : D.trR (X ^ 2 * Y * X ^ 2) = -D.trR (X ^ 2 * Y * X ^ 2) := by
    have h := D.trR_rotate X (X * Y * X ^ 2)
    rw [D.twR_x, hθc] at h
    have e1 : X * (X * Y * X ^ 2) = X ^ 2 * Y * X ^ 2 := by noncomm_ring
    have e2 : X * Y * X ^ 2 * x L b = -(X ^ 2 * Y * X ^ 2) - X ^ 3 * Y * X := by
      rw [show X * Y * X ^ 2 * x L b = X * (Y * X ^ 2 * Y) by simp only [Y, mul_assoc], hyx2y]
      noncomm_ring
    rw [e1, e2, hX3, zero_mul, zero_mul, sub_zero, map_neg] at h
    exact h
  rw [hw]
  nth_rewrite 1 [hrot]
  exact neg_add_cancel _

theorem twR_id (hθ : ∀ i, D.θ i = i) (r : R L) : D.twR r = r := by
  have : D.twR.comp (TraceAlg.mk L) = TraceAlg.mk L := by
    ext i
    simp only [RingHom.comp_apply]
    change D.twR (x L i) = x L i
    rw [D.twR_x, hθ]
  obtain ⟨a, rfl⟩ := TraceAlg.mk_surjective L r
  exact congrArg (fun f : FreeRing (Fin 3) →+* R L ↦ f a) this

include hab hac hbc hLa hLb in
/-- **The candidates of `E₇`, `E₈` are killed by two**: the classes of word degrees
`4, 8, 14`. -/
theorem trace_E78_two (hLc : L c ≤ 3) (hθ : ∀ i, D.θ i = i) :
    (D.tr [b, c, c, c] + D.tr [b, c, c, c] = 0) ∧
      (D.tr [b, c, c, c, b, c, c, c] + D.tr [b, c, c, c, b, c, c, c] = 0) ∧
      (D.tr [b, c, c, c, b, c, c, c, c, b, c, c, c, c] +
        D.tr [b, c, c, c, b, c, c, c, c, b, c, c, c, c] = 0) := by
  set X := x L c
  set Y := x L b
  have hy3 := e_hy3 hLb
  have hd1 := e_hd1 hab hac hbc hLa
  have hd3 := e_d3 hy3 hd1
  have hX5 : X ^ 5 = 0 := by
    have := x_pow L c
    rw [show 5 = (L c + 2) + (3 - L c) by omega, pow_add, this, zero_mul]
  have hXk : ∀ k, 5 ≤ k → X ^ k = 0 := fun k hk ↦ by
    rw [show k = 5 + (k - 5) by omega, pow_add, hX5, zero_mul]
  have hF := e_F hy3 hd1 hX5
  set T := D.trR
  have rot : ∀ p q : R L, T (p * q) = T (q * p) := fun p q ↦ by
    rw [D.trR_rotate, twR_id D hθ]
  have xp : ∀ q, 1 ≤ q → T (X ^ q) = 0 := fun q hq ↦ D.trR_fixed c (hθ c) q hq
  have word : ∀ w : List (Fin 3), D.tr w = T ((w.map (x L)).prod) := fun w ↦ (D.trR_word w).symm
  -- word degree four
  have t4 : T (Y * X ^ 3) + T (Y * X ^ 3) = 0 := by
    have e3 := congrArg T hd3
    have e1 := congrArg T (congrArg (· * X ^ 2) hd1)
    simp only [add_mul, zero_mul] at e1
    have r1 : T (Y * X ^ 2 * Y) = T (Y * Y * X ^ 2) := by rw [rot (Y * X ^ 2) Y, ← mul_assoc]
    have r2 : T (X * Y * X ^ 2) = T (Y * X ^ 3) := by
      rw [mul_assoc, rot X, show Y * X ^ 2 * X = Y * X ^ 3 by rw [mul_assoc, ← pow_succ]]
    have r3 : T (X ^ 2 * Y * X) = T (Y * X ^ 3) := by
      rw [mul_assoc, rot (X ^ 2), mul_assoc, ← pow_succ']
    have r4 : T (X ^ 3 * Y) = T (Y * X ^ 3) := rot _ _
    have r5 : T (Y * X * X ^ 2) = T (Y * X ^ 3) := by rw [mul_assoc, ← pow_succ']
    have r7 : T (X * X * X ^ 2) = 0 := by rw [← sq, ← pow_add]; exact xp _ (by norm_num)
    have r8 : T (2 * X ^ 4) = 0 := by rw [two_mul, map_add, xp 4 (by norm_num), add_zero]
    rw [map_add, map_add, map_add, map_add, map_add, map_zero, r1, r2, r3, r4, r8] at e3
    rw [map_add, map_add, map_add, map_zero, r5, r2, r7] at e1
    have : T (Y * X ^ 3) + T (Y * X ^ 3) =
        (T (Y * Y * X ^ 2) + T (Y * X ^ 3) + T (Y * X ^ 3) + T (Y * X ^ 3) + T (Y * X ^ 3) + 0) -
          (T (Y * Y * X ^ 2) + T (Y * X ^ 3) + T (Y * X ^ 3) + 0) := by abel
    rw [this, e3, e1, sub_zero]
  have z7 : ∀ k, 5 ≤ k → ∀ p q : R L, p * X ^ k * q = 0 := fun k hk p q ↦ by
    rw [hXk k hk, mul_zero, zero_mul]
  -- word degree eight: `[yx⁴yx²] = 0`, then `F x²`
  have a1 : T (Y * X ^ 4 * Y * X ^ 2) = 0 := by
    have h := congrArg (· * X ^ 4) hd3
    simp only [zero_mul] at h
    have e : Y * X ^ 2 * Y * X ^ 4 + X ^ 3 * Y * X ^ 4 =
        (Y * X ^ 2 * Y + Y * X ^ 3 + X * Y * X ^ 2 + X ^ 2 * Y * X + X ^ 3 * Y + 2 * X ^ 4) *
            X ^ 4 - (Y * X ^ 7 * 1 + X * Y * X ^ 6 + X ^ 2 * Y * X ^ 5 * 1 + 2 * X ^ 8 * 1) := by
      noncomm_ring
    rw [h, z7 7 (by norm_num), show X * Y * X ^ 6 = X * Y * X ^ 6 * 1 by rw [mul_one],
      z7 6 (by norm_num), z7 5 le_rfl, show (2 : R L) * X ^ 8 * 1 = 2 * X ^ 8 * 1 from rfl,
      z7 8 (by norm_num)] at e
    simp only [add_zero, sub_zero] at e
    have e2 : Y * X ^ 2 * Y * X ^ 4 = -(X ^ 3 * Y * X ^ 4) := eq_neg_of_add_eq_zero_left e
    have e3 : T (X ^ 3 * Y * X ^ 4) = 0 := by
      rw [rot, show X ^ 4 * (X ^ 3 * Y) = 1 * X ^ 7 * Y by rw [one_mul, ← mul_assoc, ← pow_add],
        z7 7 (by norm_num), map_zero]
    rw [show Y * X ^ 4 * Y * X ^ 2 = (Y * X ^ 4) * (Y * X ^ 2) by simp only [mul_assoc], rot,
      show Y * X ^ 2 * (Y * X ^ 4) = Y * X ^ 2 * Y * X ^ 4 by simp only [mul_assoc], e2, map_neg,
      e3, neg_zero]
  have t8 : T (Y * X ^ 3 * Y * X ^ 3) + T (Y * X ^ 3 * Y * X ^ 3) = 0 := by
    have e : Y * X ^ 3 * Y * X ^ 3 + X * Y * X ^ 3 * Y * X ^ 2 =
        (Y * X ^ 3 * Y * X + Y * X ^ 4 * Y + X * Y * X ^ 3 * Y - X ^ 2 * Y * X ^ 3 -
          X ^ 3 * Y * X ^ 2) * X ^ 2 - Y * X ^ 4 * Y * X ^ 2 + X ^ 2 * Y * X ^ 5 * 1 +
          X ^ 3 * Y * X ^ 4 := by noncomm_ring
    rw [hF, zero_mul, zero_sub, z7 5 le_rfl, add_zero] at e
    have e3 : T (X ^ 3 * Y * X ^ 4) = 0 := by
      rw [rot, show X ^ 4 * (X ^ 3 * Y) = 1 * X ^ 7 * Y by rw [one_mul, ← mul_assoc, ← pow_add],
        z7 7 (by norm_num), map_zero]
    have r : T (X * Y * X ^ 3 * Y * X ^ 2) = T (Y * X ^ 3 * Y * X ^ 3) := by
      rw [show X * Y * X ^ 3 * Y * X ^ 2 = X * (Y * X ^ 3 * Y * X ^ 2) by simp only [mul_assoc],
        rot, show Y * X ^ 3 * Y * X ^ 2 * X = Y * X ^ 3 * Y * X ^ 3 by
          rw [mul_assoc _ (X ^ 2), ← pow_succ]]
    have := congrArg T e
    rw [map_add, map_add, map_neg, a1, e3, r, neg_zero, zero_add] at this
    simpa using this
  -- word degree fourteen: `F x³ (yx⁴)`
  have t14 : T (Y * X ^ 3 * Y * X ^ 4 * Y * X ^ 4) + T (Y * X ^ 3 * Y * X ^ 4 * Y * X ^ 4) = 0 := by
    have e : Y * X ^ 3 * Y * X ^ 4 * Y * X ^ 4 + Y * X ^ 4 * Y * X ^ 3 * Y * X ^ 4 =
        (Y * X ^ 3 * Y * X + Y * X ^ 4 * Y + X * Y * X ^ 3 * Y - X ^ 2 * Y * X ^ 3 -
          X ^ 3 * Y * X ^ 2) * (X ^ 3 * Y * X ^ 4) - X * Y * X ^ 3 * Y * X ^ 3 * Y * X ^ 4 +
          X ^ 2 * Y * X ^ 6 * (Y * X ^ 4) + X ^ 3 * Y * X ^ 5 * (Y * X ^ 4) := by noncomm_ring
    rw [hF, zero_mul, zero_sub, z7 6 (by norm_num), z7 5 le_rfl, add_zero, add_zero] at e
    have r1 : T (X * Y * X ^ 3 * Y * X ^ 3 * Y * X ^ 4) = 0 := by
      rw [show X * Y * X ^ 3 * Y * X ^ 3 * Y * X ^ 4 = X * (Y * X ^ 3 * Y * X ^ 3 * Y * X ^ 4) by
        simp only [mul_assoc], rot, show Y * X ^ 3 * Y * X ^ 3 * Y * X ^ 4 * X =
          Y * X ^ 3 * Y * X ^ 3 * Y * X ^ 5 * 1 by rw [mul_one, mul_assoc _ (X ^ 4), ← pow_succ],
        z7 5 le_rfl, map_zero]
    have r2 : T (Y * X ^ 4 * Y * X ^ 3 * Y * X ^ 4) = T (Y * X ^ 3 * Y * X ^ 4 * Y * X ^ 4) := by
      rw [show Y * X ^ 4 * Y * X ^ 3 * Y * X ^ 4 = (Y * X ^ 4) * (Y * X ^ 3 * Y * X ^ 4) by
        simp only [mul_assoc], rot]
      simp only [mul_assoc]
    have := congrArg T e
    rw [map_add, map_neg, r1, neg_zero, r2] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [word]; simpa [X, Y, pow_succ, mul_assoc] using t4
  · rw [word]; simpa [X, Y, pow_succ, mul_assoc] using t8
  · rw [word]; simpa [X, Y, pow_succ, mul_assoc] using t14

end E

end TraceAlg

end MultiplicativeBasisDeformations
