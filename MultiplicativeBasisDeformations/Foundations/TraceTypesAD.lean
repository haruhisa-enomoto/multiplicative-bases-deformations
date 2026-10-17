import MultiplicativeBasisDeformations.Foundations.TraceAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Twisted traces of types `A` and `D` (Appendix A, "Types A and D")

`periodic-mesh-calculations.tex:423–476`, assuming `char k ≠ 2` in the form
"`m + m = 0` implies `m = 0`" on the target group:

* a path rooted at an end (one arm): `x_1 = 0` by the centre relation;
* a path rooted at its middle vertex (two arms of equal length): the two closed
  paths are `x` and `-x`, and reflection sends `x` to `-x`;
* type `D` with the short arms `a, b` and long arm `c`, with trivial twist or
  with the short-arm interchange;
* `D_4` with a three-cycle of the arms.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

open TraceData

variable {M : Type*} [AddCommGroup M]

/-- **One arm**: every positive trace vanishes. -/
theorem trace_A1 {L : Fin 1 → ℕ} (D : TraceData L M) {w : List (Fin 1)} (hw : w ≠ []) :
    D.tr w = 0 := by
  obtain ⟨i, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  have := D.centre [] w'
  simp only [Fin.sum_univ_one, List.nil_append] at this
  rwa [Subsingleton.elim i 0]

/-- **Two arms of equal length** (path of odd length rooted at its middle): every
positive trace vanishes, for the trivial twist and for the reflection. -/
theorem trace_A2 {L : Fin 2 → ℕ} (D : TraceData L M) (h2 : ∀ m : M, m + m = 0 → m = 0)
    {w : List (Fin 2)} (hw : w ≠ []) : D.tr w = 0 := by
  have hx1 : x L 1 = -x L 0 := by
    have := sum_x L
    rw [Fin.sum_univ_two] at this
    exact eq_neg_of_add_eq_zero_right this
  have hprod : ∀ w : List (Fin 2), (w.map (x L)).prod = x L 0 ^ w.length ∨
      (w.map (x L)).prod = -(x L 0 ^ w.length) := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
        fin_cases i
        · rcases ih with h | h <;> rw [h]
          · exact Or.inl rfl
          · exact Or.inr (mul_neg _ _)
        · simp only [Fin.mk_one, hx1]
          rcases ih with h | h <;> rw [h]
          · exact Or.inr (neg_mul _ _)
          · exact Or.inl (by rw [neg_mul, mul_neg, neg_neg])
  have hpow : ∀ n, 1 ≤ n → D.trR (x L 0 ^ n) = 0 := by
    intro n hn
    rcases Fin.exists_fin_two.1 ⟨D.θ 0, rfl⟩ with h0 | h0
    · exact D.trR_fixed 0 h0 n hn
    · apply h2
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have := D.trR_rotate (x L 0) (x L 0 ^ n)
      rw [twR_x, h0, hx1, ← pow_succ', mul_neg, ← pow_succ, map_neg] at this
      nth_rewrite 1 [this]
      exact neg_add_cancel _
  rw [← D.trR_word]
  rcases hprod w with h | h <;> rw [h]
  · exact hpow _ (List.length_pos_of_ne_nil hw)
  · rw [map_neg, hpow _ (List.length_pos_of_ne_nil hw), neg_zero]

/-! ### Two square-zero elements -/

section SquareZero

variable {S : Type*} [Ring S] (p q : S) (hp : p * p = 0) (hq : q * q = 0)

include hq in
theorem pq_pow_mul_q (r : ℕ) (hr : 1 ≤ r) : (p * q) ^ r * q = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ, mul_assoc, mul_assoc, hq, mul_zero, mul_zero]

theorem q_mul_pq_pow (r : ℕ) : q * (p * q) ^ r = (q * p) ^ r * q := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, ← mul_assoc, ih, pow_succ]; noncomm_ring

include hp hq in
theorem pq_add_qp_pow (r : ℕ) (hr : 1 ≤ r) : (p * q + q * p) ^ r = (p * q) ^ r + (q * p) ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
      rcases Nat.eq_zero_or_pos r with rfl | hr'
      · simp
      rw [pow_succ, ih hr', pow_succ, pow_succ]
      have h1 : (p * q) ^ r * (q * p) = 0 := by
        rw [← mul_assoc, pq_pow_mul_q p q hq r hr', zero_mul]
      have h2 : (q * p) ^ r * (p * q) = 0 := by
        rw [← mul_assoc, pq_pow_mul_q q p hp r hr', zero_mul]
      rw [add_mul, mul_add, mul_add, h1, h2]; abel

include hp hq in
theorem add_sq_pow (r : ℕ) (hr : 1 ≤ r) : (p + q) ^ (2 * r) = (p * q) ^ r + (q * p) ^ r := by
  rw [pow_mul, show (p + q) ^ 2 = p * q + q * p by rw [sq]; noncomm_ring; rw [hp, hq]; abel,
    pq_add_qp_pow p q hp hq r hr]

include hp hq in
theorem add_sq_pow_succ (r : ℕ) :
    (p + q) ^ (2 * r + 1) = (p * q) ^ r * p + (q * p) ^ r * q := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  rw [pow_succ, add_sq_pow p q hp hq r hr, add_mul, mul_add, mul_add,
    pq_pow_mul_q p q hq r hr, pq_pow_mul_q q p hp r hr]
  abel

/-- The alternating words of length `n` in `p, q`. -/
def altW (n : ℕ) : Set S :=
  if Even n then {(p * q) ^ (n / 2), (q * p) ^ (n / 2)}
  else {(p * q) ^ (n / 2) * p, (q * p) ^ (n / 2) * q}

theorem altW_symm (n : ℕ) : altW p q n = altW q p n := by
  unfold altW; split_ifs <;> exact Set.pair_comm _ _

include hp hq in
/-- Left multiplication by `p` sends alternating words to alternating words or
zero. -/
theorem p_mul_altW (n : ℕ) {y : S} (hy : y ∈ altW p q n) :
    p * y = 0 ∨ p * y ∈ altW p q (n + 1) := by
  unfold altW at hy ⊢
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨r, rfl⟩ := hn
    rw [if_pos ⟨r, rfl⟩] at hy
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨r, by ring⟩)]
    have e : (r + r) / 2 = r := by omega
    have e' : (r + r + 1) / 2 = r := by omega
    rw [e] at hy; rw [e']
    rcases hy with rfl | rfl
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · right; left; simp
      · left
        obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [pow_succ', ← mul_assoc, ← mul_assoc, hp, zero_mul, zero_mul]
    · right; left
      exact q_mul_pq_pow q p r
  · obtain ⟨r, rfl⟩ := hn
    rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨r, rfl⟩)] at hy
    rw [if_pos ⟨r + 1, by ring⟩]
    have e : (2 * r + 1) / 2 = r := by omega
    have e' : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    rw [e] at hy; rw [e']
    rcases hy with rfl | rfl
    · left
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp [hp]
      · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [pow_succ', ← mul_assoc, ← mul_assoc, ← mul_assoc, hp]; simp
    · right; left
      rw [← mul_assoc, q_mul_pq_pow q p r, mul_assoc, ← pow_succ, pow_succ']

end SquareZero

theorem sum_fin_three {N : Type*} [AddCommMonoid N] (f : Fin 3 → N) {a b c : Fin 3} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : ∑ i, f i = f a + f b + f c := by
  rw [Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> abel

theorem fin_three_cases {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 3) :
    i = a ∨ i = b ∨ i = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all

/-- The products of words lie in the span of the alternating words in the two
square-zero closed paths, once the third is eliminated. -/
theorem prod_mem_alt {L : Fin 3 → ℕ} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hp : x L a * x L a = 0) (hq : x L b * x L b = 0) (hz : x L c = -(x L a + x L b))
    (w : List (Fin 3)) :
    (w.map (x L)).prod ∈ AddSubgroup.closure (altW (x L a) (x L b) w.length) := by
  induction w with
  | nil =>
      refine AddSubgroup.subset_closure ?_
      simp [altW]
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons]
      have key : ∀ g ∈ altW (x L a) (x L b) w.length,
          x L i * g ∈ AddSubgroup.closure (altW (x L a) (x L b) (w.length + 1)) := by
        intro g hg
        have hpa : ∀ g ∈ altW (x L a) (x L b) w.length,
            x L a * g ∈ AddSubgroup.closure (altW (x L a) (x L b) (w.length + 1)) := by
          intro g hg
          rcases p_mul_altW _ _ hp hq _ hg with h | h
          · rw [h]; exact zero_mem _
          · exact AddSubgroup.subset_closure h
        have hpb : ∀ g ∈ altW (x L a) (x L b) w.length,
            x L b * g ∈ AddSubgroup.closure (altW (x L a) (x L b) (w.length + 1)) := by
          intro g hg
          rw [altW_symm] at hg ⊢
          rcases p_mul_altW _ _ hq hp _ hg with h | h
          · rw [h]; exact zero_mem _
          · exact AddSubgroup.subset_closure h
        rcases fin_three_cases hab hac hbc i with rfl | rfl | rfl
        · exact hpa g hg
        · exact hpb g hg
        · rw [hz, neg_mul, add_mul]
          exact neg_mem (add_mem (hpa g hg) (hpb g hg))
      have key' : ∀ y ∈ AddSubgroup.closure (altW (x L a) (x L b) w.length),
          x L i * y ∈ AddSubgroup.closure (altW (x L a) (x L b) (w.length + 1)) := by
        intro y hy
        induction hy using AddSubgroup.closure_induction with
        | mem g hg => exact key g hg
        | zero => simp
        | add g g' _ _ h h' => rw [mul_add]; exact add_mem h h'
        | neg g _ h => rw [mul_neg]; exact neg_mem h
      exact key' _ ih

variable {M : Type*} [AddCommGroup M]

/-- **Type `D`**: with short arms `a, b` and long arm `c` fixed by the twist, every
positive trace vanishes when two is invertible, both for the trivial twist and for
the short-arm interchange. -/
theorem trace_D {L : Fin 3 → ℕ} (D : TraceData L M) (h2 : ∀ m : M, m + m = 0 → m = 0)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hLa : L a = 0) (hLb : L b = 0)
    (hθc : D.θ c = c) (hθ : (D.θ a = a ∧ D.θ b = b) ∨ (D.θ a = b ∧ D.θ b = a))
    {w : List (Fin 3)} (hw : w ≠ []) : D.tr w = 0 := by
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
  -- the even alternating words
  have heven : ∀ r, 1 ≤ r → D.trR ((p * q) ^ r) = 0 ∧ D.trR ((q * p) ^ r) = 0 := by
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
      rw [add_sq_pow p q hp hq (r + 1) (by omega), map_add, ← h1] at hsum
      have := h2 _ hsum
      exact ⟨this, h1 ▸ this⟩
    · constructor
      · rw [e1, rot, tp, ha, q_mul_pq_pow, mul_assoc, hq, mul_zero, map_zero]
      · rw [e2, rot, tq, hb, q_mul_pq_pow, mul_assoc, hp, mul_zero, map_zero]
  -- the odd alternating words
  have hodd : ∀ r, D.trR ((p * q) ^ r * p) = 0 ∧ D.trR ((q * p) ^ r * q) = 0 := by
    intro r
    rcases hθ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [pow_zero, one_mul]
        exact ⟨by simpa using D.trR_fixed a ha 1 le_rfl, by simpa using D.trR_fixed b hb 1 le_rfl⟩
      obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      constructor
      · rw [pow_succ', mul_assoc, mul_assoc, rot, tp, ha, mul_assoc, mul_assoc, hp,
          mul_zero, mul_zero, map_zero]
      · rw [pow_succ', mul_assoc, mul_assoc, rot, tq, hb, mul_assoc, mul_assoc, hq,
          mul_zero, mul_zero, map_zero]
    · have h1 : D.trR ((p * q) ^ r * p) = D.trR ((q * p) ^ r * q) := by
        have := rot ((p * q) ^ r * p) 1
        have e : D.twR ((p * q) ^ r * p) = (q * p) ^ r * q := by
          rw [map_mul, map_pow, map_mul, tp, tq, ha, hb]
        rw [mul_one, one_mul, e] at this
        exact this
      have hsum := hzpow (2 * r + 1) (by omega)
      rw [add_sq_pow_succ p q hp hq r, map_add, ← h1] at hsum
      have := h2 _ hsum
      exact ⟨this, h1 ▸ this⟩
  have hvan : ∀ n, 1 ≤ n → ∀ g ∈ altW p q n, D.trR g = 0 := by
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
  have key : ∀ y ∈ AddSubgroup.closure (altW p q w.length), D.trR y = 0 := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem g hg => exact hvan _ hn g hg
    | zero => simp
    | add g g' _ _ h h' => rw [map_add, h, h', add_zero]
    | neg g _ h => rw [map_neg, h, neg_zero]
  exact key _ (prod_mem_alt hab hac hbc hp hq hz w)

/-- **`D_4` with a three-cycle of the arms**: the corner is spanned by `1, x, y, xy`
with `yx = -xy` and all words of length three zero, and `[xy] = 0`; so every
trace of length at least two vanishes. -/
theorem trace_D4_cycle {L : Fin 3 → ℕ} (hL : ∀ i, L i = 0) (D : TraceData L M)
    (hcyc : ∀ i, D.θ i ≠ i) {w : List (Fin 3)} (hw : 2 ≤ w.length) : D.tr w = 0 := by
  have hsq : ∀ i, x L i * x L i = 0 := fun i ↦ by have := x_pow L i; rwa [hL, zero_add, sq] at this
  have hz : x L 2 = -(x L 0 + x L 1) := by
    have := sum_x L
    rw [Fin.sum_univ_three] at this
    exact eq_neg_of_add_eq_zero_right this
  have hp : x L 0 * x L 0 = 0 := hsq 0
  have hq : x L 1 * x L 1 = 0 := hsq 1
  have hqp : x L 1 * x L 0 = -(x L 0 * x L 1) := by
    have h := hsq 2
    rw [hz, neg_mul_neg] at h
    have e : (x L 0 + x L 1) * (x L 0 + x L 1) =
        x L 0 * x L 0 + x L 0 * x L 1 + x L 1 * x L 0 + x L 1 * x L 1 := by noncomm_ring
    rw [e, hp, hq, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  -- products of two letters are multiples of `x₀ x₁`
  have two : ∀ i j : Fin 3, ∃ n : ℤ, x L i * x L j = n • (x L 0 * x L 1) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, by rw [zero_smul]; exact hsq _⟩
    · exact ⟨1, by rw [one_smul]; rfl⟩
    · exact ⟨-1, by
        show x L 0 * x L 2 = _
        rw [hz, mul_neg, mul_add, hp, zero_add, neg_one_zsmul]⟩
    · exact ⟨-1, by show x L 1 * x L 0 = _; rw [neg_one_zsmul]; exact hqp⟩
    · exact ⟨0, by rw [zero_smul]; exact hsq _⟩
    · exact ⟨1, by
        show x L 1 * x L 2 = _
        rw [hz, mul_neg, mul_add, hqp, hq, add_zero, neg_neg, one_smul]⟩
    · exact ⟨1, by
        show x L 2 * x L 0 = _
        rw [hz, neg_mul, add_mul, hp, hqp, zero_add, neg_neg, one_smul]⟩
    · exact ⟨-1, by
        show x L 2 * x L 1 = _
        rw [hz, neg_mul, add_mul, hq, add_zero, neg_one_zsmul]⟩
    · exact ⟨0, by rw [zero_smul]; exact hsq _⟩
  have pq_x : ∀ i, x L 0 * x L 1 * x L i = 0 := by
    intro i
    fin_cases i
    · show x L 0 * x L 1 * x L 0 = 0
      rw [mul_assoc, hqp, mul_neg, ← mul_assoc, hp, zero_mul, neg_zero]
    · show x L 0 * x L 1 * x L 1 = 0
      rw [mul_assoc, hq, mul_zero]
    · show x L 0 * x L 1 * x L 2 = 0
      rw [hz, mul_neg, mul_add, mul_assoc, hqp, mul_neg, ← mul_assoc, hp, zero_mul, neg_zero,
        zero_add, mul_assoc, hq, mul_zero, neg_zero]
  -- words of length at least three vanish
  have three : ∀ (i j : Fin 3) (v : List (Fin 3)), v ≠ [] →
      (((i :: j :: v).map (x L)).prod) = 0 := by
    intro i j v hv
    obtain ⟨l, v', rfl⟩ := List.exists_cons_of_ne_nil hv
    obtain ⟨n, hn⟩ := two i j
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, hn, ← mul_assoc, smul_mul_assoc, pq_x, smul_zero, zero_mul]
  -- the trace of `x₀ x₁` vanishes
  have tpq : D.trR (x L 0 * x L 1) = 0 := by
    have hθ0 : D.θ 0 = 1 ∨ D.θ 0 = 2 := by
      have h0 := hcyc 0
      generalize D.θ 0 = j at h0 ⊢
      fin_cases j <;> simp_all
    rcases hθ0 with h1 | h1
    · rw [D.trR_rotate, D.twR_x, h1, hq, map_zero]
    · have h10 : D.θ 1 = 0 := by
        have h11 := hcyc 1
        have hinj : D.θ 1 ≠ 2 := fun h ↦ absurd (D.θ.injective (h.trans h1.symm)) (by decide)
        generalize D.θ 1 = j at h11 hinj ⊢
        fin_cases j <;> simp_all
      have := D.trR_rotate (x L 1) (x L 0)
      rw [D.twR_x, h10, hp, map_zero, hqp, map_neg, neg_eq_zero] at this
      exact this
  rw [← D.trR_word]
  match w, hw with
  | i :: j :: v, _ =>
      rcases eq_or_ne v [] with rfl | hv
      · obtain ⟨n, hn⟩ := two i j
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [hn, map_zsmul, tpq, smul_zero]
      · rw [three i j v hv, map_zero]

end TraceAlg

end MultiplicativeBasisDeformations
