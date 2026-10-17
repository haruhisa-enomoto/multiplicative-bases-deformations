import MultiplicativeBasisDeformations.Foundations.TraceE78
import Mathlib.Tactic.IntervalCases

/-!
# Lemma A.6 over any coefficient ring

`lem:e78-traces` (`periodic-mesh-calculations.tex`). Over any commutative coefficient
ring, with `a = yx³`, `b = yx⁴`, `t_j = [yx^j]`:

(1) the positive part of `T₅` is spanned by `t₁, t₂, t₃, t₄, [a²], [abʳ] (r ≥ 1)`
(`span_all`), with `2t₁ = 2t₃ = 0`, `3t₂ = 0`, `5t₄ = 0`, `2[a²] = 0`, `3[ab] = 0`,
`2[abʳ] = 0` (`r ≥ 2`) (`t1_two`, `t3_two`, `t2_three`, `t4_five`, `a2_two`, `ab_three`,
`abr_two`); for nonempty `W` in `a, b`: `[a²W] = 0`, `[abW] = -[baW]`, and `[b^q] = 0`
(`q ≥ 2`) (`aa`, `ab_ba`, `bq`);

(2) if two is invertible, `(T₅)₊` is spanned by `[yx²], [yx⁴], [(yx³)(yx⁴)]`, annihilated by
`3, 5, 3`, and `(T₄)₊` (impose `x⁴ = 0`) by `[yx²]`, annihilated by `3` (`span_two`,
`span_two_E7`).

The proof is that of the source: the gap reductions (`red0`, `red1`, `red2`) lower the number
of `y`'s; a gap two between gaps of length at least three has zero trace (`gap2`); the
identity `F` multiplied by `x^k W` gives the block relations (`Fk`). As usual we work with an
additive map `tr` killing commutators and positive powers of `x`, `y`; `T_m` is the universal
such map. The char-two-free statements in `TraceE78.lean` are the case two invertible.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

namespace E78i

open E78

variable {S : Type*} [Ring S] {x y : S} {M : Type*} [AddCommGroup M] {tr : S →+ M}
  (H : Hyp0 x y tr)

theorem blk_zero_of_mem (g : List ℕ) (e : ℕ) (he : e ∈ g) (hx : x ^ e = 0) : blk x y g = 0 := by
  obtain ⟨g₁, g₂, rfl⟩ := List.append_of_mem he
  rw [blk_append, blk, hx, zero_mul, mul_zero, mul_zero]

include H in
theorem xpow_zero {e : ℕ} (he : 5 ≤ e) : x ^ e = 0 := by
  rw [show e = 5 + (e - 5) by omega, pow_add, H.x5, zero_mul]

include H in
theorem blk_zero_big (g : List ℕ) (e : ℕ) (he : e ∈ g) (h5 : 5 ≤ e) : blk x y g = 0 :=
  blk_zero_of_mem g e he (xpow_zero H h5)

include H in
/-- A leading power `x^j` rotated into the last gap of a word with a large last gap. -/
theorem tr_bump_zero (g₀ : List ℕ) (h j : ℕ) (hb : 5 ≤ h + j) :
    tr (x ^ j * blk x y (g₀ ++ [h])) = 0 := by
  rw [tr_bump H, blk_zero_big H _ (h + j) (by simp) hb, map_zero]

include H in
/-- **The identity `F x^k W`.** -/
theorem Fk (k : ℕ) (g : List ℕ) : blk x y (3 :: (k + 1) :: g) = -blk x y (4 :: k :: g) -
    x ^ 1 * blk x y (3 :: k :: g) + x ^ 2 * blk x y ((k + 3) :: g) +
      x ^ 3 * blk x y ((k + 2) :: g) := by
  have e : blk x y (3 :: (k + 1) :: g) - (-blk x y (4 :: k :: g) -
      x ^ 1 * blk x y (3 :: k :: g) + x ^ 2 * blk x y ((k + 3) :: g) +
        x ^ 3 * blk x y ((k + 2) :: g)) =
      (y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
        x ^ 3 * y * x ^ 2) * (x ^ k * blk x y g) := by
    simp only [blk]
    rw [add_comm k 1, add_comm k 3, add_comm k 2, pow_add, pow_add, pow_add]
    noncomm_ring
  rw [F_eq H, zero_mul, sub_eq_zero] at e
  exact e

/-! ### Gap two -/

include H in
/-- **A gap two between gaps of length at least three has zero trace.** -/
theorem gap2 (q p : ℕ) (U : List ℕ) (hq : 3 ≤ q) (hp : 3 ≤ p) :
    tr (blk x y (2 :: q :: (U ++ [p]))) = 0 := by
  rw [red2 H, blk_zero_big H _ (q + 3) (by simp) (by omega),
    blk_zero_big H _ (q + 2) (by simp) (by omega), xpow_zero H (e := q + 4) (by omega), zero_mul,
    mul_zero, map_sub, map_sub, map_sub, map_sub, map_neg,
    show (q + 1) :: (U ++ [p]) = ((q + 1) :: U) ++ [p] from rfl,
    show q :: (U ++ [p]) = (q :: U) ++ [p] from rfl,
    tr_bump_zero H _ p 2 (by omega), tr_bump_zero H _ p 3 (by omega)]
  simp

include H in
theorem gap2' (q : ℕ) (hq : 3 ≤ q) : tr (blk x y [2, q]) = 0 := by
  rw [red2 H, blk_zero_big H _ (q + 3) (by simp) (by omega),
    blk_zero_big H _ (q + 2) (by simp) (by omega), xpow_zero H (e := q + 4) (by omega), zero_mul,
    mul_zero, map_sub, map_sub, map_sub, map_sub, map_neg,
    show [q + 1] = ([] : List ℕ) ++ [q + 1] from rfl, show [q] = ([] : List ℕ) ++ [q] from rfl,
    tr_bump_zero H _ (q + 1) 2 (by omega), tr_bump_zero H _ q 3 (by omega)]
  simp

/-! ### Block relations -/

include H in
/-- `[a²W] = 0` for nonempty `W` with all gaps at least three. -/
theorem aa (g : List ℕ) (hne : g ≠ []) (hg : ∀ e ∈ g, 3 ≤ e) : tr (blk x y (3 :: 3 :: g)) = 0 := by
  obtain ⟨g₀, h, rfl⟩ := (nil_or_snoc g).resolve_left hne
  have hh : 3 ≤ h := hg h (by simp)
  rw [Fk H 2, map_add, map_add, map_sub, map_neg]
  have t1 : tr (blk x y (4 :: 2 :: (g₀ ++ [h]))) = 0 := by
    rw [show 4 :: 2 :: (g₀ ++ [h]) = [4] ++ 2 :: (g₀ ++ [h]) from rfl, tr_blk_rotate H]
    rcases g₀ with _ | ⟨q, U⟩
    · exact gap2 H h 4 [] hh (by norm_num)
    · rw [show (2 :: (q :: U ++ [h])) ++ [4] = 2 :: q :: ((U ++ [h]) ++ [4]) by simp]
      exact gap2 H q 4 _ (hg q (by simp)) (by norm_num)
  have t2 : tr (x ^ 1 * blk x y (3 :: 2 :: (g₀ ++ [h]))) = 0 := by
    rw [show 3 :: 2 :: (g₀ ++ [h]) = (3 :: 2 :: g₀) ++ [h] by simp, tr_bump H,
      show (3 :: 2 :: g₀) ++ [h + 1] = [3] ++ 2 :: (g₀ ++ [h + 1]) by simp, tr_blk_rotate H]
    rcases g₀ with _ | ⟨q, U⟩
    · exact gap2 H (h + 1) 3 [] (by omega) le_rfl
    · rw [show (2 :: (q :: U ++ [h + 1])) ++ [3] = 2 :: q :: ((U ++ [h + 1]) ++ [3]) by simp]
      exact gap2 H q 3 _ (hg q (by simp)) le_rfl
  have t3 : tr (x ^ 2 * blk x y ((2 + 3) :: (g₀ ++ [h]))) = 0 := by
    rw [blk_big H (2 + 3) (by norm_num), mul_zero, map_zero]
  have t4 : tr (x ^ 3 * blk x y ((2 + 2) :: (g₀ ++ [h]))) = 0 := by
    rw [show (2 + 2) :: (g₀ ++ [h]) = ((2 + 2) :: g₀) ++ [h] from rfl]
    exact tr_bump_zero H _ h 3 (by omega)
  rw [t1, t2, t3, t4]; simp

include H in
/-- `[bc] = [yx⁴yx²] = 0`. -/
theorem bc : tr (blk x y [4, 2]) = 0 := by
  rw [show [4, 2] = [4] ++ [2] from rfl, tr_blk_rotate H]
  exact gap2' H 4 (by norm_num)

include H in
/-- **`2[a²] = 0`.** -/
theorem a2_two : tr (blk x y [3, 3]) + tr (blk x y [3, 3]) = 0 := by
  have e := congrArg tr (Fk H 2 [])
  rw [map_add, map_add, map_sub, map_neg, bc H, blk_big H (2 + 3) (by norm_num), mul_zero,
    map_zero, add_zero, show [2 + 2] = ([] : List ℕ) ++ [4] from rfl,
    tr_bump_zero H [] 4 3 (by norm_num), add_zero,
    show [3, 2] = [3] ++ [2] from rfl, tr_bump H, neg_zero, zero_sub] at e
  have h1 : tr (blk x y ([3] ++ [2 + 1])) = tr (blk x y [3, 3]) := rfl
  have h2 : tr (blk x y [3, 2 + 1]) = tr (blk x y [3, 3]) := rfl
  rw [h1] at e
  rw [h2] at e
  rw [eq_neg_iff_add_eq_zero] at e
  exact e

include H in
/-- `[abW] = -[baW]` for nonempty `W` with all gaps at least three. -/
theorem ab_ba (g : List ℕ) (hne : g ≠ []) (hg : ∀ e ∈ g, 3 ≤ e) :
    tr (blk x y (3 :: 4 :: g)) = -tr (blk x y (4 :: 3 :: g)) := by
  obtain ⟨g₀, h, rfl⟩ := (nil_or_snoc g).resolve_left hne
  have hh : 3 ≤ h := hg h (by simp)
  rw [Fk H 3, map_add, map_add, map_sub, map_neg,
    blk_big H (3 + 3) (by norm_num), blk_big H (3 + 2) (by norm_num),
    mul_zero, mul_zero, map_zero, add_zero, add_zero]
  have t : tr (x ^ 1 * blk x y (3 :: 3 :: (g₀ ++ [h]))) = 0 := by
    rw [show 3 :: 3 :: (g₀ ++ [h]) = (3 :: 3 :: g₀) ++ [h] by simp, tr_bump H,
      show (3 :: 3 :: g₀) ++ [h + 1] = 3 :: 3 :: (g₀ ++ [h + 1]) by simp]
    refine aa H _ (by simp) fun e he ↦ ?_
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hg e (by simp [he])
    · omega
  rw [t, sub_zero]

include H in
/-- **`3[ab] = 0`.** -/
theorem ab_three : tr (blk x y [3, 4]) + tr (blk x y [3, 4]) + tr (blk x y [3, 4]) = 0 := by
  have e := congrArg tr (Fk H 3 [])
  rw [map_add, map_add, map_sub, map_neg,
    blk_big H (3 + 3) (by norm_num), blk_big H (3 + 2) (by norm_num),
    mul_zero, mul_zero, map_zero, add_zero, add_zero,
    show [3, 3] = [3] ++ [3] from rfl, tr_bump H,
    show [4, 3] = [4] ++ [3] from rfl, tr_blk_rotate H] at e
  have h1 : tr (blk x y ([3] ++ [3 + 1])) = tr (blk x y [3, 4]) := rfl
  have h2 : tr (blk x y ([3] ++ [4])) = tr (blk x y [3, 4]) := rfl
  have h3 : tr (blk x y [3, 3 + 1]) = tr (blk x y [3, 4]) := rfl
  rw [h3] at e
  rw [h1] at e
  rw [← sub_eq_zero.2 e]; abel

include H in
/-- `[b^{r+2}] = 0`. -/
theorem bq (r : ℕ) : tr (blk x y (List.replicate (r + 2) 4)) = 0 := by
  have e := Fk H 4 (List.replicate r 4)
  rw [show blk x y (3 :: (4 + 1) :: List.replicate r 4) = 0 by
      rw [blk, blk_big H (4 + 1) (by norm_num), mul_zero, mul_zero],
    blk_big H (4 + 3) (by norm_num), blk_big H (4 + 2) (by norm_num),
    mul_zero, mul_zero, add_zero, add_zero] at e
  have e' : blk x y (4 :: 4 :: List.replicate r 4) = -(x ^ 1 * blk x y (3 :: 4 :: List.replicate r 4)) := by
    have h := e.symm
    rw [sub_eq_add_neg, ← neg_add] at h
    exact eq_neg_iff_add_eq_zero.2 (neg_eq_zero.1 h)
  rw [List.replicate_succ, List.replicate_succ, e', map_neg,
    show 3 :: 4 :: List.replicate r 4 = (3 :: List.replicate r 4) ++ [4] by
      rw [List.cons_append, ← List.replicate_succ', List.replicate_succ],
    tr_bump_zero H _ 4 1 le_rfl, neg_zero]

include H in
/-- **`2[abʳ] = 0` for `r ≥ 2`.** -/
theorem abr_two (r : ℕ) :
    tr (blk x y (3 :: List.replicate (r + 2) 4)) + tr (blk x y (3 :: List.replicate (r + 2) 4)) = 0 := by
  have e := ab_ba H (List.replicate (r + 1) 4) (by simp) (by simp)
  have rot : tr (blk x y (4 :: 3 :: List.replicate (r + 1) 4)) =
      tr (blk x y (3 :: List.replicate (r + 2) 4)) := by
    rw [show 4 :: 3 :: List.replicate (r + 1) 4 = [4] ++ 3 :: List.replicate (r + 1) 4 from rfl,
      tr_blk_rotate H]
    congr 2
    simp [List.replicate_succ']
  rw [rot] at e
  have e2 : tr (blk x y (3 :: List.replicate (r + 2) 4)) =
      -tr (blk x y (3 :: List.replicate (r + 2) 4)) := e
  exact eq_neg_iff_add_eq_zero.1 e2

/-! ### The one-`y` relations -/

include H in
theorem tr_comm (p q : S) : tr (p * q) = tr (q * p) := H.rot p q

include H in
/-- **`2t₁ = 0`.** -/
theorem t1_two : tr (blk x y [1]) + tr (blk x y [1]) = 0 := by
  have e := congrArg tr H.d1
  rw [map_zero, map_add, map_add, map_add, H.ty2, tr_comm H x y,
    show x * x = x ^ 2 by rw [sq], H.xp 2 (by norm_num), add_zero, zero_add] at e
  simpa [blk] using e

include H in
/-- **`3t₂ = 0`.** -/
theorem t2_three : tr (blk x y [2]) + tr (blk x y [2]) + tr (blk x y [2]) = 0 := by
  have e1 := congrArg tr (I1 H x)
  have e2 := congrArg tr (I2 H 1)
  simp only [mul_one] at e2
  have r1 : tr (y * (y * x)) = tr (y * (x * y)) := by
    rw [tr_comm H y (y * x), mul_assoc]
  have r2 : tr (x * (y * x)) = tr (y * (x * x)) := by
    rw [tr_comm H x, mul_assoc]
  have r3 : tr (x * (x * x)) = 0 := by
    rw [← mul_assoc, ← sq, ← pow_succ, H.xp 3 (by norm_num)]
  rw [map_sub, map_sub, map_neg, r1, r2, r3, sub_zero] at e1
  rw [map_add, r2, r3, add_zero] at e2
  rw [e2] at e1
  have hb : tr (blk x y [2]) = tr (y * (x * x)) := by simp [blk, sq]
  rw [hb, ← sub_eq_zero.2 e1]; abel

include H in
/-- **`2t₃ = 0`.** -/
theorem t3_two : tr (blk x y [3]) + tr (blk x y [3]) = 0 := by
  have e1 := congrArg tr (I1 H (x * x))
  have e3 := congrArg tr (I3 H 1)
  simp only [mul_one] at e3
  have r5 : tr (y * (x * (x * x))) = tr (blk x y [3]) := by simp [blk, pow_succ, mul_assoc]
  have r1 : tr (y * (y * (x * x))) = tr (y * (x * (x * y))) := by
    rw [tr_comm H y (y * (x * x))]; simp only [mul_assoc]
  have r4 : tr (x * (x * (x * x))) = 0 := by
    rw [show x * (x * (x * x)) = x ^ 4 by simp [pow_succ, mul_assoc], H.xp 4 (by norm_num)]
  have w1 : tr (x * (y * (x * x))) = tr (blk x y [3]) := by
    rw [tr_comm H x, ← r5]; simp only [mul_assoc]
  have w2 : tr (x * (x * (y * x))) = tr (blk x y [3]) := by
    rw [tr_comm H x, show x * (y * x) * x = x * (y * (x * x)) by simp only [mul_assoc], w1]
  have w3 : tr (x * (x * (x * y))) = tr (blk x y [3]) := by
    rw [show x * (x * (x * y)) = (x * (x * x)) * y by simp only [mul_assoc], tr_comm H, r5]
  rw [map_sub, map_sub, map_neg, r1, r5, w1, r4, sub_zero] at e1
  rw [map_sub, map_sub, map_sub, map_sub, map_neg, r5, w1, w2, w3,
    show (2 : S) * (x * (x * (x * x))) = x * (x * (x * x)) + x * (x * (x * x)) by rw [two_mul],
    map_add, r4, add_zero, sub_zero] at e3
  rw [e1] at e3
  rw [← sub_eq_zero.2 e3]; abel

include H in
/-- **`5t₄ = 0`**, from the trace of the third identity multiplied by `x`. -/
theorem t4_five : tr (blk x y [4]) + tr (blk x y [4]) + tr (blk x y [4]) + tr (blk x y [4]) +
    tr (blk x y [4]) = 0 := by
  have e3 := congrArg tr (I3 H x)
  have e2 := congrArg tr (I2 H (x * x))
  have r5 : tr (y * (x * (x * (x * x)))) = tr (blk x y [4]) := by simp [blk, pow_succ, mul_assoc]
  have r0 : tr (x * (x * (x * (x * x)))) = 0 := by
    rw [show x * (x * (x * (x * x))) = x ^ 5 by simp [pow_succ, mul_assoc], H.xp 5 (by norm_num)]
  have rr : ∀ u : S, tr (x * u) = tr (u * x) := fun u ↦ tr_comm H x u
  have w1 : tr (x * (y * (x * (x * x)))) = tr (blk x y [4]) := by
    rw [rr, ← r5]; simp only [mul_assoc]
  have w2 : tr (x * (x * (y * (x * x)))) = tr (blk x y [4]) := by
    rw [rr, show x * (y * (x * x)) * x = x * (y * (x * (x * x))) by simp only [mul_assoc], w1]
  have w3 : tr (x * (x * (x * (y * x)))) = tr (blk x y [4]) := by
    rw [rr, show x * (x * (y * x)) * x = x * (x * (y * (x * x))) by simp only [mul_assoc], w2]
  have w4 : tr (x * (x * (x * (x * x)))) = 0 := r0
  -- `tr(y x² y x) = tr(y x y x²) = t₄`
  have l : tr (y * (x * (x * (y * x)))) = tr (blk x y [4]) := by
    have : tr (y * (x * (x * (y * x)))) = tr (y * (x * (y * (x * x)))) := by
      rw [show y * (x * (x * (y * x))) = (y * x) * (x * (y * x)) by simp only [mul_assoc],
        tr_comm H, show x * (y * x) * (y * x) = x * (y * (x * (y * x))) by simp only [mul_assoc],
        rr, show y * (x * (y * x)) * x = y * (x * (y * (x * x))) by simp only [mul_assoc]]
    rw [this, e2, map_add, w1, show x * (x * (x * (x * x))) = x * (x * (x * (x * x))) from rfl,
      r0, add_zero]
  rw [l, map_sub, map_sub, map_sub, map_sub, map_neg, r5, w1, w2, w3,
    show (2 : S) * (x * (x * (x * (x * x)))) = x * (x * (x * (x * x))) + x * (x * (x * (x * x)))
      by rw [two_mul], map_add, r0, add_zero, sub_zero] at e3
  rw [← sub_eq_zero.2 e3]; abel

/-! ### Spanning -/

variable (x y tr) in
/-- The candidate classes `t₁, t₂, t₃, t₄, [a²], [abʳ]` (`r ≥ 1`). -/
def cand : Set M :=
  {tr (blk x y [1]), tr (blk x y [2]), tr (blk x y [3]), tr (blk x y [4]), tr (blk x y [3, 3])} ∪
    Set.range fun r : ℕ ↦ tr (blk x y (3 :: List.replicate (r + 1) 4))

variable (x y tr) in
/-- Their span. -/
abbrev A : AddSubgroup M := AddSubgroup.closure (cand x y tr)

variable (x y tr) in
/-- All words with at most `K` letters `y` and positive degree have trace in `A`. -/
def Zs (K : ℕ) : Prop :=
  ∀ (j : ℕ) (g : List ℕ), g.length ≤ K → (g = [] → 1 ≤ j) → tr (x ^ j * blk x y g) ∈ A x y tr

theorem mem_A {m : M} (h : m ∈ cand x y tr) : m ∈ A x y tr := AddSubgroup.subset_closure h

include H in
theorem Zs_zero : Zs x y tr 0 := by
  intro j g hg hj
  obtain rfl : g = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [blk, mul_one, H.xp j (hj rfl)]; exact zero_mem _

include H in
theorem single (h : ℕ) : tr (blk x y [h]) ∈ A x y tr := by
  rcases Nat.lt_or_ge h 5 with hh | hh
  · interval_cases h
    · simp only [blk, pow_zero, mul_one, H.ty]; exact zero_mem _
    all_goals exact mem_A (by simp [cand])
  · rw [blk_big H h hh]; simp

include H in
/-- **A gap of length at most two, or at least five, reduces to fewer `y`'s.** -/
theorem bad_mem {K : ℕ} (hZ : Zs x y tr K) (g : List ℕ) (hg : g.length = K + 1) (hK : 1 ≤ K)
    (e : ℕ) (he : e ∈ g) (hbad : e ≤ 2 ∨ 5 ≤ e) : tr (blk x y g) ∈ A x y tr := by
  obtain ⟨g₁, g₂, rfl⟩ := List.append_of_mem he
  rw [tr_blk_rotate H, List.cons_append]
  set g' := g₂ ++ g₁ with hg'
  have hlen : g'.length = K := by
    rw [hg', List.length_append]; rw [List.length_append, List.length_cons] at hg; omega
  obtain ⟨h, g'', hh⟩ := List.exists_cons_of_length_pos (l := g') (by omega)
  rw [hh] at hlen ⊢
  simp only [List.length_cons] at hlen
  have z0 : ∀ (g : List ℕ), g.length ≤ K → g ≠ [] → tr (blk x y g) ∈ A x y tr := by
    intro g h1 h2
    have := hZ 0 g h1 (fun h ↦ absurd h h2)
    rwa [pow_zero, one_mul] at this
  have zp : ∀ j (g : List ℕ), g.length ≤ K → 1 ≤ j → tr (x ^ j * blk x y g) ∈ A x y tr :=
    fun j g h1 h2 ↦ hZ j g h1 fun _ ↦ h2
  rcases hbad with hb | hb
  · interval_cases e
    · rw [red0 H, map_sub, map_sub, map_neg]
      exact sub_mem (sub_mem (neg_mem (z0 _ (by simp; omega) (by simp)))
        (zp 1 _ (by simp; omega) le_rfl)) (zp (h + 2) _ (by omega) (by omega))
    · rw [red1 H, map_add]
      exact add_mem (zp 1 _ (by simp; omega) le_rfl) (zp (h + 3) _ (by omega) (by omega))
    · rw [red2 H, map_sub, map_sub, map_sub, map_sub, map_neg,
        show (2 : S) * (x ^ (h + 4) * blk x y g'') = x ^ (h + 4) * blk x y g'' +
          x ^ (h + 4) * blk x y g'' by rw [two_mul], map_add]
      exact sub_mem (sub_mem (sub_mem (sub_mem (neg_mem (z0 _ (by simp; omega) (by simp)))
        (zp 1 _ (by simp; omega) le_rfl)) (zp 2 _ (by simp; omega) (by norm_num)))
        (zp 3 _ (by simp; omega) (by norm_num)))
        (add_mem (zp (h + 4) _ (by omega) (by omega)) (zp (h + 4) _ (by omega) (by omega)))
  · rw [blk_big H e hb, map_zero]; exact zero_mem _

include H in
/-- Two `a`'s are brought together using `[abW] = -[baW]`. -/
theorem chain (r : ℕ) (g : List ℕ) (hg : ∀ e ∈ g, e = 3 ∨ e = 4) (hne : r ≠ 0 ∨ g ≠ []) :
    tr (blk x y (3 :: (List.replicate r 4 ++ 3 :: g))) = 0 := by
  induction r generalizing g with
  | zero =>
      have hg' : g ≠ [] := by simpa using hne
      exact aa H g hg' fun e he ↦ by rcases hg e he with rfl | rfl <;> norm_num
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append,
        ab_ba H _ (by simp) (fun e he ↦ by
          simp only [List.mem_append, List.mem_replicate, List.mem_cons] at he
          rcases he with ⟨-, rfl⟩ | rfl | he
          · norm_num
          · norm_num
          · rcases hg e he with rfl | rfl <;> norm_num),
        show 4 :: 3 :: (List.replicate r 4 ++ 3 :: g) = [4] ++ 3 :: (List.replicate r 4 ++ 3 :: g)
          from rfl, tr_blk_rotate H,
        show (3 :: (List.replicate r 4 ++ 3 :: g)) ++ [4] = 3 :: (List.replicate r 4 ++ 3 :: (g ++ [4]))
          by simp,
        ih (g ++ [4]) (fun e he ↦ by
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hg e he
          · right; rfl) (Or.inr (by simp)), neg_zero]

include H in
/-- **Cyclic words in `a, b` with at least two blocks.** -/
theorem blocks_mem (g : List ℕ) (hg : ∀ e ∈ g, e = 3 ∨ e = 4) (hlen : 2 ≤ g.length) :
    tr (blk x y g) ∈ A x y tr := by
  rcases cases34 g hg with h | ⟨r, l', h⟩
  · -- only `b`'s
    obtain ⟨q, hq⟩ : ∃ q, g.length = q + 2 := ⟨g.length - 2, by omega⟩
    rw [h, hq, bq H]; exact zero_mem _
  · have hrot : tr (blk x y g) = tr (blk x y (3 :: (l' ++ List.replicate r 4))) := by
      rw [h, tr_blk_rotate H, List.cons_append]
    rw [hrot]
    have hg' : ∀ e ∈ l' ++ List.replicate r 4, e = 3 ∨ e = 4 := by
      intro e he
      apply hg
      rw [h]; simp only [List.mem_append, List.mem_cons] at he ⊢
      rcases he with he | he
      · exact Or.inr (Or.inr he)
      · exact Or.inl he
    have hlen' : 1 ≤ (l' ++ List.replicate r 4).length := by
      rw [h] at hlen; simp at hlen ⊢; omega
    rcases cases34 _ hg' with h' | ⟨r', l'', h'⟩
    · -- `a bᵐ`, `m ≥ 1`
      rw [h']
      obtain ⟨m, hm⟩ : ∃ m, (l' ++ List.replicate r 4).length = m + 1 :=
        ⟨(l' ++ List.replicate r 4).length - 1, by omega⟩
      rw [hm]
      exact mem_A (Or.inr ⟨m, rfl⟩)
    · rw [h']
      have hg'' : ∀ e ∈ l'', e = 3 ∨ e = 4 := fun e he ↦ hg' e (by rw [h']; simp [he])
      by_cases h0 : r' = 0 ∧ l'' = []
      · obtain ⟨rfl, rfl⟩ := h0
        exact mem_A (by simp [cand])
      · rw [chain H r' l'' hg'' (by tauto)]; exact zero_mem _

include H in
theorem all_mem : ∀ K, Zs x y tr K := by
  intro K
  induction K with
  | zero => exact Zs_zero H
  | succ K ih =>
      intro j g hlen hj
      rcases Nat.lt_or_ge g.length (K + 1) with hl | hl
      · exact ih j g (by omega) hj
      obtain ⟨g₀, h, rfl⟩ := (nil_or_snoc g).resolve_left (by rintro rfl; simp at hl)
      rw [tr_bump H]
      have hlen' : (g₀ ++ [h + j]).length = K + 1 := by
        simp only [List.length_append, List.length_singleton] at hl hlen ⊢; omega
      rcases Nat.eq_zero_or_pos K with rfl | hK
      · obtain rfl : g₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen')
        exact single H (h + j)
      by_cases hgood : ∀ e ∈ g₀ ++ [h + j], e = 3 ∨ e = 4
      · exact blocks_mem H _ hgood (by omega)
      · push Not at hgood
        obtain ⟨e, he, h3e, h4e⟩ := hgood
        exact bad_mem H ih _ hlen' hK e he (by omega)

include H in
/-- **Lemma A.6(1), spanning**: every word of positive degree has trace in the span of
`t₁, t₂, t₃, t₄, [a²], [abʳ]` (`r ≥ 1`). -/
theorem span_all (j : ℕ) (g : List ℕ) (hj : g = [] → 1 ≤ j) :
    tr (x ^ j * blk x y g) ∈ A x y tr :=
  all_mem H g.length j g le_rfl hj

include H in
/-- The same for every element of the span of the words of a positive degree `n`. -/
theorem span_mem (n : ℕ) (hn : 1 ≤ n) {r : S} (hr : r ∈ E78.span x y n) : tr r ∈ A x y tr := by
  induction hr using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨j, g, hs, rfl⟩ := hr
      exact span_all H j g fun h ↦ by subst h; simp at hs; omega
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

/-! ### Two invertible -/

variable (x y tr) in
/-- The span of `[yx²], [yx⁴], [(yx³)(yx⁴)]`. -/
abbrev A2 : AddSubgroup M :=
  AddSubgroup.closure {tr (blk x y [2]), tr (blk x y [4]), tr (blk x y [3, 4])}

include H in
/-- **Lemma A.6(2)**: if two is invertible, `(T₅)₊` is spanned by `[yx²], [yx⁴],
[(yx³)(yx⁴)]`, annihilated by `3, 5, 3`. -/
theorem span_two (two : ∀ m : M, m + m = 0 → m = 0) (j : ℕ) (g : List ℕ) (hj : g = [] → 1 ≤ j) :
    tr (x ^ j * blk x y g) ∈ A2 x y tr ∧
      3 • tr (blk x y [2]) = 0 ∧ 5 • tr (blk x y [4]) = 0 ∧ 3 • tr (blk x y [3, 4]) = 0 := by
  refine ⟨?_, by rw [succ_nsmul, succ_nsmul, one_nsmul]; exact t2_three H,
    by rw [succ_nsmul, succ_nsmul, succ_nsmul, succ_nsmul, one_nsmul]; exact t4_five H,
    by rw [succ_nsmul, succ_nsmul, one_nsmul]; exact ab_three H⟩
  have hle : A x y tr ≤ A2 x y tr := by
    refine (AddSubgroup.closure_le _).2 fun m hm ↦ ?_
    rcases hm with hm | ⟨r, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      · rw [two _ (t1_two H)]; exact zero_mem _
      · exact AddSubgroup.subset_closure (by simp)
      · rw [two _ (t3_two H)]; exact zero_mem _
      · exact AddSubgroup.subset_closure (by simp)
      · rw [two _ (a2_two H)]; exact zero_mem _
    · rcases r with _ | r
      · exact AddSubgroup.subset_closure (by simp)
      · change tr (blk x y (3 :: List.replicate (r + 2) 4)) ∈ A2 x y tr
        rw [two _ (abr_two H r)]; exact zero_mem _
  exact hle (span_all H j g hj)

include H in
/-- **Lemma A.6(2) for `T₄`** (impose `x⁴ = 0`): `(T₄)₊` is spanned by `[yx²]`, annihilated
by `3`. -/
theorem span_two_E7 (two : ∀ m : M, m + m = 0 → m = 0) (x4 : x ^ 4 = 0) (j : ℕ) (g : List ℕ)
    (hj : g = [] → 1 ≤ j) :
    tr (x ^ j * blk x y g) ∈ AddSubgroup.closure {tr (blk x y [2])} ∧
      3 • tr (blk x y [2]) = 0 := by
  refine ⟨?_, (span_two H two 1 [] (by simp)).2.1⟩
  have h4 : tr (blk x y [4]) = 0 := by simp [blk, x4]
  have h34 : tr (blk x y [3, 4]) = 0 := by simp [blk, x4]
  have hle : A2 x y tr ≤ AddSubgroup.closure {tr (blk x y [2])} := by
    refine (AddSubgroup.closure_le _).2 fun m hm ↦ ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl
    · exact AddSubgroup.subset_closure rfl
    · rw [h4]; exact zero_mem _
    · rw [h34]; exact zero_mem _
  exact hle (span_two H two j g hj).1

end E78i

end TraceAlg

end MultiplicativeBasisDeformations
