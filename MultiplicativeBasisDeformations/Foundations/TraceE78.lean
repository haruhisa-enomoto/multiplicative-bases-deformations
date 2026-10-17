import MultiplicativeBasisDeformations.Foundations.TraceE6
import Mathlib.Tactic.IntervalCases

/-!
# Ordinary traces of types `E_7` and `E_8` (Lemma A.6)

`lem:e78-traces` (`periodic-mesh-calculations.tex`). Write `x, y` for
the closed paths along the long and medium arms; the short arm gives
`(x + y)² = 0`, and `x⁵ = y³ = 0`. The word identities
`y² = -yx - xy - x²`, `yxy = xyx + x³`,
`yx²y = -yx³ - xyx² - x²yx - x³y - 2x⁴` and
`F = yx³yx + yx⁴y + xyx³y - x²yx³ - x³yx² = 0` reduce cyclic words by their
gaps (the numbers of `x`'s between successive `y`'s): "If a gap has length zero,
one or two, apply the corresponding one of the first three identities. Each
resulting term has fewer `y`'s." The remaining words are cyclic words in
`a = yx³`, `b = yx⁴`, and the relations `[a²W] = 0`, `[abW] = -[baW]`,
`[b^q] = 0` dispose of them.

With two invertible only degrees three, five and nine survive (part (2)); we
record the vanishing in all other word degrees, which is what the period
exclusion uses. A word `y x^{g₁} ⋯ y x^{g_k}` is `blk [g₁, …, g_k]`; the
induction runs on the number `k` of `y`'s, in a fixed word degree.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

namespace E78

variable {S : Type*} [Ring S] (x y : S) {M : Type*} [AddCommGroup M] (tr : S →+ M)

/-- The word `y x^{g₁} y x^{g₂} ⋯ y x^{g_k}`. -/
def blk : List ℕ → S
  | [] => 1
  | g :: gs => y * (x ^ g * blk gs)

/-- The hypotheses of Lemma A.6 over any coefficient ring. -/
structure Hyp0 : Prop where
  x5 : x ^ 5 = 0
  y3 : y ^ 3 = 0
  d1 : y * y + y * x + x * y + x * x = 0
  rot : ∀ p q, tr (p * q) = tr (q * p)
  xp : ∀ q, 1 ≤ q → tr (x ^ q) = 0
  ty : tr y = 0
  ty2 : tr (y * y) = 0

/-- The hypotheses of Lemma A.6 with two invertible. -/
structure Hyp extends Hyp0 x y tr : Prop where
  two : ∀ m : M, m + m = 0 → m = 0

variable {x y tr} (H₀ : Hyp0 x y tr) (H : Hyp x y tr)

theorem blk_append (g₁ g₂ : List ℕ) : blk x y (g₁ ++ g₂) = blk x y g₁ * blk x y g₂ := by
  induction g₁ with
  | nil => simp [blk]
  | cons g gs ih => simp only [List.cons_append, blk, ih, mul_assoc]

include H₀ in
theorem tr_blk_rotate (g₁ g₂ : List ℕ) : tr (blk x y (g₁ ++ g₂)) = tr (blk x y (g₂ ++ g₁)) := by
  rw [blk_append, blk_append, H₀.rot]

theorem blk_snoc_mul (g₀ : List ℕ) (h j : ℕ) :
    blk x y (g₀ ++ [h]) * x ^ j = blk x y (g₀ ++ [h + j]) := by
  rw [blk_append, blk_append, mul_assoc]
  congr 1
  simp only [blk, mul_one, pow_add, mul_assoc]

include H₀ in
/-- Leading `x`'s rotate into the last gap. -/
theorem tr_bump (g₀ : List ℕ) (h j : ℕ) :
    tr (x ^ j * blk x y (g₀ ++ [h])) = tr (blk x y (g₀ ++ [h + j])) := by
  rw [H₀.rot, blk_snoc_mul]

include H₀ in
theorem blk_big (e : ℕ) (he : 5 ≤ e) (g : List ℕ) : blk x y (e :: g) = 0 := by
  rw [blk, show e = 5 + (e - 5) by omega, pow_add, H₀.x5, zero_mul, zero_mul, mul_zero]

/-! ### The word identities -/

include H₀ in
theorem I1 (T : S) : y * (y * T) = -(y * (x * T)) - x * (y * T) - x * (x * T) := by
  have e : y * (y * T) = (y * y + y * x + x * y + x * x) * T - (y * (x * T)) - x * (y * T) -
      x * (x * T) := by noncomm_ring
  rw [e, H₀.d1, zero_mul, zero_sub]

include H₀ in
theorem d2 : y * x * y - x * y * x - x ^ 3 = 0 := by
  have e : y * x * y - x * y * x - x ^ 3 =
      y * (y * y + y * x + x * y + x * x) - (y * y + y * x + x * y + x * x) * x - y ^ 3 := by
    noncomm_ring
  rw [e, H₀.d1, H₀.y3]; simp

include H₀ in
theorem I2 (T : S) : y * (x * (y * T)) = x * (y * (x * T)) + x * (x * (x * T)) := by
  have e : y * (x * (y * T)) = (y * x * y - x * y * x - x ^ 3) * T + x * (y * (x * T)) +
      x * (x * (x * T)) := by noncomm_ring
  rw [e, d2 H₀, zero_mul, zero_add]

include H₀ in
theorem d3 : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4 = 0 := by
  have e : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4 =
      (y * y + y * x + x * y + x * x) * x * y - x * (y * x * y - x * y * x - x ^ 3) -
        y * (y * x * y - x * y * x - x ^ 3) - (y * x * y - x * y * x - x ^ 3) * x := by
    noncomm_ring
  rw [e, H₀.d1, d2 H₀]; simp

include H₀ in
theorem I3 (T : S) : y * (x * (x * (y * T))) = -(y * (x * (x * (x * T)))) -
    x * (y * (x * (x * T))) - x * (x * (y * (x * T))) - x * (x * (x * (y * T))) -
    2 * (x * (x * (x * (x * T)))) := by
  have e : y * (x * (x * (y * T))) = (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x +
      x ^ 3 * y + 2 * x ^ 4) * T - (y * (x * (x * (x * T)))) -
      x * (y * (x * (x * T))) - x * (x * (y * (x * T))) - x * (x * (x * (y * T))) -
      2 * (x * (x * (x * (x * T)))) := by noncomm_ring
  rw [e, d3 H₀, zero_mul, zero_sub]

include H₀ in
theorem F_eq : y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
    x ^ 3 * y * x ^ 2 = 0 := by
  have e : y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
      x ^ 3 * y * x ^ 2 =
      -((y * x * y - x * y * x - x ^ 3) * x ^ 2 * y -
        y * x * (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4) +
        (y * x * y - x * y * x - x ^ 3) * x ^ 3 +
        (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4) * x ^ 2) -
      x ^ 5 * y + x ^ 5 * x - y * x ^ 5 := by noncomm_ring
  rw [e, d2 H₀, d3 H₀, H₀.x5]; simp

/-! ### Gap reductions -/

include H₀ in
/-- Gap zero (`y² = -yx - xy - x²`). -/
theorem red0 (h : ℕ) (g : List ℕ) : blk x y (0 :: h :: g) = -blk x y ((h + 1) :: g) -
    x ^ 1 * blk x y (h :: g) - x ^ (h + 2) * blk x y g := by
  simp only [blk, pow_zero, one_mul, pow_one]
  rw [I1 H₀]
  simp only [pow_succ', mul_assoc]

include H₀ in
/-- Gap one (`yxy = xyx + x³`). -/
theorem red1 (h : ℕ) (g : List ℕ) : blk x y (1 :: h :: g) = x ^ 1 * blk x y ((h + 1) :: g) +
    x ^ (h + 3) * blk x y g := by
  simp only [blk, pow_one]
  rw [I2 H₀]
  simp only [pow_succ', mul_assoc]

include H₀ in
/-- Gap two. -/
theorem red2 (h : ℕ) (g : List ℕ) : blk x y (2 :: h :: g) = -blk x y ((h + 3) :: g) -
    x ^ 1 * blk x y ((h + 2) :: g) - x ^ 2 * blk x y ((h + 1) :: g) - x ^ 3 * blk x y (h :: g) -
    2 * (x ^ (h + 4) * blk x y g) := by
  simp only [blk]
  rw [show x ^ 2 * (y * (x ^ h * blk x y g)) = x * (x * (y * (x ^ h * blk x y g))) by
    rw [sq, mul_assoc], I3 H₀]
  simp only [pow_succ', pow_zero, mul_one, mul_assoc]

variable (x y tr) in
/-- All words of word degree `n` with at most `K` letters `y` have zero trace. -/
def Z (n K : ℕ) : Prop :=
  ∀ (j : ℕ) (g : List ℕ), g.length ≤ K → j + g.length + g.sum = n → tr (x ^ j * blk x y g) = 0

include H in
theorem Z_zero (n : ℕ) (hn : 1 ≤ n) : Z x y tr n 0 := by
  intro j g hg hs
  obtain rfl : g = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.length_nil, List.sum_nil, add_zero] at hs
  rw [blk, mul_one]; exact H.xp j (by omega)

include H in
/-- **A gap of length at most two, or at least five, gives zero trace.** -/
theorem bad_zero {n K : ℕ} (hK : 1 ≤ K) (hZ : Z x y tr n K) (g : List ℕ) (hg : g.length = K + 1)
    (hs : K + 1 + g.sum = n) (e : ℕ) (he : e ∈ g) (hbad : e ≤ 2 ∨ 5 ≤ e) :
    tr (blk x y g) = 0 := by
  obtain ⟨g₁, g₂, rfl⟩ := List.append_of_mem he
  rw [tr_blk_rotate H.toHyp0, List.cons_append]
  set g' := g₂ ++ g₁ with hg'
  have hlen : g'.length = K := by
    rw [hg', List.length_append]; rw [List.length_append, List.length_cons] at hg; omega
  have hsum : K + 1 + e + g'.sum = n := by
    rw [hg', List.sum_append]; rw [List.sum_append, List.sum_cons] at hs; omega
  obtain ⟨h, g'', hh⟩ := List.exists_cons_of_length_pos (l := g') (by omega)
  rw [hh] at hlen hsum ⊢
  simp only [List.length_cons, List.sum_cons] at hlen hsum
  have z : ∀ j (g : List ℕ), g.length ≤ K → j + g.length + g.sum = n → tr (x ^ j * blk x y g) = 0 :=
    hZ
  have z0 : ∀ (g : List ℕ), g.length ≤ K → g.length + g.sum = n → tr (blk x y g) = 0 := by
    intro g h1 h2
    have := z 0 g h1 (by omega)
    rwa [pow_zero, one_mul] at this
  rcases hbad with hb | hb
  · interval_cases e
    · rw [red0 H.toHyp0, map_sub, map_sub, map_neg,
        z0 _ (by simp; omega) (by simp; omega), z 1 _ (by simp; omega) (by simp; omega),
        z (h + 2) _ (by omega) (by omega)]
      simp
    · rw [red1 H.toHyp0, map_add, z 1 _ (by simp; omega) (by simp; omega),
        z (h + 3) _ (by omega) (by omega), add_zero]
    · rw [red2 H.toHyp0, map_sub, map_sub, map_sub, map_sub, map_neg,
        z0 _ (by simp; omega) (by simp; omega), z 1 _ (by simp; omega) (by simp; omega),
        z 2 _ (by simp; omega) (by simp; omega), z 3 _ (by simp; omega) (by simp; omega),
        show (2 : S) * (x ^ (h + 4) * blk x y g'') = x ^ (h + 4) * blk x y g'' +
          x ^ (h + 4) * blk x y g'' by rw [two_mul], map_add,
        z (h + 4) _ (by omega) (by omega)]
      simp
  · rw [blk_big H.toHyp0 e hb, map_zero]

theorem Z.blk {n K : ℕ} (hZ : Z x y tr n K) (g : List ℕ) (h1 : g.length ≤ K)
    (h2 : g.length + g.sum = n) : tr (blk x y g) = 0 := by
  have := hZ 0 g h1 (by omega)
  rwa [pow_zero, one_mul] at this

/-! ### Words in `a = yx³` and `b = yx⁴` -/

theorem nil_or_snoc {α : Type*} (g : List α) : g = [] ∨ ∃ g₀ h, g = g₀ ++ [h] := by
  rcases List.eq_nil_or_concat g with h | ⟨g₀, h, e⟩
  · exact Or.inl h
  · exact Or.inr ⟨g₀, h, by rw [e, List.concat_eq_append]⟩

section Blocks

variable {n K : ℕ} (hK : 1 ≤ K) (hZ : Z x y tr n K)

include H hK hZ in
/-- `[a²W] = 0`, from the trace of `F x² W`. -/
theorem aa (g : List ℕ) (hlen : g.length + 1 = K) (hs : K + 7 + g.sum = n) :
    tr (blk x y (3 :: 3 :: g)) = 0 := by
  have hid : blk x y (3 :: 3 :: g) = -blk x y (4 :: 2 :: g) - x ^ 1 * blk x y (3 :: 2 :: g) +
      x ^ 2 * blk x y (5 :: g) + x ^ 3 * blk x y (4 :: g) := by
    have e : blk x y (3 :: 3 :: g) - (-blk x y (4 :: 2 :: g) - x ^ 1 * blk x y (3 :: 2 :: g) +
        x ^ 2 * blk x y (5 :: g) + x ^ 3 * blk x y (4 :: g)) =
        (y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
          x ^ 3 * y * x ^ 2) * (x ^ 2 * blk x y g) := by
      simp only [blk]; noncomm_ring
    rw [← sub_eq_zero, e, F_eq H.toHyp0, zero_mul]
  have t1 : tr (blk x y (4 :: 2 :: g)) = 0 :=
    bad_zero H hK hZ _ (by simp; omega) (by simp; omega) 2 (by simp) (by omega)
  have t2 : tr (x ^ 2 * blk x y (5 :: g)) = 0 := by rw [blk_big H.toHyp0 5 le_rfl, mul_zero, map_zero]
  have t3 : tr (x ^ 3 * blk x y (4 :: g)) = 0 := hZ 3 _ (by simp; omega) (by simp; omega)
  rcases nil_or_snoc g with rfl | ⟨g₀, h, rfl⟩
  · have t4 : tr (x ^ 1 * blk x y (3 :: [2])) = tr (blk x y [3, 3]) :=
      tr_bump H.toHyp0 [3] 2 1
    have h := congrArg tr hid
    rw [map_add, map_add, map_sub, map_neg, t1, t2, t3, t4] at h
    apply H.two
    nth_rewrite 1 [h]
    abel
  · have t4 : tr (x ^ 1 * blk x y (3 :: 2 :: (g₀ ++ [h]))) = 0 := by
      rw [show 3 :: 2 :: (g₀ ++ [h]) = (3 :: 2 :: g₀) ++ [h] by simp, tr_bump H.toHyp0]
      exact bad_zero H hK hZ _ (by simp at hlen ⊢; omega) (by simp at hs ⊢; omega) 2 (by simp)
        (by omega)
    rw [hid, map_add, map_add, map_sub, map_neg, t1, t2, t3, t4]; simp

include H hK hZ in
/-- `[abW] = -[baW]` for nonempty `W`, from the trace of `F x³ W`. -/
theorem ab_ba (g : List ℕ) (hne : g ≠ []) (hlen : g.length + 1 = K) (hs : K + 8 + g.sum = n) :
    tr (blk x y (3 :: 4 :: g)) = -tr (blk x y (4 :: 3 :: g)) := by
  have hid : blk x y (3 :: 4 :: g) = -blk x y (4 :: 3 :: g) - x ^ 1 * blk x y (3 :: 3 :: g) +
      x ^ 2 * blk x y (6 :: g) + x ^ 3 * blk x y (5 :: g) := by
    have e : blk x y (3 :: 4 :: g) - (-blk x y (4 :: 3 :: g) - x ^ 1 * blk x y (3 :: 3 :: g) +
        x ^ 2 * blk x y (6 :: g) + x ^ 3 * blk x y (5 :: g)) =
        (y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
          x ^ 3 * y * x ^ 2) * (x ^ 3 * blk x y g) := by
      simp only [blk]; noncomm_ring
    rw [← sub_eq_zero, e, F_eq H.toHyp0, zero_mul]
  obtain ⟨g₀, h, rfl⟩ := (nil_or_snoc g).resolve_left hne
  have t4 : tr (x ^ 1 * blk x y (3 :: 3 :: (g₀ ++ [h]))) = 0 := by
    rw [show 3 :: 3 :: (g₀ ++ [h]) = (3 :: 3 :: g₀) ++ [h] by simp, tr_bump H.toHyp0,
      show (3 :: 3 :: g₀) ++ [h + 1] = 3 :: 3 :: (g₀ ++ [h + 1]) by simp]
    exact aa H hK hZ _ (by simp at hlen ⊢; omega) (by simp at hs ⊢; omega)
  rw [hid, map_add, map_add, map_sub, map_neg, t4, blk_big H.toHyp0 6 (by norm_num),
    blk_big H.toHyp0 5 le_rfl]
  simp

include H in
/-- `[b²W] = -[x a b W]`, from the trace of `F x⁴ W`. -/
theorem bb (g : List ℕ) : tr (blk x y (4 :: 4 :: g)) = -tr (x ^ 1 * blk x y (3 :: 4 :: g)) := by
  have hid : blk x y (4 :: 4 :: g) = -blk x y (3 :: 5 :: g) - x ^ 1 * blk x y (3 :: 4 :: g) +
      x ^ 2 * blk x y (7 :: g) + x ^ 3 * blk x y (6 :: g) := by
    have e : blk x y (4 :: 4 :: g) - (-blk x y (3 :: 5 :: g) - x ^ 1 * blk x y (3 :: 4 :: g) +
        x ^ 2 * blk x y (7 :: g) + x ^ 3 * blk x y (6 :: g)) =
        (y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
          x ^ 3 * y * x ^ 2) * (x ^ 4 * blk x y g) := by
      simp only [blk]; noncomm_ring
    rw [← sub_eq_zero, e, F_eq H.toHyp0, zero_mul]
  have h35 : blk x y (3 :: 5 :: g) = 0 := by
    rw [blk, blk_big H.toHyp0 5 le_rfl, mul_zero, mul_zero]
  rw [hid, h35, blk_big H.toHyp0 7 (by norm_num), blk_big H.toHyp0 6 (by norm_num)]
  simp

theorem cases34 (l : List ℕ) (hl : ∀ e ∈ l, e = 3 ∨ e = 4) :
    l = List.replicate l.length 4 ∨ ∃ r l', l = List.replicate r 4 ++ 3 :: l' := by
  induction l with
  | nil => left; rfl
  | cons e l ih =>
      rcases hl e List.mem_cons_self with rfl | rfl
      · right; exact ⟨0, l, rfl⟩
      · rcases ih (fun e he ↦ hl e (List.mem_cons_of_mem _ he)) with h | ⟨r, l', h⟩
        · left; rw [List.length_cons, List.replicate_succ, ← h]
        · right; exact ⟨r + 1, l', by rw [h, List.replicate_succ, List.cons_append]⟩

include H hK hZ in
/-- Two `a`'s are brought together using `[abW] = -[baW]`. -/
theorem chain (r : ℕ) (g : List ℕ) (hlen : r + g.length + 1 = K)
    (hs : K + 7 + 4 * r + g.sum = n) : tr (blk x y (3 :: (List.replicate r 4 ++ 3 :: g))) = 0 := by
  induction r generalizing g with
  | zero => exact aa H hK hZ g (by omega) (by simpa using hs)
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append,
        ab_ba H hK hZ _ (by simp) (by simp; omega) (by simp [List.sum_replicate]; omega)]
      rw [show 4 :: 3 :: (List.replicate r 4 ++ 3 :: g) = [4] ++ 3 :: (List.replicate r 4 ++ 3 :: g)
        from rfl, tr_blk_rotate H.toHyp0,
        show (3 :: (List.replicate r 4 ++ 3 :: g)) ++ [4] = 3 :: (List.replicate r 4 ++ 3 :: (g ++ [4]))
          by simp,
        ih (g ++ [4]) (by simp; omega) (by simp; omega), neg_zero]

include H hK hZ in
/-- **Cyclic words in `a, b` with at least two blocks vanish** outside word
degree nine. -/
theorem blocks_zero (h9 : n = 9 → tr (blk x y [3, 4]) = 0) (g : List ℕ) (hlen : g.length = K + 1)
    (hg : ∀ e ∈ g, e = 3 ∨ e = 4) (hs : K + 1 + g.sum = n) : tr (blk x y g) = 0 := by
  rcases cases34 g hg with h | ⟨r, l', h⟩
  · -- only `b`'s
    rw [hlen] at h
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [h, List.replicate_succ, List.replicate_succ, bb H,
      show 3 :: 4 :: List.replicate K' 4 = (3 :: List.replicate K' 4) ++ [4] by
        rw [List.cons_append, ← List.replicate_succ', List.replicate_succ],
      tr_bump H.toHyp0]
    rw [bad_zero H hK hZ _ (by simp <;> omega) (by
        rw [h] at hs; simp [List.sum_replicate] at hs ⊢ <;> omega) 5 (by simp) (by omega), neg_zero]
  · -- rotate an `a` to the front
    have hrot : tr (blk x y g) = tr (blk x y (3 :: (l' ++ List.replicate r 4))) := by
      rw [h, tr_blk_rotate H.toHyp0, List.cons_append]
    rw [hrot]
    have hg' : ∀ e ∈ l' ++ List.replicate r 4, e = 3 ∨ e = 4 := by
      intro e he
      apply hg
      rw [h]; simp only [List.mem_append, List.mem_cons] at he ⊢
      rcases he with he | he
      · exact Or.inr (Or.inr he)
      · exact Or.inl he
    have hlen' : (l' ++ List.replicate r 4).length = K := by
      rw [h] at hlen; simp at hlen ⊢; omega
    have hs' : K + 4 + (l' ++ List.replicate r 4).sum = n := by
      rw [h] at hs; simp [List.sum_append] at hs ⊢; omega
    rcases cases34 _ hg' with h' | ⟨r', l'', h'⟩
    · rw [hlen'] at h'
      rw [h']
      rw [h'] at hs'
      simp [List.sum_replicate] at hs'
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rcases Nat.eq_zero_or_pos K' with rfl | hK'
      · exact h9 (by omega)
      · obtain ⟨K'', rfl⟩ : ∃ K'', K' = K'' + 1 := ⟨K' - 1, by omega⟩
        apply H.two
        nth_rewrite 1 [List.replicate_succ, ab_ba H hK hZ _ (by simp) (by simp)
          (by simp [List.sum_replicate]; omega)]
        rw [show 4 :: 3 :: List.replicate (K'' + 1) 4 = [4] ++ 3 :: List.replicate (K'' + 1) 4 from rfl,
          tr_blk_rotate H.toHyp0, show (3 :: List.replicate (K'' + 1) 4) ++ [4] =
            3 :: List.replicate (K'' + 1 + 1) 4 by simp [List.replicate_succ']]
        abel
    · rw [h']
      rw [h'] at hlen' hs'
      simp [List.sum_replicate] at hlen' hs'
      exact chain H hK hZ r' l'' (by omega) (by omega)

end Blocks

include H in
/-- Words with one `y`: `t_j = [yx^j]` vanishes for `j = 0, 1, 3` and `j ≥ 5`. -/
theorem single (j : ℕ) (hj : j ≠ 2) (hj4 : j = 4 → tr (blk x y [4]) = 0) :
    tr (blk x y [j]) = 0 := by
  have rot := H.rot
  simp only [blk, mul_one]
  rcases Nat.lt_or_ge j 5 with h | h
  · interval_cases j
    · rw [pow_zero, mul_one]; exact H.ty
    · -- `2 t₁ = 0`
      have e := congrArg tr H.d1
      rw [map_add, map_add, map_add, map_zero, H.ty2, rot x y, ← sq, H.xp 2 (by norm_num)] at e
      apply H.two
      rw [pow_one]
      rw [← e]; abel
    · exact absurd rfl hj
    · -- `2 t₃ = 0`: compare the traces of `yx²y` and `y² x²`
      have e3 := congrArg tr (d3 H.toHyp0)
      have e1 := congrArg tr (congrArg (· * x ^ 2) H.d1)
      simp only [add_mul, zero_mul] at e1
      have r1 : tr (y * x ^ 2 * y) = tr (y * y * x ^ 2) := by
        rw [rot (y * x ^ 2) y, ← mul_assoc]
      have r2 : tr (x * y * x ^ 2) = tr (y * x ^ 3) := by
        rw [mul_assoc, rot x, show y * x ^ 2 * x = y * x ^ 3 by rw [mul_assoc, ← pow_succ]]
      have r3 : tr (x ^ 2 * y * x) = tr (y * x ^ 3) := by
        rw [mul_assoc, rot (x ^ 2), mul_assoc, ← pow_succ']
      have r4 : tr (x ^ 3 * y) = tr (y * x ^ 3) := rot _ _
      have r5 : tr (y * x * x ^ 2) = tr (y * x ^ 3) := by rw [mul_assoc, ← pow_succ']
      have r6 : tr (x * y * x ^ 2) = tr (y * x ^ 3) := r2
      have r7 : tr (x * x * x ^ 2) = 0 := by
        rw [← sq, ← pow_add]; exact H.xp _ (by norm_num)
      have r8 : tr (2 * x ^ 4) = 0 := by
        rw [two_mul, map_add, H.xp 4 (by norm_num), add_zero]
      rw [map_add, map_add, map_add, map_add, map_add, map_zero, r1, r2, r3, r4, r8] at e3
      rw [map_add, map_add, map_add, map_zero, r5, r6, r7] at e1
      apply H.two
      have : tr (y * x ^ 3) + tr (y * x ^ 3) =
          (tr (y * y * x ^ 2) + tr (y * x ^ 3) + tr (y * x ^ 3) + tr (y * x ^ 3) + tr (y * x ^ 3) + 0) -
            (tr (y * y * x ^ 2) + tr (y * x ^ 3) + tr (y * x ^ 3) + 0) := by abel
      rw [this, e3, e1, sub_zero]
    · simpa [blk] using hj4 rfl
  · rw [show j = 5 + (j - 5) by omega, pow_add, H.x5, zero_mul, mul_zero, map_zero]

include H in
/-- **Lemma A.6 with two invertible, by word degree**: in word degree `n ∉ {3}`,
every word in `x, y` has zero trace, provided `[yx⁴] = 0` in degree five and
`[ab] = 0` in degree nine. -/
theorem all_zero (n : ℕ) (hn : 1 ≤ n) (h3 : n ≠ 3) (h5 : n = 5 → tr (blk x y [4]) = 0)
    (h9 : n = 9 → tr (blk x y [3, 4]) = 0) : ∀ K, Z x y tr n K := by
  intro K
  induction K with
  | zero => exact Z_zero H n hn
  | succ K ih =>
      intro j g hlen hs
      rcases Nat.lt_or_ge g.length (K + 1) with hl | hl
      · exact ih j g (by omega) hs
      obtain ⟨g₀, h, rfl⟩ := (nil_or_snoc g).resolve_left (by rintro rfl; simp at hl)
      rw [tr_bump H.toHyp0]
      have hlen' : (g₀ ++ [h + j]).length = K + 1 := by
        simp only [List.length_append, List.length_singleton] at hl hlen ⊢; omega
      have hs' : K + 1 + (g₀ ++ [h + j]).sum = n := by
        simp only [List.length_append, List.length_singleton, List.sum_append, List.sum_singleton]
          at hs hl hlen ⊢; omega
      rcases Nat.eq_zero_or_pos K with rfl | hK
      · obtain rfl : g₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen')
        have hn' : 1 + (h + j) = n := by simpa using hs'
        exact single H (h + j) (by omega) (fun h4 ↦ h5 (by omega))
      by_cases hgood : ∀ e ∈ g₀ ++ [h + j], e = 3 ∨ e = 4
      · exact blocks_zero H hK ih h9 _ hlen' hgood hs'
      · push Not at hgood
        obtain ⟨e, he, h3e, h4e⟩ := hgood
        exact bad_zero H hK ih _ hlen' hs' e he (by omega)

/-! ### Words as combinations of gap words -/

variable (x y) in
/-- The span of the gap words of word degree `n`. -/
def span (n : ℕ) : AddSubgroup S :=
  AddSubgroup.closure {r | ∃ (j : ℕ) (g : List ℕ), j + g.length + g.sum = n ∧ r = x ^ j * blk x y g}

theorem span_mul_left (n : ℕ) {u r : S}
    (hu : ∀ (j : ℕ) (g : List ℕ), j + g.length + g.sum = n → u * (x ^ j * blk x y g) ∈ span x y (n + 1))
    (hr : r ∈ span x y n) : u * r ∈ span x y (n + 1) := by
  induction hr using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨j, g, hs, rfl⟩ := hr
      exact hu j g hs
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem x_mul_mem (n : ℕ) {r : S} (hr : r ∈ span x y n) : x * r ∈ span x y (n + 1) :=
  span_mul_left n (fun j g hs ↦ AddSubgroup.subset_closure
    ⟨j + 1, g, by omega, by rw [← mul_assoc, ← pow_succ']⟩) hr

theorem y_mul_mem (n : ℕ) {r : S} (hr : r ∈ span x y n) : y * r ∈ span x y (n + 1) :=
  span_mul_left n (fun j g hs ↦ AddSubgroup.subset_closure
    ⟨0, j :: g, by simp; omega, by rw [pow_zero, one_mul]; rfl⟩) hr

include H in
/-- **Vanishing on the span** in word degrees other than three. -/
theorem span_zero (n : ℕ) (hn : 1 ≤ n) (h3 : n ≠ 3) (h5 : n = 5 → tr (blk x y [4]) = 0)
    (h9 : n = 9 → tr (blk x y [3, 4]) = 0) {r : S} (hr : r ∈ span x y n) : tr r = 0 := by
  induction hr using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨j, g, hs, rfl⟩ := hr
      exact all_zero H n hn h3 h5 h9 g.length j g le_rfl hs
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | neg a _ ha => rw [map_neg, ha, neg_zero]

end E78

/-! ### Application to the twisted traces of `E_7` and `E_8` -/

section E78Trace

variable {M : Type*} [AddCommGroup M] {L : Fin 3 → ℕ} (D : TraceData L M)
  (h2 : ∀ m : M, m + m = 0 → m = 0) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hLa : L a = 0) (hLb : L b = 1)

theorem TraceData.tw2_id (hθ : ∀ i, D.θ i = i) (r : R2 L) : D.tw2 r = r := by
  have : D.tw2.comp (mk2 L) = mk2 L := by
    ext i
    simp only [RingHom.comp_apply]
    change D.tw2 (y L i) = y L i
    rw [D.tw2_y, hθ]
  obtain ⟨a, rfl⟩ := mk2_surjective L r
  exact congrArg (fun f : FreeRing (Fin 3) →+* R2 L ↦ f a) this

include h2 hab hac hbc hLa hLb in
/-- **Ordinary traces of `E_7` and `E_8` vanish outside word degrees `3, 5, 9`**
(Lemma A.6(2)); for `E_7` only word degree three remains. -/
theorem trace_E78 (hLc : L c = 2 ∨ L c = 3) (hθ : ∀ i, D.θ i = i) (w : List (Fin 3))
    (hw : 1 ≤ w.length) (h3 : w.length ≠ 3) (h59 : L c = 3 → w.length ≠ 5 ∧ w.length ≠ 9) :
    D.tr w = 0 := by
  set X := y L c
  set Y := y L b
  have hX5 : X ^ 5 = 0 := by
    have := y_pow L c
    rcases hLc with h | h <;> rw [h] at this
    · rw [show 5 = 4 + 1 from rfl, pow_succ, this, zero_mul]
    · exact this
  have hs : y L a + Y + X = 0 := by
    have := sum_y L
    rwa [sum_fin_three _ hab hac hbc] at this
  have hz : y L a = -(X + Y) := by rw [← sub_eq_zero, ← hs]; abel
  have H : E78.Hyp X Y (D.tr2 h2) :=
    { x5 := hX5
      y3 := by have := y_pow L b; rwa [hLb] at this
      d1 := by
        have := y_pow L a
        rw [hLa, zero_add, hz, neg_sq] at this
        rw [← this]; noncomm_ring
      rot := fun p q ↦ by rw [D.tr2_rotate h2, D.tw2_id hθ]
      xp := fun q hq ↦ D.tr2_fixed h2 c (hθ c) q hq
      ty := by have := D.tr2_fixed h2 b (hθ b) 1 le_rfl; rwa [pow_one] at this
      ty2 := by have := D.tr2_fixed h2 b (hθ b) 2 (by norm_num); rwa [sq] at this
      two := h2 }
  -- every word lies in the span of the gap words of its length
  have hmem : ∀ w : List (Fin 3), (w.map (y L)).prod ∈ E78.span X Y w.length := by
    intro w
    induction w with
    | nil => exact AddSubgroup.subset_closure ⟨0, [], rfl, by simp [E78.blk]⟩
    | cons i w ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons]
        rcases fin_three_cases hab hac hbc i with rfl | rfl | rfl
        · rw [hz, neg_mul, add_mul]
          exact neg_mem (add_mem (E78.x_mul_mem _ ih) (E78.y_mul_mem _ ih))
        · exact E78.y_mul_mem _ ih
        · exact E78.x_mul_mem _ ih
  rw [← D.tr2_word h2]
  refine E78.span_zero H w.length hw h3 (fun h5 ↦ ?_) (fun h9 ↦ ?_) (hmem w)
  · rcases hLc with h | h
    · have hX4 : X ^ 4 = 0 := by have := y_pow L c; rwa [h] at this
      simp [E78.blk, hX4]
    · exact absurd h5 (h59 h).1
  · rcases hLc with h | h
    · have hX4 : X ^ 4 = 0 := by have := y_pow L c; rwa [h] at this
      simp [E78.blk, hX4]
    · exact absurd h9 (h59 h).2

end E78Trace

end TraceAlg

end MultiplicativeBasisDeformations
