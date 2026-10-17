import MultiplicativeBasisDeformations.Foundations.TraceE78
import MultiplicativeBasisDeformations.Foundations.R5Span
import MultiplicativeBasisDeformations.Foundations.TraceAlgebraChar2

/-!
# Ordinary traces of `E_7` and `E_8` in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex`: "Apply Lemma A.6(1) in
characteristic two. For `a = yx³` and `b = yx⁴`, its block relations and `3[ab] = 0`
give `[a²W] = 0` (`W ≠ 1`), `[abW] = [baW]` (`W ≠ 1`), `[ab] = 0`, `[b^q] = 0`
(`q ≥ 2`). Words with two `a`'s and at least three blocks vanish by bringing the `a`'s
together. With exactly one `a`, only `ab²` can remain: `abʳ` has word degree greater
than fourteen for `r ≥ 3`. For the one-`y` words, the identities `3[yx²] = 0` and
`5[yx⁴] = 0` still hold, whereas no vanishing follows from `2[yx] = 2[yx³] = 0`. Thus
the ordinary positive trace is spanned by `yx, yx³, (yx³)², (yx³)(yx⁴)²` in word
degrees `2, 4, 8, 14`."

We run the induction of Lemma A.6 on the number of `y`'s in a fixed word degree `n`,
with values in a subgroup `A` of the target containing the candidate class of degree
`n` (`all_mem`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TraceAlg

namespace E78c

open E78

variable {S : Type*} [Ring S] (x y : S) {M : Type*} [AddCommGroup M] (tr : S →+ M)

/-- The hypotheses in characteristic two. -/
structure Hyp : Prop where
  x5 : x ^ 5 = 0
  y3 : y ^ 3 = 0
  d1 : y * y + y * x + x * y + x * x = 0
  two : (2 : S) = 0
  rot : ∀ p q, tr (p * q) = tr (q * p)
  xp : ∀ q, 1 ≤ q → tr (x ^ q) = 0
  ty : tr y = 0
  ty2 : tr (y * y) = 0

variable {x y tr} (H : Hyp x y tr)

include H in
theorem r5 : R5.Hyp x y := ⟨H.x5, H.y3, H.d1, H.two⟩

include H in
theorem tr_self (r : S) : tr r + tr r = 0 := by
  rw [← map_add, ← two_mul, H.two, zero_mul, map_zero]

include H in
theorem tr_eq_neg (r : S) : tr (-r) = tr r := by
  rw [map_neg]; exact neg_eq_of_add_eq_zero_left (tr_self H r)

include H in
theorem tr_blk_rotate (g₁ g₂ : List ℕ) : tr (blk x y (g₁ ++ g₂)) = tr (blk x y (g₂ ++ g₁)) := by
  rw [blk_append, blk_append, H.rot]

include H in
theorem tr_bump (g₀ : List ℕ) (h j : ℕ) :
    tr (x ^ j * blk x y (g₀ ++ [h])) = tr (blk x y (g₀ ++ [h + j])) := by
  rw [H.rot, blk_snoc_mul]

include H in
theorem blk_big (e : ℕ) (he : 5 ≤ e) (g : List ℕ) : blk x y (e :: g) = 0 := by
  rw [blk, show e = 5 + (e - 5) by omega, pow_add, H.x5, zero_mul, zero_mul, mul_zero]

/-! ### Gap reductions in characteristic two -/

include H in
theorem red0 (h : ℕ) (g : List ℕ) : blk x y (0 :: h :: g) = blk x y ((h + 1) :: g) +
    x ^ 1 * blk x y (h :: g) + x ^ (h + 2) * blk x y g := by
  simp only [blk, pow_zero, one_mul, pow_one]
  rw [← mul_assoc, R5.Ry0 (r5 H)]
  simp only [add_mul, mul_assoc, pow_succ', pow_zero, mul_one]

include H in
theorem red1 (h : ℕ) (g : List ℕ) : blk x y (1 :: h :: g) = x ^ 1 * blk x y ((h + 1) :: g) +
    x ^ (h + 3) * blk x y g := by
  simp only [blk, pow_one]
  rw [show y * (x * (y * (x ^ h * blk x y g))) = y * x * y * (x ^ h * blk x y g) by
    simp only [mul_assoc], R5.Ry1 (r5 H)]
  simp only [add_mul, mul_assoc, pow_succ', pow_zero, mul_one]

include H in
theorem red2 (h : ℕ) (g : List ℕ) : blk x y (2 :: h :: g) = blk x y ((h + 3) :: g) +
    x ^ 1 * blk x y ((h + 2) :: g) + x ^ 2 * blk x y ((h + 1) :: g) + x ^ 3 * blk x y (h :: g) := by
  simp only [blk]
  rw [show y * (x ^ 2 * (y * (x ^ h * blk x y g))) = y * x ^ 2 * y * (x ^ h * blk x y g) by
    simp only [mul_assoc], R5.Ry2 (r5 H)]
  simp only [add_mul, mul_assoc, pow_succ', pow_zero, mul_one]

/-! ### Words with one `y` -/

include H in
theorem t2_zero : tr (y * x ^ 2) = 0 := by
  have R := r5 H
  have e1 : tr (y * x * y) = tr (y * x ^ 2) := by
    rw [R5.Ry1 R, map_add, H.xp 3 (by norm_num), add_zero, mul_assoc, H.rot x, mul_assoc, ← sq]
  have e2 : tr (y * x * y) = tr (y * y * x) := by rw [H.rot (y * x), ← mul_assoc]
  have e3 : tr (y * y * x) = 0 := by
    rw [R5.Ry0 R, add_mul, add_mul, map_add, map_add, ← pow_succ, H.xp 3 (by norm_num), add_zero,
      mul_assoc, ← sq, mul_assoc, H.rot x, mul_assoc, ← sq]
    exact tr_self H _
  rw [← e1, e2, e3]

include H in
theorem t4_zero : tr (y * x ^ 4) = 0 := by
  have R := r5 H
  have lhs : tr (y * x ^ 2 * y * x) = tr (y * x ^ 4) := by
    rw [show y * x ^ 2 * y * x = (y * x ^ 2) * (y * x) by noncomm_ring, H.rot (y * x ^ 2),
      show y * x * (y * x ^ 2) = y * x * y * x ^ 2 by noncomm_ring, R5.Ry1 R,
      add_mul, map_add, ← pow_add, H.xp 5 (by norm_num), add_zero,
      show x * y * x * x ^ 2 = x * (y * x ^ 3) by noncomm_ring, H.rot x, mul_assoc, ← pow_succ]
  have rhs := congrArg (fun r ↦ tr (r * x)) (R5.Ry2 R)
  simp only [add_mul, map_add] at rhs
  rw [lhs] at rhs
  have r1 : tr (y * x ^ 3 * x) = tr (y * x ^ 4) := by rw [mul_assoc, ← pow_succ]
  have r2 : tr (x * y * x ^ 2 * x) = tr (y * x ^ 4) := by
    rw [show x * y * x ^ 2 * x = x * (y * x ^ 3) by noncomm_ring, H.rot x, mul_assoc, ← pow_succ]
  have r3 : tr (x ^ 2 * y * x * x) = tr (y * x ^ 4) := by
    rw [show x ^ 2 * y * x * x = x ^ 2 * (y * x ^ 2) by noncomm_ring, H.rot (x ^ 2), mul_assoc,
      ← pow_add]
  have r4 : tr (x ^ 3 * y * x) = tr (y * x ^ 4) := by
    rw [mul_assoc, H.rot (x ^ 3), mul_assoc, ← pow_succ']
  rw [r1, r2, r3, r4] at rhs
  rw [rhs, tr_self H, zero_add, tr_self H]

variable (x y tr) in
/-- All words of word degree `n` with at most `K` letters `y` have trace in `A`. -/
def Zs (n K : ℕ) (A : AddSubgroup M) : Prop :=
  ∀ (j : ℕ) (g : List ℕ), g.length ≤ K → j + g.length + g.sum = n → tr (x ^ j * blk x y g) ∈ A

variable {A : AddSubgroup M}

include H in
theorem Zs_zero (n : ℕ) (hn : 1 ≤ n) : Zs x y tr n 0 A := by
  intro j g hg hs
  obtain rfl : g = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [List.length_nil, List.sum_nil, add_zero] at hs
  rw [blk, mul_one, H.xp j (by omega)]; exact zero_mem _

include H in
theorem single (h : ℕ) (h2 : h = 1 → tr (blk x y [1]) ∈ A) (h4 : h = 3 → tr (blk x y [3]) ∈ A) :
    tr (blk x y [h]) ∈ A := by
  rcases Nat.lt_or_ge h 5 with hh | hh
  · interval_cases h
    · simp only [blk, pow_zero, mul_one, H.ty]; exact zero_mem _
    · exact h2 rfl
    · simp only [blk, mul_one]; rw [t2_zero H]; exact zero_mem _
    · exact h4 rfl
    · simp only [blk, mul_one]; rw [t4_zero H]; exact zero_mem _
  · rw [blk_big H h hh]; simp

theorem blk_zero_of_mem (g : List ℕ) (e : ℕ) (he : e ∈ g) (hx : x ^ e = 0) : blk x y g = 0 := by
  obtain ⟨g₁, g₂, rfl⟩ := List.append_of_mem he
  rw [blk_append, blk, hx, zero_mul, mul_zero, mul_zero]

/-! ### Bad gaps -/

include H in
/-- **A gap of length at most two, or at least five, reduces to fewer `y`'s.** -/
theorem bad_mem {n K : ℕ} (hK : 1 ≤ K) (hZ : Zs x y tr n K A) (g : List ℕ) (hg : g.length = K + 1)
    (hs : K + 1 + g.sum = n) (e : ℕ) (he : e ∈ g) (hbad : e ≤ 2 ∨ 5 ≤ e) :
    tr (blk x y g) ∈ A := by
  obtain ⟨g₁, g₂, rfl⟩ := List.append_of_mem he
  rw [tr_blk_rotate H, List.cons_append]
  set g' := g₂ ++ g₁ with hg'
  have hlen : g'.length = K := by
    rw [hg', List.length_append]; rw [List.length_append, List.length_cons] at hg; omega
  have hsum : K + 1 + e + g'.sum = n := by
    rw [hg', List.sum_append]; rw [List.sum_append, List.sum_cons] at hs; omega
  obtain ⟨h, g'', hh⟩ := List.exists_cons_of_length_pos (l := g') (by omega)
  rw [hh] at hlen hsum ⊢
  simp only [List.length_cons, List.sum_cons] at hlen hsum
  have z0 : ∀ (g : List ℕ), g.length ≤ K → g.length + g.sum = n → tr (blk x y g) ∈ A := by
    intro g h1 h2
    have := hZ 0 g h1 (by omega)
    rwa [pow_zero, one_mul] at this
  rcases hbad with hb | hb
  · interval_cases e
    · rw [red0 H, map_add, map_add]
      exact add_mem (add_mem (z0 _ (by simp; omega) (by simp; omega))
        (hZ 1 _ (by simp; omega) (by simp; omega))) (hZ (h + 2) _ (by omega) (by omega))
    · rw [red1 H, map_add]
      exact add_mem (hZ 1 _ (by simp; omega) (by simp; omega)) (hZ (h + 3) _ (by omega) (by omega))
    · rw [red2 H, map_add, map_add, map_add]
      exact add_mem (add_mem (add_mem (z0 _ (by simp; omega) (by simp; omega))
        (hZ 1 _ (by simp; omega) (by simp; omega))) (hZ 2 _ (by simp; omega) (by simp; omega)))
        (hZ 3 _ (by simp; omega) (by simp; omega))
  · rw [blk_big H e hb, map_zero]; exact zero_mem _

/-! ### Words in `a = yx³` and `b = yx⁴` -/

include H in
/-- `F x^k W`: `blk (3 :: (k+1) :: g) = blk (4 :: k :: g) + …`. -/
theorem Fk (k : ℕ) (g : List ℕ) : blk x y (3 :: (k + 1) :: g) = blk x y (4 :: k :: g) +
    x ^ 1 * blk x y (3 :: k :: g) + x ^ 2 * blk x y ((k + 3) :: g) +
      x ^ 3 * blk x y ((k + 2) :: g) := by
  have R := r5 H
  have e : blk x y (3 :: (k + 1) :: g) - (blk x y (4 :: k :: g) + x ^ 1 * blk x y (3 :: k :: g) +
      x ^ 2 * blk x y ((k + 3) :: g) + x ^ 3 * blk x y ((k + 2) :: g)) =
      (R5.ω3 x y * x - (R5.ω4 x y + x * R5.ω3 x y + x ^ 2 * y * x ^ 3 + x ^ 3 * y * x ^ 2)) *
        (x ^ k * blk x y g) := by
    simp only [blk, R5.ω3, R5.ω4]
    rw [add_comm k 1, add_comm k 3, add_comm k 2, pow_add, pow_add, pow_add]
    noncomm_ring
  rw [R5.Rω3x R, sub_self, zero_mul, sub_eq_zero] at e
  exact e

variable {n K : ℕ} (hK : 1 ≤ K) (hZ : Zs x y tr n K A)

include H hK hZ in
/-- `[a²W] ∈ A` for nonempty `W`; `[a²]` is the candidate of degree eight. -/
theorem aa_mem (g : List ℕ) (hlen : g.length + 1 = K) (hs : K + 7 + g.sum = n)
    (h8 : g = [] → tr (blk x y [3, 3]) ∈ A) : tr (blk x y (3 :: 3 :: g)) ∈ A := by
  rcases E78.nil_or_snoc g with rfl | ⟨g₀, h, rfl⟩
  · exact h8 rfl
  rw [Fk H 2 _, map_add, map_add, map_add]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  · exact bad_mem H hK hZ _ (by simp at hlen ⊢; omega) (by simp at hlen hs ⊢; omega) 2 (by simp)
      (by omega)
  · rw [show 3 :: 2 :: (g₀ ++ [h]) = (3 :: 2 :: g₀) ++ [h] by simp, tr_bump H]
    exact bad_mem H hK hZ _ (by simp at hlen ⊢; omega) (by simp at hlen hs ⊢; omega) 2 (by simp)
      (by omega)
  · rw [blk_big H 5 le_rfl, mul_zero, map_zero]; exact zero_mem _
  · exact hZ 3 _ (by simp at hlen ⊢; omega) (by simp at hlen hs ⊢; omega)

include H hK hZ in
/-- `[abW] - [baW] ∈ A` for nonempty `W`. -/
theorem ab_sub_mem (g : List ℕ) (hne : g ≠ []) (hlen : g.length + 1 = K)
    (hs : K + 8 + g.sum = n) :
    tr (blk x y (3 :: 4 :: g)) - tr (blk x y (4 :: 3 :: g)) ∈ A := by
  rw [Fk H 3 g, map_add, map_add, map_add,
    show ∀ a b c d : M, a + b + c + d - a = b + c + d from fun a b c d ↦ by abel]
  obtain ⟨g₀, h, rfl⟩ := (E78.nil_or_snoc g).resolve_left hne
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [show 3 :: 3 :: (g₀ ++ [h]) = (3 :: 3 :: g₀) ++ [h] by simp, tr_bump H,
      show (3 :: 3 :: g₀) ++ [h + 1] = 3 :: 3 :: (g₀ ++ [h + 1]) by simp]
    exact aa_mem H hK hZ _ (by simp at hlen ⊢; omega) (by simp at hlen hs ⊢; omega) (by simp)
  · rw [blk_big H 6 (by norm_num), mul_zero, map_zero]; exact zero_mem _
  · rw [blk_big H 5 le_rfl, mul_zero, map_zero]; exact zero_mem _

include H in
theorem ab_zero : tr (blk x y [3, 4]) = 0 := by
  have e := congrArg tr (Fk H 3 [])
  rw [map_add, map_add, map_add, blk_big H 6 (by norm_num), blk_big H 5 le_rfl, mul_zero,
    mul_zero, map_zero, add_zero, add_zero] at e
  have r1 : tr (blk x y [4, 3]) = tr (blk x y [3, 4]) := tr_blk_rotate H [4] [3]
  have r2 : tr (x ^ 1 * blk x y [3, 3]) = tr (blk x y [3, 4]) := tr_bump H [3] 3 1
  rw [r1, r2, tr_self H] at e
  exact e

include H in
/-- `[b²W] = [x a b W]`. -/
theorem bb_eq (g : List ℕ) : tr (blk x y (4 :: 4 :: g)) = tr (x ^ 1 * blk x y (3 :: 4 :: g)) := by
  have e := Fk H 4 g
  rw [show blk x y (3 :: (4 + 1) :: g) = 0 by rw [blk, blk_big H 5 le_rfl, mul_zero, mul_zero],
    blk_big H 7 (by norm_num), blk_big H 6 (by norm_num), mul_zero, mul_zero, add_zero,
    add_zero] at e
  have e' : blk x y (4 :: 4 :: g) = -(x ^ 1 * blk x y (3 :: 4 :: g)) := by
    rw [eq_neg_iff_add_eq_zero, ← e]
  rw [e', tr_eq_neg H]

/-! ### The degree bound -/

variable (x y) in
/-- A gap word as a list of letters. -/
def blkL (g : List ℕ) : List S := g.flatMap fun e ↦ y :: List.replicate e x

theorem blkL_prod (g : List ℕ) : (blkL x y g).prod = blk x y g := by
  induction g with
  | nil => rfl
  | cons e g ih =>
      simp only [blkL, List.flatMap_cons, List.prod_append, List.prod_cons, List.prod_replicate]
        at ih ⊢
      rw [ih, blk, mul_assoc]

theorem blkL_length (g : List ℕ) : (blkL x y g).length = g.length + g.sum := by
  induction g with
  | nil => rfl
  | cons e g ih =>
      simp only [blkL, List.flatMap_cons, List.length_append, List.length_cons,
        List.length_replicate] at ih ⊢
      rw [ih, List.sum_cons]; ring

include H in
/-- **Words of degree at least fifteen vanish** (`R5.spn_big`). -/
theorem blk_big15 (g : List ℕ) (hg : 15 ≤ g.length + g.sum) : blk x y g = 0 := by
  rw [← blkL_prod]
  refine R5.spn_big (r5 H) (n := (blkL x y g).length) (by rw [blkL_length]; exact hg) ?_
  refine R5.prod_mem (r5 H) _ fun u hu ↦ ?_
  simp only [blkL, List.mem_flatMap, List.mem_cons, List.mem_replicate] at hu
  obtain ⟨_, _, hu | ⟨_, hu⟩⟩ := hu
  · exact Or.inr (Or.inl hu)
  · exact Or.inl hu

include H hK hZ in
/-- Two `a`'s are brought together using `[abW] = [baW]`. -/
theorem chain_mem (r : ℕ) (g : List ℕ) (hlen : r + g.length + 1 = K)
    (hs : K + 7 + 4 * r + g.sum = n) (hne : r ≠ 0 ∨ g ≠ []) :
    tr (blk x y (3 :: (List.replicate r 4 ++ 3 :: g))) ∈ A := by
  induction r generalizing g with
  | zero =>
      have hg : g ≠ [] := by simpa using hne
      exact aa_mem H hK hZ g (by omega) (by simpa using hs) (fun h ↦ absurd h hg)
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append]
      have h1 := ab_sub_mem H hK hZ (List.replicate r 4 ++ 3 :: g) (by simp)
        (by simp; omega) (by simp [List.sum_replicate]; omega)
      have h2 : tr (blk x y (4 :: 3 :: (List.replicate r 4 ++ 3 :: g))) ∈ A := by
        rw [show 4 :: 3 :: (List.replicate r 4 ++ 3 :: g) = [4] ++ 3 :: (List.replicate r 4 ++ 3 :: g)
          from rfl, tr_blk_rotate H,
          show (3 :: (List.replicate r 4 ++ 3 :: g)) ++ [4] = 3 :: (List.replicate r 4 ++ 3 :: (g ++ [4]))
            by simp]
        exact ih (g ++ [4]) (by simp; omega) (by simp; omega) (Or.inr (by simp))
      have := add_mem h1 h2
      rwa [sub_add_cancel] at this

include H hK hZ in
/-- **Cyclic words in `a, b`.** -/
theorem blocks_mem (h8 : n = 8 → tr (blk x y [3, 3]) ∈ A)
    (h14 : n = 14 → tr (blk x y [3, 4, 4]) ∈ A) (g : List ℕ) (hlen : g.length = K + 1)
    (hg : ∀ e ∈ g, e = 3 ∨ e = 4) (hs : K + 1 + g.sum = n) : tr (blk x y g) ∈ A := by
  rcases E78.cases34 g hg with h | ⟨r, l', h⟩
  · -- only `b`'s
    rw [hlen] at h
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [h, List.replicate_succ, List.replicate_succ, bb_eq H,
      show 3 :: 4 :: List.replicate K' 4 = (3 :: List.replicate K' 4) ++ [4] by
        rw [List.cons_append, ← List.replicate_succ', List.replicate_succ],
      tr_bump H, blk_zero_of_mem (x := x) (y := y) _ 5 (by simp) H.x5, map_zero]
    exact zero_mem _
  · -- rotate an `a` to the front
    have hrot : tr (blk x y g) = tr (blk x y (3 :: (l' ++ List.replicate r 4))) := by
      rw [h, tr_blk_rotate H, List.cons_append]
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
    rcases E78.cases34 _ hg' with h' | ⟨r', l'', h'⟩
    · -- `a b^K`
      rw [hlen'] at h'
      rw [h']
      rw [h'] at hs'
      simp [List.sum_replicate] at hs'
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rcases Nat.lt_or_ge K' 2 with hK' | hK'
      · interval_cases K'
        · rw [show 3 :: List.replicate (0 + 1) 4 = [3, 4] from rfl, ab_zero H]; exact zero_mem _
        · exact h14 (by omega)
      · rw [blk_big15 H _ (by simp [List.sum_replicate]; omega), map_zero]; exact zero_mem _
    · rw [h']
      rw [h'] at hlen' hs'
      simp [List.sum_replicate] at hlen' hs'
      by_cases h0 : r' = 0 ∧ l'' = []
      · obtain ⟨rfl, rfl⟩ := h0
        simp only [List.length_nil, List.sum_nil] at hlen' hs'
        exact h8 (by omega)
      · exact chain_mem H hK hZ r' l'' (by omega) (by omega) (by tauto)

include H in
/-- **The ordinary traces in characteristic two, by word degree**: in word degree `n`,
every gap word has trace in any subgroup containing the candidate of degree `n`. -/
theorem all_mem (n : ℕ) (hn : 1 ≤ n) (h2 : n = 2 → tr (blk x y [1]) ∈ A)
    (h4 : n = 4 → tr (blk x y [3]) ∈ A) (h8 : n = 8 → tr (blk x y [3, 3]) ∈ A)
    (h14 : n = 14 → tr (blk x y [3, 4, 4]) ∈ A) : ∀ K, Zs x y tr n K A := by
  intro K
  induction K with
  | zero => exact Zs_zero H n hn
  | succ K ih =>
      intro j g hlen hs
      rcases Nat.lt_or_ge g.length (K + 1) with hl | hl
      · exact ih j g (by omega) hs
      obtain ⟨g₀, h, rfl⟩ := (E78.nil_or_snoc g).resolve_left (by rintro rfl; simp at hl)
      rw [tr_bump H]
      have hlen' : (g₀ ++ [h + j]).length = K + 1 := by
        simp only [List.length_append, List.length_singleton] at hl hlen ⊢; omega
      have hs' : K + 1 + (g₀ ++ [h + j]).sum = n := by
        simp only [List.length_append, List.length_singleton, List.sum_append, List.sum_singleton]
          at hs hl hlen ⊢; omega
      rcases Nat.eq_zero_or_pos K with rfl | hK
      · obtain rfl : g₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen')
        have hn' : 1 + (h + j) = n := by simpa using hs'
        exact single H (h + j) (fun h1 ↦ h2 (by omega)) (fun h3 ↦ h4 (by omega))
      by_cases hgood : ∀ e ∈ g₀ ++ [h + j], e = 3 ∨ e = 4
      · exact blocks_mem H hK ih h8 h14 _ hlen' hgood hs'
      · push Not at hgood
        obtain ⟨e, he, h3e, h4e⟩ := hgood
        exact bad_mem H hK ih _ hlen' hs' e he (by omega)

include H in
theorem span_mem (n : ℕ) (hn : 1 ≤ n) (h2 : n = 2 → tr (blk x y [1]) ∈ A)
    (h4 : n = 4 → tr (blk x y [3]) ∈ A) (h8 : n = 8 → tr (blk x y [3, 3]) ∈ A)
    (h14 : n = 14 → tr (blk x y [3, 4, 4]) ∈ A) {r : S} (hr : r ∈ E78.span x y n) : tr r ∈ A := by
  induction hr using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨j, g, hs, rfl⟩ := hr
      exact all_mem H n hn h2 h4 h8 h14 g.length j g le_rfl hs
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end E78c

end TraceAlg

end MultiplicativeBasisDeformations
