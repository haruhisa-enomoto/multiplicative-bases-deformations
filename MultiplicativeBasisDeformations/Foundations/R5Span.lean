module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.List.Induction

/-!
# The centre corner of `E₈` in characteristic two (Appendix B)

`characteristic-two-mesh-calculations.tex`. In
`R₅ = k⟨x, y⟩/(x⁵, y³, (x + y)²)` over a ring with `2 = 0`, put
`ω₃ = yx³y`, `ω₄ = yx⁴y`, `ω₅ = ω₄x³y`. "The following words span `R₅`:
`xⁱ`, `xⁱyxʲ` (`j ≤ 4`), `xⁱω₃`, `xⁱω₄xʲ` (`j ≤ 3`), `xⁱω₅`. Their span contains `1`
and is closed under multiplication on the right by `x, y`. … The highest word degree in
the list is fourteen." We prove the closure (`spn_mul_x`, `spn_mul_y`), so that every
word of degree `n` lies in the span `spn n` of the listed words of degree `n`, and
`spn n = 0` for `n ≥ 15`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace R5

variable {S : Type*} [Ring S] (x y : S)

/-- `ω₃ = yx³y`. -/
abbrev ω3 : S := y * x ^ 3 * y
/-- `ω₄ = yx⁴y`. -/
abbrev ω4 : S := y * x ^ 4 * y
/-- `ω₅ = ω₄x³y`. -/
abbrev ω5 : S := y * x ^ 4 * y * x ^ 3 * y

/-- The listed words of word degree `n`. -/
def Gen (n : ℕ) : Set S :=
  {r | r = x ^ n ∨ (∃ i j, j ≤ 4 ∧ i + j + 1 = n ∧ r = x ^ i * y * x ^ j) ∨
    (∃ i, i + 5 = n ∧ r = x ^ i * ω3 x y) ∨
    (∃ i j, j ≤ 3 ∧ i + j + 6 = n ∧ r = x ^ i * ω4 x y * x ^ j) ∨
    (∃ i, i + 10 = n ∧ r = x ^ i * ω5 x y)}

/-- Their additive span. -/
def spn (n : ℕ) : AddSubgroup S := AddSubgroup.closure (Gen x y n)

structure Hyp : Prop where
  x5 : x ^ 5 = 0
  y3 : y ^ 3 = 0
  d1 : y * y + y * x + x * y + x * x = 0
  two : (2 : S) = 0

variable {x y} (H : Hyp x y)

include H in
theorem add_self (a : S) : a + a = 0 := by rw [← two_mul, H.two, zero_mul]

include H in
theorem neg_self (a : S) : -a = a := neg_eq_of_add_eq_zero_left (add_self H a)

include H in
theorem xpow_big (k : ℕ) (hk : 5 ≤ k) : x ^ k = 0 := by
  rw [show k = 5 + (k - 5) by omega, pow_add, H.x5, zero_mul]

/-! ### The word identities in characteristic two -/

include H in
theorem Ry0 : y * y = y * x + x * y + x ^ 2 := by
  have h := H.d1
  rw [sq]
  have e : y * y = -(y * x + x * y + x * x) := by
    rw [eq_neg_iff_add_eq_zero, ← h]; abel
  rw [e, neg_self H]

include H in
theorem Ry1 : y * x * y = x * y * x + x ^ 3 := by
  have e : y * x * y - x * y * x - x ^ 3 =
      y * (y * y + y * x + x * y + x * x) - (y * y + y * x + x * y + x * x) * x - y ^ 3 := by
    noncomm_ring
  rw [H.d1, H.y3] at e
  simp only [mul_zero, zero_mul, sub_zero] at e
  rw [sub_sub, sub_eq_zero] at e
  exact e

include H in
theorem Ry2 : y * x ^ 2 * y = y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y := by
  have hd2 : y * x * y - x * y * x - x ^ 3 = 0 := by rw [Ry1 H]; abel
  have e : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + 2 * x ^ 4 =
      (y * y + y * x + x * y + x * x) * x * y - x * (y * x * y - x * y * x - x ^ 3) -
        y * (y * x * y - x * y * x - x ^ 3) - (y * x * y - x * y * x - x ^ 3) * x := by
    noncomm_ring
  rw [H.d1, hd2, H.two] at e
  simp only [zero_mul, mul_zero, sub_zero, add_zero] at e
  have e' : y * x ^ 2 * y = -(y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y) := by
    rw [eq_neg_iff_add_eq_zero, ← e]; abel
  rw [e', neg_self H]

include H in
theorem Z2 : y * x * y - x * y * x - x ^ 3 = 0 := by rw [Ry1 H]; abel

include H in
theorem Z3 : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + (x ^ 4 + x ^ 4) =
    0 := by
  have e : y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + (x ^ 4 + x ^ 4) =
      (y * y + y * x + x * y + x * x) * x * y - x * (y * x * y - x * y * x - x ^ 3) -
        y * (y * x * y - x * y * x - x ^ 3) - (y * x * y - x * y * x - x ^ 3) * x := by
    noncomm_ring
  rw [e, H.d1, Z2 H]; simp

include H in
/-- `F`: `ω₃x = ω₄ + xω₃ + x²yx³ + x³yx²`. -/
theorem Rω3x : ω3 x y * x = ω4 x y + x * ω3 x y + x ^ 2 * y * x ^ 3 + x ^ 3 * y * x ^ 2 := by
  have e : y * x ^ 3 * y * x + y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
      x ^ 3 * y * x ^ 2 =
      -((y * x * y - x * y * x - x ^ 3) * x ^ 2 * y -
        y * x * (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + (x ^ 4 + x ^ 4)) +
        (y * x * y - x * y * x - x ^ 3) * x ^ 3 +
        (y * x ^ 2 * y + y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y + (x ^ 4 + x ^ 4)) * x ^ 2) -
      x ^ 5 * y + x ^ 5 * x - y * x ^ 5 := by noncomm_ring
  rw [Z2 H, Z3 H, H.x5] at e
  simp only [zero_mul, mul_zero, sub_zero, add_zero, neg_zero, zero_sub, zero_add] at e
  have e' : y * x ^ 3 * y * x = -(y * x ^ 4 * y + x * y * x ^ 3 * y - x ^ 2 * y * x ^ 3 -
      x ^ 3 * y * x ^ 2) := by
    rw [eq_neg_iff_add_eq_zero, ← e]; abel
  rw [e', neg_self H, sub_eq_add_neg, sub_eq_add_neg, neg_self H, neg_self H]
  simp only [ω3, ω4, mul_assoc]

include H in
theorem Rω3y : ω3 x y * y = x * ω3 x y + x ^ 2 * y * x ^ 3 + x ^ 3 * y * x ^ 2 := by
  have h1 : ω3 x y * y = ω3 x y * x + ω4 x y := by
    simp only [ω3, ω4]
    rw [show y * x ^ 3 * y * y = y * x ^ 3 * (y * y) by noncomm_ring, Ry0 H,
      show y * x ^ 3 * (y * x + x * y + x ^ 2) = y * x ^ 3 * y * x + y * x ^ 4 * y + y * x ^ 5 by
        noncomm_ring, H.x5, mul_zero, add_zero]
  rw [h1, Rω3x H]
  have := add_self H (ω4 x y)
  calc ω4 x y + x * ω3 x y + x ^ 2 * y * x ^ 3 + x ^ 3 * y * x ^ 2 + ω4 x y
      = (ω4 x y + ω4 x y) + (x * ω3 x y + x ^ 2 * y * x ^ 3 + x ^ 3 * y * x ^ 2) := by abel
    _ = _ := by rw [this, zero_add]

include H in
theorem Rω4y : ω4 x y * y = ω4 x y * x := by
  simp only [ω4]
  rw [show y * x ^ 4 * y * y = y * x ^ 4 * (y * y) by noncomm_ring, Ry0 H,
    show y * x ^ 4 * (y * x + x * y + x ^ 2) = y * x ^ 4 * y * x + y * x ^ 5 * y + y * x ^ 6 by
      noncomm_ring, H.x5, xpow_big H 6 (by norm_num)]
  simp

include H in
theorem Rω4xy : ω4 x y * x * y = 0 := by
  simp only [ω4]
  rw [show y * x ^ 4 * y * x * y = y * x ^ 4 * (y * x * y) by noncomm_ring, Ry1 H,
    show y * x ^ 4 * (x * y * x + x ^ 3) = y * x ^ 5 * y * x + y * x ^ 7 by noncomm_ring, H.x5,
    xpow_big H 7 (by norm_num)]
  simp

include H in
theorem Rω4x2y : ω4 x y * x ^ 2 * y = ω4 x y * x ^ 3 := by
  simp only [ω4]
  rw [show y * x ^ 4 * y * x ^ 2 * y = y * x ^ 4 * (y * x ^ 2 * y) by noncomm_ring, Ry2 H,
    show y * x ^ 4 * (y * x ^ 3 + x * y * x ^ 2 + x ^ 2 * y * x + x ^ 3 * y) =
      y * x ^ 4 * y * x ^ 3 + y * x ^ 5 * y * x ^ 2 + y * x ^ 6 * y * x + y * x ^ 7 * y by
      noncomm_ring, H.x5, xpow_big H 6 (by norm_num), xpow_big H 7 (by norm_num)]
  simp

include H in
theorem mono0 (a b : ℕ) (h : 5 ≤ a ∨ 5 ≤ b) : x ^ a * y * x ^ b = 0 := by
  rcases h with h | h
  · rw [xpow_big H a h, zero_mul, zero_mul]
  · rw [xpow_big H b h, mul_zero]

include H in
theorem Rω4x4 : ω4 x y * x ^ 4 =
    x * ω4 x y * x ^ 3 + x ^ 2 * ω4 x y * x ^ 2 + x ^ 3 * ω4 x y * x + x ^ 4 * ω4 x y := by
  set E := ω3 x y * x - (ω4 x y + x * ω3 x y + x ^ 2 * y * x ^ 3 + x ^ 3 * y * x ^ 2) with hE
  have hE0 : E = 0 := by rw [hE, Rω3x H, sub_self]
  have e : ω3 x y * x ^ 5 - x ^ 5 * ω3 x y -
      (ω4 x y * x ^ 4 + x * ω4 x y * x ^ 3 + x ^ 2 * ω4 x y * x ^ 2 + x ^ 3 * ω4 x y * x +
        x ^ 4 * ω4 x y) -
      (x ^ 2 * y * x ^ 7 + x ^ 3 * y * x ^ 6 + x ^ 3 * y * x ^ 6 + x ^ 4 * y * x ^ 5 +
        x ^ 4 * y * x ^ 5 + x ^ 5 * y * x ^ 4 + x ^ 5 * y * x ^ 4 + x ^ 6 * y * x ^ 3 +
        x ^ 6 * y * x ^ 3 + x ^ 7 * y * x ^ 2) =
      E * x ^ 4 + x * E * x ^ 3 + x ^ 2 * E * x ^ 2 + x ^ 3 * E * x + x ^ 4 * E := by
    rw [hE]; noncomm_ring
  rw [hE0, mono0 H 2 7 (by omega), mono0 H 3 6 (by omega), mono0 H 4 5 (by omega),
    mono0 H 5 4 (by omega), mono0 H 6 3 (by omega), mono0 H 7 2 (by omega), H.x5] at e
  simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero] at e
  have e' : ω4 x y * x ^ 4 = -(x * ω4 x y * x ^ 3 + x ^ 2 * ω4 x y * x ^ 2 + x ^ 3 * ω4 x y * x +
      x ^ 4 * ω4 x y) := by
    rw [eq_neg_iff_add_eq_zero, ← neg_eq_zero, ← e]; abel
  rw [e', neg_self H]

include H in
theorem Rω5x : ω5 x y * x = x * ω5 x y + x ^ 2 * ω4 x y * x ^ 3 + x ^ 4 * ω4 x y * x := by
  have h1 : ω5 x y * x = ω4 x y * x ^ 4 * y := by
    have := congrArg (y * x ^ 4 * ·) (Rω3x H)
    simp only [ω3, ω4, ω5] at this ⊢
    have l : y * x ^ 4 * y * x ^ 3 * y * x = y * x ^ 4 * (y * x ^ 3 * y * x) := by noncomm_ring
    rw [l, this]
    have r1 : y * x ^ 4 * (y * x ^ 4 * y) = y * x ^ 4 * y * x ^ 4 * y := by noncomm_ring
    have r2 : y * x ^ 4 * (x * (y * x ^ 3 * y)) = y * x ^ 5 * (y * x ^ 3 * y) := by noncomm_ring
    have r3 : y * x ^ 4 * (x ^ 2 * y * x ^ 3) = y * (x ^ 6 * y * x ^ 3) := by noncomm_ring
    have r4 : y * x ^ 4 * (x ^ 3 * y * x ^ 2) = y * (x ^ 7 * y * x ^ 2) := by noncomm_ring
    rw [mul_add, mul_add, mul_add, r1, r2, r3, r4, H.x5, mono0 H 6 3 (by omega),
      mono0 H 7 2 (by omega)]
    simp
  rw [h1]
  have := congrArg (· * y) (Rω4x4 H)
  simp only [add_mul] at this
  rw [this]
  have e1 : x * ω4 x y * x ^ 3 * y = x * ω5 x y := by simp only [ω4, ω5]; noncomm_ring
  have e2 : x ^ 2 * ω4 x y * x ^ 2 * y = x ^ 2 * ω4 x y * x ^ 3 := by
    rw [mul_assoc (x ^ 2 * ω4 x y), mul_assoc (x ^ 2), ← mul_assoc (ω4 x y) (x ^ 2) y, Rω4x2y H,
      ← mul_assoc]
  have e3 : x ^ 3 * ω4 x y * x * y = 0 := by
    rw [mul_assoc (x ^ 3 * ω4 x y), mul_assoc (x ^ 3), ← mul_assoc (ω4 x y) x y, Rω4xy H,
      mul_zero]
  have e4 : x ^ 4 * ω4 x y * y = x ^ 4 * ω4 x y * x := by rw [mul_assoc, Rω4y H, ← mul_assoc]
  rw [e1, e2, e3, e4, add_zero]

include H in
theorem Rω5y : ω5 x y * y = 0 := by
  have h1 : ω5 x y * y = ω5 x y * x + ω4 x y * x ^ 4 * y := by
    simp only [ω5, ω4]
    rw [show y * x ^ 4 * y * x ^ 3 * y * y = y * x ^ 4 * y * x ^ 3 * (y * y) by noncomm_ring, Ry0 H,
      show y * x ^ 4 * y * x ^ 3 * (y * x + x * y + x ^ 2) =
        y * x ^ 4 * y * x ^ 3 * y * x + y * x ^ 4 * y * x ^ 4 * y + y * x ^ 4 * y * x ^ 5 by
        noncomm_ring, H.x5, mul_zero, add_zero]
  have h2 : ω5 x y * x = ω4 x y * x ^ 4 * y := by
    have := congrArg (y * x ^ 4 * ·) (Rω3x H)
    simp only [ω3, ω4, ω5] at this ⊢
    have l : y * x ^ 4 * y * x ^ 3 * y * x = y * x ^ 4 * (y * x ^ 3 * y * x) := by noncomm_ring
    rw [l, this]
    have r1 : y * x ^ 4 * (y * x ^ 4 * y) = y * x ^ 4 * y * x ^ 4 * y := by noncomm_ring
    have r2 : y * x ^ 4 * (x * (y * x ^ 3 * y)) = y * x ^ 5 * (y * x ^ 3 * y) := by noncomm_ring
    have r3 : y * x ^ 4 * (x ^ 2 * y * x ^ 3) = y * (x ^ 6 * y * x ^ 3) := by noncomm_ring
    have r4 : y * x ^ 4 * (x ^ 3 * y * x ^ 2) = y * (x ^ 7 * y * x ^ 2) := by noncomm_ring
    rw [mul_add, mul_add, mul_add, r1, r2, r3, r4, H.x5, mono0 H 6 3 (by omega),
      mono0 H 7 2 (by omega)]
    simp
  rw [h1, h2, add_self H]

/-! ### Closure of the span -/

variable (x y) in
theorem gen_mem {n : ℕ} {r : S} (h : r ∈ Gen x y n) : r ∈ spn x y n := AddSubgroup.subset_closure h

theorem m1 (n : ℕ) : x ^ n ∈ spn x y n := gen_mem x y (Or.inl rfl)

include H in
theorem m2 (j n : ℕ) (h : j + 1 = n) : y * x ^ j ∈ spn x y n := by
  by_cases hj : j ≤ 4
  · exact gen_mem x y (Or.inr (Or.inl ⟨0, j, hj, by omega, by rw [pow_zero, one_mul]⟩))
  · rw [xpow_big H j (by omega), mul_zero]; exact zero_mem _

theorem m3 : ω3 x y ∈ spn x y 5 :=
  gen_mem x y (Or.inr (Or.inr (Or.inl ⟨0, rfl, by rw [pow_zero, one_mul]⟩)))

theorem m4 (j n : ℕ) (hj : j ≤ 3) (h : j + 6 = n) : ω4 x y * x ^ j ∈ spn x y n :=
  gen_mem x y (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, j, hj, by omega, by rw [pow_zero, one_mul]⟩))))

theorem m5 : ω5 x y ∈ spn x y 10 :=
  gen_mem x y (Or.inr (Or.inr (Or.inr (Or.inr ⟨0, rfl, by rw [pow_zero, one_mul]⟩))))

theorem Lx_gen {n : ℕ} {r : S} (h : r ∈ Gen x y n) : x * r ∈ spn x y (n + 1) := by
  rcases h with rfl | ⟨i, j, hj, hn, rfl⟩ | ⟨i, hn, rfl⟩ | ⟨i, j, hj, hn, rfl⟩ | ⟨i, hn, rfl⟩
  · rw [← pow_succ']; exact m1 _
  · refine gen_mem x y (Or.inr (Or.inl ⟨i + 1, j, hj, by omega, ?_⟩))
    rw [pow_succ', mul_assoc, mul_assoc, mul_assoc]
  · refine gen_mem x y (Or.inr (Or.inr (Or.inl ⟨i + 1, by omega, ?_⟩)))
    rw [pow_succ', mul_assoc]
  · refine gen_mem x y (Or.inr (Or.inr (Or.inr (Or.inl ⟨i + 1, j, hj, by omega, ?_⟩))))
    rw [pow_succ']; simp only [mul_assoc]
  · refine gen_mem x y (Or.inr (Or.inr (Or.inr (Or.inr ⟨i + 1, by omega, ?_⟩))))
    rw [pow_succ', mul_assoc]

theorem Lx {n : ℕ} {r : S} (h : r ∈ spn x y n) : x * r ∈ spn x y (n + 1) := by
  induction h using AddSubgroup.closure_induction with
  | mem r hr => exact Lx_gen hr
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem Lxpow (i : ℕ) {n : ℕ} {r : S} (h : r ∈ spn x y n) : x ^ i * r ∈ spn x y (n + i) := by
  induction i with
  | zero => rw [pow_zero, one_mul]; exact h
  | succ i ih => rw [pow_succ', mul_assoc, ← add_assoc]; exact Lx ih

theorem spn_congr {n n' : ℕ} (h : n = n') {r : S} (hr : r ∈ spn x y n) : r ∈ spn x y n' := h ▸ hr

/-! #### The core words times `x` and `y` -/

include H in
theorem core_y (j : ℕ) (hj : j ≤ 4) : (y * x ^ j) * x ∈ spn x y (j + 2) ∧
    (y * x ^ j) * y ∈ spn x y (j + 2) := by
  constructor
  · rw [mul_assoc, ← pow_succ]; exact m2 H _ _ rfl
  · interval_cases j
    · rw [pow_zero, mul_one, Ry0 H]
      refine add_mem (add_mem ?_ ?_) (m1 2)
      · simpa using m2 H 1 2 rfl
      · have := Lx (m2 H 0 1 rfl); simpa using this
    · rw [pow_one, Ry1 H]
      refine add_mem ?_ (m1 3)
      have := Lx (m2 H 1 2 rfl)
      rw [← mul_assoc, pow_one] at this; exact this
    · rw [Ry2 H]
      refine add_mem (add_mem (add_mem (m2 H 3 4 rfl) ?_) ?_) ?_
      · have := Lx (m2 H 2 3 rfl); rwa [← mul_assoc] at this
      · have := Lxpow 2 (m2 H 1 2 rfl); rwa [← mul_assoc, pow_one] at this
      · have := Lxpow 3 (m2 H 0 1 rfl); rwa [pow_zero, mul_one] at this
    · exact m3
    · simpa using m4 (x := x) (y := y) 0 6 (by norm_num) rfl

include H in
theorem core_ω3 : ω3 x y * x ∈ spn x y 6 ∧ ω3 x y * y ∈ spn x y 6 := by
  have t2 : x ^ 2 * y * x ^ 3 ∈ spn x y 6 := by
    have := Lxpow 2 (m2 H 3 4 rfl); rwa [← mul_assoc] at this
  have t3 : x ^ 3 * y * x ^ 2 ∈ spn x y 6 := by
    have := Lxpow 3 (m2 H 2 3 rfl); rwa [← mul_assoc] at this
  constructor
  · rw [Rω3x H]
    exact add_mem (add_mem (add_mem (by simpa using m4 (x := x) (y := y) 0 6 (by norm_num) rfl)
      (Lx m3)) t2) t3
  · rw [Rω3y H]
    exact add_mem (add_mem (Lx m3) t2) t3

include H in
theorem core_ω4 (j : ℕ) (hj : j ≤ 3) : (ω4 x y * x ^ j) * x ∈ spn x y (j + 7) ∧
    (ω4 x y * x ^ j) * y ∈ spn x y (j + 7) := by
  constructor
  · rw [mul_assoc, ← pow_succ]
    by_cases hj' : j ≤ 2
    · exact m4 _ _ (by omega) rfl
    · obtain rfl : j = 3 := by omega
      rw [Rω4x4 H]
      refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
      · have := Lx (m4 (x := x) (y := y) 3 9 le_rfl rfl); rwa [← mul_assoc] at this
      · have := Lxpow 2 (m4 (x := x) (y := y) 2 8 (by norm_num) rfl); rwa [← mul_assoc] at this
      · have := Lxpow 3 (m4 (x := x) (y := y) 1 7 (by norm_num) rfl)
        rwa [← mul_assoc, pow_one] at this
      · have := Lxpow 4 (m4 (x := x) (y := y) 0 6 (by norm_num) rfl)
        rwa [pow_zero, mul_one] at this
  · interval_cases j
    · rw [pow_zero, mul_one, Rω4y H]
      simpa using m4 (x := x) (y := y) 1 7 (by norm_num) rfl
    · rw [pow_one, Rω4xy H]; exact zero_mem _
    · rw [Rω4x2y H]; exact m4 _ _ le_rfl rfl
    · exact m5

include H in
theorem core_ω5 : ω5 x y * x ∈ spn x y 11 ∧ ω5 x y * y ∈ spn x y 11 := by
  constructor
  · rw [Rω5x H]
    refine add_mem (add_mem (Lx m5) ?_) ?_
    · have := Lxpow 2 (m4 (x := x) (y := y) 3 9 le_rfl rfl); rwa [← mul_assoc] at this
    · have := Lxpow 4 (m4 (x := x) (y := y) 1 7 (by norm_num) rfl)
      rwa [← mul_assoc, pow_one] at this
  · rw [Rω5y H]; exact zero_mem _

include H in
theorem gen_mul {n : ℕ} {r : S} (h : r ∈ Gen x y n) :
    r * x ∈ spn x y (n + 1) ∧ r * y ∈ spn x y (n + 1) := by
  rcases h with rfl | ⟨i, j, hj, hn, rfl⟩ | ⟨i, hn, rfl⟩ | ⟨i, j, hj, hn, rfl⟩ | ⟨i, hn, rfl⟩
  · refine ⟨by rw [← pow_succ]; exact m1 _, ?_⟩
    have := Lxpow n (m2 H 0 1 rfl)
    rw [pow_zero, mul_one] at this
    exact spn_congr (by omega) this
  · obtain ⟨h1, h2⟩ := core_y H j hj
    refine ⟨?_, ?_⟩
    · rw [show x ^ i * y * x ^ j * x = x ^ i * (y * x ^ j * x) by simp only [mul_assoc]]
      refine spn_congr ?_ (Lxpow i h1); omega
    · rw [show x ^ i * y * x ^ j * y = x ^ i * (y * x ^ j * y) by simp only [mul_assoc]]
      refine spn_congr ?_ (Lxpow i h2); omega
  · obtain ⟨h1, h2⟩ := core_ω3 H
    refine ⟨?_, ?_⟩ <;> rw [mul_assoc (x ^ i)]
    · refine spn_congr ?_ (Lxpow i h1); omega
    · refine spn_congr ?_ (Lxpow i h2); omega
  · obtain ⟨h1, h2⟩ := core_ω4 H j hj
    refine ⟨?_, ?_⟩
    · rw [show x ^ i * ω4 x y * x ^ j * x = x ^ i * (ω4 x y * x ^ j * x) by simp only [mul_assoc]]
      refine spn_congr ?_ (Lxpow i h1); omega
    · rw [show x ^ i * ω4 x y * x ^ j * y = x ^ i * (ω4 x y * x ^ j * y) by simp only [mul_assoc]]
      refine spn_congr ?_ (Lxpow i h2); omega
  · obtain ⟨h1, h2⟩ := core_ω5 H
    refine ⟨?_, ?_⟩ <;> rw [mul_assoc (x ^ i)]
    · refine spn_congr ?_ (Lxpow i h1); omega
    · refine spn_congr ?_ (Lxpow i h2); omega

include H in
/-- **The span is closed under right multiplication by `x` and `y`.** -/
theorem spn_mul {n : ℕ} {r : S} (h : r ∈ spn x y n) (u : S) (hu : u = x ∨ u = y) :
    r * u ∈ spn x y (n + 1) := by
  induction h using AddSubgroup.closure_induction with
  | mem r hr => rcases hu with rfl | rfl; exacts [(gen_mul H hr).1, (gen_mul H hr).2]
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

include H in
/-- **Words of degree at least fifteen vanish.** -/
theorem spn_big {n : ℕ} (hn : 15 ≤ n) {r : S} (h : r ∈ spn x y n) : r = 0 := by
  induction h using AddSubgroup.closure_induction with
  | mem r hr =>
      rcases hr with rfl | ⟨i, j, hj, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, j, hj, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · exact xpow_big H n (by omega)
      · rw [xpow_big H i (by omega)]; simp
      · rw [xpow_big H i (by omega)]; simp
      · rw [xpow_big H i (by omega)]; simp
      · rw [xpow_big H i (by omega)]; simp
  | zero => rfl
  | add a b _ _ ha hb => rw [ha, hb, add_zero]
  | neg a _ ha => rw [ha, neg_zero]

include H in
/-- Products of `n` letters `x`, `y`, `x + y` lie in the span of degree `n`. -/
theorem prod_mem (l : List S) (hl : ∀ u ∈ l, u = x ∨ u = y ∨ u = x + y) :
    l.prod ∈ spn x y l.length := by
  induction l using List.reverseRec with
  | nil => simpa using m1 (x := x) (y := y) 0
  | append_singleton l u ih =>
      rw [List.prod_append, List.prod_singleton, List.length_append, List.length_singleton]
      have ih' := ih fun v hv ↦ hl v (List.mem_append_left _ hv)
      rcases hl u (by simp) with rfl | rfl | rfl
      · exact spn_mul H ih' _ (Or.inl rfl)
      · exact spn_mul H ih' _ (Or.inr rfl)
      · rw [mul_add]; exact add_mem (spn_mul H ih' _ (Or.inl rfl)) (spn_mul H ih' _ (Or.inr rfl))

end R5

end MultiplicativeBasisDeformations
