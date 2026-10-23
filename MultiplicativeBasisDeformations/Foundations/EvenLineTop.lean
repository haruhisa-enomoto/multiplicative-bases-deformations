module

public import MultiplicativeBasisDeformations.Foundations.LineTopPaths
public import MultiplicativeBasisDeformations.Foundations.ASort

/-!
# Top paths of `Π(A_M)` for a path rooted at an end

`characteristic-two-mesh-calculations.tex`: for the line on `1, …, M`,
`(V_d)_{ij} = 1` exactly when `|i − j| ≤ d ≤ min(i + j − 2, 2M − i − j)` and
`d ≡ i − j (mod 2)`, for `0 ≤ d ≤ M − 1`; "`V_{M−1}` is reflection". With the lower bound
`eq:preprojective-lower-bound`, every vertex of `Π(A_M)` has a nonzero path of degree
`M − 1` to its reflection. This is the form used for the even lines `A_{r+1}` retained
in the odd quotients of even `A`.

Here the line is the one-armed star (`L 0 = M − 2`), and the position of a vertex is
its depth plus one.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace LineTop

open DTop

/-- The line formula on positions `1, …, M`. -/
def VL (M d : ℕ) (i j : ℤ) : ℤ :=
  if i - j ≤ d ∧ j - i ≤ d ∧ (d : ℤ) + 2 ≤ i + j ∧ (d : ℤ) + i + j ≤ 2 * M ∧
    ((d : ℤ) - (i - j)) % 2 = 0 then 1 else 0

theorem VL_nonneg (M d : ℕ) (i j : ℤ) : 0 ≤ VL M d i j := by unfold VL; split_ifs <;> norm_num

theorem VL_rec (M d : ℕ) (hd : d + 2 ≤ M - 1) (i j : ℤ) (hi : 1 ≤ i ∧ i ≤ M) (hj : 1 ≤ j ∧ j ≤ M) :
    VL M (d + 2) i j = VL M (d + 1) (i - 1) j + VL M (d + 1) (i + 1) j - VL M d i j := by
  unfold VL; push_cast; split_ifs <;> omega

theorem VL_out (M d : ℕ) (j : ℤ) (hj : 1 ≤ j ∧ j ≤ M) : VL M d (M + 1) j = 0 ∧ VL M d 0 j = 0 := by
  unfold VL; constructor <;> split_ifs <;> omega

variable {L : Fin 1 → ℕ}

/-- The position of a vertex: its depth plus one. -/
abbrev psn (v : StarV L) : ℤ := (starDepth v : ℤ) + 1

theorem psn_le (v : StarV L) : 1 ≤ psn v ∧ psn v ≤ L 0 + 2 := by
  have := depth_le (L := L) v
  simp only [psn]
  constructor <;> omega

theorem nb_psn (x : StarV L) (G : ℤ → ℤ) (hG : G (L 0 + 3) = 0) (hG' : G 0 = 0) :
    ∑ z : (starTree L).Dbl, (starTree L).adjM x z * G (psn (z : StarV L)) =
      G (psn x - 1) + G (psn x + 1) := by
  classical
  have hx := psn_le x
  have hsplit : ∀ z : StarV L, (starTree L).adjM x z * G (psn z) =
      (if psn z = psn x - 1 then G (psn z) else 0) + (if psn z = psn x + 1 then G (psn z) else 0) := by
    intro z
    rw [DTop.adjM_eq x z (starDepth z = starDepth x + 1 ∨ starDepth x = starDepth z + 1)
      (ReRoot.adj_one x z)]
    by_cases h1 : psn z = psn x - 1
    · rw [if_pos (Or.inr (by simp only [psn] at h1; omega)), if_pos h1, if_neg (by omega), one_mul,
        add_zero]
    · by_cases h2 : psn z = psn x + 1
      · rw [if_pos (Or.inl (by simp only [psn] at h2; omega)), if_neg h1, if_pos h2, one_mul,
          zero_add]
      · rw [if_neg (by simp only [psn] at h1 h2; omega), if_neg h1, if_neg h2, zero_mul, add_zero]
  change ∑ z : StarV L, _ = _
  rw [Finset.sum_congr rfl fun z _ ↦ hsplit z, Finset.sum_add_distrib]
  have one : ∀ q : ℤ, (G q = 0 ∨ (1 ≤ q ∧ q ≤ L 0 + 2)) →
      ∑ z : StarV L, (if psn z = q then G (psn z) else 0) = G q := by
    intro q hq
    by_cases hin : 1 ≤ q ∧ q ≤ L 0 + 2
    · have hq0 : (q - 1).toNat ≤ L 0 + 1 := by omega
      rw [Finset.sum_eq_single (ofDep L (q - 1).toNat hq0)]
      · rw [if_pos (by simp only [psn]; rw [starDepth_ofDep]; omega)]
        congr 1; simp only [psn]; rw [starDepth_ofDep]; omega
      · intro z _ hz
        rw [if_neg]
        intro h; apply hz; apply depth_injective
        rw [starDepth_ofDep]; simp only [psn] at h; omega
      · simp
    · rcases hq with hq | hq
      · rw [hq]; refine Finset.sum_eq_zero fun z _ ↦ ?_
        rw [if_neg]; intro h; have := psn_le z; omega
      · exact absurd hq hin
  rw [one _ (by
      by_cases h : psn x - 1 = 0
      · left; rw [h]; exact hG'
      · right; omega),
    one _ (by
      by_cases h : psn x + 1 = L 0 + 3
      · left; rw [h]; exact hG
      · right; omega)]

/-- **The recurrence matrices of the line rooted at an end.** -/
theorem U_eq_VL : ∀ d, d ≤ L 0 + 1 → ∀ x y : (starTree L).Dbl,
    UBound.U (starTree L).adjM d x y = VL (L 0 + 2) d (psn (x : StarV L)) (psn (y : StarV L)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd x y
    have hx := psn_le (x : StarV L)
    have hy := psn_le (y : StarV L)
    match d, ih, hd with
    | 0, _, _ =>
        rw [UBound.U, Matrix.one_apply]
        unfold VL
        by_cases hxy : x = y
        · subst hxy; rw [if_pos rfl, if_pos (by omega)]
        · rw [if_neg hxy, if_neg]
          intro h
          exact hxy (depth_injective (L := L) (by simp only [psn] at h; omega))
    | 1, _, _ =>
        rw [UBound.U, DTop.adjM_eq x y _ (ReRoot.adj_one x y)]
        unfold VL
        simp only [psn] at hx hy ⊢
        split_ifs <;> omega
    | d + 2, ih, hd =>
        rw [UBound.U, Matrix.sub_apply, Matrix.mul_apply]
        have h1 : ∀ z : (starTree L).Dbl, UBound.U (starTree L).adjM (d + 1) z y =
            VL (L 0 + 2) (d + 1) (psn (z : StarV L)) (psn (y : StarV L)) :=
          fun z ↦ ih (d + 1) (by omega) (by omega) z y
        simp only [h1]
        rw [nb_psn x (fun p ↦ VL (L 0 + 2) (d + 1) p (psn (y : StarV L)))
          (by have := (VL_out (L 0 + 2) (d + 1) _ hy).1; push_cast at this ⊢; convert this using 2; ring)
          (VL_out (L 0 + 2) (d + 1) _ hy).2,
          ih d (by omega) (by omega) x y, VL_rec (L 0 + 2) d (by omega) _ _ hx hy]

/-- **Top paths of `Π(A_M)`**, `M = L 0 + 2`: every vertex has a path of degree `M − 1` to
its reflection outside the ideal, over every field. -/
theorem end_return {k : Type*} [Field k] (v w : (starTree L).Dbl)
    (hw : psn (w : StarV L) = L 0 + 3 - psn (v : StarV L)) :
    ∃ p : Quiver.Path v w, p.length = L 0 + 1 ∧
      LinearPaths.path (k := k) p ∉ (starTree L).Id k v w := by
  have hU : ∀ d ≤ L 0 + 1, ∀ x y : (starTree L).Dbl, 0 ≤ UBound.U (starTree L).adjM d x y := by
    intro d hd x y
    rw [U_eq_VL d hd]
    exact VL_nonneg _ _ _ _
  have hdiag : UBound.U (starTree L).adjM (L 0 + 1) v w = 1 := by
    rw [U_eq_VL _ le_rfl, hw]
    have := psn_le (v : StarV L)
    unfold VL; push_cast; split_ifs <;> omega
  have := OrientedTree.U_le_finrank (T := starTree L) (k := k) w (L 0 + 1) hU v
  rw [hdiag] at this
  exact OrientedTree.exists_path_of_finrank (by exact_mod_cast this)

end LineTop

end MultiplicativeBasisDeformations
