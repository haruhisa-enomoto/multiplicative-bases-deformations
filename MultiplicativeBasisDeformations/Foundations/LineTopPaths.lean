import MultiplicativeBasisDeformations.Foundations.DTopPaths
import MultiplicativeBasisDeformations.Foundations.ReRoot

/-!
# Top paths of `Π(A_{2N+1})`

`characteristic-two-mesh-calculations.tex`: for a line, "`V_{d+1} = 𝒜V_d − V_{d−1}`
… the remaining parity interval is exactly `|i − j| ≤ d ≤ min(i + j − 2, 2M − i − j)`,
`d ≡ i − j (mod 2)`. This proves the claimed formula and `V_{M−1}` is reflection."
With the lower bound `eq:preprojective-lower-bound`, every vertex of `Π(A_{2N+1})` has a
nonzero path of degree `2N` to its reflection, over every field.

We use the line rooted at its middle vertex, `ReRoot.Lmid N` (two arms of `N` vertices),
with signed positions `−N, …, N`; there the recurrence matrices are `U_d = V_d` of
`DTop.V`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace LineTop

open DTop ReRoot

variable (N : ℕ) (hN : 1 ≤ N)

include hN in
theorem pos_le (v : StarV (Lmid N)) : -(N : ℤ) ≤ pos v ∧ pos v ≤ N := by
  rcases v with _ | ⟨i, ⟨j, hj⟩⟩
  · simp [pos]
  · simp only [Lmid] at hj
    fin_cases i
    · simp only [pos, if_true]; omega
    · simp only [pos, Fin.mk_one, one_ne_zero, if_false]; omega

include hN in
/-- The sum over neighbours, through positions. -/
theorem nb_pos (x : StarV (Lmid N)) (G : ℤ → ℤ) (hG : G (N + 1) = 0) (hG' : G (-(N + 1)) = 0) :
    ∑ z : (starTree (Lmid N)).Dbl, (starTree (Lmid N)).adjM x z * G (pos (z : StarV (Lmid N))) =
      G (pos x - 1) + G (pos x + 1) := by
  classical
  have hx := pos_le N hN x
  -- the vertices at positions `pos x ∓ 1`
  have hsplit : ∀ z : StarV (Lmid N), (starTree (Lmid N)).adjM x z * G (pos z) =
      (if pos z = pos x - 1 then G (pos z) else 0) + (if pos z = pos x + 1 then G (pos z) else 0) := by
    intro z
    rw [DTop.adjM_eq x z (pos z = pos x + 1 ∨ pos x = pos z + 1) (adj_two x z)]
    by_cases h1 : pos z = pos x - 1
    · rw [if_pos (Or.inr (by omega)), if_pos h1, if_neg (by omega), one_mul, add_zero]
    · by_cases h2 : pos z = pos x + 1
      · rw [if_pos (Or.inl h2), if_neg h1, if_pos h2, one_mul, zero_add]
      · rw [if_neg (by omega), if_neg h1, if_neg h2, zero_mul, add_zero]
  change ∑ z : StarV (Lmid N), _ = _
  rw [Finset.sum_congr rfl fun z _ ↦ hsplit z, Finset.sum_add_distrib]
  have one : ∀ q : ℤ, (G q = 0 ∨ (-(N : ℤ) ≤ q ∧ q ≤ N)) →
      ∑ z : StarV (Lmid N), (if pos z = q then G (pos z) else 0) = G q := by
    intro q hq
    by_cases hin : -(N : ℤ) ≤ q ∧ q ≤ N
    · rw [Finset.sum_eq_single (ofPos N q hin)]
      · rw [pos_ofPos, if_pos rfl]
      · intro z _ hz
        rw [if_neg]
        intro h; apply hz; apply pos_injective; rw [pos_ofPos, h]
      · simp
    · rcases hq with hq | hq
      · rw [hq]; refine Finset.sum_eq_zero fun z _ ↦ ?_
        rw [if_neg]; intro h; have := pos_le N hN z; omega
      · exact absurd hq hin
  rw [one _ (by
      by_cases h : pos x - 1 = -(N + 1)
      · left; rw [h]; exact hG'
      · right; omega),
    one _ (by
      by_cases h : pos x + 1 = N + 1
      · left; rw [h]; exact_mod_cast hG
      · right; omega)]

include hN in
/-- **The recurrence matrices of the line are `V_d`.** -/
theorem U_eq_V : ∀ d, d ≤ 2 * N → ∀ x y : (starTree (Lmid N)).Dbl,
    UBound.U (starTree (Lmid N)).adjM d x y = V N d (pos (x : StarV (Lmid N))) (pos (y : StarV (Lmid N))) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd x y
    have hx := pos_le N hN x
    have hy := pos_le N hN y
    match d, ih, hd with
    | 0, _, _ =>
        rw [UBound.U, Matrix.one_apply]
        unfold V
        by_cases hxy : x = y
        · subst hxy; rw [if_pos rfl, if_pos (by omega)]
        · rw [if_neg hxy, if_neg]
          intro h
          exact hxy (pos_injective (by omega))
    | 1, _, _ =>
        rw [UBound.U, DTop.adjM_eq x y _ (adj_two x y)]
        unfold V
        split_ifs <;> omega
    | d + 2, ih, hd =>
        rw [UBound.U, Matrix.sub_apply, Matrix.mul_apply]
        have h1 : ∀ z : (starTree (Lmid N)).Dbl, UBound.U (starTree (Lmid N)).adjM (d + 1) z y =
            V N (d + 1) (pos (z : StarV (Lmid N))) (pos (y : StarV (Lmid N))) :=
          fun z ↦ ih (d + 1) (by omega) (by omega) z y
        simp only [h1]
        rw [nb_pos N hN x (fun p ↦ V N (d + 1) p (pos (y : StarV (Lmid N))))
          (V_out N (d + 1) _ (by omega))
          (by rw [show -((N : ℤ) + 1) = -((N : ℤ) + 1) from rfl, ← V_neg, neg_neg];
              exact V_out N (d + 1) _ (by omega)),
          ih d (by omega) (by omega) x y, V_rec N d hd _ _ hx hy]

include hN in
/-- **Top paths of `Π(A_{2N+1})`**: every vertex has a path of degree `2N` to its
reflection outside the ideal, over every field. -/
theorem line_return {k : Type*} [Field k] (v w : (starTree (Lmid N)).Dbl)
    (hw : pos (w : StarV (Lmid N)) = -pos (v : StarV (Lmid N))) :
    ∃ p : Quiver.Path v w, p.length = 2 * N ∧
      LinearPaths.path (k := k) p ∉ (starTree (Lmid N)).Id k v w := by
  have hU : ∀ d ≤ 2 * N, ∀ x y : (starTree (Lmid N)).Dbl, 0 ≤ UBound.U (starTree (Lmid N)).adjM d x y := by
    intro d hd x y
    rw [U_eq_V N hN d hd]
    exact V_nonneg _ _ _ _
  have hdiag : UBound.U (starTree (Lmid N)).adjM (2 * N) v w = 1 := by
    rw [U_eq_V N hN _ le_rfl, hw]
    have := pos_le N hN v
    unfold V; split_ifs <;> omega
  have := OrientedTree.U_le_finrank (T := starTree (Lmid N)) (k := k) w (2 * N) hU v
  rw [hdiag] at this
  exact OrientedTree.exists_path_of_finrank (by exact_mod_cast this)

end LineTop

end MultiplicativeBasisDeformations
