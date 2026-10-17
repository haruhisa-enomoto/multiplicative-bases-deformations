import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Positive definiteness of `2I - Adj(Δ)`

Proof of Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex:112–118`):
"For `M = 2I - Adj(Δ)`, direct expansion gives, for any real vector `z`,
`zᵀMz = ∑_{{i,j}} n_i n_j (z_i/n_i - z_j/n_j)² + ∑_i ((Mn)_i/n_i) z_i²`.
Thus `M` is positive definite."

`qform G z = ∑_i 2 z_i² - ∑_i ∑_{j ∼ i} z_i z_j` is `zᵀ M z`. If `n > 0` and
`Mn > 0` componentwise, then `qform G z > 0` for `z ≠ 0` (`qform_pos`). For a
vector `z ≥ 0` supported on a configuration of edges, `qform` is bounded above
by the same expression over the configuration (`qform_le_of_pattern`); this is
how the forbidden subtrees are excluded.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace MultiplicativeBasisDeformations

universe v

variable {D : Type v} [Fintype D] [DecidableEq D] (G : SimpleGraph D) [DecidableRel G.Adj]

/-- The quadratic form `zᵀ (2I - A) z`. -/
def qform (z : D → ℚ) : ℚ :=
  ∑ i, 2 * z i ^ 2 - ∑ i, ∑ j ∈ G.neighborFinset i, z i * z j

theorem sum_neighbors_swap (f : D → D → ℚ) :
    ∑ i, ∑ j ∈ G.neighborFinset i, f i j = ∑ i, ∑ j ∈ G.neighborFinset i, f j i := by
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [G.adj_comm]

/-- **The quadratic identity**: positivity from a positive vector with `Mn > 0`. -/
theorem qform_pos (n : D → ℚ) (hn : ∀ i, 0 < n i)
    (hMn : ∀ i, 0 < 2 * n i - ∑ j ∈ G.neighborFinset i, n j) {z : D → ℚ} (hz : z ≠ 0) :
    0 < qform G z := by
  have key : qform G z = (1 / 2) * ∑ i, ∑ j ∈ G.neighborFinset i,
        n i * n j * (z i / n i - z j / n j) ^ 2 +
      ∑ i, (2 * n i - ∑ j ∈ G.neighborFinset i, n j) / n i * z i ^ 2 := by
    have h1 : ∑ i, ∑ j ∈ G.neighborFinset i, n i * n j * (z i / n i - z j / n j) ^ 2 =
        ∑ i, ∑ j ∈ G.neighborFinset i, (n j / n i * z i ^ 2 - 2 * (z i * z j)) +
        ∑ i, ∑ j ∈ G.neighborFinset i, n i / n j * z j ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have := hn i; have := hn j
      field_simp
      ring
    have h2 : ∑ i, ∑ j ∈ G.neighborFinset i, n i / n j * z j ^ 2 =
        ∑ i, ∑ j ∈ G.neighborFinset i, n j / n i * z i ^ 2 :=
      sum_neighbors_swap G fun i j ↦ n i / n j * z j ^ 2
    have hB : ∀ i, (2 * n i - ∑ j ∈ G.neighborFinset i, n j) / n i * z i ^ 2 =
        2 * z i ^ 2 - ∑ j ∈ G.neighborFinset i, n j / n i * z i ^ 2 := by
      intro i
      have hi := hn i
      rw [show ∑ j ∈ G.neighborFinset i, n j / n i * z i ^ 2 =
          (∑ j ∈ G.neighborFinset i, n j) * (z i ^ 2 / n i) by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ ↦ ?_; ring]
      field_simp
    rw [h1, h2, Finset.sum_congr rfl fun i _ ↦ hB i]
    unfold qform
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [key]
  have hA : 0 ≤ ∑ i, ∑ j ∈ G.neighborFinset i, n i * n j * (z i / n i - z j / n j) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (mul_nonneg (hn i).le (hn j).le) (sq_nonneg _)
  obtain ⟨i₀, hi₀⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push_neg at h; exact hz (funext h)
  have hB : 0 < ∑ i, (2 * n i - ∑ j ∈ G.neighborFinset i, n j) / n i * z i ^ 2 := by
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
    · exact mul_nonneg (div_nonneg (hMn i).le (hn i).le) (sq_nonneg _)
    · exact mul_pos (div_pos (hMn i₀) (hn i₀)) (by positivity)
  linarith

open Classical in
/-- Extension by zero of weights on an embedded configuration. -/
noncomputable def zOf {ι : Type*} (h : ι → D) (w : ι → ℚ) : D → ℚ :=
  fun d ↦ if hd : ∃ i, h i = d then w hd.choose else 0

theorem zOf_apply {ι : Type*} {h : ι → D} (hh : Function.Injective h) (w : ι → ℚ) (i : ι) :
    zOf h w (h i) = w i := by
  have hd : ∃ j, h j = h i := ⟨i, rfl⟩
  simp only [zOf, dif_pos hd]
  rw [hh hd.choose_spec]

theorem zOf_apply_of_not {ι : Type*} {h : ι → D} (w : ι → ℚ) {d : D} (hd : ¬ ∃ i, h i = d) :
    zOf h w d = 0 := by
  simp only [zOf, dif_neg hd]

/-- **The configuration bound**: for nonnegative weights on embedded vertices
and a family of distinct ordered pairs of adjacent vertices among them,
`zᵀMz ≤ ∑ 2 w² - ∑_{pairs} w w`. -/
theorem qform_le_config {ι κ : Type*} [Fintype ι] [Fintype κ] {h : ι → D}
    (hh : Function.Injective h) (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (e : κ → ι × ι)
    (he : Function.Injective e) (hadj : ∀ c, G.Adj (h (e c).1) (h (e c).2)) :
    qform G (zOf h w) ≤ ∑ i, 2 * w i ^ 2 - ∑ c, w (e c).1 * w (e c).2 := by
  classical
  unfold qform
  have h1 : ∑ d, 2 * zOf h w d ^ 2 = ∑ i, 2 * w i ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image h))]
    · rw [Finset.sum_image (fun i _ j _ hij ↦ hh hij)]
      simp only [zOf_apply hh]
    · intro d _ hd
      rw [zOf_apply_of_not w (by simpa using hd)]
      ring
  have h2 : ∑ c, w (e c).1 * w (e c).2 ≤ ∑ d, ∑ j ∈ G.neighborFinset d, zOf h w d * zOf h w j := by
    have hnn : ∀ d, 0 ≤ zOf h w d := by
      intro d
      by_cases hd : ∃ i, h i = d
      · obtain ⟨i, rfl⟩ := hd; rw [zOf_apply hh]; exact hw i
      · rw [zOf_apply_of_not w hd]
    have hsum : ∑ d, ∑ j ∈ G.neighborFinset d, zOf h w d * zOf h w j =
        ∑ p ∈ Finset.univ ×ˢ Finset.univ,
          (if G.Adj p.1 p.2 then zOf h w p.1 * zOf h w p.2 else 0) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [hsum]
    · let E : κ → D × D := fun c ↦ (h (e c).1, h (e c).2)
      have hE : Function.Injective E := by
        intro c c' hc
        simp only [E, Prod.mk.injEq] at hc
        exact he (Prod.ext (hh hc.1) (hh hc.2))
      calc ∑ c, w (e c).1 * w (e c).2
          = ∑ p ∈ Finset.univ.image E, (if G.Adj p.1 p.2 then zOf h w p.1 * zOf h w p.2 else 0) := by
            rw [Finset.sum_image (fun c _ c' _ hcc ↦ hE hcc)]
            refine Finset.sum_congr rfl fun c _ ↦ ?_
            simp only [E, if_pos (hadj c), zOf_apply hh]
        _ ≤ ∑ p ∈ Finset.univ ×ˢ Finset.univ,
              (if G.Adj p.1 p.2 then zOf h w p.1 * zOf h w p.2 else 0) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) fun p _ _ ↦ ?_
            split_ifs
            · exact mul_nonneg (hnn _) (hnn _)
            · exact le_rfl
  linarith

end MultiplicativeBasisDeformations
