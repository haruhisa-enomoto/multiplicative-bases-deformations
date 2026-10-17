import Mathlib

/-!
# The lower bound by the matrices `U_d`

`periodic-mesh-calculations.tex`: "For a finite graph with adjacency
matrix `M`, define integer matrices `U_0 = I`, `U_1 = M`,
`U_{d+1} = M U_d - U_{d-1}`. If `U_0, …, U_N` are entrywise nonnegative, then
`(dim_k e_i Π(Δ)_N e_j)_{ij} ≥ U_N`. … If `K(t)` records the kernels of the
leftmost maps, … `(I - tM + t²I) H(t) = I + K(t)`,
`H(t) = (∑ U_d t^d)(I + K(t))`. The coefficients of `K` are nonnegative."

We record the coefficientwise form: a sequence of vectors `h_d` with
`κ_d = h_d - M h_{d-1} + h_{d-2} ≥ 0` satisfies `h_N = ∑_{e ≤ N} U_{N-e} κ_e`,
hence `h_N ≥ U_N h_0` when `U_0, …, U_N ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace UBound

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)

/-- `U_0 = I`, `U_1 = M`, `U_{d+2} = M U_{d+1} - U_d`. -/
def U : ℕ → Matrix ι ι ℤ
  | 0 => 1
  | 1 => M
  | d + 2 => M * U (d + 1) - U d

/-- The defects `κ_d = h_d - M h_{d-1} + h_{d-2}`. -/
def κ (h : ℕ → ι → ℤ) : ℕ → ι → ℤ
  | 0 => h 0
  | 1 => h 1 - M *ᵥ h 0
  | d + 2 => h (d + 2) - M *ᵥ h (d + 1) + h d

/-- `S_N = ∑_{e ≤ N} U_{N-e} κ_e`. -/
def S (h : ℕ → ι → ℤ) (N : ℕ) : ι → ℤ :=
  ∑ e ∈ Finset.range (N + 1), U M (N - e) *ᵥ κ M h e

theorem S_eq (h : ℕ → ι → ℤ) : ∀ N, S M h N = h N
  | 0 => by simp [S, U, κ]
  | 1 => by
      simp [S, U, κ, Finset.sum_range_succ]
  | N + 2 => by
      have h1 := S_eq h (N + 1)
      have h0 := S_eq h N
      -- split off the last two terms
      have e1 : S M h (N + 2) = ∑ e ∈ Finset.range (N + 1), U M (N + 2 - e) *ᵥ κ M h e +
          M *ᵥ κ M h (N + 1) + κ M h (N + 2) := by
        simp only [S, Finset.sum_range_succ, show N + 2 - (N + 1) = 1 by omega, Nat.sub_self, U,
          one_mulVec]
      have e2 : ∑ e ∈ Finset.range (N + 1), U M (N + 2 - e) *ᵥ κ M h e =
          M *ᵥ (∑ e ∈ Finset.range (N + 1), U M (N + 1 - e) *ᵥ κ M h e) -
            ∑ e ∈ Finset.range (N + 1), U M (N - e) *ᵥ κ M h e := by
        rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun e he ↦ ?_
        rw [Finset.mem_range] at he
        rw [show N + 2 - e = (N - e) + 2 by omega, show N + 1 - e = (N - e) + 1 by omega, U,
          Matrix.sub_mulVec, Matrix.mulVec_mulVec]
      have e3 : ∑ e ∈ Finset.range (N + 1), U M (N + 1 - e) *ᵥ κ M h e =
          S M h (N + 1) - κ M h (N + 1) := by
        simp only [S, Finset.sum_range_succ (n := N + 1), Nat.sub_self, U, one_mulVec,
          add_sub_cancel_right]
      rw [e1, e2, e3, show (∑ e ∈ Finset.range (N + 1), U M (N - e) *ᵥ κ M h e) = S M h N from rfl,
        h1, h0, Matrix.mulVec_sub]
      simp only [κ]
      abel

theorem mulVec_nonneg {A : Matrix ι ι ℤ} (hA : ∀ i j, 0 ≤ A i j) {v : ι → ℤ} (hv : ∀ i, 0 ≤ v i)
    (i : ι) : 0 ≤ (A *ᵥ v) i :=
  Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hv j)

/-- **The `U` bound.** -/
theorem le_of_U (h : ℕ → ι → ℤ) (j : ι) (N : ℕ)
    (hU : ∀ d ≤ N, ∀ a b, 0 ≤ U M d a b)
    (hκ : ∀ d, 1 ≤ d → d ≤ N → ∀ i, 0 ≤ κ M h d i)
    (h0 : ∀ i, (if i = j then 1 else 0) ≤ h 0 i) (i : ι) : U M N i j ≤ h N i := by
  rw [← S_eq M h N, S, Finset.sum_range_succ', Nat.sub_zero]
  have hrest : 0 ≤ (∑ e ∈ Finset.range N, U M (N - (e + 1)) *ᵥ κ M h (e + 1)) i := by
    rw [Finset.sum_apply]
    refine Finset.sum_nonneg fun e he ↦ ?_
    rw [Finset.mem_range] at he
    exact mulVec_nonneg (hU _ (by omega)) (hκ (e + 1) (by omega) (by omega)) i
  have hmain : U M N i j ≤ (U M N *ᵥ κ M h 0) i := by
    have : (U M N *ᵥ κ M h 0) i - U M N i j = (U M N *ᵥ (fun a ↦ h 0 a - if a = j then 1 else 0)) i := by
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, κ]
    have h2 := mulVec_nonneg (hU N le_rfl) (fun a ↦ sub_nonneg.2 (h0 a)) i
    linarith
  rw [Pi.add_apply]
  linarith

end UBound

end MultiplicativeBasisDeformations
