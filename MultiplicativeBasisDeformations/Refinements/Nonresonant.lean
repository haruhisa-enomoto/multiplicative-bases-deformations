import Mathlib

/-!
# Lemma 12.7: nonresonant polynomials

`deformation-refinements.tex` (`lem:nonresonant-polynomials`): grade `k[t_1, …, t_s]` by
`deg t_i = χ_i` in an abelian group `L`. If the `χ_i` are pairwise distinct and no `χ_j` is a
sum `∑ n_i χ_i` with `n_i ≥ 0` and `∑ n_i ≥ 2`, then a homogeneous polynomial of weight `χ_j`
with zero constant term is `a_j t_j`.

The remark after the lemma ("characters forming part of an integer basis of a lattice satisfy
these hypotheses") is `nonresonant_of_basis`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

open MvPolynomial

variable {k : Type*} [CommRing k] {L : Type*} [AddCommGroup L] {σ : Type*}

/-- The nonresonance hypotheses of Lemma 12.7. -/
def Nonresonant (χ : σ → L) : Prop :=
  Function.Injective χ ∧ ∀ (j : σ) (n : σ →₀ ℕ), 2 ≤ n.degree → Finsupp.weight χ n ≠ χ j

/-- **Lemma 12.7.** -/
theorem eq_C_mul_X_of_nonresonant {χ : σ → L} (hχ : Nonresonant χ) (j : σ) {F : MvPolynomial σ k}
    (hF : F.IsWeightedHomogeneous χ (χ j)) (h0 : constantCoeff F = 0) :
    ∃ a : k, F = C a * X j := by
  classical
  refine ⟨coeff (Finsupp.single j 1) F, ?_⟩
  ext d
  rw [coeff_C_mul, coeff_X']
  split_ifs with hd
  · rw [← hd, mul_one]
  · rw [mul_zero]
    by_contra hne
    have hw := hF hne
    by_cases hd0 : d = 0
    · rw [hd0, ← constantCoeff_eq, h0] at hne
      exact hne rfl
    rcases Nat.lt_or_ge (d.degree) 2 with hlt | hge
    · -- degree one: `d` is a single variable
      have hdeg : d.degree = 1 := by
        have : d.degree ≠ 0 := fun h ↦ hd0 ((Finsupp.degree_eq_zero_iff d).1 h)
        omega
      obtain ⟨i, rfl⟩ : ∃ i, d = Finsupp.single i 1 := by
        obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hd0 (Finsupp.ext h)
        refine ⟨i, ?_⟩
        have hsum : d.degree = ∑ x ∈ d.support, d x := rfl
        have hle : d i ≤ 1 := by
          rw [← hdeg, hsum]
          exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.2 hi)
        have hi1 : d i = 1 := by omega
        ext x
        by_cases hx : x = i
        · rw [hx, Finsupp.single_eq_same, hi1]
        · rw [Finsupp.single_apply, if_neg (Ne.symm hx)]
          by_contra hx0
          have : d i + d x ≤ d.degree := by
            rw [hsum, ← Finset.sum_pair (Ne.symm hx)]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro y hy
                rw [Finset.mem_insert, Finset.mem_singleton] at hy
                rcases hy with rfl | rfl
                · exact Finsupp.mem_support_iff.2 hi
                · exact Finsupp.mem_support_iff.2 hx0)
              (fun _ _ _ ↦ Nat.zero_le _)
          omega
      rw [Finsupp.weight_single, one_smul] at hw
      exact hd (by rw [hχ.1 hw])
    · exact hχ.2 j d hge hw

/-- Characters forming part of an integer basis are nonresonant. -/
theorem nonresonant_of_basis {ι : Type*} (B : Module.Basis ι ℤ L) {e : σ → ι}
    (he : Function.Injective e) : Nonresonant (fun i ↦ B (e i)) := by
  classical
  refine ⟨fun i i' h ↦ he (B.injective h), fun j n hn hw ↦ ?_⟩
  -- compare coordinates
  have hcoord : ∀ i, B.repr (Finsupp.weight (fun i ↦ B (e i)) n) (e i) = (n i : ℤ) := by
    intro i
    rw [Finsupp.weight_apply, map_finsuppSum, Finsupp.sum, Finset.sum_apply']
    rw [Finset.sum_eq_single i]
    · rw [map_nsmul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        nsmul_eq_mul, mul_one]
    · intro b _ hb
      rw [map_nsmul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, if_neg (fun h ↦ hb (he h)), smul_zero]
    · intro hi
      rw [Finsupp.notMem_support_iff.1 hi, zero_smul, map_zero, Finsupp.zero_apply]
  have hcoef : ∀ i, n i = if i = j then 1 else 0 := by
    intro i
    have h := hcoord i
    rw [hw, Module.Basis.repr_self, Finsupp.single_apply] at h
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at h
      rw [if_pos rfl]
      exact_mod_cast h.symm
    · rw [if_neg (fun h ↦ hij (he h).symm)] at h
      rw [if_neg hij]
      exact_mod_cast h.symm
  have hnj : n = Finsupp.single j 1 := by
    ext i
    rw [hcoef i, Finsupp.single_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  rw [hnj, Finsupp.degree_single] at hn
  omega

end MultiplicativeBasisDeformations
