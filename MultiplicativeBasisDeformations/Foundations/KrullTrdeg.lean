module

public import Mathlib

/-!
# Krull dimension bounds for finitely generated algebras (for Lemma 8.8)

`local-ray-geometry.tex` (`lem:dimension-infinity`): "Every component of such a zero
set has dimension at least `N − F`. The change-of-basis group has dimension `D`, and its
simultaneous scalar subgroup stabilizes every representation. An orbit has dimension equal
to that of the group minus that of the stabilizer, so each orbit has dimension at most
`D − 1`."

The dimension theory used:
* `ringKrullDim_le_of_isIntegral`: integral extensions do not raise the Krull dimension
  (incomparability);
* `ringKrullDim_le_of_noether`: by Noether normalization, the Krull dimension of a finitely
  generated algebra is bounded by the number of variables of any injective polynomial
  subalgebra bound;
* `card_le_of_inj_localization`: a polynomial algebra embedding in a localization of a
  polynomial ring in `n` variables has at most `n` variables (transcendence degree);
* `height_ge_of_chain`: a chain of primes bounds the height from below.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

/-- **Incomparability**: an integral extension does not raise the Krull dimension. -/
theorem ringKrullDim_le_of_isIntegral (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] : ringKrullDim A ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum A ↦ (⟨p.asIdeal.comap (algebraMap R A), inferInstance⟩ : PrimeSpectrum R))
    fun p q hpq ↦ ?_
  exact Ideal.IsIntegral.comap_lt_comap (R := R) hpq

variable (k : Type*) [Field k]

/-- **Noether normalization bound.** -/
theorem ringKrullDim_le_of_noether (A : Type*) [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A]
    (n : ℕ) (h : ∀ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A), Function.Injective g → s ≤ n) :
    ringKrullDim A ≤ n := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x ↦ hint x⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin s) k) := ringKrullDim_le_of_isIntegral _ _
    _ = s := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    _ ≤ n := by exact_mod_cast h s g hg

/-- **Transcendence degree bound**: a polynomial algebra in `s` variables embeds in a
localization of a polynomial ring in the variables `σ` only if `s ≤ |σ|`. -/
theorem card_le_of_inj_localization {σ : Type} [Fintype σ] (δ : MvPolynomial σ k) (hδ : δ ≠ 0)
    {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] Localization.Away δ) (hg : Function.Injective g) :
    s ≤ Fintype.card σ := by
  have hind : AlgebraicIndependent k (fun i : Fin s ↦ g (MvPolynomial.X i)) := by
    have : MvPolynomial.aeval (fun i : Fin s ↦ g (MvPolynomial.X i)) = g :=
      MvPolynomial.algHom_ext fun i ↦ by simp
    rw [AlgebraicIndependent, this]; exact hg
  have h1 := hind.lift_cardinalMk_le_trdeg
  haveI : IsDomain (Localization.Away δ) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers δ)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hδ)
  haveI : FaithfulSMul (MvPolynomial σ k) (Localization.Away δ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hδ))
  haveI : Algebra.IsAlgebraic (MvPolynomial σ k) (Localization.Away δ) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers δ)
  have h2 := trdeg_add_eq (R := k) (S := MvPolynomial σ k) (A := Localization.Away δ)
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial σ k) (A := Localization.Away δ), add_zero] at h2
  rw [← h2] at h1
  simp only [Cardinal.lift_natCast, Cardinal.mk_fintype] at h1
  have := (Nat.cast_le (α := Cardinal)).1 h1
  simpa using this

/-- **Heights from chains of primes.** -/
theorem height_ge_of_chain {R : Type*} [CommRing R] (n : ℕ) (P : Fin (n + 1) → Ideal R)
    (hP : ∀ i, (P i).IsPrime) (hlt : ∀ i : Fin n, P i.castSucc < P i.succ) :
    (n : ℕ∞) ≤ (P (Fin.last n)).height := by
  have key : ∀ j : ℕ, (hj : j ≤ n) → (j : ℕ∞) ≤ (P ⟨j, by omega⟩).height := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have := hP ⟨j, by omega⟩
      have := hP ⟨j + 1, by omega⟩
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (hlt ⟨j, by omega⟩)
      have h2 := ih (by omega)
      calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; ring
        _ ≤ (P ⟨j, by omega⟩).height + 1 := by gcongr
        _ ≤ _ := h1
  exact key n le_rfl

end MultiplicativeBasisDeformations
