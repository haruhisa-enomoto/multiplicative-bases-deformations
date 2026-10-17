import MultiplicativeBasisDeformations.Foundations.SupportedBockstein

/-!
# Lemma 10.4 for free `ℤ/p²`-modules

`lem:supported-bockstein` (`integral-deformations.tex`) as stated: `C^*` a complex of free
`ℤ/p²`-modules and `U ⊆ C²` spanned by a subset of a fixed basis. The consequences of freeness
used by `supported_bockstein` hold: the annihilator of `p` is `pM` (`ann_p_free`), and
`U ∩ pC² = pU` (`smul_mem_span_image`). So the lemma holds as stated
(`supported_bockstein_free`).
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

variable (p : ℕ) [hp : Fact p.Prime]

/-- Division by `p` on representatives. -/
def divP (x : ZMod (p ^ 2)) : ZMod (p ^ 2) := ((x.val / p : ℕ) : ZMod (p ^ 2))

theorem divP_zero : divP p 0 = 0 := by simp [divP]

/-- In `ℤ/p²`, an element killed by `p` is `p` times its quotient by `p`. -/
theorem eq_p_mul_divP (x : ZMod (p ^ 2)) (hx : (p : ZMod (p ^ 2)) * x = 0) :
    x = (p : ZMod (p ^ 2)) * divP p x := by
  have hp0 : 0 < p := hp.out.pos
  have hval : p ^ 2 ∣ p * x.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hx
  have hdvd : p ∣ x.val := by
    have h2 : p * p ∣ p * x.val := by rwa [← pow_two]
    exact Nat.dvd_of_mul_dvd_mul_left hp0 h2
  rw [divP]
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.mul_div_cancel' hdvd]
  push_cast
  ring

variable {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ 2)) M]

/-- **In a free `ℤ/p²`-module the annihilator of `p` is `pM`.** -/
theorem ann_p_free [Module.Free (ZMod (p ^ 2)) M] (m : M) (hm : (p : ZMod (p ^ 2)) • m = 0) :
    ∃ m', m = (p : ZMod (p ^ 2)) • m' := by
  let b := Module.Free.chooseBasis (ZMod (p ^ 2)) M
  refine ⟨b.repr.symm ((b.repr m).mapRange (divP p) (divP_zero p)), b.repr.injective ?_⟩
  ext i
  have hc : (p : ZMod (p ^ 2)) * b.repr m i = 0 := by
    have := congrArg (fun x ↦ b.repr x i) hm
    simpa using this
  simp only [map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul]
  exact eq_p_mul_divP p _ hc

/-- **`U ∩ pM = pU` for `U` spanned by part of a basis.** -/
theorem smul_mem_span_image {ι : Type*} (b : Module.Basis ι (ZMod (p ^ 2)) M) (S : Set ι)
    (m : M) (hm : (p : ZMod (p ^ 2)) • m ∈ Submodule.span (ZMod (p ^ 2)) (b '' S)) :
    ∃ u ∈ Submodule.span (ZMod (p ^ 2)) (b '' S),
      (p : ZMod (p ^ 2)) • m = (p : ZMod (p ^ 2)) • u := by
  classical
  rw [Module.Basis.mem_span_image] at hm
  refine ⟨b.repr.symm ((b.repr m).filter (· ∈ S)), ?_, b.repr.injective ?_⟩
  · rw [Module.Basis.mem_span_image, LinearEquiv.apply_symm_apply]
    intro i hi
    exact (Finsupp.mem_support_iff.1 hi |> fun h ↦ by
      by_contra hS
      exact h (Finsupp.filter_apply_neg _ _ hS))
  · ext i
    simp only [map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hi : i ∈ S
    · rw [Finsupp.filter_apply_pos _ _ hi]
    · rw [Finsupp.filter_apply_neg _ _ hi, mul_zero]
      by_contra h
      apply hi
      apply hm
      rw [Finset.mem_coe, Finsupp.mem_support_iff, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact h

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module (ZMod (p ^ 2)) M₁]
  [AddCommGroup M₂] [Module (ZMod (p ^ 2)) M₂] [AddCommGroup M₃] [Module (ZMod (p ^ 2)) M₃]
  [Module.Free (ZMod (p ^ 2)) M₂] [Module.Free (ZMod (p ^ 2)) M₃]

/-- **Lemma 10.4** (`lem:supported-bockstein`) as stated: for a complex `M₁ → M₂ → M₃` of free
`ℤ/p²`-modules (the terms `C¹ → C² → C³`) and `U` spanned by a subset `S` of a basis of `C²`,
if (1) multiplication by `p` kills the classes of `H²(C̄)` in `H²(C)`, and (2) every cocycle of
`C̄¹` lifts to `δ` with `dδ ∈ U`, then every class of `H²(C̄)` (a `z` with `dz ∈ pC³`) has a
representative `u ∈ U` (with `du ∈ pC³` and `z − u ∈ dC¹ + pC²`). -/
theorem supported_bockstein_free (d₁ : M₁ →ₗ[ZMod (p ^ 2)] M₂) (d₂ : M₂ →ₗ[ZMod (p ^ 2)] M₃)
    (hdd : ∀ m, d₂ (d₁ m) = 0) {ι : Type*} (b : Module.Basis ι (ZMod (p ^ 2)) M₂) (S : Set ι)
    (h1 : ∀ z : M₂, (∃ w, d₂ z = (p : ZMod (p ^ 2)) • w) → ∃ δ, (p : ZMod (p ^ 2)) • z = d₁ δ)
    (h2 : ∀ δ : M₁, (∃ m, d₁ δ = (p : ZMod (p ^ 2)) • m) →
      ∃ ε, d₁ (δ + (p : ZMod (p ^ 2)) • ε) ∈ Submodule.span (ZMod (p ^ 2)) (b '' S))
    (z : M₂) (hz : ∃ w, d₂ z = (p : ZMod (p ^ 2)) • w) :
    ∃ u ∈ Submodule.span (ZMod (p ^ 2)) (b '' S), (∃ w, d₂ u = (p : ZMod (p ^ 2)) • w) ∧
      ∃ δ m, z - u = d₁ δ + (p : ZMod (p ^ 2)) • m :=
  supported_bockstein (p : ZMod (p ^ 2)) d₁ d₂ hdd _ (ann_p_free p) (ann_p_free p)
    (smul_mem_span_image p b S) h1 h2 z hz

end MultiplicativeBasisDeformations
