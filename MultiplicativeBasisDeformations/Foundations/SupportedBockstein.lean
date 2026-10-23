module

public import Mathlib

/-!
# Lemma 11.4: a coefficient criterion for supported representatives

`integral-deformations.tex` (`lem:supported-bockstein`): "Let `p` be a prime, let
`C^*` be a complex of free `ℤ/p²`-modules, and put `C̄^* = C^*/pC^*`. Let `U ⊆ C²` be
spanned by a subset of a fixed basis. Assume: (1) the coefficient-inclusion map
`H²(C̄^*) → H²(C^*)`, induced by multiplication by `p`, is zero; (2) every
`δ̄ ∈ Z¹(C̄^*)` has a lift `δ ∈ C¹` with `dδ ∈ U`. Then every class in `H²(C̄^*)` has a
cocycle representative in the image of `U/pU`."

Formalized on three terms `M₁ → M₂ → M₃` of a complex over a commutative ring, with the
consequences of freeness used in the proof: the annihilator of `p` is `pM` on `M₂` and
`M₃`, and `U ∩ pM₂ = pU`. A class of `C̄` is represented by `z ∈ M₂` with `dz ∈ pM₃`; its
representative is `u ∈ U` with `du ∈ pM₃` and `z − u ∈ d(M₁) + pM₂`.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

variable {R : Type*} [CommRing R] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]

/-- **Lemma 11.4** (`lem:supported-bockstein`). -/
theorem supported_bockstein (p : R) (d₁ : M₁ →ₗ[R] M₂) (d₂ : M₂ →ₗ[R] M₃)
    (hdd : ∀ m, d₂ (d₁ m) = 0) (U : Submodule R M₂)
    (hann₂ : ∀ m : M₂, p • m = 0 → ∃ m', m = p • m')
    (hann₃ : ∀ m : M₃, p • m = 0 → ∃ m', m = p • m')
    (hU : ∀ m : M₂, p • m ∈ U → ∃ u ∈ U, p • m = p • u)
    -- (1): the coefficient inclusion is zero on second cohomology
    (h1 : ∀ z : M₂, (∃ w, d₂ z = p • w) → ∃ δ, p • z = d₁ δ)
    -- (2): cocycles modulo `p` lift with coboundary in `U`
    (h2 : ∀ δ : M₁, (∃ m, d₁ δ = p • m) → ∃ ε, d₁ (δ + p • ε) ∈ U)
    (z : M₂) (hz : ∃ w, d₂ z = p • w) :
    ∃ u ∈ U, (∃ w, d₂ u = p • w) ∧ ∃ δ m, z - u = d₁ δ + p • m := by
  obtain ⟨δ, hδ⟩ := h1 z hz
  obtain ⟨ε, hε⟩ := h2 δ ⟨z, hδ.symm⟩
  have hd : d₁ (δ + p • ε) = p • (z + d₁ ε) := by
    rw [map_add, map_smul, ← hδ, smul_add]
  obtain ⟨u, hu, hpu⟩ := hU (z + d₁ ε) (hd ▸ hε)
  -- `p (z + dε − u) = 0`
  have h3 : p • (z + d₁ ε - u) = 0 := by rw [smul_sub, hpu, sub_self]
  obtain ⟨m, hm⟩ := hann₂ _ h3
  refine ⟨u, hu, ?_, -ε, m, ?_⟩
  · -- `p du = d(pu) = d(d(δ + pε)) = 0`
    have h4 : p • d₂ u = 0 := by
      rw [← map_smul, ← hpu, ← hd, hdd]
    exact hann₃ _ h4
  · rw [map_neg, ← hm]; abel

end MultiplicativeBasisDeformations
