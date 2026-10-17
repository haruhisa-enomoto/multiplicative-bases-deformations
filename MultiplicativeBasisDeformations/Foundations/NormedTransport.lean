import MultiplicativeBasisDeformations.Foundations.NormedBasis

/-!
# Normed multiplicative bases along algebra isomorphisms

Corollary 5.5(2) (`mesh-deformations.tex:249–251`): "The ray basis transports to
a normed multiplicative basis of `A`." An algebra isomorphism preserves
products, idempotents, primitivity and the radical powers, so it transports
normed multiplicative bases (`HasNormedMultiplicativeBasis.of_algEquiv`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A B : Type v} [Ring A] [Ring B] [Algebra k A] [Algebra k B]

theorem jacobson_map_mem (φ : A ≃+* B) {x : A} (hx : x ∈ Ring.jacobson A) :
    φ x ∈ Ring.jacobson B := by
  rw [← Ideal.jacobson_bot] at hx ⊢
  have h := Ideal.map_jacobson_of_bijective (f := (φ : A →+* B)) φ.bijective (I := ⊥)
  rw [Ideal.map_bot] at h
  rw [← h]
  exact Ideal.mem_map_of_mem _ hx

theorem map_algebraRadical (φ : A ≃ₐ[k] B) :
    (algebraRadical k A).map φ.toLinearMap = algebraRadical k B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact jacobson_map_mem φ.toRingEquiv hx
  · intro hy
    refine ⟨φ.symm y, jacobson_map_mem φ.symm.toRingEquiv hy, ?_⟩
    exact φ.apply_symm_apply y

theorem map_algebraRadicalPow (φ : A ≃ₐ[k] B) (n : ℕ) :
    (algebraRadicalPow k A n).map φ.toLinearMap = algebraRadicalPow k B n := by
  rw [algebraRadicalPow, algebraRadicalPow, ← map_algebraRadical φ]
  exact Submodule.map_pow _ (φ : A →ₐ[k] B) n

theorem isPrimitiveIdempotent_map (φ : A ≃ₐ[k] B) {x : A} (hx : IsPrimitiveIdempotent x) :
    IsPrimitiveIdempotent (φ x) := by
  refine ⟨hx.1.map φ, fun h ↦ hx.2.1 (φ.injective (by rw [h, map_zero])), fun f hf h1 h2 ↦ ?_⟩
  have hf' : IsIdempotentElem (φ.symm f) := hf.map φ.symm
  have h1' : x * φ.symm f = φ.symm f := by
    apply φ.injective; rw [map_mul, φ.apply_symm_apply, h1]
  have h2' : φ.symm f * x = φ.symm f := by
    apply φ.injective; rw [map_mul, φ.apply_symm_apply, h2]
  rcases hx.2.2 _ hf' h1' h2' with h | h
  · left; rw [← φ.apply_symm_apply f, h, map_zero]
  · right; rw [← φ.apply_symm_apply f, h]

/-- **Transport of normed multiplicative bases.** -/
theorem HasNormedMultiplicativeBasis.of_algEquiv (φ : A ≃ₐ[k] B)
    (h : HasNormedMultiplicativeBasis k B) : HasNormedMultiplicativeBasis k A := by
  obtain ⟨ι, b, hb⟩ := h
  let b' : Module.Basis ι k A := b.map φ.symm.toLinearEquiv
  have hb' : ∀ i, b' i = φ.symm (b i) := fun i ↦ rfl
  refine ⟨ι, b', ⟨fun i j ↦ ?_, ?_, fun n hn ↦ ?_⟩⟩
  · rw [hb', hb', ← map_mul]
    rcases hb.multiplicative i j with h0 | ⟨l, hl⟩
    · left; rw [h0, map_zero]
    · right; exact ⟨l, by rw [hl, hb']⟩
  · obtain ⟨E, hE, hprim⟩ := hb.idempotents
    refine ⟨E, ?_, fun i hi ↦ ?_⟩
    · have := hE.map (φ.symm : B →+* A)
      exact this
    · rw [hb']
      exact isPrimitiveIdempotent_map φ.symm (hprim i hi)
  · have h := hb.radicalPow n hn
    have hmap := congrArg (Submodule.map φ.symm.toLinearMap) h
    rw [Submodule.map_span, map_algebraRadicalPow φ.symm n] at hmap
    refine Eq.trans ?_ hmap
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨b i, ⟨i, ?_, rfl⟩, rfl⟩
      have := Submodule.mem_map_of_mem (f := φ.toLinearMap) hi
      rw [map_algebraRadicalPow φ n] at this
      change φ (φ.symm (b i)) ∈ _ at this
      rwa [φ.apply_symm_apply] at this
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨i, ?_, rfl⟩
      rw [← map_algebraRadicalPow φ.symm n]
      exact Submodule.mem_map_of_mem hi

end MultiplicativeBasisDeformations
