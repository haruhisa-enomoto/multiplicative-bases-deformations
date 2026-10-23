module

public import MultiplicativeBasisDeformations.Foundations.RayTransport
public import MultiplicativeBasisDeformations.Foundations.RayStandard
public import MultiplicativeBasisDeformations.Foundations.Prop103

/-!
# Theorem 11.7(1)(2) in characteristic two

`main-theorems.tex` (`thm:final-basis`). For a basic representation-finite algebra in
characteristic two, Proposition 8.3 (`exists_normedRayBasis_basic_char2`), with Corollary 10.5
now proved (`cor105Hyp`), gives a normed multiplicative ray transversal for one complete set of
primitive idempotents; conjugation (`exists_algEquiv_idempotents`) moves it to any other
(`exists_rayTransversal_of_algEquiv`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Type u} [Ring A] [Ring B] [Algebra k A]
  [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
  (ψ : A ≃ₐ[k] B) (F : PrimitiveIdempotents A) (F' : PrimitiveIdempotents B)
  (σ : Fin F.m ≃ Fin F'.m) (hψ : ∀ i, ψ (F.e i) = F'.e (σ i))

include hψ in
/-- **Normed ray transversals transport along an algebra isomorphism matching the
idempotents.** -/
theorem exists_rayTransversal_of_algEquiv (b' : Module.Basis (F'.NonzeroRay k) k B)
    (hn : IsNormedMultiplicativeBasis b') (htr : F'.IsRayTransversal b') :
    ∃ b : Module.Basis (F.NonzeroRay k) k A,
      IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b := by
  obtain ⟨hmem, hid⟩ := htr
  set R := F.rayEquiv ψ F' σ hψ
  let b : Module.Basis (F.NonzeroRay k) k A := (b'.map ψ.symm.toLinearEquiv).reindex R.symm
  have hb : ∀ r, b r = ψ.symm (b' (R r)) := fun r ↦ by
    simp only [b, Module.Basis.reindex_apply, Equiv.symm_symm]; rfl
  refine ⟨b, (hn.map_algEquiv ψ).reindex R.symm, fun r ↦ ?_, fun r i hi ↦ ?_⟩
  · obtain ⟨g, hg, hgb⟩ := hmem (R r)
    rw [hb, ← hgb, ψ.symm_apply_apply]
    exact hg
  · have : F'.e (σ i) ∈ (R r).1 := ⟨F.e i, hi, hψ i⟩
    rw [hb, hid (R r) (σ i) this, F.symm_e ψ F' σ hψ, σ.symm_apply_apply]

end PrimitiveIdempotents

variable (k : Type u) [Field k] [IsAlgClosed k]
  (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Theorem 11.7(2) in characteristic two**: a normed multiplicative ray transversal for any
complete set of primitive idempotents. -/
theorem finalBasis_ray_char2 [CharP k 2] (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (F : PrimitiveIdempotents A) :
    ∃ b : Module.Basis (F.NonzeroRay k) k A,
      IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · obtain ⟨b, hb, htr, -⟩ := PrimitiveIdempotents.hasRayBasis_of_subsingleton (k := k) F
    exact ⟨b, hb, htr⟩
  obtain ⟨F', b', hn', htr'⟩ := exists_normedRayBasis_basic_char2 (k := k) CharTwo.two_eq_zero
    (cor105Hyp k) A hbasic hA hn
  obtain ⟨ψ, σ, hψ⟩ := exists_algEquiv_idempotents (k := k) hbasic F F'
  exact F.exists_rayTransversal_of_algEquiv ψ F' σ hψ b' hn' htr'

/-- **Theorem A for basic algebras in characteristic two.** -/
theorem basic_hasNormedBasis_char2 [CharP k 2] (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) : HasNormedMultiplicativeBasis k A := by
  obtain ⟨n, e, he, hprim, -⟩ := id hbasic
  obtain ⟨b, hb, -⟩ := finalBasis_ray_char2 k A hbasic hA ⟨n, e, he, hprim⟩
  exact ⟨_, b, hb⟩

end MultiplicativeBasisDeformations
