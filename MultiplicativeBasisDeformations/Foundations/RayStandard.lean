module

public import MultiplicativeBasisDeformations.Foundations.StandardForm
public import MultiplicativeBasisDeformations.Foundations.A0Rays
public import MultiplicativeBasisDeformations.Foundations.RayTransport

/-!
# The ray basis of a standard basic algebra

Corollary 5.5 (`mesh-deformations.tex`): "Construction 2.8 and
Proposition 4.14 give `A ≅ A₀ ≅ kP`, where `P = ray A₀`. This isomorphism
preserves endpoint actions and the subspaces `M(f,h)` of Definition 3.4, and
therefore identifies `ray A` with `P`. The ray basis is multiplicative, contains
the primitive idempotents, and intersects every radical power in a basis by
Corollary 3.3."

Here: the ray basis of `A₀` (`exists_hasRayBasis_A0`) is transported along
`A ≅ A₀` (`hasRayBasis_of_algEquiv`) to the pulled-back vertex idempotents, and
then, by conjugacy of complete sets of primitive idempotents in a basic algebra,
to any given complete set `F`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- The idempotents pulled back along an algebra isomorphism. -/
def comap {B : Type u} [Ring B] [Algebra k B] (φ : A ≃ₐ[k] B) (F : PrimitiveIdempotents B) :
    PrimitiveIdempotents A where
  m := F.m
  e i := φ.symm (F.e i)
  complete := F.complete.map (φ.symm : B →+* A)
  primitive i := isPrimitiveIdempotent_map φ.symm (F.primitive i)

/-- A trivial algebra has a ray basis (there are no nonzero rays). -/
theorem hasRayBasis_of_subsingleton [Subsingleton A] (F : PrimitiveIdempotents A) :
    F.HasRayBasis k := by
  haveI : IsEmpty (F.NonzeroRay k) := ⟨fun r ↦ by
    obtain ⟨_, _, f, -, hf0, -⟩ := r.2
    exact hf0 (Subsingleton.elim _ _)⟩
  refine ⟨Module.Basis.empty A, ⟨fun i ↦ isEmptyElim i, ⟨∅, ?_, fun i hi ↦ by simp at hi⟩,
    fun n _ ↦ Subsingleton.elim _ _⟩, ⟨fun r ↦ isEmptyElim r, fun r ↦ isEmptyElim r⟩,
    fun r ↦ isEmptyElim r⟩
  refine ⟨⟨fun i ↦ absurd i.2 (Finset.notMem_empty _), fun i ↦ absurd i.2 (Finset.notMem_empty _)⟩,
    Subsingleton.elim _ _⟩

end PrimitiveIdempotents

namespace IndSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- **A standard basic algebra has a ray basis for every complete set of
primitive orthogonal idempotents** (Corollary 5.5). -/
theorem hasRayBasis_of_isStandard (hbasic : IsBasicAlgebra A) (hstd : S.IsStandard)
    (F : PrimitiveIdempotents A) : F.HasRayBasis k := by
  classical
  obtain ⟨n, e, he, hprim, hb⟩ := hbasic
  by_cases hn : n = 0
  · subst hn
    haveI : Subsingleton A := by
      have h := he.complete
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact subsingleton_of_zero_eq_one h
    exact F.hasRayBasis_of_subsingleton
  obtain ⟨b, Φ0, hEq, hlin, hβ⟩ := hstd
  haveI := hEq
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  let φ := S.algEquivA0 b he hprim hb Φ0 hlin fun x ↦ (hβ x).some
  let v₀ : S.ARVertex := ((S.pvEquiv b he hprim hb).symm ⟨0, Nat.pos_of_ne_zero hn⟩).1
  obtain ⟨Fp, hFp⟩ := MeshWalk.exists_hasRayBasis_A0 (D := S.arMeshData b) v₀
    (CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b))
  let Fφ := Fp.comap φ
  have h1 : Fφ.HasRayBasis k :=
    Fφ.hasRayBasis_of_algEquiv φ Fp (Equiv.refl _) (fun i ↦ φ.apply_symm_apply _) hFp
  obtain ⟨ψ, σ, hψ⟩ := exists_algEquiv_idempotents (k := k) ⟨n, e, he, hprim, hb⟩ F Fφ
  exact F.hasRayBasis_of_algEquiv ψ Fφ σ hψ h1

end IndSkeleton

end MultiplicativeBasisDeformations
