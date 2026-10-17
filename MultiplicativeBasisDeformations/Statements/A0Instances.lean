import MultiplicativeBasisDeformations.Statements.PartOne
import MultiplicativeBasisDeformations.Foundations.A0RayTable
import MultiplicativeBasisDeformations.Foundations.EvaluationEquivalence
import MultiplicativeBasisDeformations.Foundations.StandardConverse

/-!
# Propositions 3.8 and 4.14 for the algebra `A₀` of Construction 2.8

`prop:projective-ray-product` (`projective-rays.tex`) and `prop:scalar-normalization`
(`scalar-normalization.tex`) are stated for `A₀`, the projective corner of
`C = gr_J ind(mod A) ≅ k(Γ_A)` for a basic representation-finite algebra `A` over an
algebraically closed field. The general theorems (`projectiveRayProduct` for length-graded
algebras with degree-zero local corners; `MeshWalk.scalarNormalization` for scalar mesh categories
with mesh data) are instantiated here for the Auslander–Reiten mesh data of `A`
(`arMeshData`), whose `A₀` is representation-finite (`isRepresentationFinite_A0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

attribute [local instance] Classical.decEq

/-- **Proposition 3.8 for `A₀`** (`prop:projective-ray-product`): for `A₀` of the
Auslander–Reiten mesh category, with its length grading and labelled primitive idempotents,
each nonzero ray contains a unique homogeneous line, products of homogeneous lines detect the
ray products, and the ray table is associative. -/
theorem projectiveRayProduct_A0 (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    let F := MeshWalk.FpA0 (S.arMeshData b) v₀ hF
    let G := MeshWalk.lenA0 (S.arMeshData b) (MeshWalk.hfinObj (c := S.arCoefficients b))
    (∀ (x y : Fin F.m) (f : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ), f ∈ F.corner (k := k) x y →
      f ≠ 0 → ∃ g d, G.IsHom d g ∧ g ≠ 0 ∧ g ∈ F.ray (k := k) x y f ∧
        ∀ g' ∈ F.ray (k := k) x y f, ∀ d', G.IsHom d' g' → g' ∈ k ∙ g) ∧
    (∀ (x y z : Fin F.m) (f h : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) (p q : ℕ), G.IsHom p f →
      G.IsHom q h → (f * h ∈ F.insertionSpan (k := k) x y z f h ↔ f * h = 0)) ∧
    (∀ (x y z w : Fin F.m) (f g h : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ),
      f ∈ F.corner (k := k) x y → f ≠ 0 → g ∈ F.corner (k := k) y z → g ≠ 0 →
      h ∈ F.corner (k := k) z w → h ≠ 0 →
      ((f * g ∉ F.insertionSpan (k := k) x y z f g ∧
          f * g * h ∉ F.insertionSpan (k := k) x z w (f * g) h) ↔
        (g * h ∉ F.insertionSpan (k := k) y z w g h ∧
          f * (g * h) ∉ F.insertionSpan (k := k) x y w f (g * h)))) := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  haveI := MeshWalk.finiteDimensional_A0 (S.arMeshData b) v₀ hF
  exact projectiveRayProduct _ _ (MeshWalk.FpA0_he0 (S.arMeshData b) v₀ hF)
    (MeshWalk.FpA0_hcorner0 (S.arMeshData b) v₀ hF) hF

/-- **Proposition 4.14 for `A₀`** (`prop:scalar-normalization`): `A₀ ≅ kP` for `P = ray A₀`,
preserving the labelled primitive idempotents and the homogeneous ray lines; `A₀` has a normed
multiplicative basis. -/
theorem scalarNormalization_A0 (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    (MeshWalk.FpA0 (S.arMeshData b) v₀ hF).IsRayPres (k := k) (MeshWalk.A0Mult (S.arMeshData b) v₀ hF)
        (MeshWalk.idxA0 (S.arMeshData b) v₀ hF) (MeshWalk.basisR (S.arMeshData b) v₀ hF) ∧
      (∀ t, MeshWalk.thetaA0 (S.arMeshData b) v₀ hF
        ((MeshWalk.A0Tab (S.arMeshData b) v₀ hF).b k t) = MeshWalk.basisR (S.arMeshData b) v₀ hF t) ∧
      HasNormedMultiplicativeBasis k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  have h := MeshWalk.scalarNormalization (S.arMeshData b) v₀
    (CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b))
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

/-- **Proposition 2.10(1) for `A₀`** (`prop:projective-evaluation`(1)): evaluation at the
projective labels is an equivalence `add C ≃ mod A₀` for the Auslander–Reiten mesh category. -/
theorem projectiveEvaluation_equivalence :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    (CatAlg.MeshData.evFunctor (S.arMeshData b)).IsEquivalence := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  exact CatAlg.MeshData.evFunctor_isEquivalence _ (S.arInjData b)

/-- **Corollary 4.15** (`cor:graded-standard-form`) as stated: `kP`, for `P = ray A₀`, is
representation-finite and `add k(Γ_A) ≃ mod kP` (evaluation, then `A₀ ≅ kP`); and `A` is
standard if and only if `A ≅ A₀`. -/
theorem gradedStandardForm_asStated (hbasic : IsBasicAlgebra A) (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    IsRepresentationFinite k ((MeshWalk.A0Tab (S.arMeshData b) v₀ hF).Lin k) ∧
      Nonempty (CatAlg.AddC (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b)) ≌
        (CatAlg.MeshData.FGProp
          ((MeshWalk.A0Tab (S.arMeshData b) v₀ hF).Lin k)ᵐᵒᵖ).FullSubcategory) ∧
      (S.IsStandard ↔ ∃ b' : S.ArrowBases, Nonempty (A ≃ₐ[k] S.A0 b')) := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro hF
  haveI := MeshWalk.finiteDimensional_A0 (S.arMeshData b) v₀ hF
  let θ := MeshWalk.thetaA0 (S.arMeshData b) v₀ hF
  refine ⟨isRepresentationFinite_of_algEquiv θ.symm hF, ⟨CatAlg.MeshData.evEquivOfRingEquiv
    (S.arMeshData b) (S.arInjData b)
    ((RingEquiv.op θ.toRingEquiv).trans (RingEquiv.opOp _).symm)⟩, ⟨fun hstd ↦ ?_, ?_⟩⟩
  · exact (gradedStandardForm S hbasic).2 hstd
  · rintro ⟨b', ⟨ψ⟩⟩
    exact S.isStandard_of_algEquiv b' ψ

end MultiplicativeBasisDeformations.IndSkeleton
