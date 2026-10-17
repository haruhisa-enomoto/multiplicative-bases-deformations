import MultiplicativeBasisDeformations.Refinements.MeshFirstOrder
import MultiplicativeBasisDeformations.Foundations.Char2Basic

/-!
# Proposition 12.5 for the algebra `A₀` of a representation-finite algebra

`deformation-refinements.tex:254–289` (`prop:full-hochschild-comparison`). For the mesh
category `C = k(Γ_A)` of a basic representation-finite algebra `A`, the mesh presentations are
resolutions (they come from the almost split sequences; the paragraph after Lemma 12.3), so
`Ψ : HH²(A₀)_q → coker D_{q+1}` is an isomorphism in every internal degree `q ≥ 1`
(`MeshWalk.fullHochschildComparison`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.IndSkeleton

open FlatPert

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **The mesh presentations of `k(Γ_A)` are resolutions**: the representables applied to the
almost split sequences (`deformation-refinements.tex:213–226`). -/
theorem hres_ar (w x : S.ARVertex) :
    Function.Injective (relMap (meshPres (S.arCoefficients b))
      (idealC (meshPres (S.arCoefficients b))) (meshPres (S.arCoefficients b)).r w x) ∧
    LinearMap.ker (alpha (idealC (meshPres (S.arCoefficients b))) w x) ≤
      LinearMap.range (relMap (meshPres (S.arCoefficients b))
        (idealC (meshPres (S.arCoefficients b))) (meshPres (S.arCoefficients b)).r w x) :=
  MeshFirstOrder.hres_of_exact (S.arCoefficients b)
    (fun x w z hz ↦ S.ar_cov_mono b x.1 x.2 w z hz)
    (fun x w g hg ↦ S.ar_cov_exact b x.1 x.2 w g hg)
    (fun x hx w g hg a ↦ S.ar_proj_mono b x hx w g hg a) w x

/-- **Proposition 12.5** for `A₀ = k(Γ_A)`-projective corner: `Ψ` is an isomorphism in every
internal degree `q ≥ 1`. -/
theorem fullHochschildComparison_ar {q : ℕ} (hq : 1 ≤ q) :
    haveI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    (∀ (z : ScalarMeshCategory.MeshFamily (S.arCoefficients b)),
      (∀ x, z x ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) (q + 2)
        (S.arTranslationQuiver.tau x).1 x.1) →
      ∃ (μ : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
          (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) (_ : GExt.IsHCocycle μ)
        (_ : GExt.HDeg (MeshWalk.galgA0 (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y))
          μ (q : ℤ))
        (Ld : MeshWalk.LiftData (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y) q μ),
        MeshWalk.Ψc Ld = Submodule.Quotient.mk z) ∧
    ∀ (μ : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
        (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) (_ : GExt.IsHCocycle μ)
      (_ : GExt.HDeg (MeshWalk.galgA0 (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y))
        μ (q : ℤ))
      (Ld : MeshWalk.LiftData (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y) q μ),
      MeshWalk.Ψc Ld = 0 →
      ∃ H : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ,
        (∀ p a, (MeshWalk.galgA0 (S.arMeshData b)
            (fun x y ↦ S.finiteDimensional_meshHom b x y)).gr.IsHom p a →
          (MeshWalk.galgA0 (S.arMeshData b)
            (fun x y ↦ S.finiteDimensional_meshHom b x y)).gr.IsHom (p + q) (H a)) ∧
        μ = GExt.hcobdry H :=
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  MeshWalk.fullHochschildComparison (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y)
    (S.arInjData b) (S.arDegOne b) (S.hres_ar b) hq

end MultiplicativeBasisDeformations.IndSkeleton
