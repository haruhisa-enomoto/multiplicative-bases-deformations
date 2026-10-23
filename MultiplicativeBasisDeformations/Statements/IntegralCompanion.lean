module

public import MultiplicativeBasisDeformations.Foundations.IntegralPresentation
public import MultiplicativeBasisDeformations.Foundations.PrimeWeight

/-!
# Proposition 10.1 for a basic representation-finite algebra

`prop:fixed-integral-companion` (`integral-deformations.tex`), for `A` basic and
representation-finite over an algebraically closed field of characteristic two, `C⁽²⁾` the
all-one mesh category of `Γ_A` over `𝔽₂`, `A⁽²⁾` its projective corner and `A⁽⁴⁾ = 𝒪P`
(`tab₂`): the statement `Prop101Stmt` (module and arrow lifts; (1) free Hom modules in every
degree with `E₄/2E₄ = C⁽²⁾`; (2) regular lifts at projective labels; (3) the quadratic mesh
presentation of `E₄` with unit coefficients reducing to one) holds (`fixedIntegralCompanion`).
The weight refinement is `exists_modLiftW₂`, `exists_arrowLiftW₂` (`PrimeWeight.lean`).
The instance arguments are those of the Auslander–Reiten quiver (`S.hasAtMostOneArrow`,
`S.finiteDimensional_meshHom`, `S.prime_fd`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace IndSkeleton

universe w

open ScalarMeshCategory CatAlg MeshWalk WLift GExt

attribute [local instance] Classical.decEq

variable {k A : Type w} [Field k] [IsAlgClosed k] [CharP k 2] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)
  [∀ x y : S.ARVertex, Subsingleton (x ⟶ y)]
  [∀ x y : S.ARVertex, FiniteDimensional k (MeshWalk.meshFam S.arTranslationQuiver
    (S.arCoefficients b) x ⟶ MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y)]
  [∀ x y : S.ARVertex, FiniteDimensional (ZMod 2) (MeshWalk.meshFam S.arTranslationQuiver
    (S.oneC (ZMod 2)) x ⟶ MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) y)]
  (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (Alg (S.arMeshData b).F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt S.arTranslationQuiver ℤ)

/-- **Proposition 10.1** (`prop:fixed-integral-companion`) for a basic representation-finite
algebra in characteristic two. -/
theorem fixedIntegralCompanion : Prop101Stmt (S.tab₂ b v₀ hF Wd) :=
  prop101 _ (S.primeInjData b) (S.primeDegOne b)

end IndSkeleton

end MultiplicativeBasisDeformations
