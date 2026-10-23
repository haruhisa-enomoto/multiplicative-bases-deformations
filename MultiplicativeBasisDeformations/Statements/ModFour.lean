module

public import MultiplicativeBasisDeformations.Foundations.ModFourComparison
public import MultiplicativeBasisDeformations.Foundations.PrimeWeight
public import MultiplicativeBasisDeformations.Foundations.PrimeCoker

/-!
# Lemma 10.2 for a basic representation-finite algebra

`lem:mod-four-comparison` (`integral-deformations.tex`), for `A` basic and
representation-finite over an algebraically closed field of characteristic two, `A⁽²⁾` the
projective corner of the prime-field mesh category and `A⁽⁴⁾ = 𝒪P` (`tab₂`): for a normalized
Hochschild two-cocycle `μ̄` of `A⁽²⁾` of internal degree `q > 0`, `2μ̃` is a coboundary in the
normalized Hochschild complex of `A⁽⁴⁾`; and for every mesh weight `W` (values in any abelian
group, e.g. `ℤ^r` for simultaneous integer weights) and every character `χ` of `μ̄`, the
coboundary can be chosen homogeneous of weight `χ` for the restricted ray weights (`hvW`).
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

/-- **Lemma 10.2** (`lem:mod-four-comparison`) for a basic representation-finite algebra in
characteristic two (`ModFourStmt`): for a normalized Hochschild two-cocycle `μ̄` of `A⁽²⁾` of
internal degree `q > 0`, `2μ̃` is a coboundary in the normalized Hochschild complex of `A⁽⁴⁾`. -/
theorem modFourComparison : ModFourStmt (S.tab₂ b v₀ hF Wd) := by
  obtain ⟨RS, hspan, htwo⟩ := S.prime_cokerSpan b
  exact modFourStmt _ (S.primeInjData b) (S.primeDegOne b) hspan htwo

/-- **Lemma 10.2 in every simultaneous weight** (`ModFourWeightStmt`): for any mesh weight `W`
(values in any abelian group) and any character `χ` of `μ̄`, the normalized coboundary can be
chosen homogeneous of weight `χ` for the restricted ray weights `hvW`. -/
theorem modFourComparison_weight {M : Type} [AddCommGroup M] (W : MeshWt S.arTranslationQuiver M) :
    ModFourWeightStmt (S.tab₂ b v₀ hF Wd) W (S.hvW b v₀ W) := by
  obtain ⟨RS, hspan, htwo⟩ := S.prime_cokerSpan b
  exact modFourWeightStmt _ W _ (S.hvW_mul b v₀ hF Wd W) (S.hvW_e b v₀ hF Wd W)
    (S.hΘ₂ b v₀ hF Wd W) (S.primeInjData b) (S.primeDegOne b) hspan htwo

/-- **Proposition 10.3** (`prop:integral-bockstein`) for a basic representation-finite algebra
in characteristic two (`BocksteinStmt`): the connecting map `HH¹(A⁽²⁾)_q → HH²(A⁽²⁾)_q` is
surjective for `q > 0`, with `β(δ̄)` represented by `(dδ)/2` for any lift `δ`. -/
theorem integralBockstein_AR : BocksteinStmt (S.tab₂ b v₀ hF Wd) := by
  obtain ⟨RS, hspan, htwo⟩ := S.prime_cokerSpan b
  exact bockstein _ (S.primeInjData b) (S.primeDegOne b) hspan htwo

/-- **Proposition 10.3 in every simultaneous weight** (`BocksteinWeightStmt`). -/
theorem integralBockstein_AR_weight {M : Type} [AddCommGroup M]
    (W : MeshWt S.arTranslationQuiver M) :
    BocksteinWeightStmt (S.tab₂ b v₀ hF Wd) W (S.hvW b v₀ W) := by
  obtain ⟨RS, hspan, htwo⟩ := S.prime_cokerSpan b
  exact bocksteinWeight _ (S.primeInjData b) (S.primeDegOne b) hspan htwo W _
    (S.hvW_mul b v₀ hF Wd W) (S.hvW_e b v₀ hF Wd W) (S.hΘ₂ b v₀ hF Wd W)

end IndSkeleton

end MultiplicativeBasisDeformations
