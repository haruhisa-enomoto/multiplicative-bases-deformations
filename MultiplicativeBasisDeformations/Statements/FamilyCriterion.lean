import MultiplicativeBasisDeformations.Foundations.Char2Basic
import MultiplicativeBasisDeformations.Foundations.FamilyCriterionA0

/-!
# Proposition 7.9 for a basic representation-finite algebra

`prop:family-criterion` (`characteristic-two-construction.tex`), for `A` basic and
representation-finite over an algebraically closed field, `A₀` the projective corner of its
Auslander–Reiten mesh category, and the rows and dual weights of Proposition 6.1: for any family
`μ_i`, `i ∈ I₀`, satisfying (1)–(3), `A` is isomorphic to a binary fibre, the transported basis is
a normed multiplicative ray basis of `A` presenting `P = ray A₀`, and the leading term of the
image of each ray vector `b_r` (for the radical filtration of `A`, `posFiltA`) is a nonzero
multiple of `b_r`. The argument does not use the characteristic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

open MeshWalk

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Proposition 7.9** (`prop:family-criterion`) for a basic representation-finite algebra `A`. -/
theorem familyCriterion {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
    (hprim : ∀ i, IsPrimitiveIdempotent (e i))
    (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
      y * x = e j) → i = j)
    (v₀ : S.ARVertex) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Wd : ι → MeshWt S.arTranslationQuiver ℤ)
    (Rw : ι → Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    (∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0) →
    ScalarMeshCategory.CokerSpan (S.arCoefficients b) (Set.range Rw) →
    ∀ μ : I0 (S.arMeshData b) v₀ hF Wd Rw → (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
        (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ,
    (∀ i, (latA0 (dualWt Wd) (hfinObj (c := S.arCoefficients b)) (S.arMeshData b)).Char₂
      (rowChar Wd Rw i.1) (μ i)) →
    (∀ i, LenGrading.IsCocycle₂ (μ i)) →
    (∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f) →
    ∀ (hrel : ∀ i, LenGrading.IsRel₂ (VxA0 (S.arMeshData b) v₀ hF Wd) (μ i))
      (hassoc : ∀ (lam : I0 (S.arMeshData b) v₀ hF Wd Rw → k)
        (a b' z : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ),
        famMulI μ lam (famMulI μ lam a b') z = famMulI μ lam a (famMulI μ lam b' z)),
    (∀ lam : I0 (S.arMeshData b) v₀ hF Wd Rw → k, (∀ i, lam i = 0 ∨ lam i = 1) →
      IsNormedMultiplicativeBasis
          ((basisR (S.arMeshData b) v₀ hF).map (Fib.toΛ (fibAM hrel hassoc lam)).symm) ∧
        ∃ (F : PrimitiveIdempotents (Fib (fibAM hrel hassoc lam)))
          (ιF : (S.arMeshData b).PV ≃ Fin F.m),
          F.IsRayPres (k := k) (A0Mult (S.arMeshData b) v₀ hF) ιF
            (fun r ↦ (Fib.toΛ (fibAM hrel hassoc lam)).symm (basisR (S.arMeshData b) v₀ hF r))) →
    ∃ (lam : I0 (S.arMeshData b) v₀ hF Wd Rw → k) (_ : ∀ i, lam i = 0 ∨ lam i = 1)
      (Ψ : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ ≃ₗ[k] A),
      (∀ a b', Ψ (famMulI μ lam a b') = Ψ a * Ψ b') ∧
      IsNormedMultiplicativeBasis ((basisR (S.arMeshData b) v₀ hF).map Ψ) ∧
      (∃ (F : PrimitiveIdempotents A) (ιF : (S.arMeshData b).PV ≃ Fin F.m),
        F.IsRayPres (k := k) (A0Mult (S.arMeshData b) v₀ hF) ιF
          (fun r ↦ Ψ (basisR (S.arMeshData b) v₀ hF r))) ∧
      ∀ r, ∃ t : k, t ≠ 0 ∧
        (S.posFiltA b he hprim hbasic).σ
          ((SysD (S.arMeshData b) v₀ hF Wd).P.deg ((SysD (S.arMeshData b) v₀ hF Wd).P.wt r)).toNat
            (Ψ (basisR (S.arMeshData b) v₀ hF r)) = t • basisR (S.arMeshData b) v₀ hF r := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  intro hF hWd hS μ hchar hcoc hnz hrel hassoc hfib
  exact familyCriterion_A0 (S.arMeshData b) v₀ hF Wd Rw (S.arInjData b) (S.arDegOne b) hWd hS μ
    hrel hchar hcoc hnz hassoc hfib (S.posFiltA b he hprim hbasic)

end MultiplicativeBasisDeformations.IndSkeleton
