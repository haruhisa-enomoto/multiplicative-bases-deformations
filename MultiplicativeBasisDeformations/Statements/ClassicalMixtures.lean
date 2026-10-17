import MultiplicativeBasisDeformations.Foundations.Prop103
import MultiplicativeBasisDeformations.Foundations.RelativeHochschild

/-!
# Remark 11.5: the indicator cocycles span `HH²(A₀)_{>0}`

`rem:classical-mixtures` (`binary-families.tex:215`): if `V` is the span of the indicator cocycles
of Proposition 11.2, Corollary 10.5 gives the exact sequence
`0 → V ∩ B²(A₀) → V → HH²(A₀)_{>0} → 0`.

The left part is the definition of the map `V → HH²`. The content is surjectivity: every
Hochschild two-cocycle of `A₀` of positive internal degree is a combination of indicator cocycles
plus a coboundary (`classicalMixtures`), for a basic representation-finite algebra in
characteristic two. Here `HH²` is ordinary Hochschild cohomology (all cocycles and coboundaries of
the given internal degree; `RelativeHochschild.lean`), and Corollary 10.5 is the proved
`cor105Hyp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Remark 11.5** (`rem:classical-mixtures`): for a basic representation-finite algebra in
characteristic two, the transported indicator cocycles `μ_E` of Proposition 11.2 (normalized
relative cocycles of positive degree) span `HH²(A₀)_{>0}`: every Hochschild two-cocycle `φ` of
`A₀` of internal degree `q > 0` is `Σ c_j μ_{E_j} + d f` with `f` of degree `q`. -/
theorem classicalMixtures [CharP k 2] (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A)
    (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let D := S.arMeshData b
    let G := MeshWalk.lenA0 D (MeshWalk.hfinObj (c := S.arCoefficients b))
    ∃ (hF : IsRepresentationFinite k (CatAlg.Alg D.F0)ᵐᵒᵖ) (ι : Type) (_ : Fintype ι)
      (_ : DecidableEq ι) (Wd : ι → MeshWalk.MeshWt S.arTranslationQuiver ℤ) (n : ℕ)
      (E : Fin n → Quotient (MeshWalk.SysD D v₀ hF Wd).pairSetoid) (qd : Fin n → ℕ),
      (∀ j, 0 < qd j ∧
        LenGrading.IsRel₂ (MeshWalk.VxA0 D v₀ hF Wd) ((MeshWalk.SysD D v₀ hF Wd).transp k
          (MeshWalk.ΘD D v₀ hF Wd) ((MeshWalk.SysD D v₀ hF Wd).muE k (E j))) ∧
        LenGrading.IsCocycle₂ ((MeshWalk.SysD D v₀ hF Wd).transp k
          (MeshWalk.ΘD D v₀ hF Wd) ((MeshWalk.SysD D v₀ hF Wd).muE k (E j))) ∧
        LenGrading.HasDeg₂ G (qd j) ((MeshWalk.SysD D v₀ hF Wd).transp k
          (MeshWalk.ΘD D v₀ hF Wd) ((MeshWalk.SysD D v₀ hF Wd).muE k (E j)))) ∧
      ∀ q, 0 < q → ∀ φ, LenGrading.HasDeg₂ G q φ → LenGrading.IsCocycle₂ φ →
        ∃ (cf : Fin n → k) (f : (CatAlg.Alg D.F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg D.F0)ᵐᵒᵖ),
          LenGrading.HasDeg₁ G q f ∧
          φ = (∑ j ∈ Finset.univ.filter (fun j ↦ qd j = q),
            cf j • (MeshWalk.SysD D v₀ hF Wd).transp k (MeshWalk.ΘD D v₀ hF Wd)
              ((MeshWalk.SysD D v₀ hF Wd).muE k (E j))) + LenGrading.cobdry k f := by
  classical
  have : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  have hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  have : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  obtain ⟨SR, hper, hcomp, hspan, hdual⟩ := residual_dual (S.arCoefficients b)
    S.hasAtMostOneArrow h2 (S.hfinA0 b) (S.brickHypothesis b)
  have hfinSR : SR.Finite := by
    refine Set.Finite.of_finite_image (f := fun R ↦ R.1.1) (Set.toFinite _) ?_
    intro R hR R' hR' h
    exact hcomp R hR R' hR' (by
      have : R'.1.1 = R.1.1 := h.symm
      rw [this]; exact TranslationQuiver.mem_component_self (hper R hR))
  have : Fintype SR := hfinSR.fintype
  choose Wd hWd using fun R : SR ↦ hdual R.1 R.2
  have hWd' : ∀ i j : SR, MeshWalk.rowWt (Wd i) (j : _) = if j = i then 1 else 0 := by
    intro i j
    have := hWd i j.1 j.2
    unfold MeshWalk.rowWt
    rw [this]
    simp only [Subtype.ext_iff]
  have hS : ScalarMeshCategory.CokerSpan (S.arCoefficients b)
      (Set.range (fun R : SR ↦ (R : _))) := by
    rw [Subtype.range_coe]; exact hspan
  have hcorAR := cor105Hyp k A hbasic hA (lift2_all h2 (cor105Hyp k) _) S b
  obtain ⟨n, E, qd, hμ, hsp⟩ := MeshWalk.indicator_span_A0 (S.arMeshData b) v₀ hF Wd
    (S.arInjData b) (S.arDegOne b) (fun R : SR ↦ (R : _)) hWd' hS (hcorAR v₀ hF Wd _ hWd')
  refine ⟨hF, SR, inferInstance, inferInstance, Wd, n, E, qd, hμ, fun q hq ↦ ?_⟩
  exact (LenGrading.span_rel_iff _ _ qd (fun j ↦ (hμ j).2.1) q).1 (hsp q hq)

end MultiplicativeBasisDeformations.IndSkeleton
