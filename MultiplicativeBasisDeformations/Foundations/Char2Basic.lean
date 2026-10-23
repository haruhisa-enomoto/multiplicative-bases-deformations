module

public import MultiplicativeBasisDeformations.Foundations.Char2A0
public import MultiplicativeBasisDeformations.Foundations.FilteredA
public import MultiplicativeBasisDeformations.Foundations.ResidualDual
public import MultiplicativeBasisDeformations.Foundations.ARInjData
public import MultiplicativeBasisDeformations.Foundations.ARBrick
public import MultiplicativeBasisDeformations.Foundations.HochschildMesh

/-!
# Normed bases of basic algebras in characteristic two (given Corollary 10.5)

The proof of Proposition 8.3(1) in characteristic two (`main-theorems.tex`), for a
basic representation-finite algebra `A`: the rows of Proposition 6.1 with their dual mesh
weights (`residual_dual`), the filtered structure of `A` over `A₀` (`posFiltA`), and the
characteristic-two step on `A₀` (`char2_A0`). Corollary 10.5 is a hypothesis here; it is
discharged by `cor105Hyp` in `FinalBasis.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The mesh maps of `Γ_A` have degree one. -/
theorem arDegOne : MeshWalk.DegOne (S.arMeshData b) := by
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  exact ⟨fun _ a ↦ MeshWalk.arrowMor_mem_degreePart a.2,
    fun _ _ _ ↦ Submodule.smul_mem _ _ (MeshWalk.arrowMor_mem_degreePart _)⟩

/-- **Corollary 10.5 for the algebra `A₀` of `A`**, for every choice of rows and dual weights. -/
def Cor105AR : Prop :=
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  ∀ (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWalk.MeshWt S.arTranslationQuiver ℤ)
    (Rw : ι → Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1),
    (∀ i j, MeshWalk.rowWt (Wd i) (Rw j) = if j = i then (1 : ℤ) else 0) →
      MeshWalk.Cor105 (S.arMeshData b) v₀ hF Wd Rw

/-- The rays of `A₀` for the Auslander–Reiten mesh data. -/
def rayA0AR (v₀ : S.ARVertex) : Type :=
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  MeshWalk.RayA0 (S.arMeshData b) v₀

/-- The ray table of `A₀` for the Auslander–Reiten mesh data. -/
def A0MultAR (v₀ : S.ARVertex)
    (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) :
    RaySys.Mult (S.arMeshData b).PV (S.rayA0AR b v₀) :=
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  MeshWalk.A0Mult (S.arMeshData b) v₀ hF

/-- **A basic algebra in characteristic two has a normed multiplicative ray basis**, given
Corollary 10.5 for its algebra `A₀` (proof of Proposition 8.3(1), `main-theorems.tex`). -/
theorem exists_normedRayBasis_char2 (h2 : (2 : k) = 0) (hA : IsRepresentationFinite k A)
    {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
    (hprim : ∀ i, IsPrimitiveIdempotent (e i))
    (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
      y * x = e j) → i = j) (hn : n ≠ 0)
    (hcor : S.Cor105AR b) :
    ∃ (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
      (F : PrimitiveIdempotents A) (bF : Module.Basis (F.NonzeroRay k) k A),
      IsNormedMultiplicativeBasis bF ∧ F.IsRayTransversal bF ∧
        ∃ (ι : (S.arMeshData b).PV ≃ Fin F.m) (β : S.rayA0AR b v₀ → A),
          F.IsRayPres (k := k) (S.A0MultAR b v₀ hF) ι β := by
  classical
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  let v₀ : S.ARVertex := ((S.pvEquiv b he hprim hbasic).symm ⟨0, Nat.pos_of_ne_zero hn⟩).1
  have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  obtain ⟨SR, hper, hcomp, hspan, hdual⟩ := residual_dual (S.arCoefficients b)
    S.hasAtMostOneArrow h2 (S.hfinA0 b) (S.brickHypothesis b)
  have hfinSR : SR.Finite := by
    refine Set.Finite.of_finite_image (f := fun R ↦ R.1.1) (Set.toFinite _) ?_
    intro R hR R' hR' h
    exact hcomp R hR R' hR' (by
      have : R'.1.1 = R.1.1 := h.symm
      rw [this]; exact TranslationQuiver.mem_component_self (hper R hR))
  haveI : Fintype SR := hfinSR.fintype
  choose Wd hWd using fun R : SR ↦ hdual R.1 R.2
  have hWd' : ∀ i j : SR, MeshWalk.rowWt (Wd i) (j : _) = if j = i then 1 else 0 := by
    intro i j
    have := hWd i j.1 j.2
    unfold MeshWalk.rowWt
    rw [this]
    simp only [Subtype.ext_iff]
  have hS : ScalarMeshCategory.CokerSpan (S.arCoefficients b) (Set.range (fun R : SR ↦ (R : _))) := by
    rw [Subtype.range_coe]; exact hspan
  obtain ⟨F, bF, hnorm, htr, ι, β, hpres⟩ := MeshWalk.char2_A0 (S.arMeshData b) v₀ hF Wd
    (S.arInjData b) (S.arDegOne b) (fun R : SR ↦ (R : _)) hWd' hS (hcor v₀ hF Wd _ hWd')
    (S.posFiltA b he hprim hbasic)
  exact ⟨v₀, hF, F, bF, hnorm, htr, ι, β, hpres⟩

end MultiplicativeBasisDeformations.IndSkeleton
