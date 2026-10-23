module

public import MultiplicativeBasisDeformations.Foundations.ARMeshFinite
public import MultiplicativeBasisDeformations.Foundations.SquareFree
public import MultiplicativeBasisDeformations.Foundations.PeriodicDepth

/-!
# Lemma 4.2 for the Auslander--Reiten quiver

`lem:mesh-walk-free` (`scalar-normalization.tex`): the complex `K` of
`Γ_A` has free vertex groups. The hypotheses of `MeshWalk.isFreeGroup_end` are
Lemma 2.2 (at most one arrow, `hasAtMostOneArrow`) and the finite-dimensionality
of `k(Γ_A)` (`finiteDimensional_meshHom`), which is what Proposition 4.1 needs.
The source assumes `A` connected; the vertex group at every vertex is free
without this assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- **Lemma 4.2** (`lem:mesh-walk-free`): the fundamental group of the mesh
complex `K` of `Γ_A` at every vertex is free. -/
theorem meshWalk_isFreeGroup (X : S.ARVertex) :
    IsFreeGroup (End (MeshWalk.obK S.arTranslationQuiver X)) := by
  classical
  obtain ⟨b⟩ := S.nonempty_arrowBases
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  exact MeshWalk.isFreeGroup_end (S.arCoefficients b) (fun x y ↦ S.finiteDimensional_meshHom b x y) X

end MultiplicativeBasisDeformations.IndSkeleton
