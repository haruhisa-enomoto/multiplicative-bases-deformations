import MultiplicativeBasisDeformations.Foundations.ARInjData
import MultiplicativeBasisDeformations.Foundations.DeletionBrick

/-!
# The brick hypothesis for `k(Γ_A)`

Lemma 5.2 (`periodic-mesh-calculations.tex`, the deletion brick lemma) for
`C = k(Γ_A)`: by Proposition 2.10, `C` satisfies the hypotheses of the abstract
statement `CatAlg.MeshData.brick` (labels outside `Σ` of least evaluation
dimension have their radical endomorphisms factoring through `Σ`). In the
object quotient `C/[Σ]` the kernel on `C(x, y)` is the span of composites
through objects of `Σ`; hence such a label has endomorphism ring `k` in
`C/[Σ]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations

namespace ScalarMeshCategory

universe u w

variable {k : Type u} [Field k] {V : Type} [Quiver.{w} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)

/-- The kernel of `C → C/[D]` is the span of the composites through `D`. -/
theorem objectQuotient_map_eq_zero_iff (D : Set V) {x y : V} (f : obj c x ⟶ obj c y) :
    (RelationCategory.functor k (identityRelations c D)).map f = 0 ↔
      f ∈ CatAlg.MeshData.through (k := k) (fun x ↦ obj c x) D x y := by
  rw [RelationCategory.functor_map_eq_zero_iff]
  change f ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule k _ _ _ ↔ _
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨A, B, r, ⟨s, hs, hX, hY, rfl⟩, a, b', rfl⟩ := hg
        subst hX
        subst hY
        exact Submodule.subset_span ⟨s, hs, a, b', by simp⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul t a _ ha => exact Submodule.smul_mem _ t ha
  · intro hf
    refine (Submodule.span_le.2 ?_) hf
    rintro _ ⟨s, hs, g, h, rfl⟩
    exact Submodule.subset_span ⟨obj c s, obj c s, 𝟙 _, ⟨s, hs, rfl, rfl, by simp⟩, g, h, by simp⟩

/-- The brick hypothesis follows from Lemma 5.2 in the form of
`CatAlg.MeshData.brick`. -/
theorem brickHypothesis_of (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
    (h : ∀ D : Set V, (∃ x, x ∉ D) → ∃ x, x ∉ D ∧
      (localFamily c hfin).rad x x ≤ CatAlg.MeshData.through (k := k) (fun x ↦ obj c x) D x x) :
    BrickHypothesis c := by
  intro D ⟨x0, hx0⟩
  have hne : ∃ x, x ∉ D := by
    refine ⟨x0, fun hx ↦ hx0 ?_⟩
    rw [← CategoryTheory.Functor.map_id, objectQuotient_map_eq_zero_iff]
    exact Submodule.subset_span ⟨x0, hx, 𝟙 _, 𝟙 _, by simp⟩
  obtain ⟨x, hx, hrad⟩ := h D hne
  refine ⟨x, ?_⟩
  have hid : (RelationCategory.functor k (identityRelations c D)).map (𝟙 (obj c x)) ≠ 0 := by
    rw [Ne, objectQuotient_map_eq_zero_iff]
    intro h1
    exact (localFamily c hfin).id_not_mem x (CatAlg.MeshData.through_le_rad D hx h1)
  rw [CategoryTheory.Functor.map_id] at hid
  apply (finrank_eq_one_iff_of_nonzero' _ hid).2
  intro g
  obtain ⟨f, rfl⟩ := RelationCategory.functor_map_surjective _ g
  obtain ⟨c0, hc0⟩ := (localFamily c hfin).diag x f
  refine ⟨c0, ?_⟩
  have h0 := (objectQuotient_map_eq_zero_iff c D _).2 (hrad hc0)
  rw [Functor.map_sub, Functor.map_smul, sub_eq_zero, CategoryTheory.Functor.map_id] at h0
  exact h0.symm

end ScalarMeshCategory

namespace IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **The brick hypothesis for `k(Γ_A)`** (Lemma 5.2 with Proposition 2.10). -/
theorem brickHypothesis : ScalarMeshCategory.BrickHypothesis (S.arCoefficients b) := by
  haveI := S.finiteDimensional_meshHom b
  apply ScalarMeshCategory.brickHypothesis_of _ (S.finiteDimensional_meshHom b)
  intro D hD
  exact CatAlg.MeshData.brick (S.arMeshData b) (S.arInjData b) D hD

end IndSkeleton

end MultiplicativeBasisDeformations
