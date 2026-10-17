import MultiplicativeBasisDeformations.Independent.Skeleton
import MultiplicativeBasisDeformations.Foundations.FormFunctor
import MultiplicativeBasisDeformations.Statements.PartOne

/-!
# The independent mesh category and the scalar mesh categories of `Γ_A`

The path category of the independent quiver `Γ_A` is definitionally the linear
path category of the proof library. Granted that the independent translate,
defined by almost split sequences, is the translation of `Γ_A` in the proof
library (`TranslateCompatible`), the independent mesh relations are the
all-one mesh relations, so the independent `k(Γ_A)` is the scalar mesh
category with all coefficients one. A gauge transformation (Lemma 4.4) then
identifies it with the scalar mesh category whose coefficients come from the
almost split sequences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra
open MultiplicativeBasisDeformations.CategoricalIdeal
set_option linter.unusedSectionVars false

namespace MultiplicativeBasisDeformations.Statement

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : IndecomposableFamily k A)

/-- The all-one coefficient system on `Γ_A`. -/
def oneCoeff : MeshCoefficients k (toSkeleton S).arTranslationQuiver := fun _ _ _ ↦ 1

/-- The independent translate agrees with the translation of `Γ_A` in the proof
library. -/
def TranslateCompatible : Prop :=
  ∀ t i : Vertex S, IsTranslate S t i ↔
    ∃ x : (toSkeleton S).arTranslationQuiver.nonprojective,
      x.1 = i ∧ ((toSkeleton S).arTranslationQuiver.tau x).1 = t

set_option maxHeartbeats 4000000 in
/-- The independent mesh relation in the vocabulary of the proof library (a
definitional unfolding). -/
theorem meshRelation_internal (t i : (toSkeleton S).ARVertex) :
    meshRelation S t i = ∑ j : (toSkeleton S).ARVertex, ∑ b : (t ⟶ j), ∑ a : (j ⟶ i),
      LinearPaths.path (k := k) (b.toPath.comp a.toPath) := rfl

/-- The all-one mesh relation as a sum over all paths of length two. -/
theorem meshRelation_one (x : (toSkeleton S).arTranslationQuiver.nonprojective) :
    ∑ j : (toSkeleton S).ARVertex, ∑ b : (((toSkeleton S).arTranslationQuiver.tau x).1 ⟶ j),
        ∑ a : (j ⟶ x.1), LinearPaths.path (k := k) (b.toPath.comp a.toPath) =
      MultiplicativeBasisDeformations.meshRelation (k := k) (oneCoeff S) x := by
  classical
  have : ∀ y z : (toSkeleton S).ARVertex, Subsingleton (y ⟶ z) :=
    (toSkeleton S).hasAtMostOneArrow
  unfold MultiplicativeBasisDeformations.meshRelation
  rw [Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ fun j ↦ ?_
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun a ↦ ?_
  rw [Fintype.sum_subsingleton _ ((toSkeleton S).arTranslationQuiver.mate x j a)]
  simp only [oneCoeff, Units.val_one, one_smul]

set_option maxHeartbeats 4000000 in
/-- The independent mesh relation at a nonprojective vertex is the all-one mesh
relation. -/
theorem meshRelation_eq (x : (toSkeleton S).arTranslationQuiver.nonprojective) :
    meshRelation S ((toSkeleton S).arTranslationQuiver.tau x).1 x.1 =
      MultiplicativeBasisDeformations.meshRelation (k := k) (oneCoeff S) x :=
  (meshRelation_internal S _ _).trans (meshRelation_one S x)

variable {S}

set_option maxHeartbeats 4000000 in
/-- Under translate compatibility, the independent mesh relations are the
all-one mesh relations. -/
theorem meshRelations_eq (hτ : TranslateCompatible S) (X Y : (toSkeleton S).ARVertex) :
    meshRelations S X Y =
      MultiplicativeBasisDeformations.meshRelations (k := k) (oneCoeff S)
        (LinearPaths.obj X) (LinearPaths.obj Y) := by
  ext r
  constructor
  · rintro ⟨t, i, ht, hX, hY, rfl⟩
    obtain ⟨x, rfl, rfl⟩ := (hτ t i).1 ht
    exact ⟨x, hX, hY, by rw [meshRelation_eq]⟩
  · rintro ⟨x, hX, hY, rfl⟩
    exact ⟨_, _, (hτ _ _).2 ⟨x, rfl, rfl⟩, hX, hY, by rw [meshRelation_eq]⟩

set_option maxHeartbeats 4000000 in
theorem meshIdeal_eq (hτ : TranslateCompatible S) (X Y : (toSkeleton S).ARVertex) :
    meshIdeal S X Y =
      HomIdeal.generatedHomSubmodule k
        (MultiplicativeBasisDeformations.meshRelations (k := k) (oneCoeff S))
        (LinearPaths.obj X) (LinearPaths.obj Y) := by
  have h : meshRelations S =
      MultiplicativeBasisDeformations.meshRelations (k := k) (oneCoeff S) := by
    funext X' Y'
    exact meshRelations_eq hτ X' Y'
  unfold meshIdeal HomIdeal.generatedHomSubmodule HomIdeal.twoSidedCompositeSet
  rw [h]
  rfl

set_option maxHeartbeats 4000000 in
theorem meshRel_iff (hτ : TranslateCompatible S) {X Y : PathCategory S} (f g : X ⟶ Y) :
    meshRel S f g ↔
      (HomIdeal.linearSpan k
        (MultiplicativeBasisDeformations.meshRelations (k := k) (oneCoeff S))).rel f g := by
  change f - g ∈ meshIdeal S X Y ↔ f - g ∈ HomIdeal.generatedHomSubmodule k _ X Y
  rw [meshIdeal_eq hτ]

end MultiplicativeBasisDeformations.Statement
