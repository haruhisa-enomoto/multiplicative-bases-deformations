import MBDVendor.Magnitude.Algebra.RightModuleTranslationMultiplicity
import MBDVendor.Magnitude.Algebra.RightModuleProjectiveBoundary
import MBDVendor.Magnitude.CategoryTheory.ModuleIrreducibleSpaceComparison
import MBDVendor.Magnitude.CategoryTheory.AlgebraicallyClosedOccurrenceBasis
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtWeight

/-!
# Intrinsic irreducible quotients compute arrow multiplicities

Borrowed from `formalization/magnitude_conjecture` (commit `52fbbfa2b`):
`meshProjectiveBoundaryMap`, `meshRightAlmostSplitAt` and its equation lemmas,
and `labelRightMesh_X₂` from `Algebra/RightModuleStandardMesh.lean`; the
multiplicity lemmas `indecomposableMultiplicity*` from
`Algebra/RightModulePrimitiveDeletion.lean`; and
`intrinsicIrreducible_finrank_eq_arrowMultiplicity` from
`Algebra/RightModuleIntrinsicArrowMultiplicity.lean`. Statements and proofs
are unchanged apart from the namespace rename. The rest of those files is not
needed and is not copied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The projective radical inclusion written in the selected skeleton's
object vocabulary. -/
def meshProjectiveBoundaryMap (z : Fin S.n) :
    S.projectiveBoundaryRadical z ⟶ S.almostSplitSkeleton.obj z :=
  S.projectiveBoundaryRadicalInclusion z

/-- A minimal right almost-split decomposition at every vertex, using the
radical inclusion at a projective vertex and the chosen AR decomposition at
a nonprojective vertex. -/
def meshRightAlmostSplitAt (z : Fin S.n) :
    S.almostSplitSkeleton.MinimalRightAlmostSplitDecomposition z := by
  classical
  by_cases hz : Projective (S.fgObj z)
  · exact
      IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap
        S.almostSplitSkeleton
        (S.meshProjectiveBoundaryMap z)
        (fgModule_isFiniteLength (k := k) (A := A)
          (S.projectiveBoundaryRadical z))
        (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit z hz)
        (S.projectiveBoundaryRadicalInclusion_isRightMinimal z)
  · exact S.minimalRightAlmostSplitAt z

@[simp]
theorem meshRightAlmostSplitAt_eq_of_not_projective
    (z : Fin S.n) (hz : ¬ Projective (S.fgObj z)) :
    S.meshRightAlmostSplitAt z = S.minimalRightAlmostSplitAt z := by
  simp [meshRightAlmostSplitAt, hz]

theorem meshRightAlmostSplitAt_eq_of_projective
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    S.meshRightAlmostSplitAt z =
      IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap
        S.almostSplitSkeleton
        (S.meshProjectiveBoundaryMap z)
        (fgModule_isFiniteLength (k := k) (A := A)
          (S.projectiveBoundaryRadical z))
        (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit z hz)
        (S.projectiveBoundaryRadicalInclusion_isRightMinimal z) := by
  simp [meshRightAlmostSplitAt, hz]

/-- The middle term of the unified label mesh is the displayed middle term
of the corresponding minimal right almost-split decomposition. -/
theorem labelRightMesh_X₂ (z : Fin S.n) :
    (S.labelRightMesh z).X₂ =
      (S.meshRightAlmostSplitAt z).middle := by
  classical
  by_cases hz : Projective (S.fgObj z)
  · rw [S.meshRightAlmostSplitAt_eq_of_projective z hz]
    simp [labelRightMesh, hz, projectiveRightMesh,
      IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap]
  · rw [S.meshRightAlmostSplitAt_eq_of_not_projective z hz]
    simp [labelRightMesh, hz, nonprojectiveRightMesh]

/-- Multiplicity of one ambient skeleton label in the fixed displayed
Krull--Schmidt decomposition of a finitely generated module. -/
def indecomposableMultiplicity
    (p : Fin S.n) (M : FinitelyGeneratedCategory A) : ℕ :=
  ∑ i : Fin (S.chosenLabelDecomposition M).n,
    if (S.chosenLabelDecomposition M).label i = p then 1 else 0

/-- The fixed multiplicity agrees with the occurrence count in any other
displayed decomposition into the same ambient skeleton. -/
theorem indecomposableMultiplicity_eq_of_decomposition
    (p : Fin S.n) (M : FinitelyGeneratedCategory A)
    {n : ℕ} {label : Fin n → Fin S.n}
    (d : M ≅ ⨁ fun i ↦ S.fgObj (label i)) :
    S.indecomposableMultiplicity p M =
      ∑ i : Fin n, if label i = p then 1 else 0 := by
  let T := S.finiteTauCategoryData
  let c := S.chosenLabelDecomposition M
  change (∑ i : Fin c.n, if c.label i = p then 1 else 0) = _
  exact T.label_multiplicity_eq_of_nonempty_iso_finBiproduct_obj
    p c.n n c.label label ⟨c.iso.symm.trans d⟩

/-- The fixed multiplicity agrees with a decomposition indexed by any finite
type.  This is the index-neutral form used by almost-split decompositions,
whose index is stored as a `FintypeCat`. -/
theorem indecomposableMultiplicity_eq_of_fintype_decomposition
    (p : Fin S.n) (M : FinitelyGeneratedCategory A)
    {I : Type} [Fintype I] [Finite I]
    {label : I → Fin S.n}
    (d : M ≅ ⨁ fun i : I ↦ S.fgObj (label i)) :
    S.indecomposableMultiplicity p M =
      ∑ i : I, if label i = p then 1 else 0 := by
  classical
  let ε : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let labelFin : Fin (Fintype.card I) → Fin S.n :=
    fun j ↦ label (ε.symm j)
  let factors : ∀ i : I,
      S.fgObj (labelFin (ε i)) ≅ S.fgObj (label i) := fun i ↦
    eqToIso (by simp [labelFin, ε])
  let reindex : (⨁ fun i : I ↦ S.fgObj (label i)) ≅
      ⨁ fun j : Fin (Fintype.card I) ↦ S.fgObj (labelFin j) :=
    biproduct.whiskerEquiv ε factors
  rw [S.indecomposableMultiplicity_eq_of_decomposition
    p M (d.trans reindex)]
  simpa only [labelFin, ε, Equiv.symm_apply_apply] using
    (Equiv.sum_comp ε
      (fun j ↦ if labelFin j = p then 1 else 0)).symm

/-- At every ambient endpoint, including the projective boundary, the fixed
object multiplicity of the standard right-mesh middle term is exactly the
ambient arrow multiplicity. -/
theorem indecomposableMultiplicity_meshRightMiddle
    (p z : Fin S.n) :
    S.indecomposableMultiplicity p
        (S.meshRightAlmostSplitAt z).middle =
      MBDVendor.Magnitude.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p z := by
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let B := S.meshRightAlmostSplitAt z
  have hmiddle : (T.rightMesh (T.obj z)).X₂ = B.middle := by
    change (S.canonicalRightMesh (S.fgObj z)).X₂ = B.middle
    rw [S.canonicalRightMesh_at_label z]
    exact S.labelRightMesh_X₂ z
  let d : B.middle ≅
      ⨁ fun i ↦ T.obj
        (MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleLabel T z i) :=
    (eqToIso hmiddle.symm).trans
      (Classical.choice
        (MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleIso T z))
  rw [S.indecomposableMultiplicity_eq_of_decomposition p B.middle d]
  change (∑ i, if
      MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleLabel T z i = p
        then 1 else 0) =
    MBDVendor.Magnitude.FiniteTauMatrix.arrowMultiplicity T p z
  rw [MBDVendor.Magnitude.FiniteTauMatrix.arrowMultiplicity]
  congr 1
  funext i
  by_cases h :
      MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleLabel T z i = p <;>
    simp [h]

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u'

variable {k A : Type u'} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Over an algebraically closed field the dimension of the intrinsic
categorical irreducible quotient is the literal finite-tau arrow multiplicity,
including arrows into projective vertices. -/
theorem intrinsicIrreducible_finrank_eq_arrowMultiplicity
    (source target : Fin S.n) :
    Module.finrank k (CategoricalIrreducible.Space k (S.fgObj source) (S.fgObj target)) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target := by
  classical
  let sigma := S.almostSplitSkeleton
  let : ∀ i : Fin S.n, Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  let : ∀ i : Fin S.n, IsScalarTower k Aᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  refine (sigma.intrinsicIrreducibleEquiv (k := k) source target).finrank_eq.trans ?_
  let B := S.meshRightAlmostSplitAt target
  letI : Fintype B.index := Fintype.ofFinite _
  rw [sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
    (K := k) B source]
  rw [← S.indecomposableMultiplicity_meshRightMiddle source target,
    S.indecomposableMultiplicity_eq_of_fintype_decomposition
      source B.middle B.decomposition]
  change Nat.card {i : B.index // B.label i = source} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
