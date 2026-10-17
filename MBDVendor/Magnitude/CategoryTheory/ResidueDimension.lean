import MBDVendor.Magnitude.CategoryTheory.HomMeshInverse
import MBDVendor.QSE.CategoryTheory.IyamaLadderRadical
import MBDVendor.QSE.CategoryTheory.SplitMorphismComplement

/-!
# Residue-field discharge for the Hom--mesh recurrence

This file reduces the residue-dimension equation to a concrete residue map on
each chosen indecomposable endomorphism ring.  The off-diagonal assertion is
proved from the finite Krull--Schmidt skeleton itself: a morphism between two
distinct skeletal indecomposables cannot be split monic and is therefore
categorically radical.

The remaining module-theoretic input is a surjective linear residue map
`End(X) -> k` whose kernel is the categorical radical.  Rank-nullity then gives
codimension one on the diagonal.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.Magnitude.FiniteTauMatrix

open MBDVendor.QSE
open MBDVendor.QSE.CategoricalRadical
open MBDVendor.QSE.Iyama

universe s v u w

variable {k : Type s} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] [Linear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

omit [DecidableEq Ind] in
/-- A split monomorphism between two chosen indecomposable representatives is
an isomorphism. -/
theorem isIso_of_isSplitMono_obj_obj
    (T : FiniteRightTauCategoryData C Ind)
    {p q : Ind} (f : T.obj p ⟶ T.obj q) [IsSplitMono f] :
    IsIso f := by
  let d := splitMonoComplement f
  let e : T.obj q ≅ T.obj p ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hcomp : IsZero d.complement :=
    ((T.obj_indec q).2 (T.obj p) d.complement e).resolve_left
      (T.obj_indec p).1
  apply IsIso.mk
  refine ⟨retraction f, IsSplitMono.id f, ?_⟩
  rw [← d.total]
  have hp : d.projection = 0 := hcomp.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hcomp.eq_of_src _ _
  rw [hp, hi, zero_comp, add_zero]

omit [DecidableEq Ind] in
/-- Every morphism between two distinct chosen skeletal indecomposables is
categorically radical. -/
theorem isRadicalMorphism_obj_obj_of_ne
    (T : FiniteRightTauCategoryData C Ind)
    {X Y : Ind} (hXY : X ≠ Y) (f : T.obj X ⟶ T.obj Y) :
    IsRadicalMorphism f := by
  rw [T.isRadicalMorphism_iff_not_isSplitMono_from_obj]
  intro hSplit
  letI : IsSplitMono f := hSplit
  letI : IsIso f := isIso_of_isSplitMono_obj_obj T f
  apply hXY
  exact T.obj_skeletal ⟨asIso f⟩

/-- Concrete residue-field data on the chosen indecomposable endomorphism
rings.  In the module-category specialization this is obtained from the
finite-dimensional local endomorphism algebra over an algebraically closed
field. -/
structure ResidueFieldData (T : FiniteRightTauCategoryData C Ind) where
  residueMap : ∀ X : Ind, (T.obj X ⟶ T.obj X) →ₗ[k] k
  residueMap_surjective : ∀ X : Ind, Function.Surjective (residueMap X)
  radical_eq_ker :
    ∀ X : Ind,
      MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
          k (T.obj X) (T.obj X) =
        LinearMap.ker (residueMap X)

omit [DecidableEq Ind] in
theorem radical_finrank_add_one_eq_end
    (T : FiniteRightTauCategoryData C Ind)
    (R : ResidueFieldData (k := k) T) (X : Ind) :
    Module.finrank k
        (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
          k (T.obj X) (T.obj X)) + 1 =
      Module.finrank k (T.obj X ⟶ T.obj X) := by
  have hRankNullity :=
    (ResidueFieldData.residueMap R X).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (ResidueFieldData.residueMap_surjective R X),
    finrank_top, Module.finrank_self,
    ← ResidueFieldData.radical_eq_ker R X] at hRankNullity
  exact (Nat.add_comm _ _).trans hRankNullity

/-- The residue maps imply the exact diagonal/off-diagonal dimension formula
used by the Hom--mesh inverse theorem. -/
theorem radicalFinrank_add_delta
    (T : FiniteRightTauCategoryData C Ind)
    (R : ResidueFieldData (k := k) T) (X Y : Ind) :
    Module.finrank k
        (MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
          k (T.obj X) (T.obj Y)) +
      (if X = Y then 1 else 0) =
        Module.finrank k (T.obj X ⟶ T.obj Y) := by
  by_cases hXY : X = Y
  · subst Y
    simpa only [if_pos] using radical_finrank_add_one_eq_end T R X
  · rw [if_neg hXY, add_zero]
    have hTop :
        MBDVendor.Magnitude.CategoryTheory.radicalSubmodule
            k (T.obj X) (T.obj Y) = ⊤ := by
      ext f
      simp only [Submodule.mem_top, iff_true]
      exact isRadicalMorphism_obj_obj_of_ne T hXY f
    rw [hTop, finrank_top]

/-- Strictness together with concrete residue maps constructs all hypotheses
of the Hom--mesh inverse theorem. -/
theorem HomMeshInverseData.ofResidue
    (T : FiniteTauCategoryData C Ind)
    (rightMono : ∀ Y : Ind, Mono (T.rightMesh (T.obj Y)).f)
    (R : ResidueFieldData (k := k)
      (T : FiniteRightTauCategoryData C Ind)) :
    HomMeshInverseData (k := k) T where
  rightMono := rightMono
  radicalFinrank_add_delta :=
    MBDVendor.Magnitude.FiniteTauMatrix.radicalFinrank_add_delta
      (k := k)
      (T : FiniteRightTauCategoryData C Ind) R

end MBDVendor.Magnitude.FiniteTauMatrix
