module

public import MBDVendor.Magnitude.Algebra.IndecomposableLocalEnd
public import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd
public import MBDVendor.QSE.RepresentationTheory.AlmostSplitUniqueness
public import MBDVendor.QSE.RepresentationTheory.FiniteTypeAlmostSplit

/-!
# Finite-type almost-split data for right modules

This file connects the magnitude campaign's categorical finite
indecomposable skeleton with the donor's module-theoretic finite-type
almost-split existence theorem.  The two notions of indecomposability are
bridged through the local endomorphism ring, and no classification of modules
is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The categorical endomorphism ring of an FG module agrees with its usual
module endomorphism ring. -/
def fgEndModuleEndRingEquiv
    (M : RightModule.FinitelyGeneratedCategory A) :
    End M ≃+* Module.End Aᵐᵒᵖ M := by
  let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
    (RightModule.Category A)
  letI : U.Additive := ⟨by intros; rfl⟩
  exact
    (CategoryTheory.Functor.endRingEquivOfFullyFaithful U M).trans
      (ModuleCat.endRingEquiv (U.obj M))

omit [IsNoetherianRing Aᵐᵒᵖ] in
include k in
/-- Every finitely generated right module over a finite-dimensional algebra
has finite length over the opposite algebra. -/
theorem fgModule_isFiniteLength
    (M : RightModule.FinitelyGeneratedCategory A) :
    IsFiniteLength Aᵐᵒᵖ M := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  exact
    ((IsArtinianRing.tfae Aᵐᵒᵖ M).out 1 4).mp
      (inferInstance : Module.Finite Aᵐᵒᵖ M)

include k in
/-- For finitely generated modules over a finite-dimensional algebra, the
module-theoretic indecomposability used by the almost-split construction is
equivalent to categorical indecomposability. -/
theorem fgModule_isIndecomposableModule_iff_indecomposable
    (M : RightModule.FinitelyGeneratedCategory A) :
    MBDVendor.QSE.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ M ↔
      Indecomposable M := by
  constructor
  · intro hM
    have hlength : IsFiniteLength Aᵐᵒᵖ M :=
      fgModule_isFiniteLength (k := k) (A := A) M
    letI : Nontrivial M := hM.nontrivial
    letI : IsLocalRing (Module.End Aᵐᵒᵖ M) :=
      MBDVendor.QSE.Foundation.isLocalRing_end_of_isIndecomposable
        hlength hM
    letI : IsLocalRing (End M) :=
      RingEquiv.isLocalRing_noncomm
        (fgEndModuleEndRingEquiv (A := A) M).symm
    exact MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end M
  · intro hM
    have hMobj : Indecomposable M.obj :=
      (indecomposable_iff_obj (k := k) (A := A) M).1 hM
    have hnsub : ¬ Subsingleton M :=
      (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1 hMobj.1
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hnsub
    letI : Module k M := Module.restrictScalars k Aᵐᵒᵖ M
    letI : IsScalarTower k Aᵐᵒᵖ M :=
      IsScalarTower.restrictScalars k Aᵐᵒᵖ M
    letI : Module.Finite k Aᵐᵒᵖ := inferInstance
    letI : Module.Finite k M :=
      finite_over_field_of_finitelyGenerated k A M
    letI : IsLocalRing (End M.obj) :=
      moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖ) M.obj hMobj
    letI : IsLocalRing (Module.End Aᵐᵒᵖ M) :=
      RingEquiv.isLocalRing_noncomm (ModuleCat.endRingEquiv M.obj)
    exact
      MBDVendor.QSE.Foundation.isIndecomposableModule_of_isLocalRing_end

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Each chosen categorical indecomposable is indecomposable in the donor's
module-theoretic sense. -/
theorem fgObj_isIndecomposableModule (i : Fin S.n) :
    MBDVendor.QSE.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ (S.fgObj i) := by
  have hnsub : ¬ Subsingleton (S.obj i) :=
    (not_iff_not.2 ModuleCat.isZero_iff_subsingleton).1
      (S.obj_indecomposable i).1
  letI : Nontrivial (S.fgObj i) :=
    not_subsingleton_iff_nontrivial.mp hnsub
  letI : IsLocalRing (End (S.fgObj i)) :=
    S.fgObj_end_isLocalRing i
  letI : IsLocalRing (Module.End Aᵐᵒᵖ (S.fgObj i)) :=
    RingEquiv.isLocalRing_noncomm
      (fgEndModuleEndRingEquiv (A := A) (S.fgObj i))
  exact
    MBDVendor.QSE.Foundation.isIndecomposableModule_of_isLocalRing_end

/-- The chosen finite right-module skeleton, expressed in the exact interface
consumed by the finite-type almost-split construction. -/
def almostSplitSkeleton :
    MBDVendor.QSE.IndecomposableSkeleton
      Aᵐᵒᵖ (Fin S.n) where
  obj := S.fgObj
  indecomposable := S.fgObj_isIndecomposableModule
  finiteLength := fun i ↦
    fgModule_isFiniteLength (k := k) (A := A) (S.fgObj i)
  eq_of_iso := fun h ↦ S.fgObj_skeletal h
  complete := by
    intro M hM
    exact S.fgObj_complete M
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := A) M).1 hM)
  decomposes := S.fgObj_decomposition

/-- A chosen minimal right almost-split decomposition at every selected
indecomposable right module. -/
def minimalRightAlmostSplitAt (i : Fin S.n) :
    S.almostSplitSkeleton.MinimalRightAlmostSplitDecomposition i :=
  Classical.choice
    (S.almostSplitSkeleton
      |>.minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional
        k i)

/-- A chosen minimal left almost-split decomposition at every selected
indecomposable right module. -/
def minimalLeftAlmostSplitAt (i : Fin S.n) :
    S.almostSplitSkeleton.MinimalLeftAlmostSplitDecomposition i :=
  Classical.choice
    (S.almostSplitSkeleton
      |>.minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional
        k i)

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
