module

public import MBDVendor.Magnitude.CategoryTheory.ModuleRadicalSquareComparison
public import MBDVendor.QSE.RepresentationTheory.LinearIrreducibleHomSpace

/-! # Intrinsic irreducible spaces and the existing module multiplicity interface -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
open MBDVendor.Magnitude
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.CategoricalRadical
namespace MBDVendor.QSE.IndecomposableSkeleton
universe u v
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [IsNoetherianRing R]
variable {ι : Type v} (S : IndecomposableSkeleton.{u,v,u} R ι)
local instance comparisonModule (i : ι) : Module k (S.obj i) :=
  Module.restrictScalars k R (S.obj i)
local instance comparisonTower (i : ι) : IsScalarTower k R (S.obj i) :=
  IsScalarTower.restrictScalars k R (S.obj i)

/-- The categorical radical numerator is the existing space of nonsplit
linear maps between the chosen indecomposables. -/
def intrinsicRadicalEquiv (x y : ι) :
    CategoricalIrreducible.radical k (S.obj x) (S.obj y) ≃ₗ[k]
      S.radicalHom (K := k) x y where
  toFun f := ⟨f.val.hom.hom,
    (S.isRadicalMorphism_iff_not_isSplitEpi_to_obj f.val).mp f.property⟩
  invFun f := by
    let g : S.obj x ⟶ S.obj y := ⟨ModuleCat.ofHom f.val⟩
    refine ⟨g, (S.isRadicalMorphism_iff_not_isSplitEpi_to_obj g).mpr ?_⟩
    exact (S.mem_radicalHom_iff_not_isSplitEpi f.val).mp f.property
  left_inv f := by
    apply Subtype.ext
    apply FGModuleCat.hom_ext
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The numerator comparison identifies the two radical-square denominators. -/
theorem intrinsicDenominator_map (x y : ι) :
    (CategoricalIrreducible.denominator k (S.obj x) (S.obj y)).map
      (S.intrinsicRadicalEquiv (k := k) x y).toLinearMap =
        S.radicalSquareInRadicalSubmodule (K := k) x y := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    change g.val ∈ ((homIdeal : HomIdeal (FGModuleCat.{u} R)) ⋆ᵢ homIdeal).hom _ _ at hg
    rw [S.intrinsic_radicalSquare_eq x y] at hg
    exact hg
  · intro hf
    refine ⟨(S.intrinsicRadicalEquiv (k := k) x y).symm f, ?_,
      (S.intrinsicRadicalEquiv (k := k) x y).apply_symm_apply f⟩
    change (ConcreteCategory.ofHom f.val : S.obj x ⟶ S.obj y) ∈
      ((homIdeal : HomIdeal (FGModuleCat.{u} R)) ⋆ᵢ homIdeal).hom _ _
    rw [S.intrinsic_radicalSquare_eq x y]
    exact hf

/-- The intrinsic categorical quotient is the established module irreducible
space used by the almost-split occurrence-basis theorems. -/
def intrinsicIrreducibleEquiv (x y : ι) :
    CategoricalIrreducible.Space k (S.obj x) (S.obj y) ≃ₗ[k]
      S.irreducibleHomSpace (K := k) x y :=
  Submodule.Quotient.equiv _ _ (S.intrinsicRadicalEquiv x y)
    (S.intrinsicDenominator_map x y)

end MBDVendor.QSE.IndecomposableSkeleton
