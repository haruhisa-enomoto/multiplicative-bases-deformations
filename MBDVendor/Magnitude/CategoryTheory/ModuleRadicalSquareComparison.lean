import MBDVendor.Magnitude.CategoryTheory.CategoricalIrreducibleSpace
import MBDVendor.QSE.RepresentationTheory.IrreducibleRadicalQuotient

/-! # Intrinsic and module-skeleton radical-square definitions agree -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.CategoricalRadical
namespace MBDVendor.QSE.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {ι : Type v} (S : IndecomposableSkeleton.{u,v,w} R ι)

/-- The intrinsic product ideal has the same Hom subgroup as the existing
arbitrary-middle radical-square factorization predicate. -/
theorem intrinsic_radicalSquare_eq (x y : ι) :
    ((homIdeal : HomIdeal (FGModuleCat.{w} R)) ⋆ᵢ homIdeal).hom (S.obj x) (S.obj y) =
      S.radicalSquareHomAddSubgroup x y := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    rintro f ⟨M, a, b, ha, hb, rfl⟩
    exact (S.hasRadicalSquareFactorization_iff_categoricalRadical (a ≫ b)).mpr
      ⟨M, a, b, ha, hb, rfl⟩
  · intro f hf
    obtain ⟨M, a, b, ha, hb, rfl⟩ :=
      (S.hasRadicalSquareFactorization_iff_categoricalRadical f).mp hf
    exact HomIdeal.comp_mem_mul ha hb

end MBDVendor.QSE.IndecomposableSkeleton
