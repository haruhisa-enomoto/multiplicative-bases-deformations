import MBDVendor.Magnitude.Algebra.IndecomposableLocalEnd
import MBDVendor.Magnitude.CategoryTheory.FiniteGeneratorRadicalNilpotence

/-!
# Nilpotence of the radical of a representation-finite module category

The biproduct of the chosen indecomposable representatives is a finite
additive generator of `FGModuleCat Aᵐᵒᵖ`.  Its endomorphism ring is
finite-dimensional over the coefficient field and hence Artinian.  The generic
finite-generator theorem therefore supplies the canonical nilpotent
categorical radical required by the tau-category interface.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton

open MBDVendor.QSE.CategoricalRadical

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The finite biproduct of all chosen indecomposable right modules. -/
def additiveGenerator : RightModule.FinitelyGeneratedCategory A :=
  ⨁ S.fgObj

/-- Every finitely generated right module is a retract of a finite biproduct
of copies of the chosen additive generator. -/
theorem additiveGenerator_isFiniteAddGenerator :
    MBDVendor.Magnitude.CategoryTheory.IsFiniteAddGenerator
      S.additiveGenerator := by
  intro X
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition (k := k) X
  let F : Fin n → RightModule.FinitelyGeneratedCategory A :=
    fun j ↦ S.fgObj (label j)
  let intoGenerator : ∀ j : Fin n, F j ⟶ S.additiveGenerator :=
    fun j ↦ biproduct.ι S.fgObj (label j)
  let outOfGenerator : ∀ j : Fin n, S.additiveGenerator ⟶ F j :=
    fun j ↦ biproduct.π S.fgObj (label j)
  let iB : (⨁ F) ⟶
      ⨁ fun _ : Fin n ↦ S.additiveGenerator :=
    biproduct.map intoGenerator
  let rB : (⨁ fun _ : Fin n ↦ S.additiveGenerator) ⟶ ⨁ F :=
    biproduct.map outOfGenerator
  have hir : iB ≫ rB = 𝟙 (⨁ F) := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro l
    by_cases hjl : j = l
    · subst l
      simp [iB, rB, intoGenerator, outOfGenerator]
      change biproduct.ι S.fgObj (label j) ≫
        biproduct.π S.fgObj (label j) = 𝟙 (S.fgObj (label j))
      exact biproduct.ι_π_self S.fgObj (label j)
    · simp [iB, rB, intoGenerator, outOfGenerator, hjl]
  exact ⟨{
    n := n
    retract := {
      i := e.hom ≫ iB
      r := rB ≫ e.inv
      retract := by
        rw [Category.assoc, ← Category.assoc iB, hir]
        simp } }⟩

/-- The additive generator's endomorphism ring is Artinian because its Hom
space is finite-dimensional over the coefficient field. -/
noncomputable instance additiveGeneratorEndArtinian :
    IsArtinianRing (End S.additiveGenerator) := by
  letI : Module.Finite k (End S.additiveGenerator) := by
    change Module.Finite k
      (S.additiveGenerator ⟶ S.additiveGenerator)
    exact fgModuleCatHomFinite (k := k) (A := A)
      S.additiveGenerator S.additiveGenerator
  exact IsArtinianRing.of_finite k (End S.additiveGenerator)

/-- The canonical categorical radical of the literal finitely generated
right-module category is nilpotent in finite representation type. -/
def fgNilpotentRadicalData :
    NilpotentRadicalData (RightModule.FinitelyGeneratedCategory A) :=
  MBDVendor.Magnitude.CategoryTheory.nilpotentRadicalDataOfArtinianGenerator
    S.additiveGenerator S.additiveGenerator_isFiniteAddGenerator

end MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton
