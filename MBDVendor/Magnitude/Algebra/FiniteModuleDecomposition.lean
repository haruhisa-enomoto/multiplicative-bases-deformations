import MBDVendor.Magnitude.CategoryTheory.FiniteIndecomposableDecomposition
import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional modules decompose into indecomposables

The standard existence half of Krull--Schmidt is proved by strong induction on
the coefficient-field dimension.  This is a bounded adaptation of the module
specialization in the Cartan formalization's
`ClosedRayChain/GenericFiniteness.lean` at commit `eade4e75`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MBDVendor.Magnitude

open MBDVendor.Magnitude.CategoryTheory

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- Every displayed indecomposable summand of a finite-dimensional module is
again finite-dimensional. -/
theorem CategoryTheory.FiniteIndecomposableDecomposition.summand_finite
    {M : ModuleCat.{v} A} (d : FiniteIndecomposableDecomposition M)
    (hM : Module.Finite k M) (j : Fin d.n) :
    Module.Finite k (d.summand j) := by
  letI : Module.Finite k M := hM
  let i : d.summand j ⟶ M :=
    biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  let p : M ⟶ d.summand j :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand j
  have hip : i ≫ p = 𝟙 (d.summand j) := by
    simp [i, p, Category.assoc]
  apply Module.Finite.of_injective (i.hom.restrictScalars k)
  exact (show Function.LeftInverse p i from fun x ↦ by
    change (i ≫ p) x = x
    rw [hip]
    rfl).injective

/-- Every finite-dimensional module over a finite-dimensional algebra is a
finite biproduct of indecomposable modules. -/
theorem finiteIndecomposableDecomposition_module_exists
    [Module.Finite k A] (M : ModuleCat.{v} A) [Module.Finite k M] :
    Nonempty (FiniteIndecomposableDecomposition M) := by
  classical
  generalize hn : Module.finrank k M = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
      by_cases hMzero : IsZero M
      · exact ⟨{
          n := 0
          summand := fun i ↦ Fin.elim0 i
          indecomposable := fun i ↦ Fin.elim0 i
          isoBiproduct := zeroIsoEmptyBiproduct M hMzero }⟩
      by_cases hMind : Indecomposable M
      · exact ⟨{
          n := 1
          summand := fun _ ↦ M
          indecomposable := fun _ ↦ hMind
          isoBiproduct :=
            (biproductUniqueIso (fun _ : Fin 1 ↦ M)).symm }⟩
      have hsplit : ∃ X Y : ModuleCat.{v} A, ∃ e : M ≅ X ⊞ Y,
          ¬ IsZero X ∧ ¬ IsZero Y := by
        rw [Indecomposable] at hMind
        push Not at hMind
        exact hMind hMzero
      obtain ⟨X, Y, e, hXzero, hYzero⟩ := hsplit
      let iX : X ⟶ M := biprod.inl ≫ e.inv
      let pX : M ⟶ X := e.hom ≫ biprod.fst
      have hiX : Function.Injective (iX.hom.restrictScalars k) :=
        (show Function.LeftInverse pX iX from fun x ↦ by
          change (iX ≫ pX) x = x
          simp [iX, pX, Category.assoc]).injective
      letI : Module.Finite k X := Module.Finite.of_injective
        (iX.hom.restrictScalars k) hiX
      let iY : Y ⟶ M := biprod.inr ≫ e.inv
      let pY : M ⟶ Y := e.hom ≫ biprod.snd
      have hiY : Function.Injective (iY.hom.restrictScalars k) :=
        (show Function.LeftInverse pY iY from fun y ↦ by
          change (iY ≫ pY) y = y
          simp [iY, pY, Category.assoc]).injective
      letI : Module.Finite k Y := Module.Finite.of_injective
        (iY.hom.restrictScalars k) hiY
      let eLinear : M ≃ₗ[k] X × Y :=
        ((e.trans (ModuleCat.biprodIsoProd X Y)).toLinearEquiv).restrictScalars k
      have hdim : Module.finrank k M =
          Module.finrank k X + Module.finrank k Y := by
        calc
          Module.finrank k M = Module.finrank k (X × Y) := eLinear.finrank_eq
          _ = Module.finrank k X + Module.finrank k Y := Module.finrank_prod
      have hXnontrivial : Nontrivial X :=
        not_subsingleton_iff_nontrivial.mp
          ((not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hXzero)
      have hYnontrivial : Nontrivial Y :=
        not_subsingleton_iff_nontrivial.mp
          ((not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hYzero)
      letI : Nontrivial X := hXnontrivial
      letI : Nontrivial Y := hYnontrivial
      have hXlt : Module.finrank k X < n := by
        rw [← hn, hdim]
        exact Nat.lt_add_of_pos_right Module.finrank_pos
      have hYlt : Module.finrank k Y < n := by
        rw [← hn, hdim]
        exact Nat.lt_add_of_pos_left Module.finrank_pos
      obtain ⟨dX⟩ := ih (Module.finrank k X) hXlt X rfl
      obtain ⟨dY⟩ := ih (Module.finrank k Y) hYlt Y rfl
      let d := dX.biprod dY
      exact ⟨{
        n := d.n
        summand := d.summand
        indecomposable := d.indecomposable
        isoBiproduct := e.trans d.isoBiproduct }⟩

/-- Every finitely generated module that is finite-dimensional over the
coefficient field admits a finite indecomposable decomposition inside
`FGModuleCat`. -/
theorem finiteIndecomposableDecomposition_fgModule_exists
    [Module.Finite k A] [IsNoetherianRing A]
    (M : FGModuleCat.{v} A) [Module.Finite k M] :
    Nonempty (FiniteIndecomposableDecomposition M) := by
  let U := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  letI : U.Additive := ⟨by intros; rfl⟩
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_module_exists
    (k := k) M.obj
  let summandFG : Fin d.n → FGModuleCat.{v} A := fun j ↦ by
    letI : Module.Finite k (d.summand j) :=
      d.summand_finite (k := k) inferInstance j
    letI : Module.Finite A (d.summand j) :=
      Module.Finite.of_restrictScalars_finite k A (d.summand j)
    exact FGModuleCat.of A (d.summand j)
  have hIndec (j : Fin d.n) : Indecomposable (summandFG j) :=
    MBDVendor.Magnitude.CategoryTheory.indecomposable_of_fully_faithful_additive
      U (summandFG j) (d.indecomposable j)
  exact ⟨{
    n := d.n
    summand := summandFG
    indecomposable := hIndec
    isoBiproduct := U.preimageIso
      (d.isoBiproduct.trans (U.mapBiproduct summandFG).symm) }⟩

end MBDVendor.Magnitude
