module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.HopkinsLevitzki
public import MBDVendor.QSE.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Chosen representatives of indecomposable modules

The manuscript works with a chosen set `ind A` of representatives rather
than with a quotient of all modules by isomorphism.  This file packages that
choice as a type `ι` and a family of finitely generated modules indexed by
`ι`.

The structure is not restricted to representation-finite rings.  Later
finite-type statements add `[Finite ι]`; the arbitrary-type structural
theorems use the same interface without that hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Finitely generated right `A`-modules, represented using Mathlib's
left-module convention over the opposite ring. -/
abbrev RightFGModule (A : Type*) [Ring A] [IsNoetherianRing Aᵐᵒᵖ] :=
  FGModuleCat Aᵐᵒᵖ

/-- A chosen, duplicate-free and complete family of representatives of
indecomposable finitely generated `R`-modules, together with a finite
Krull--Schmidt decomposition for every finitely generated module.

The decomposition field is kept explicit as the interface consumed by the
later closure arguments.  `FiniteLengthDecomposition.lean` constructs it
from finite module length. -/
structure IndecomposableSkeleton
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (ι : Type v) where
  obj : ι → FGModuleCat.{w} R
  indecomposable :
    ∀ i, MBDVendor.QSE.Foundation.IsIndecomposableModule R (obj i)
  finiteLength :
    ∀ i, IsFiniteLength R (obj i)
  eq_of_iso :
    ∀ {i j}, Nonempty (obj i ≅ obj j) → i = j
  complete :
    ∀ X : FGModuleCat.{w} R,
      MBDVendor.QSE.Foundation.IsIndecomposableModule R X →
        ∃ i, Nonempty (X ≅ obj i)
  decomposes :
    ∀ X : FGModuleCat.{w} R,
      ∃ (n : ℕ) (a : Fin n → ι),
        Nonempty (X ≅ biproduct fun t ↦ obj (a t))

set_option linter.checkUnivs false in
/-- A finite chosen skeleton, with its representative type bundled.
The index and module universes intentionally occur together in the bundled
`IndecomposableSkeleton`. -/
structure FiniteIndecomposableSkeleton
    (R : Type u) [Ring R] [IsNoetherianRing R] where
  ι : Type v
  finite_ι : Finite ι
  skeleton : IndecomposableSkeleton.{u, v, w} R ι

namespace FiniteIndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]

instance (M : FiniteIndecomposableSkeleton.{u, v, w} R) :
    Finite M.ι :=
  M.finite_ι

end FiniteIndecomposableSkeleton

namespace IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- The finite direct sum of the representatives indexed by `a`. -/
abbrev sum (n : ℕ) (a : Fin n → ι) : FGModuleCat.{w} R :=
  biproduct fun t ↦ σ.obj (a t)

/-- The chosen representative family has no isomorphic duplicates. -/
theorem eq_iff_nonempty_iso {i j : ι} :
    i = j ↔ Nonempty (σ.obj i ≅ σ.obj j) := by
  constructor
  · rintro rfl
    exact ⟨Iso.refl _⟩
  · exact σ.eq_of_iso

/-- Equality of chosen representative objects forces equality of their
indices. -/
theorem obj_injective : Function.Injective σ.obj := by
  intro i j hij
  apply σ.eq_of_iso
  exact ⟨eqToIso hij⟩

end IndecomposableSkeleton

end MBDVendor.QSE
