module

public import MBDVendor.QSE.RepresentationTheory.IrreducibleRadicalQuotient
public import Mathlib.Algebra.Category.ModuleCat.Algebra
/-!
# The linear irreducible-morphism space

This file upgrades the field-free quotient `rad(X,Y) / rad²(X,Y)` to a
vector-space quotient over a central ground field.  It supplies the exact
object whose finrank occurs in the multiplicity-one theorem for a
representation-finite algebra.

No finite-dimensionality, directedness, algebra presentation, or module
classification is used in the construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

universe u uIota

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [IsNoetherianRing R]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)
  [∀ i : Iota, Module K (sigma.obj i)]
  [∀ i : Iota, IsScalarTower K R (sigma.obj i)]

/-- The square of the categorical radical as a `K`-subspace of the
`R`-linear Hom-space. -/
def radicalSquareHomSubmodule (x y : Iota) :
    Submodule K (sigma.obj x →ₗ[R] sigma.obj y) where
  carrier := fun f =>
    (ConcreteCategory.ofHom f : sigma.obj x ⟶ sigma.obj y) ∈
      sigma.radicalSquareHomAddSubgroup x y
  zero_mem' := by
    have hz : sigma.HasRadicalSquareFactorization
        (0 : sigma.obj x ⟶ sigma.obj y) := by
      change (0 : sigma.obj x ⟶ sigma.obj y) ∈
        sigma.radicalSquareHomAddSubgroup x y
      exact (sigma.radicalSquareHomAddSubgroup x y).zero_mem
    have heq :
        (ConcreteCategory.ofHom (0 : sigma.obj x →ₗ[R] sigma.obj y) :
          sigma.obj x ⟶ sigma.obj y) = 0 := by
      apply FGModuleCat.hom_ext
      rfl
    show sigma.HasRadicalSquareFactorization
      (ConcreteCategory.ofHom (0 : sigma.obj x →ₗ[R] sigma.obj y))
    rw [heq]
    exact hz
  add_mem' := by
    intro f g hf hg
    exact (sigma.radicalSquareHomAddSubgroup x y).add_mem hf hg
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · subst c
      rw [zero_smul]
      have heq :
          (ConcreteCategory.ofHom (0 : sigma.obj x →ₗ[R] sigma.obj y) :
            sigma.obj x ⟶ sigma.obj y) = 0 := by
        apply FGModuleCat.hom_ext
        rfl
      show sigma.HasRadicalSquareFactorization
        (ConcreteCategory.ofHom (0 : sigma.obj x →ₗ[R] sigma.obj y))
      rw [heq]
      exact (sigma.radicalSquareHomAddSubgroup x y).zero_mem
    · obtain ⟨M, g, h, hg, hh, hcomp⟩ := hf
      letI : Module K M := Module.restrictScalars K R M
      letI : IsScalarTower K R M :=
        IsScalarTower.restrictScalars K R M
      refine ⟨M, c • g, h, ?_, hh, ?_⟩
      · intro hsplit
        obtain ⟨sm⟩ := hsplit.exists_splitMono
        apply hg
        exact IsSplitMono.mk'
          { retraction := c • sm.retraction
            id := by
              simpa only [Linear.comp_smul, Linear.smul_comp] using sm.id }
      · calc
          (c • g) ≫ h = c • (g ≫ h) := by simp
          _ = c • ConcreteCategory.ofHom f := by rw [hcomp]
          _ = ConcreteCategory.ofHom (c • f) := by
            apply FGModuleCat.hom_ext
            ext m
            change algebraMap K R c • f m = c • f m
            exact IsScalarTower.algebraMap_smul R c (f m)

@[simp] theorem mem_radicalSquareHomSubmodule_iff
    {x y : Iota} (f : sigma.obj x →ₗ[R] sigma.obj y) :
    f ∈ sigma.radicalSquareHomSubmodule (K := K) x y ↔
      sigma.HasRadicalSquareFactorization
        (ConcreteCategory.ofHom f : sigma.obj x ⟶ sigma.obj y) :=
  Iff.rfl

/-- The linear denominator `rad²(X,Y)` regarded as a subspace of
`rad(X,Y)`. -/
def radicalSquareInRadicalSubmodule (x y : Iota) :
    Submodule K (sigma.radicalHom (K := K) x y) :=
  (sigma.radicalSquareHomSubmodule (K := K) x y).comap
    (sigma.radicalHom (K := K) x y).subtype

/-- The manuscript's `K`-linear irreducible-morphism space
`Irr(X,Y) = rad(X,Y) / rad²(X,Y)`. -/
abbrev irreducibleHomSpace (x y : Iota) :=
  (sigma.radicalHom (K := K) x y) ⧸
    sigma.radicalSquareInRadicalSubmodule (K := K) x y

/-- The linear irreducible-morphism space is nontrivial exactly when there
is an irreducible morphism between the two indecomposables. -/
theorem nontrivial_irreducibleHomSpace_iff_hasIrreducibleMorphism
    (x y : Iota) :
    Nontrivial (sigma.irreducibleHomSpace (K := K) x y) ↔
      HasIrreducibleMorphism (sigma.obj x) (sigma.obj y) := by
  rw [Submodule.Quotient.nontrivial_iff]
  constructor
  · intro hproper
    obtain ⟨f, hf⟩ :=
      SetLike.exists_not_mem_of_ne_top
        (sigma.radicalSquareInRadicalSubmodule (K := K) x y) hproper
    refine ⟨ConcreteCategory.ofHom f.1, ?_⟩
    apply (sigma.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare
      (ConcreteCategory.ofHom f.1)).2
    exact ⟨f.2, hf⟩
  · rintro ⟨f, hf⟩ htop
    obtain ⟨hfrad, hfsquare⟩ :=
      (sigma.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare
        f).1 hf
    let fr : sigma.radicalHom (K := K) x y := ⟨f.hom.hom, hfrad⟩
    have hmem : fr ∈
        sigma.radicalSquareInRadicalSubmodule (K := K) x y := by
      rw [htop]
      exact Set.mem_univ _
    exact hfsquare hmem

/-- Manuscript-style orientation of the nonzero-space criterion. -/
theorem hasIrreducibleMorphism_iff_nontrivial_irreducibleHomSpace
    (x y : Iota) :
    HasIrreducibleMorphism (sigma.obj x) (sigma.obj y) ↔
      Nontrivial (sigma.irreducibleHomSpace (K := K) x y) :=
  (sigma.nontrivial_irreducibleHomSpace_iff_hasIrreducibleMorphism
    (K := K) x y).symm

end MBDVendor.QSE.IndecomposableSkeleton
