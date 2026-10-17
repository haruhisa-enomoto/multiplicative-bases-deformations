import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite displayed decompositions into indecomposables

This small generic interface and its biproduct combiner are adapted from the
Cartan formalization's `ClosedRayChain/GenericFiniteness.lean` at
homological-conjectures commit `eade4e75`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.Magnitude.CategoryTheory

universe v u

/-- A concrete finite biproduct decomposition into indecomposable objects. -/
structure FiniteIndecomposableDecomposition
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C] (X : C) where
  n : ℕ
  summand : Fin n → C
  indecomposable : ∀ j, Indecomposable (summand j)
  isoBiproduct : X ≅ ⨁ summand

/-- The one-term displayed decomposition of an indecomposable object. -/
def FiniteIndecomposableDecomposition.singleton
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    (X : C) (hX : Indecomposable X) :
    FiniteIndecomposableDecomposition X where
  n := 1
  summand := fun _ ↦ X
  indecomposable := fun _ ↦ hX
  isoBiproduct := (biproductUniqueIso (fun _ : Fin 1 ↦ X)).symm

/-- The empty biproduct is isomorphic to every zero object. -/
def zeroIsoEmptyBiproduct
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) (hX : IsZero X) :
    X ≅ ⨁ (fun i : Fin 0 ↦ Fin.elim0 i) where
  hom := 0
  inv := 0
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 i

/-- Concatenate two displayed finite biproduct decompositions. -/
def FiniteIndecomposableDecomposition.biprod
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    {X Y : C}
    (dX : FiniteIndecomposableDecomposition X)
    (dY : FiniteIndecomposableDecomposition Y) :
    FiniteIndecomposableDecomposition (X ⊞ Y) := by
  classical
  let N : Fin (dX.n + dY.n) → C := fun i ↦
    Sum.elim dX.summand dY.summand (finSumFinEquiv.symm i)
  let I : WalkingPair → Type
    | WalkingPair.left => Fin dX.n
    | WalkingPair.right => Fin dY.n
  let G : (i : WalkingPair) → I i → C
    | WalkingPair.left => dX.summand
    | WalkingPair.right => dY.summand
  let sigmaEquiv : (Σ i, I i) ≃ Fin (dX.n + dY.n) := {
    toFun
      | ⟨WalkingPair.left, j⟩ => finSumFinEquiv (Sum.inl j)
      | ⟨WalkingPair.right, j⟩ => finSumFinEquiv (Sum.inr j)
    invFun i :=
      match finSumFinEquiv.symm i with
      | Sum.inl j => ⟨WalkingPair.left, j⟩
      | Sum.inr j => ⟨WalkingPair.right, j⟩
    left_inv := by
      rintro ⟨i, j⟩
      cases i <;> simp [I]
    right_inv := by
      intro i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i <;> simp [I] }
  letI : ∀ i, HasBiproduct (G i) := fun i ↦ by
    cases i <;> simp only [G, I] <;> infer_instance
  let pairToOuter :
      (⨁ dX.summand) ⊞ (⨁ dY.summand) ≅
        ⨁ (fun i ↦ ⨁ G i) :=
    (biproduct.uniqueUpToIso
      (pairFunction (⨁ dX.summand) (⨁ dY.summand))
      ((BinaryBicone.toBiconeIsBilimit _).symm
        (BinaryBiproduct.isBilimit
          (⨁ dX.summand) (⨁ dY.summand)))).trans
      (biproduct.mapIso fun i ↦ by
        cases i
        · change (⨁ dX.summand) ≅ (⨁ dX.summand)
          exact Iso.refl _
        · change (⨁ dY.summand) ≅ (⨁ dY.summand)
          exact Iso.refl _)
  let e : (⨁ dX.summand) ⊞ (⨁ dY.summand) ≅ ⨁ N :=
    pairToOuter |>.trans (biproductBiproductIso I G) |>.trans
      (biproduct.whiskerEquiv
        (f := fun q : Σ i, I i ↦ G q.1 q.2) (g := N) sigmaEquiv fun q ↦
        eqToIso (by
          rcases q with ⟨i, j⟩
          cases i <;> simp [N, G, I, sigmaEquiv]))
  exact {
    n := dX.n + dY.n
    summand := N
    indecomposable := by
      intro i
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      · simpa [N] using dX.indecomposable j
      · simpa [N] using dY.indecomposable j
    isoBiproduct :=
      (biprod.mapIso dX.isoBiproduct dY.isoBiproduct).trans e }

/-- Transport a displayed decomposition across an isomorphism. -/
def FiniteIndecomposableDecomposition.ofIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    {X Y : C} (e : X ≅ Y) (d : FiniteIndecomposableDecomposition Y) :
    FiniteIndecomposableDecomposition X where
  n := d.n
  summand := d.summand
  indecomposable := d.indecomposable
  isoBiproduct := e ≪≫ d.isoBiproduct

universe v' u'

/-- An additive functor carries a displayed finite indecomposable
decomposition to one in the target whenever it preserves the
indecomposability of the displayed summands. -/
def FiniteIndecomposableDecomposition.mapOfIndecomposable
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasBinaryBiproducts D] [HasFiniteBiproducts D]
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    (F : C ⥤ D) [F.Additive] {X : C}
    (d : FiniteIndecomposableDecomposition X)
    (h : ∀ i, Indecomposable (F.obj (d.summand i))) :
    FiniteIndecomposableDecomposition (F.obj X) where
  n := d.n
  summand := fun i ↦ F.obj (d.summand i)
  indecomposable := h
  isoBiproduct := F.mapIso d.isoBiproduct ≪≫ F.mapBiproduct d.summand

/-- An additive functor out of the opposite category carries a displayed
finite indecomposable decomposition to the corresponding dual
decomposition.  Opposite passage turns the source biproduct, viewed as a
coproduct, into a product; additivity then identifies the resulting product
with the target biproduct. -/
def FiniteIndecomposableDecomposition.mapOpOfIndecomposable
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasBinaryBiproducts D] [HasFiniteBiproducts D]
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    (F : Cᵒᵖ ⥤ D) [F.Additive] {X : C}
    (d : FiniteIndecomposableDecomposition X)
    (h : ∀ i, Indecomposable (F.obj (Opposite.op (d.summand i)))) :
    FiniteIndecomposableDecomposition (F.obj (Opposite.op X)) := by
  letI : HasFiniteBiproducts Cᵒᵖ :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  exact {
    n := d.n
    summand := fun i ↦ F.obj (Opposite.op (d.summand i))
    indecomposable := h
    isoBiproduct :=
      F.mapIso
          (d.isoBiproduct.op.symm ≪≫
            (biproduct.isoCoproduct d.summand).op.symm ≪≫
            opCoproductIsoProduct d.summand ≪≫
            (biproduct.isoProduct
              (fun i ↦ Opposite.op (d.summand i))).symm) ≪≫
        F.mapBiproduct (fun i ↦ Opposite.op (d.summand i)) }

/-- A natural-number-valued rank which is positive on nonzero objects and
additive across binary biproduct decompositions guarantees existence of a
finite decomposition into indecomposable objects. -/
theorem finiteIndecomposableDecomposition_of_rank
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] [HasFiniteBiproducts C]
    (rank : C → ℕ)
    (zero_of_rank_eq_zero : ∀ X, rank X = 0 → IsZero X)
    (rank_biprod : ∀ {X Y Z : C},
      (X ≅ (Y ⊞ Z : C)) → rank X = rank Y + rank Z) :
    ∀ X : C, Nonempty (FiniteIndecomposableDecomposition X) := by
  intro X
  induction h : rank X using Nat.strong_induction_on generalizing X with
  | h n ih =>
      by_cases hXzero : IsZero X
      · exact ⟨{
          n := 0
          summand := fun i ↦ Fin.elim0 i
          indecomposable := fun i ↦ Fin.elim0 i
          isoBiproduct := zeroIsoEmptyBiproduct X hXzero }⟩
      · by_cases hXindec : Indecomposable X
        · exact ⟨FiniteIndecomposableDecomposition.singleton X hXindec⟩
        · have hsplit : ¬ ∀ Y Z,
              (X ≅ (Y ⊞ Z : C)) → IsZero Y ∨ IsZero Z := by
            intro hs
            exact hXindec ⟨hXzero, hs⟩
          push Not at hsplit
          obtain ⟨Y, Z, e, hY, hZ⟩ := hsplit
          have hrank := rank_biprod e
          have hYpos : 0 < rank Y := by
            exact Nat.pos_of_ne_zero
              (fun h0 ↦ hY (zero_of_rank_eq_zero Y h0))
          have hZpos : 0 < rank Z := by
            exact Nat.pos_of_ne_zero
              (fun h0 ↦ hZ (zero_of_rank_eq_zero Z h0))
          have hYlt : rank Y < n := by omega
          have hZlt : rank Z < n := by omega
          obtain ⟨dY⟩ := ih (rank Y) hYlt Y rfl
          obtain ⟨dZ⟩ := ih (rank Z) hZlt Z rfl
          exact ⟨FiniteIndecomposableDecomposition.ofIso e (dY.biprod dZ)⟩

/-- An additive functor is essentially surjective if every target object has
a finite indecomposable decomposition and every indecomposable target object
has a lift. -/
theorem functor_essSurj_of_indec_dense
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasBinaryBiproducts D]
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive]
    (decomposition : ∀ Y : D, Nonempty (FiniteIndecomposableDecomposition Y))
    (dense : ∀ Y : D, Indecomposable Y →
      ∃ X : C, Nonempty (F.obj X ≅ Y)) :
    F.EssSurj := by
  constructor
  intro Y
  obtain ⟨d⟩ := decomposition Y
  choose X e using fun j ↦ dense (d.summand j) (d.indecomposable j)
  refine ⟨⨁ X, ⟨?_⟩⟩
  exact F.mapBiproduct X ≪≫
    biproduct.mapIso (fun j ↦ Classical.choice (e j)) ≪≫
      d.isoBiproduct.symm

end MBDVendor.Magnitude.CategoryTheory
