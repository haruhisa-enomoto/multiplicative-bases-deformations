module

public import MBDVendor.QSE.CategoryTheory.IyamaLadderComparisonEndpoint
public import MBDVendor.QSE.CategoryTheory.IyamaRightLadderIteration

/-!
# Categorical assembly of Iyama's finite ladder comparison

This file contains only the diagrammatic assembly which remains after
Iyama, *Tau-categories I*, Lemma 6.3.1(2)(i) has supplied the comparison
isomorphisms.  It converts those isomorphisms into the literal finite
invertible-ladder relation used for Nakayama pairs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.RightLadder.Comparison

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]
variable {T : FiniteTauCategoryData C Ind}
  {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}

/-- The actual right-ladder arrow before its zero source summand is
cancelled. -/
def paddedArrow
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ) :
    L.Z i ⊞ L.U i ⟶ L.Y i :=
  biprod.desc (L.b i) (0 : L.U i ⟶ L.Y i)

/-- Negation of the identity as an automorphism. -/
def negIso (X : C) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- Explicit cancellation data for the zero-padded previous vertical arrow.
Keeping the component isomorphisms explicit avoids dependent `Arrow`
projection noise in the matrix calculation. -/
structure PreviousCancellation
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ) where
  sourceIso : L.Z i ⊞ L.U i ≅ L.Z i
  targetIso : L.Y i ≅ L.Y i
  inv_comm : sourceIso.inv ≫ paddedArrow L i =
    L.b i ≫ targetIso.inv

/-- Extract explicit cancellation data from an arrow-category
isomorphism. -/
def PreviousCancellation.ofArrowIso
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ)
    (e : Arrow.mk (paddedArrow L i) ≅ Arrow.mk (L.b i)) :
    PreviousCancellation L i where
  sourceIso := Arrow.leftFunc.mapIso e
  targetIso := Arrow.rightFunc.mapIso e
  inv_comm := e.inv.w

/-- Horizontal target map in the invariant square obtained after cancelling
the previous zero-padded source summand. -/
def squareF
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ)
    (p : PreviousCancellation L i) :
    L.Y (Nat.succ i) ⟶ L.Y i :=
  (-L.f i) ≫ p.targetIso.inv

/-- Horizontal source map in the same invariant square.  The signs are
forced by the convention in `NakayamaLadder.stepComplex`. -/
def squareG
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ)
    (p : PreviousCancellation L i) :
    L.Z (Nat.succ i) ⊞ L.U (Nat.succ i) ⟶ L.Z i ⊞ L.U i :=
  biprod.desc (-L.g i) (L.h i) ≫
    p.sourceIso.inv

/-- The transformed square commutes. -/
theorem square_comm
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ)
    (p : PreviousCancellation L i) :
    paddedArrow L (Nat.succ i) ≫ squareF L i p =
      squareG L i p ≫ paddedArrow L i := by
  have hcomm : L.b (Nat.succ i) ≫ L.f i = L.g i ≫ L.b i :=
    L.comm i
  have hzero : L.h i ≫ L.b i = 0 := L.hzero i
  have hinv : p.sourceIso.inv ≫
      biprod.desc (L.b i) (0 : L.U i ⟶ L.Y i) =
      L.b i ≫ p.targetIso.inv := by
    simpa only [paddedArrow] using p.inv_comm
  apply biprod.hom_ext'
  · simp only [paddedArrow, squareF, squareG,
      biprod.inl_desc_assoc, Preadditive.comp_neg,
      Preadditive.neg_comp, Category.assoc]
    rw [← Category.assoc, hcomm, Category.assoc, ← hinv]
  · simp only [paddedArrow, squareF, squareG,
      biprod.inr_desc_assoc, Category.assoc, zero_comp]
    rw [hinv, ← Category.assoc, hzero]
    simp

/-- The common short complex used by one candidate invertible-ladder
square. -/
def squareComplex
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ)
    (p : PreviousCancellation L i) :
    ShortComplex C :=
  NakayamaLadder.stepComplex
    (Arrow.mk (paddedArrow L i))
    (Arrow.mk (paddedArrow L (Nat.succ i)))
    (squareF L i p) (squareG L i p)
    (square_comm L i p)

/-- Cancelling the previous padded summand turns the explicit constructed
right rung into the common Nakayama-ladder square. -/
def rightStepIsoSquareComplex
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (i : ℕ)
    (p : PreviousCancellation L i) :
    RightLadder.stepComplex (L.b i) (L.b (Nat.succ i))
        (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i) ≅
      squareComplex L i p := by
  let e₁ : L.Z (Nat.succ i) ⊞ L.U (Nat.succ i) ≅
      L.Z (Nat.succ i) ⊞ L.U (Nat.succ i) :=
    Iso.refl _
  let e₂ : L.Y (Nat.succ i) ⊞ L.Z i ≅
      L.Y (Nat.succ i) ⊞ (L.Z i ⊞ L.U i) :=
    biprod.mapIso (negIso _) p.sourceIso.symm
  let e₃ : L.Y i ≅ L.Y i :=
    p.targetIso.symm
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · change e₁.hom ≫
        biprod.lift (-(paddedArrow L (Nat.succ i))) (squareG L i p) =
      (RightLadder.stepComplex (L.b i) (L.b (Nat.succ i))
        (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i)).f ≫ e₂.hom
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [e₁, e₂, negIso, squareG,
          RightLadder.stepComplex, paddedArrow, Category.assoc,
          Preadditive.comp_neg]
      · simp [e₁, e₂, negIso, squareG,
          RightLadder.stepComplex, paddedArrow, Category.assoc,
          Preadditive.neg_comp]
    · apply biprod.hom_ext
      · simp [e₁, e₂, negIso, squareG,
          RightLadder.stepComplex, paddedArrow, Category.assoc,
          Preadditive.comp_neg]
      · simp [e₁, e₂, negIso, squareG,
          RightLadder.stepComplex, paddedArrow, Category.assoc]
  · change e₂.hom ≫
        biprod.desc (squareF L i p) (paddedArrow L i) =
      (RightLadder.stepComplex (L.b i) (L.b (Nat.succ i))
        (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i)).g ≫ e₃.hom
    apply biprod.hom_ext'
    · simp [e₂, e₃, negIso, squareF,
        RightLadder.stepComplex]
    · simp [e₂, e₃, squareF,
        RightLadder.stepComplex]
      simpa only [Category.assoc] using p.inv_comm

/-! ## Finite assembly after the comparison theorem -/

/-- The exact categorical output needed from Iyama's comparison argument.

For step `i`, `previousCancellation i` cancels the zero summand in the
constructed right arrow `a_i`.  The `leftSquareIso` field says that the same
square is a chosen left mesh at the source of `a_(i+1)`.  In an application
to a length-`n` left ladder, this field is obtained from its rung
`n-i-1`, so the left ladder is read in reverse.  Finally, `terminalIso`
identifies the right terminal arrow `a_n` with the left zero boundary.

The nonzero endpoint part of Tau I, 6.3.1(2)(i) is proved separately in
`IyamaLadderComparisonEndpoint`.  Constructing the remaining reversed
cross-mesh isomorphisms is kept explicit in this certificate. -/
structure Certificate
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (n : ℕ)
    {Xₙ Yₙ : C} (finish : Xₙ ⟶ Yₙ) where
  previousCancellation : ∀ i : Fin n, PreviousCancellation L i.val
  leftSquareIso : ∀ i : Fin n, Nonempty
    (T.leftMesh (L.Z i.succ.val ⊞ L.U i.succ.val) ≅
      squareComplex L i.val (previousCancellation i))
  terminalIso : Nonempty
    (Arrow.mk (paddedArrow L n) ≅ Arrow.mk finish)

/-- A comparison certificate assembles the constructed right prefix into an
invertible ladder of the same distance. -/
theorem Certificate.invertibleLadderOfDistance
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (n : ℕ)
    {Xₙ Yₙ : C} {finish : Xₙ ⟶ Yₙ}
    (K : Certificate L n finish) :
    NakayamaLadder.InvertibleLadderOfDistance T n a₀ finish := by
  let X : Fin (n + 1) → C :=
    fun i ↦ L.Z i.val ⊞ L.U i.val
  let Y : Fin (n + 1) → C := fun i ↦ L.Y i.val
  let a : ∀ i, X i ⟶ Y i := fun i ↦ paddedArrow L i.val
  refine ⟨X, Y, a, ?_, ?_, ?_⟩
  · change Nonempty (Arrow.mk a₀ ≅ Arrow.mk (paddedArrow L 0))
    simpa only [paddedArrow] using L.initialIso
  · simpa only [a, X, Y, Fin.val_last] using K.terminalIso
  · intro i
    refine ⟨squareF L i.val (K.previousCancellation i),
      squareG L i.val (K.previousCancellation i),
      square_comm L i.val (K.previousCancellation i), ?_, ?_⟩
    · obtain ⟨e⟩ := L.meshIso i.val
      exact ⟨e.trans (rightStepIsoSquareComplex L i.val
        (K.previousCancellation i))⟩
    · simpa only [X, Y, a, Fin.val_castSucc, Fin.val_succ,
        squareComplex, Nat.succ_eq_add_one] using K.leftSquareIso i

/-- The assembly retains the terminal arrow-category isomorphism explicitly,
which is useful when the caller needs both conclusions of Tau I, 6.3.1. -/
theorem Certificate.invertibleLadderOfDistance_and_terminalIso
    (L : InfiniteSpecialRightLadder T.toFiniteRightTauCategoryData a₀)
    (n : ℕ)
    {Xₙ Yₙ : C} {finish : Xₙ ⟶ Yₙ}
    (K : Certificate L n finish) :
    NakayamaLadder.InvertibleLadderOfDistance T n a₀ finish ∧
      Nonempty (Arrow.mk (paddedArrow L n) ≅ Arrow.mk finish) :=
  ⟨K.invertibleLadderOfDistance L n, K.terminalIso⟩

end MBDVendor.QSE.Iyama.RightLadder.Comparison
