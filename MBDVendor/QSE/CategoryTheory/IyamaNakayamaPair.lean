import Mathlib.CategoryTheory.Preadditive.Biproducts
import MBDVendor.QSE.CategoryTheory.FiniteTauCategory

/-!
# Finite invertible ladders and Nakayama pairs

This file formalizes the diagrammatic definition in Iyama,
*Tau-categories II*, Definition 2.1.  A step from
`aPrev : XPrev ⟶ YPrev` to `aNext : XNext ⟶ YNext` consists of maps

`f : YNext ⟶ YPrev`, `g : XNext ⟶ XPrev`

making the square commute, such that

`XNext ⟶ YNext ⨁ XPrev ⟶ YPrev`

with maps `(-aNext, g)` and `(f, aPrev)` is simultaneously the right
tau-sequence ending at `YPrev` and the left tau-sequence starting at `XNext`.

The endpoints of a finite ladder are identified in the arrow category.  This
is the invariant form of Iyama's literal equalities `a₀ = muMinus A` and
`aₙ = muPlus B`, and accommodates the chosen representatives in
`FiniteTauCategoryData`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

namespace NakayamaLadder

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- The short complex in one square of Iyama's invertible-ladder diagram.

The sign convention is exactly the one in *Tau-categories II*, Definition
2.1: the first map has components `(-aNext, g)`, and the second has components
`(f, aPrev)`. -/
def stepComplex (aPrev aNext : Arrow C)
    (f : aNext.right ⟶ aPrev.right)
    (g : aNext.left ⟶ aPrev.left)
    (comm : aNext.hom ≫ f = g ≫ aPrev.hom) : ShortComplex C :=
  ShortComplex.mk
    (biprod.lift (-aNext.hom) g)
    (biprod.desc f aPrev.hom)
    (by
      rw [biprod.lift_desc, Preadditive.neg_comp, comm]
      exact neg_add_cancel (g ≫ aPrev.hom))

/-- One invertible ladder step in the chosen meshes of `T`.

The two explicit short-complex isomorphisms are the literal categorical
rendering of Iyama's `(YPrev] = [XNext)` condition.  The facts that the source
complexes are a right and a left tau-sequence are supplied by `T.rightTau` and
`T.leftTau`; they need not be duplicated in this predicate. -/
def InvertibleLadderStep (T : FiniteTauCategoryData C Ind)
    {XPrev YPrev XNext YNext : C}
    (aPrev : XPrev ⟶ YPrev) (aNext : XNext ⟶ YNext) : Prop :=
  ∃ (f : YNext ⟶ YPrev) (g : XNext ⟶ XPrev)
    (comm : aNext ≫ f = g ≫ aPrev),
      Nonempty
        (T.rightMesh YPrev ≅
          stepComplex (Arrow.mk aPrev) (Arrow.mk aNext) f g comm) ∧
        Nonempty
          (T.leftMesh XNext ≅
            stepComplex (Arrow.mk aPrev) (Arrow.mk aNext) f g comm)

/-- An invertible ladder of a specified distance.

The family has `n + 1` vertical arrows.  For `i : Fin n`, `castSucc i` is the
previous arrow and `succ i` is the next arrow.  The first and last arrows are
only required to be isomorphic to the supplied endpoints in `Arrow C`, which
is invariant under choices of representatives. -/
def InvertibleLadderOfDistance (T : FiniteTauCategoryData C Ind) (n : ℕ)
    {X₀ Y₀ Xₙ Yₙ : C} (start : X₀ ⟶ Y₀) (finish : Xₙ ⟶ Yₙ) : Prop :=
  ∃ (X Y : Fin (n + 1) → C) (a : ∀ i, X i ⟶ Y i),
    Nonempty (Arrow.mk start ≅ Arrow.mk (a 0)) ∧
      Nonempty (Arrow.mk (a (Fin.last n)) ≅ Arrow.mk finish) ∧
        ∀ i : Fin n,
          InvertibleLadderStep T (a i.castSucc) (a i.succ)

/-- Two arrows are connected by a finite invertible ladder. -/
def InvertibleLadder (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ Xₙ Yₙ : C} (start : X₀ ⟶ Y₀) (finish : Xₙ ⟶ Yₙ) : Prop :=
  ∃ n : ℕ, InvertibleLadderOfDistance T n start finish

/-- The exact projective-support consequence of Iyama's invertible-ladder
theory: every right mesh used by a finite ladder ends at an object supported
on nonprojective indecomposables.

For a family indexed by `Fin (n + 1)`, step `i : Fin n` uses the right mesh
ending at `Y i.castSucc`; the terminal object `Y (Fin.last n)` is deliberately
absent.  In *Tau-categories I*, 6.2.1 this is the implication from an
invertible ladder to `Y_i|ind⁺₁ C = 0` for `i < n`. -/
def HasNonprojectiveRightSupport (T : FiniteTauCategoryData C Ind) : Prop :=
  ∀ {n : ℕ} (X Y : Fin (n + 1) → C) (a : ∀ i, X i ⟶ Y i),
    (∀ i : Fin n,
      InvertibleLadderStep T (a i.castSucc) (a i.succ)) →
    ∀ i : Fin n, T.SupportedOnNonprojectives (Y i.castSucc)

/-- Distance zero is precisely the endpoint-isomorphism case needed by the
finite definition. -/
theorem invertibleLadderOfDistance_zero_of_arrowIso
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ Xₙ Yₙ : C} {start : X₀ ⟶ Y₀} {finish : Xₙ ⟶ Yₙ}
    (e : Arrow.mk start ≅ Arrow.mk finish) :
    InvertibleLadderOfDistance T 0 start finish := by
  refine ⟨fun _ ↦ X₀, fun _ ↦ Y₀, fun _ ↦ start,
    ⟨Iso.refl _⟩, ⟨e⟩, ?_⟩
  exact Fin.elim0

/-- Arrow-isomorphic endpoints are connected by an invertible ladder. -/
theorem invertibleLadder_of_arrowIso
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ Xₙ Yₙ : C} {start : X₀ ⟶ Y₀} {finish : Xₙ ⟶ Yₙ}
    (e : Arrow.mk start ≅ Arrow.mk finish) :
    InvertibleLadder T start finish :=
  ⟨0, invertibleLadderOfDistance_zero_of_arrowIso T e⟩

end NakayamaLadder

namespace FiniteTauCategoryData

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteTauCategoryData C Ind)

/-- Iyama's diagrammatic Nakayama-pair relation at a fixed distance. -/
def NakayamaPairOfDistance (A B : Ind) (n : ℕ) : Prop :=
  NakayamaLadder.InvertibleLadderOfDistance T n
    (T.muMinus A) (T.muPlus B)

/-- A Nakayama pair is a pair of indecomposable labels whose boundary mesh
maps are connected by a finite invertible ladder. -/
def NakayamaPair (A B : Ind) : Prop :=
  NakayamaLadder.InvertibleLadder T (T.muMinus A) (T.muPlus B)

theorem nakayamaPair_iff_exists_distance (A B : Ind) :
    T.NakayamaPair A B ↔ ∃ n : ℕ, T.NakayamaPairOfDistance A B n :=
  Iff.rfl

/-- The still-open extraction theorem, specialized to the genuine finite
ladder relation.  This is a proposition, not an assumed field. -/
def HasMuMinusNakayamaExtraction : Prop :=
  T.MuMinusNakayamaExtraction T.NakayamaPair

end FiniteTauCategoryData

end MBDVendor.QSE.Iyama
