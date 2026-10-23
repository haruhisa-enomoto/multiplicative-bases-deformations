module

public import MBDVendor.QSE.CategoryTheory.IyamaLadderComparisonCertificate
public import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtDirectFinite

/-!
# Finite Krull--Schmidt specialization of ladder comparison

This is the exact bridge from the general terminal cycle to the categorical
finiteness recorded in `FiniteTauCategoryData`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.TauSequenceComparison

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- In a finite tau-category, a terminal essential-arrow identification
canonically supplies the first cancellation datum for the genuine right
ladder. -/
theorem initialPreviousCancellation_of_terminalEssentialIso_finite
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T
      ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R (n + 1)).U 0)
      (n + 1))
    (hterminal : Nonempty
      (Arrow.mk (L.b (Fin.last (n + 1))) ≅ Arrow.mk a₀)) :
    Nonempty (RightLadder.Comparison.PreviousCancellation R 0) := by
  apply initialPreviousCancellation_of_terminalEssentialIso R n L
  · intro X e he
    letI : IsSplitMono e := he
    exact T.isIso_of_isSplitMono_end e
  · exact hterminal

/-- Finite Krull--Schmidt specialization of the full comparison-certificate
constructor. -/
theorem nonempty_certificate_to_leftZeroBoundary_finite
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ U₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk
          ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
            (Fin.last n)))) :
    Nonempty (RightLadder.Comparison.Certificate R n (L.b 0)) := by
  apply nonempty_certificate_to_leftZeroBoundary_of_boundaryEmbedding
    R n L E
  · intro X e he
    letI : IsSplitMono e := he
    exact T.isIso_of_isSplitMono_end e
  · exact hlast

/-- More directly usable endpoint form: identifying the terminal essential
left arrow with the genuine initial right-ladder arrow automatically closes
the reversed last diagonal via `R.initialIso`. -/
theorem nonempty_certificate_to_leftZeroBoundary_of_terminalEssentialIso_finite
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ U₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hterminal : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅ Arrow.mk a₀)) :
    Nonempty (RightLadder.Comparison.Certificate R n (L.b 0)) := by
  apply nonempty_certificate_to_leftZeroBoundary_finite T R n L E
  exact terminalIso_to_reversedInitialPadding R n L hterminal

end MBDVendor.QSE.Iyama.TauSequenceComparison
