module

public import MBDVendor.QSE.CategoryTheory.IyamaReversedRightPrefix

/-!
# Actual-index certificate assembly for a genuine right ladder

This file combines the pure `Fin.rev` adapter with the abstract reversed-rung
propagation.  It remains entirely categorical.
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

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Pointwise arrows at equal indices are isomorphic in the arrow category.
Writing this by equality elimination avoids exposing dependent transports in
later statements. -/
def familyArrowIso
    (Z Y : ℕ → C) (b : ∀ k, Z k ⟶ Y k)
    {m n : ℕ} (e : m = n) : Arrow.mk (b m) ≅ Arrow.mk (b n) := by
  subst n
  exact Iso.refl _

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- A family of short complexes takes equal indices to isomorphic
complexes. -/
def familyShortComplexIso
    (S : ℕ → ShortComplex C) {m n : ℕ} (e : m = n) :
    S m ≅ S n := by
  subst n
  exact Iso.refl _

/-- The genuine displayed right-ladder step at a natural-number index. -/
def genuineRightStep
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (i : ℕ) :
    ShortComplex C :=
  RightLadder.stepComplex
    (R.b i) (R.b (i + 1)) (R.f i) (R.g i) (R.h i)
    (R.comm i) (R.hzero i)

/-- Forgetting the reversed-prefix wrapper at one index changes no arrow. -/
def ofInfiniteSpecialRightLadder_essentialArrowIso_at
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    (n : ℕ) (j : Fin (n + 1)) :
    Arrow.mk
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).b j) ≅
      Arrow.mk (R.b j.rev.val) :=
  Iso.refl _

/-- The same pointwise identification for zero-padded arrows. -/
def ofInfiniteSpecialRightLadder_paddedArrowIso_at
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    (n : ℕ) (j : Fin (n + 1)) :
    Arrow.mk
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow j) ≅
      Arrow.mk (RightLadder.Comparison.paddedArrow R j.rev.val) :=
  Iso.refl _

/-- The last arrow of a reversed finite window is the original arrow at
index zero. -/
def ofInfiniteSpecialRightLadder_essentialArrowIso_last
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ) :
    Arrow.mk
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).b
          (Fin.last n)) ≅
      Arrow.mk (R.b 0) := by
  change Arrow.mk (R.b ((Fin.last n).rev.val)) ≅ Arrow.mk (R.b 0)
  exact familyArrowIso R.Z R.Y R.b (by simp)

/-- At the last reversed index, the aligned padded arrow is literally the
initial padded arrow of the genuine right ladder. -/
def ofInfiniteSpecialRightLadder_paddedArrowIso_last
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ) :
    Arrow.mk
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
          (Fin.last n)) ≅
      Arrow.mk (RightLadder.Comparison.paddedArrow R 0) := by
  let padded : ∀ k, R.Z k ⊞ R.U k ⟶ R.Y k := fun k ↦
    RightLadder.Comparison.paddedArrow R k
  change Arrow.mk (padded ((Fin.last n).rev.val)) ≅
    Arrow.mk (padded 0)
  exact familyArrowIso (fun k ↦ R.Z k ⊞ R.U k) R.Y padded (by simp)

/-- An isomorphism from the terminal essential left arrow to the genuine
initial arrow closes the reversed comparison at its final index. -/
theorem terminalIso_to_reversedInitialPadding
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ U₀ : C}
    {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (hterminal : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅ Arrow.mk a₀)) :
    Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk
          ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
            (Fin.last n))) := by
  obtain ⟨eTerminal⟩ := hterminal
  obtain ⟨eInitial⟩ := R.initialIso
  exact ⟨eTerminal ≪≫ eInitial ≪≫
    (ofInfiniteSpecialRightLadder_paddedArrowIso_last R n).symm⟩

/-- The terminal four-cycle of a nonempty reversed window cancels the zero
summand in the genuine initial right arrow.  This is the first
`PreviousCancellation` datum required by the finite comparison certificate.

The direct-finiteness argument is a parameter here; for a finite tau-category
it is discharged by `FiniteTauCategoryData.isIso_of_isSplitMono_end`. -/
theorem initialPreviousCancellation_of_terminalEssentialIso
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T
      ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R (n + 1)).U 0)
      (n + 1))
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hterminal : Nonempty
      (Arrow.mk (L.b (Fin.last (n + 1))) ≅ Arrow.mk a₀)) :
    Nonempty (RightLadder.Comparison.PreviousCancellation R 0) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R (n + 1)
  have hclose : Nonempty
      (Arrow.mk (L.b (Fin.last (n + 1))) ≅
        Arrow.mk (RR.paddedArrow (Fin.last (n + 1)))) :=
    terminalIso_to_reversedInitialPadding R (n + 1) L hterminal
  let i : Fin (n + 1) := Fin.last n
  have hi : i.succ = Fin.last (n + 1) := by
    apply Fin.ext
    simp [i]
  have hcloseAt : Nonempty
      (Arrow.mk (L.b i.succ) ≅ Arrow.mk (RR.paddedArrow i.succ)) := by
    rw [hi]
    exact hclose
  obtain ⟨hprevious, _, _, _⟩ :=
    terminal_four_cycle_adjacent_isos RR L i hfinite hcloseAt
  obtain ⟨ePrevious⟩ := hprevious
  refine ⟨RightLadder.Comparison.PreviousCancellation.ofArrowIso R 0 ?_⟩
  rw [hi] at ePrevious
  exact
    (ofInfiniteSpecialRightLadder_paddedArrowIso_last R (n + 1)).symm ≪≫
      ePrevious ≪≫
      ofInfiniteSpecialRightLadder_essentialArrowIso_last R (n + 1)

/-! ## Actual-index certificate data -/

/-- Reindex every aligned cancellation isomorphism back to the corresponding
natural-number step of the genuine right ladder. -/
theorem actualPreviousCancellationIso_all_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ U₀ : C}
    {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk
          ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
            (Fin.last n))))
    (i : Fin n) :
    Nonempty
      (Arrow.mk (RightLadder.Comparison.paddedArrow R i.val) ≅
        Arrow.mk (R.b i.val)) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R n
  let j : Fin n := i.rev
  let k : Fin (n + 1) := j.succ
  obtain ⟨eAligned⟩ :=
    reversedPreviousCancellationIso_all_of_boundaryEmbedding
      RR L E hfinite hlast j
  let padded : ∀ r, R.Z r ⊞ R.U r ⟶ R.Y r := fun r ↦
    RightLadder.Comparison.paddedArrow R r
  let ePadAt := ofInfiniteSpecialRightLadder_paddedArrowIso_at R n k
  let eEssentialAt :=
    ofInfiniteSpecialRightLadder_essentialArrowIso_at R n k
  have hk : k.rev.val = i.val := by
    dsimp only [k]
    rw [Fin.rev_succ]
    simp [j]
  let ePadIndex : Arrow.mk (padded k.rev.val) ≅
      Arrow.mk (padded i.val) :=
    familyArrowIso (fun r ↦ R.Z r ⊞ R.U r) R.Y padded hk
  let eEssentialIndex : Arrow.mk (R.b k.rev.val) ≅
      Arrow.mk (R.b i.val) :=
    familyArrowIso R.Z R.Y R.b hk
  exact ⟨(ePadAt ≪≫ ePadIndex).symm ≪≫ eAligned ≪≫
    eEssentialAt ≪≫ eEssentialIndex⟩

/-- Reindex every aligned cross-mesh isomorphism back to the corresponding
genuine right-ladder step. -/
theorem actualReversedStepIso_all_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ U₀ : C}
    {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk
          ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
            (Fin.last n))))
    (i : Fin n) :
    Nonempty
      (LeftLadder.stepComplex
          (L.b i.rev.castSucc) (L.b i.rev.succ)
          (L.f i.rev) (L.g i.rev) (L.h i.rev)
          (L.comm i.rev) (L.hzero i.rev) ≅
        genuineRightStep R i.val) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R n
  let j : Fin n := i.rev
  obtain ⟨eAligned⟩ :=
    reversedStepIso_all_of_boundaryEmbedding RR L E hfinite hlast j
  let eTransport :=
    ReversedRightPrefix.ofInfiniteSpecialRightLadder_stepIso R n j
  let eIndex : genuineRightStep R j.rev.val ≅
      genuineRightStep R i.val :=
    familyShortComplexIso (genuineRightStep R) (by simp [j])
  exact ⟨eAligned ≪≫ eTransport.symm ≪≫ eIndex⟩

/-- One actual-index package containing exactly the two dependent fields of
`RightLadder.Comparison.Certificate`: cancellation of the previous padded
arrow and identification of the next-source left mesh with the common square
complex. -/
theorem exists_actualCertificateStep_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ U₀ : C}
    {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk
          ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
            (Fin.last n))))
    (i : Fin n) :
    ∃ p : RightLadder.Comparison.PreviousCancellation R i.val,
      Nonempty
        (T.leftMesh (R.Z (i.val + 1) ⊞ R.U (i.val + 1)) ≅
          RightLadder.Comparison.squareComplex R i.val p) := by
  obtain ⟨ePrevious⟩ :=
    actualPreviousCancellationIso_all_of_boundaryEmbedding
      R n L E hfinite hlast i
  let p := RightLadder.Comparison.PreviousCancellation.ofArrowIso
    R i.val ePrevious
  obtain ⟨eStep⟩ :=
    actualReversedStepIso_all_of_boundaryEmbedding
      R n L E hfinite hlast i
  let j : Fin n := i.rev
  let eSource : L.Y j.castSucc ≅
      R.Z (i.val + 1) ⊞ R.U (i.val + 1) :=
    ShortComplex.π₁.mapIso eStep
  let eFirst :
      (T.leftMesh (R.Z (i.val + 1) ⊞ R.U (i.val + 1))).X₁ ≅
        (T.leftMesh (L.Y j.castSucc)).X₁ :=
    (T.leftTermIso (R.Z (i.val + 1) ⊞ R.U (i.val + 1))).trans
      (eSource.symm.trans (T.leftTermIso (L.Y j.castSucc)).symm)
  obtain ⟨eChosenLeft⟩ :=
    LeftTauSequence.nonempty_iso_of_iso_X₁
      (T.leftTau (R.Z (i.val + 1) ⊞ R.U (i.val + 1)))
      (T.leftTau (L.Y j.castSucc)) eFirst
  obtain ⟨eDisplayedLeft⟩ := L.meshIso j
  let eRightSquare :=
    RightLadder.Comparison.rightStepIsoSquareComplex R i.val p
  exact ⟨p, ⟨eChosenLeft ≪≫ eDisplayedLeft ≪≫ eStep ≪≫
    eRightSquare⟩⟩

/-- Full finite comparison certificate, ending at the chosen left
zero-boundary arrow.  This is the production-facing assembly theorem: all
dependent `PreviousCancellation` and `leftSquareIso` fields are constructed
from the closed reversed comparison. -/
theorem nonempty_certificate_to_leftZeroBoundary_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ U₀ : C}
    {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk
          ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).paddedArrow
            (Fin.last n)))) :
    Nonempty (RightLadder.Comparison.Certificate R n (L.b 0)) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R n
  choose previousCancellation leftSquareIso using
    fun i ↦ exists_actualCertificateStep_of_boundaryEmbedding
      R n L E hfinite hlast i
  obtain ⟨eTerminalAligned⟩ :=
    terminalArrowIsoAt_all_of_boundaryEmbedding
      RR L E hfinite hlast (0 : Fin (n + 1))
  let padded : ∀ r, R.Z r ⊞ R.U r ⟶ R.Y r := fun r ↦
    RightLadder.Comparison.paddedArrow R r
  let ePadAt := ofInfiniteSpecialRightLadder_paddedArrowIso_at
    R n (0 : Fin (n + 1))
  let ePadIndex : Arrow.mk (padded (0 : Fin (n + 1)).rev.val) ≅
      Arrow.mk (padded n) :=
    familyArrowIso (fun r ↦ R.Z r ⊞ R.U r) R.Y padded (by simp)
  let eTerminal : Arrow.mk (RightLadder.Comparison.paddedArrow R n) ≅
      Arrow.mk (L.b 0) :=
    (eTerminalAligned ≪≫ ePadAt ≪≫ ePadIndex).symm
  exact ⟨
    { previousCancellation := previousCancellation
      leftSquareIso := leftSquareIso
      terminalIso := ⟨eTerminal⟩ }⟩

end MBDVendor.QSE.Iyama.TauSequenceComparison
