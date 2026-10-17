import MBDVendor.QSE.CategoryTheory.IyamaFiniteLadderComparison
import MBDVendor.QSE.CategoryTheory.IyamaRightLadderRadicalWitness
import MBDVendor.QSE.CategoryTheory.IyamaLadderComparisonEndpoint

/-!
# Nakayama-pair extraction from Iyama's finite ladder comparison

This file assembles the abstract categorical ingredients of the finite-ladder
argument.  A radical-power witness is restricted to an indecomposable
summand, the reversed comparison identifies the terminal essential arrow,
and the resulting positive-length certificate is truncated by one rung to
produce a Nakayama pair.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteTauCategoryData

/-- A nonzero radical-power morphism remains nonzero on some chosen
indecomposable direct summand of its source. -/
theorem exists_chosenSummand_radicalWitness
    (T : FiniteTauCategoryData C Ind)
    {X W : C} (n : ℕ) (q : X ⟶ W)
    (hq : q ∈ (T.radical.ideal.pow n).hom X W) (hqne : q ≠ 0) :
    ∃ (I : Ind) (j : T.obj I ⟶ X),
      IsSplitMono j ∧
        j ≫ q ∈ (T.radical.ideal.pow n).hom (T.obj I) W ∧
          j ≫ q ≠ 0 := by
  classical
  obtain ⟨m, label, ⟨e⟩⟩ := T.obj_decomposition X
  let component : ∀ i : Fin m, T.obj (label i) ⟶ W := fun i ↦
    biproduct.ι (fun k ↦ T.obj (label k)) i ≫ e.inv ≫ q
  have hcomponent : ∃ i : Fin m, component i ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsumZero : e.inv ≫ q = 0 := by
      ext i
      simpa only [component, Category.assoc, comp_zero] using hall i
    apply hqne
    rw [← cancel_epi e.inv]
    simpa only [comp_zero] using hsumZero
  obtain ⟨i, hi⟩ := hcomponent
  let j : T.obj (label i) ⟶ X :=
    biproduct.ι (fun k ↦ T.obj (label k)) i ≫ e.inv
  have hj : IsSplitMono j := by
    dsimp only [j]
    infer_instance
  refine ⟨label i, j, hj, ?_, ?_⟩
  · exact (T.radical.ideal.pow n).precomp j hq
  · simpa only [j, component, Category.assoc] using hi

end FiniteTauCategoryData

namespace TauSequenceComparison

/-- The boundary object of the reversed prefix is the actual complementary
object at the end of the finite right-ladder window. -/
theorem ofInfiniteSpecialRightLadder_U_zero_eq
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ) :
    (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).U 0 = R.U n := by
  simp [ReversedRightPrefix.ofInfiniteSpecialRightLadder]

/-- A radical-power witness on the actual terminal complementary object
transports to the zero boundary of the reversed prefix and forces the chosen
left ladder to have nonzero terminal domain. -/
theorem terminalLeftDomain_not_isZero_of_radicalWitness
    {T : FiniteTauCategoryData C Ind} {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀) (n : ℕ)
    {W : C} (q : R.U n ⟶ W)
    (hq : q ∈ (T.radical.ideal.pow n).hom (R.U n) W)
    (hqne : q ≠ 0) :
    ¬ IsZero
      ((LeftLadder.chosenFiniteSpecialLeftLadderFromZero T
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).U 0) n).Y
          (Fin.last n)) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R n
  have eU : RR.U 0 = R.U n :=
    ofInfiniteSpecialRightLadder_U_zero_eq R n
  let q' : RR.U 0 ⟶ W := eqToHom eU ≫ q
  have hq' : q' ∈ (T.radical.ideal.pow n).hom (RR.U 0) W :=
    (T.radical.ideal.pow n).precomp (eqToHom eU) hq
  have hqne' : q' ≠ 0 := by
    intro hzero
    apply hqne
    rw [← cancel_epi (eqToHom eU)]
    simpa only [q', comp_zero] using hzero
  exact
    LeftLadder.chosenFiniteSpecialLeftLadderFromZero_terminalDomain_not_isZero
      T (RR.U 0) n q' hq' hqne'

/-- The terminal essential left arrow is isomorphic to the initial
`muMinus` arrow when its boundary is a split subobject of the reversed right
complement. -/
theorem terminalEssentialArrow_iso_muMinus_of_boundaryEmbedding
    (T : FiniteTauCategoryData C Ind) (A : Ind)
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData (T.muMinus A)) (n : ℕ)
    (U₀ : C)
    (E : BoundaryEmbedding
      (ReversedRightPrefix.ofInfiniteSpecialRightLadder R n) U₀)
    (hY : ¬ IsZero
      ((LeftLadder.chosenFiniteSpecialLeftLadderFromZero T U₀ n).Y
        (Fin.last n))) :
    Nonempty
      (Arrow.mk
          ((LeftLadder.chosenFiniteSpecialLeftLadderFromZero T U₀ n).b
            (Fin.last n)) ≅
        Arrow.mk (T.muMinus A)) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R n
  let L := LeftLadder.chosenFiniteSpecialLeftLadderFromZero T U₀ n
  obtain ⟨q, hqleft, hqright⟩ :=
    diagonalComparisonAt_all_of_boundaryEmbedding RR L E (Fin.last n)
  let ePad := ofInfiniteSpecialRightLadder_paddedArrowIso_last R n
  obtain ⟨eInitial⟩ := R.initialIso
  let ePadLeft := Arrow.leftFunc.mapIso ePad
  let ePadRight := Arrow.rightFunc.mapIso ePad
  let eInitialLeft := Arrow.leftFunc.mapIso eInitial
  let eInitialRight := Arrow.rightFunc.mapIso eInitial
  let d : Arrow.mk (L.b (Fin.last n)) ⟶ Arrow.mk (T.muMinus A) :=
    q ≫ ePad.hom ≫ eInitial.inv
  have hdleft : IsSplitMono d.left := by
    change IsSplitMono (q.left ≫ ePadLeft.hom ≫ eInitialLeft.inv)
    letI : IsSplitMono q.left := hqleft
    infer_instance
  have hdright : IsSplitMono d.right := by
    change IsSplitMono (q.right ≫ ePadRight.hom ≫ eInitialRight.inv)
    letI : IsSplitMono q.right := hqright
    infer_instance
  let p₀ := LeftLadder.zeroInitialPackedCosplitState T U₀
  let P : ℕ → LeftLadder.PackedSpecialCosplitState T :=
    LeftLadder.iteratePackedCosplitState T
      (LeftLadder.specialLeftLadderBuilder T) p₀
  let s : LeftLadder.SpecialCosplitState T (P n).1 := (P n).2
  let sourceMap : (P n).1 ⟶ (T.leftMesh (T.obj A)).X₁ := d.left
  let targetMap : s.Z ⟶ (T.leftMesh (T.obj A)).X₂ := d.right
  have hsourceMap : IsSplitMono sourceMap := by
    change IsSplitMono d.left
    exact hdleft
  have htargetMap : IsSplitMono targetMap := by
    change IsSplitMono d.right
    exact hdright
  letI : IsSplitMono sourceMap := hsourceMap
  letI : IsSplitMono targetMap := htargetMap
  change Nonempty (Arrow.mk s.b ≅ Arrow.mk (T.muMinus A))
  apply LeftLadder.Comparison.nonempty_essentialArrow_iso_muMinus_of_leftDominance
    T A s.p sourceMap targetMap hY
  have hcomm : d.left ≫ T.muMinus A = L.b (Fin.last n) ≫ d.right :=
    d.w
  change sourceMap ≫ T.muMinus A = s.b ≫ targetMap at hcomm
  exact hcomm

/-- Whole-boundary specialization of the terminal endpoint theorem. -/
theorem terminalEssentialArrow_iso_muMinus
    (T : FiniteTauCategoryData C Ind) (A : Ind)
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData (T.muMinus A)) (n : ℕ)
    (hY : ¬ IsZero
      ((LeftLadder.chosenFiniteSpecialLeftLadderFromZero T
        ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).U 0) n).Y
          (Fin.last n))) :
    Nonempty
      (Arrow.mk
          ((LeftLadder.chosenFiniteSpecialLeftLadderFromZero T
            ((ReversedRightPrefix.ofInfiniteSpecialRightLadder R n).U 0) n).b
              (Fin.last n)) ≅
        Arrow.mk (T.muMinus A)) := by
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R n
  exact terminalEssentialArrow_iso_muMinus_of_boundaryEmbedding
    T A R n (RR.U 0) (BoundaryEmbedding.identity RR) hY

/-- Under the nonzero-middle hypothesis of the extraction theorem, a
radical witness cannot occur at index zero. -/
theorem radicalWitness_index_ne_zero
    (T : FiniteTauCategoryData C Ind) (A : Ind)
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData (T.muMinus A))
    (n : ℕ) {W : C} (q : R.U n ⟶ W)
    (hq : q ∈ (T.radical.ideal.pow n).hom (R.U n) W)
    (hqne : q ≠ 0) (hTheta : ¬ IsZero (T.thetaMinus A)) :
    n ≠ 0 := by
  intro hn
  subst n
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R 0
  let L := LeftLadder.chosenFiniteSpecialLeftLadderFromZero T (RR.U 0) 0
  have hY : ¬ IsZero (L.Y (Fin.last 0)) :=
    terminalLeftDomain_not_isZero_of_radicalWitness R 0 q hq hqne
  obtain ⟨eTerminal⟩ :=
    terminalEssentialArrow_iso_muMinus T A R 0 hY
  have hzero : IsZero (L.Z (Fin.last 0)) := by
    simpa only [Fin.last_zero] using L.initialTargetZero
  have hThetaZero : IsZero (T.thetaMinus A) :=
    hzero.of_iso (Arrow.rightFunc.mapIso eTerminal).symm
  exact hTheta hThetaZero

end TauSequenceComparison

namespace NakayamaExtraction

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Indecomposability transports backwards across an object isomorphism. -/
theorem indecomposable_of_iso
    {X Y : C} (hY : Indecomposable Y) (e : X ≅ Y) :
    Indecomposable X := by
  constructor
  · intro hX
    exact hY.1 (hX.of_iso e.symm)
  · intro A B d
    exact hY.2 A B (e.symm ≪≫ d)

/-- A comparison certificate can be truncated just before its last rung. -/
def certificatePrefix
    {T : FiniteTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    {n : ℕ} {X Y : C} {finish : X ⟶ Y}
    (K : RightLadder.Comparison.Certificate R (n + 1) finish) :
    RightLadder.Comparison.Certificate R n
      (RightLadder.Comparison.paddedArrow R n) where
  previousCancellation i := K.previousCancellation i.castSucc
  leftSquareIso i := K.leftSquareIso i.castSucc
  terminalIso := ⟨Iso.refl _⟩

/-- The prefix of a length-`n+1` comparison ends at the arrow immediately
before its terminal rung. -/
theorem certificatePrefix_invertibleLadderOfDistance
    {T : FiniteTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    {n : ℕ} {X Y : C} {finish : X ⟶ Y}
    (K : RightLadder.Comparison.Certificate R (n + 1) finish) :
    NakayamaLadder.InvertibleLadderOfDistance T n a₀
      (RightLadder.Comparison.paddedArrow R n) :=
  (certificatePrefix R K).invertibleLadderOfDistance R n

/-- Each certificate entry is the invertible step between the corresponding
two padded arrows. -/
theorem certificateStep
    {T : FiniteTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    {n : ℕ} {X Y : C} {finish : X ⟶ Y}
    (K : RightLadder.Comparison.Certificate R n finish)
    (i : Fin n) :
    NakayamaLadder.InvertibleLadderStep T
      (RightLadder.Comparison.paddedArrow R i.val)
      (RightLadder.Comparison.paddedArrow R (i.val + 1)) := by
  refine ⟨RightLadder.Comparison.squareF R i.val
      (K.previousCancellation i),
    RightLadder.Comparison.squareG R i.val
      (K.previousCancellation i),
    RightLadder.Comparison.square_comm R i.val
      (K.previousCancellation i), ?_, ?_⟩
  · obtain ⟨e⟩ := R.meshIso i.val
    exact ⟨e.trans
      (RightLadder.Comparison.rightStepIsoSquareComplex R i.val
        (K.previousCancellation i))⟩
  · simpa only [RightLadder.Comparison.squareComplex, Fin.val_succ,
      Nat.succ_eq_add_one] using K.leftSquareIso i

/-- The terminal endpoint of a finite ladder can be replaced by an
arrow-isomorphic morphism without changing its distance. -/
theorem invertibleLadderOfDistance_finish_iso
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    {X₀ Y₀ X Y X' Y' : C}
    {start : X₀ ⟶ Y₀} {finish : X ⟶ Y} {finish' : X' ⟶ Y'}
    (h : NakayamaLadder.InvertibleLadderOfDistance T n start finish)
    (e : Arrow.mk finish ≅ Arrow.mk finish') :
    NakayamaLadder.InvertibleLadderOfDistance T n start finish' := by
  obtain ⟨F, G, a, hstart, ⟨hend⟩, hstep⟩ := h
  exact ⟨F, G, a, hstart, ⟨hend.trans e⟩, hstep⟩

/-- The terminal-boundary argument only needs the next source to be
abstractly indecomposable. -/
theorem exists_nonprojective_muPlus_predecessor_of_step_to_zeroTarget_of_indec
    (T : FiniteTauCategoryData C Ind)
    {XPrev YPrev XNext YNext : C}
    {aPrev : XPrev ⟶ YPrev} {aNext : XNext ⟶ YNext}
    (hstep : NakayamaLadder.InvertibleLadderStep T aPrev aNext)
    (hXNext : Indecomposable XNext)
    (hYNext : IsZero YNext) :
    ∃ B : Ind, ¬ T.IsProjective B ∧
      Nonempty (Arrow.mk aPrev ≅ Arrow.mk (T.muPlus B)) := by
  obtain ⟨I, ⟨eX⟩⟩ := T.obj_complete XNext hXNext
  have hstepCopy := hstep
  obtain ⟨f, g, comm, _, ⟨eLeft⟩⟩ := hstep
  let eStep :
      Arrow.mk (biprod.desc f aPrev) ≅ Arrow.mk aPrev :=
    NakayamaLadder.biprodDescIsoRightOfIsZero hYNext f aPrev
  let ePrevX :
      Arrow.mk aPrev ≅ Arrow.mk (T.leftMesh XNext).g :=
    eStep.symm ≪≫ (ShortComplex.gFunctor.mapIso eLeft).symm
  let e₁ : (T.leftMesh XNext).X₁ ≅
      (T.leftMesh (T.obj I)).X₁ :=
    T.leftTermIso XNext ≪≫ eX ≪≫ (T.leftTermIso (T.obj I)).symm
  obtain ⟨eMesh⟩ := LeftTauSequence.nonempty_iso_of_iso_X₁
    (T.leftTau XNext) (T.leftTau (T.obj I)) e₁
  let ePrevI : Arrow.mk aPrev ≅ Arrow.mk (T.nuMinus I) :=
    ePrevX ≪≫ ShortComplex.gFunctor.mapIso eMesh
  have hYPrev : ¬ IsZero YPrev :=
    NakayamaLadder.not_isZero_previousTarget_of_step hstepCopy hXNext.1
  have hI : ¬ T.IsInjective I := by
    intro hInjective
    have hMeshX : IsZero (T.leftMesh XNext).X₃ :=
      hInjective.of_iso (ShortComplex.π₃.mapIso eMesh)
    exact hYPrev (hMeshX.of_iso (ShortComplex.π₃.mapIso eLeft).symm)
  let A : T.Noninjective := ⟨I, hI⟩
  refine ⟨T.tauMinus A, (T.tauPlusEquiv.symm A).2, ?_⟩
  exact ⟨ePrevI ≪≫ T.secondMapIso A⟩

/-- Deleting the last rung of a positive-length certificate gives the
required `muPlus`-ending Nakayama ladder.  A witness at index `n+1`
therefore produces a Nakayama pair of distance `n`. -/
theorem exists_nakayamaPairOfDistance_of_succ_certificate
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    {n : ℕ} {U Z : C} {finish : U ⟶ Z}
    (K : RightLadder.Comparison.Certificate R (n + 1) finish)
    (hZ : IsZero Z)
    (hterminalSource :
      Indecomposable (R.Z (n + 1) ⊞ R.U (n + 1))) :
    ∃ B : Ind, ¬ T.IsProjective B ∧
      NakayamaLadder.InvertibleLadderOfDistance T n a₀ (T.muPlus B) := by
  let i : Fin (n + 1) := Fin.last n
  have hi : i.val = n := by simp [i]
  have hstep := certificateStep R K i
  rw [hi] at hstep
  have hterminalTarget : IsZero (R.Y (n + 1)) := by
    obtain ⟨eTerminal⟩ := K.terminalIso
    exact hZ.of_iso (Arrow.rightFunc.mapIso eTerminal)
  obtain ⟨B, hB, ePrev⟩ :=
    exists_nonprojective_muPlus_predecessor_of_step_to_zeroTarget_of_indec
      T hstep hterminalSource hterminalTarget
  refine ⟨B, hB, ?_⟩
  exact invertibleLadderOfDistance_finish_iso
    (certificatePrefix_invertibleLadderOfDistance R K)
    (Classical.choice ePrev)

/-- If the certificate ends at a chosen indecomposable zero boundary, its
terminal source is automatically indecomposable. -/
theorem exists_nakayamaPairOfDistance_of_succ_certificate_to_leftBoundary
    (T : FiniteTauCategoryData C Ind)
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData a₀)
    {n : ℕ} {U₀ : C}
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ (n + 1))
    (hU₀ : Indecomposable U₀)
    (K : RightLadder.Comparison.Certificate R (n + 1) (L.b 0)) :
    ∃ B : Ind, ¬ T.IsProjective B ∧
      NakayamaLadder.InvertibleLadderOfDistance T n a₀ (T.muPlus B) := by
  obtain ⟨eTerminal⟩ := K.terminalIso
  let eSource : R.Z (n + 1) ⊞ R.U (n + 1) ≅ U₀ :=
    Arrow.leftFunc.mapIso eTerminal ≪≫ L.initialSourceIso.symm
  have hterminalSource :
      Indecomposable (R.Z (n + 1) ⊞ R.U (n + 1)) :=
    indecomposable_of_iso hU₀ eSource
  exact exists_nakayamaPairOfDistance_of_succ_certificate
    T R K L.initialTargetZero hterminalSource

end NakayamaExtraction

open NakayamaExtraction TauSequenceComparison

namespace FiniteTauCategoryData

/-- Iyama's finite ladder construction extracts a Nakayama partner from
every nonzero nonmonic `muMinus` boundary map. -/
theorem hasMuMinusNakayamaExtraction
    (T : FiniteTauCategoryData C Ind) :
    T.HasMuMinusNakayamaExtraction := by
  intro A hTheta hmono
  let R : RightLadder.InfiniteSpecialRightLadder
      T.toFiniteRightTauCategoryData (T.muMinus A) :=
    RightLadder.infiniteSpecialRightLadder T.toFiniteRightTauCategoryData
      (T.muMinus A)
      ((T.leftTau (T.obj A)).isSpecial_f T.radical)
  obtain ⟨N, q, hq, hqne⟩ :=
    RightLadder.exists_nonzero_initial_source_map_mem_power_of_isSpecial_of_not_mono
      T.toFiniteRightTauCategoryData (T.muMinus A)
      ((T.leftTau (T.obj A)).isSpecial_f T.radical) hmono
  have hN : N ≠ 0 :=
    radicalWitness_index_ne_zero T A R N q hq hqne hTheta
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  obtain ⟨I, j, hj, hjq, hjqne⟩ :=
    T.exists_chosenSummand_radicalWitness (n + 1) q hq hqne
  let RR := ReversedRightPrefix.ofInfiniteSpecialRightLadder R (n + 1)
  have eU : RR.U 0 = R.U (n + 1) :=
    ofInfiniteSpecialRightLadder_U_zero_eq R (n + 1)
  let j' : T.obj I ⟶ RR.U 0 := j ≫ eqToHom eU.symm
  have hj' : IsSplitMono j' := by
    dsimp only [j']
    letI : IsSplitMono j := hj
    infer_instance
  let E : BoundaryEmbedding RR (T.obj I) :=
    { hom := j'
      isSplitMono := hj' }
  let L := LeftLadder.chosenFiniteSpecialLeftLadderFromZero
    T (T.obj I) (n + 1)
  have hterminalDomain : ¬ IsZero (L.Y (Fin.last (n + 1))) :=
    LeftLadder.chosenFiniteSpecialLeftLadderFromZero_terminalDomain_not_isZero
      T (T.obj I) (n + 1) (j ≫ q) hjq hjqne
  have hterminal : Nonempty
      (Arrow.mk (L.b (Fin.last (n + 1))) ≅ Arrow.mk (T.muMinus A)) :=
    terminalEssentialArrow_iso_muMinus_of_boundaryEmbedding
      T A R (n + 1) (T.obj I) E hterminalDomain
  obtain ⟨K⟩ :=
    nonempty_certificate_to_leftZeroBoundary_of_terminalEssentialIso_finite
      T R (n + 1) L E hterminal
  obtain ⟨B, hB, hpair⟩ :=
    exists_nakayamaPairOfDistance_of_succ_certificate_to_leftBoundary
      T R L (T.obj_indec I) K
  exact ⟨B, hB, ⟨n, hpair⟩⟩

end FiniteTauCategoryData

end MBDVendor.QSE.Iyama
