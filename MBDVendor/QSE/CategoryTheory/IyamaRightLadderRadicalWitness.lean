module

public import MBDVendor.QSE.CategoryTheory.IyamaRightLadderIteration
public import MBDVendor.QSE.CategoryTheory.IyamaLadderRadical

/-!
# The initial complementary branch in an infinite Iyama right ladder

This module integrates the dependent infinite special right ladder with the
radical-power annihilator propagation from Iyama, Lemma 6.4.1(1)(i). It treats
the zero-th padded summand separately. The argument is entirely categorical
and contains no concrete algebra or module classification.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.RightLadder

open CategoricalIdeal

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable {T : FiniteRightTauCategoryData C Ind}
  {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}

/-- The weak-kernel mesh models stored in an infinite special right ladder
give exactly the annihilator-propagation hypothesis used by the radical-power
argument. -/
theorem InfiniteSpecialRightLadder.hasAnnihilatorPropagation
    (L : InfiniteSpecialRightLadder T a₀) :
    HasAnnihilatorPropagation L.Z L.Y L.U L.b L.g L.h :=
  hasAnnihilatorPropagation_of_rightTauSequence_stepFamily
    (fun n ↦ T.rightMesh (L.Y n)) L.Z L.Y L.U L.b L.f L.g L.h
    L.comm L.hzero (fun n ↦ T.rightTau (L.Y n)) L.meshIso

/-- The connecting maps in an infinite special right ladder are radical. -/
theorem InfiniteSpecialRightLadder.connectingMaps_mem_radical
    (L : InfiniteSpecialRightLadder T a₀) :
    (∀ n : ℕ,
      L.g n ∈ T.radical.ideal.hom (L.Z (n + 1)) (L.Z n)) ∧
      ∀ n : ℕ,
        L.h n ∈ T.radical.ideal.hom (L.U (n + 1)) (L.Z n) :=
  connectingMaps_mem_radical_of_rightTauSequence_stepFamily
    T.radical (fun n ↦ T.rightMesh (L.Y n)) L.Z L.Y L.U L.b L.f L.g L.h
    L.comm L.hzero (fun n ↦ T.rightTau (L.Y n)) L.meshIso

/-- Ladder-specific form of radical-power annihilator propagation. -/
theorem InfiniteSpecialRightLadder.exists_nonzero_remainder_in_radical_power
    (L : InfiniteSpecialRightLadder T a₀)
    {W : C} (s₀ : W ⟶ L.Z 0)
    (hs₀ : s₀ ≫ L.b 0 = 0) (hs₀ne : s₀ ≠ 0) :
    ∃ n : ℕ,
      L.h n ≫ backwardComposite L.Z L.g n ∈
          (T.radical.ideal.pow (n + 1)).hom (L.U (n + 1)) (L.Z 0) ∧
        L.h n ≫ backwardComposite L.Z L.g n ≠ 0 := by
  have hrad := L.connectingMaps_mem_radical
  exact RightLadder.exists_nonzero_remainder_in_radical_power
    T.radical L.Z L.Y L.U L.b L.g L.h
    L.hasAnnihilatorPropagation hrad.1 hrad.2 s₀ hs₀ hs₀ne

/-- The source-facing radical-power witness required in Iyama 6.4.1(1)(i). -/
def InfiniteSpecialRightLadder.HasRadicalWitnessAtInitialSource
    (L : InfiniteSpecialRightLadder T a₀) (n : ℕ) : Prop :=
  ∃ q : L.U n ⟶ X₀,
    q ∈ (T.radical.ideal.pow n).hom (L.U n) X₀ ∧ q ≠ 0

/-- If the initial padded summand is nonzero, its split inclusion into the
source of `a₀` is already a nonzero degree-zero witness. -/
theorem InfiniteSpecialRightLadder.has_radical_witness_at_initial_source_zero
    (L : InfiniteSpecialRightLadder T a₀) (hU : ¬ IsZero (L.U 0)) :
    L.HasRadicalWitnessAtInitialSource 0 := by
  obtain ⟨e⟩ := L.initialIso
  let eX : X₀ ≅ L.Z 0 ⊞ L.U 0 := Arrow.leftFunc.mapIso e
  let q : L.U 0 ⟶ X₀ := biprod.inr ≫ eX.inv
  refine ⟨q, by simp, ?_⟩
  intro hq
  have hinr : (biprod.inr : L.U 0 ⟶ L.Z 0 ⊞ L.U 0) = 0 := by
    rw [← cancel_mono eX.inv]
    simpa [q] using hq
  apply hU
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (L.U 0) =
        (biprod.inr : L.U 0 ⟶ L.Z 0 ⊞ L.U 0) ≫ biprod.snd := by simp
    _ = 0 := by rw [hinr, zero_comp]

/-- If the initial padded summand is zero, a nonzero annihilator of `a₀`
transports across the initial arrow isomorphism to a nonzero annihilator of
the essential map `b 0`. -/
theorem InfiniteSpecialRightLadder.exists_nonzero_initial_annihilator
    (L : InfiniteSpecialRightLadder T a₀) (hU : IsZero (L.U 0))
    {W : C} (s : W ⟶ X₀) (hs : s ≫ a₀ = 0) (hsne : s ≠ 0) :
    ∃ sZ : W ⟶ L.Z 0, sZ ≠ 0 ∧ sZ ≫ L.b 0 = 0 := by
  obtain ⟨e⟩ := L.initialIso
  let eX : X₀ ≅ L.Z 0 ⊞ L.U 0 := Arrow.leftFunc.mapIso e
  let eY : Y₀ ≅ L.Y 0 := Arrow.rightFunc.mapIso e
  have he :
      eX.hom ≫ biprod.desc (L.b 0) (0 : L.U 0 ⟶ L.Y 0) =
        a₀ ≫ eY.hom := by
    exact Arrow.w e.hom
  let sPad : W ⟶ L.Z 0 ⊞ L.U 0 := s ≫ eX.hom
  let sZ : W ⟶ L.Z 0 := sPad ≫ biprod.fst
  let sU : W ⟶ L.U 0 := sPad ≫ biprod.snd
  have hsPad :
      sPad ≫ biprod.desc (L.b 0) (0 : L.U 0 ⟶ L.Y 0) = 0 := by
    calc
      sPad ≫ biprod.desc (L.b 0) (0 : L.U 0 ⟶ L.Y 0) =
          s ≫ (eX.hom ≫
            biprod.desc (L.b 0) (0 : L.U 0 ⟶ L.Y 0)) := by
              simp only [sPad, Category.assoc]
      _ = s ≫ (a₀ ≫ eY.hom) := by rw [he]
      _ = (s ≫ a₀) ≫ eY.hom := by rw [Category.assoc]
      _ = 0 := by rw [hs, zero_comp]
  have hsU : sU = 0 := hU.eq_of_tgt sU 0
  have hsplit : sPad = biprod.lift sZ sU := by
    apply biprod.hom_ext <;> simp [sZ, sU]
  have hsZzero : sZ ≫ L.b 0 = 0 := by
    rw [hsplit, biprod.lift_desc, hsU, zero_comp, add_zero] at hsPad
    exact hsPad
  refine ⟨sZ, ?_, hsZzero⟩
  intro hsZ
  apply hsne
  rw [← cancel_mono eX.hom]
  calc
    s ≫ eX.hom = sPad := rfl
    _ = biprod.lift sZ sU := hsplit
    _ = 0 := by
      rw [hsZ, hsU]
      ext <;> simp
    _ = 0 ≫ eX.hom := by simp

/-- The complete `U₀`-aware radical-power conclusion.

Given a nonzero map annihilating the initial special arrow, some padded
summand `U n` admits a nonzero map back to the original source in the `n`th
power of the chosen categorical radical.  The `n = 0` case is supplied by
the initial padded complement; if that complement is zero, the existing
right-ladder propagation supplies a witness with index `n + 1`. -/
theorem InfiniteSpecialRightLadder.exists_radical_witness_at_initial_source
    (L : InfiniteSpecialRightLadder T a₀)
    {W : C} (s : W ⟶ X₀) (hs : s ≫ a₀ = 0) (hsne : s ≠ 0) :
    ∃ n : ℕ, L.HasRadicalWitnessAtInitialSource n := by
  by_cases hU : IsZero (L.U 0)
  · obtain ⟨sZ, hsZne, hsZ⟩ :=
      L.exists_nonzero_initial_annihilator hU s hs hsne
    obtain ⟨n, hmem, hne⟩ :=
      L.exists_nonzero_remainder_in_radical_power sZ hsZ hsZne
    obtain ⟨e⟩ := L.initialIso
    let eX : X₀ ≅ L.Z 0 ⊞ L.U 0 := Arrow.leftFunc.mapIso e
    let q : L.U (n + 1) ⟶ X₀ :=
      L.h n ≫ backwardComposite L.Z L.g n ≫ biprod.inl ≫ eX.inv
    refine ⟨n + 1, q, ?_, ?_⟩
    · simpa only [q, Category.assoc] using
        (T.radical.ideal.pow (n + 1)).postcomp
          ((biprod.inl : L.Z 0 ⟶ L.Z 0 ⊞ L.U 0) ≫ eX.inv) hmem
    · intro hq
      apply hne
      rw [← cancel_mono
        ((biprod.inl : L.Z 0 ⟶ L.Z 0 ⊞ L.U 0) ≫ eX.inv)]
      simpa [q, Category.assoc] using hq
  · exact ⟨0, L.has_radical_witness_at_initial_source_zero hU⟩

/-- Direct existential form of the preceding theorem. -/
theorem InfiniteSpecialRightLadder.exists_nonzero_initial_source_map_mem_power
    (L : InfiniteSpecialRightLadder T a₀)
    {W : C} (s : W ⟶ X₀) (hs : s ≫ a₀ = 0) (hsne : s ≠ 0) :
    ∃ (n : ℕ) (q : L.U n ⟶ X₀),
      q ∈ (T.radical.ideal.pow n).hom (L.U n) X₀ ∧ q ≠ 0 := by
  simpa only [InfiniteSpecialRightLadder.HasRadicalWitnessAtInitialSource]
    using L.exists_radical_witness_at_initial_source s hs hsne

/-- Paper-facing form: build the infinite ladder from a special initial arrow
and then obtain the radical-power witness at its original source. -/
theorem exists_nonzero_initial_source_map_mem_power_of_isSpecial
    (T : FiniteRightTauCategoryData C Ind)
    {X₀ Y₀ W : C} (a₀ : X₀ ⟶ Y₀) (ha₀ : IsSpecial T.radical a₀)
    (s : W ⟶ X₀) (hs : s ≫ a₀ = 0) (hsne : s ≠ 0) :
    let L := infiniteSpecialRightLadder T a₀ ha₀
    ∃ (n : ℕ) (q : L.U n ⟶ X₀),
      q ∈ (T.radical.ideal.pow n).hom (L.U n) X₀ ∧ q ≠ 0 := by
  exact
    (infiniteSpecialRightLadder T a₀ ha₀).exists_nonzero_initial_source_map_mem_power
      s hs hsne

/-- A nonmonic special arrow has a nonzero radical-power witness on one of
the padded terms in its infinite right ladder. This is the finite
nilpotent-radical specialization of the first conclusion in Iyama
6.4.1(1)(i). -/
theorem exists_nonzero_initial_source_map_mem_power_of_isSpecial_of_not_mono
    (T : FiniteRightTauCategoryData C Ind)
    {X₀ Y₀ : C} (a₀ : X₀ ⟶ Y₀) (ha₀ : IsSpecial T.radical a₀)
    (hmono : ¬ Mono a₀) :
    let L := infiniteSpecialRightLadder T a₀ ha₀
    ∃ (n : ℕ) (q : L.U n ⟶ X₀),
      q ∈ (T.radical.ideal.pow n).hom (L.U n) X₀ ∧ q ≠ 0 := by
  obtain ⟨W, s, hsne, hs⟩ :=
    exists_nonzero_comp_eq_zero_of_not_mono hmono
  exact exists_nonzero_initial_source_map_mem_power_of_isSpecial
    T a₀ ha₀ s hs hsne

end MBDVendor.QSE.Iyama.RightLadder
