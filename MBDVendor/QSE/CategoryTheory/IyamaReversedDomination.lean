import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderPropagation
import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderIteration
import MBDVendor.QSE.CategoryTheory.IyamaLadderComparisonAssembly
import MBDVendor.QSE.CategoryTheory.IyamaMixedMeshSplitLifting
import MBDVendor.QSE.CategoryTheory.IyamaRightLadderPropagation

/-!
# Reversed domination and finite comparison propagation

This is the explicit triangular-matrix step used when a finite left ladder is
read backwards against a right ladder.  It is entirely categorical: no
concrete algebra or module classification is involved.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.TauSequenceComparison

open CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The composite of two explicitly split-monic morphisms is split monic. -/
theorem isSplitMono_comp_of_isSplitMono
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSplitMono f) (hg : IsSplitMono g) :
    IsSplitMono (f ≫ g) := by
  letI : IsSplitMono f := hf
  letI : IsSplitMono g := hg
  apply IsSplitMono.mk'
  exact
    (Classical.choice (IsSplitMono.exists_splitMono (f := f))).comp
      (Classical.choice (IsSplitMono.exists_splitMono (f := g)))

/-- Transport dual mixed split lifting across displayed mesh isomorphisms. -/
theorem splitMono_components_of_displayed_steps
    (T : FiniteTauCategoryData C Ind)
    {X Y : C} {S R : ShortComplex C}
    (eS : T.leftMesh X ≅ S) (eR : T.rightMesh Y ≅ R)
    (phi : S ⟶ R) (hphi₁ : IsSplitMono phi.τ₁) :
    IsSplitMono phi.τ₂ ∧ IsSplitMono phi.τ₃ := by
  letI : IsSplitMono phi.τ₁ := hphi₁
  let psi : T.leftMesh X ⟶ T.rightMesh Y :=
    eS.hom ≫ phi ≫ eR.inv
  have hpsi₁ : IsSplitMono psi.τ₁ := by
    change IsSplitMono (eS.hom.τ₁ ≫ phi.τ₁ ≫ eR.inv.τ₁)
    infer_instance
  obtain ⟨hpsi₂, hpsi₃⟩ :=
    splitMono_components_of_leftMesh_hom_rightMesh T X Y psi hpsi₁
  letI : IsSplitMono psi.τ₂ := hpsi₂
  letI : IsSplitMono psi.τ₃ := hpsi₃
  have hback₂ : IsSplitMono
      (eS.inv.τ₂ ≫ psi.τ₂ ≫ eR.hom.τ₂) := by
    infer_instance
  have hback₃ : IsSplitMono
      (eS.inv.τ₃ ≫ psi.τ₃ ≫ eR.hom.τ₃) := by
    infer_instance
  have heS₂ : eS.inv.τ₂ ≫ eS.hom.τ₂ = 𝟙 S.X₂ := by
    have h := congrArg ShortComplex.Hom.τ₂ eS.inv_hom_id
    change eS.inv.τ₂ ≫ eS.hom.τ₂ = 𝟙 S.X₂ at h
    exact h
  have heS₃ : eS.inv.τ₃ ≫ eS.hom.τ₃ = 𝟙 S.X₃ := by
    have h := congrArg ShortComplex.Hom.τ₃ eS.inv_hom_id
    change eS.inv.τ₃ ≫ eS.hom.τ₃ = 𝟙 S.X₃ at h
    exact h
  have heR₂ : eR.inv.τ₂ ≫ eR.hom.τ₂ = 𝟙 R.X₂ := by
    have h := congrArg ShortComplex.Hom.τ₂ eR.inv_hom_id
    change eR.inv.τ₂ ≫ eR.hom.τ₂ = 𝟙 R.X₂ at h
    exact h
  have heR₃ : eR.inv.τ₃ ≫ eR.hom.τ₃ = 𝟙 R.X₃ := by
    have h := congrArg ShortComplex.Hom.τ₃ eR.inv_hom_id
    change eR.inv.τ₃ ≫ eR.hom.τ₃ = 𝟙 R.X₃ at h
    exact h
  have heq₂ : eS.inv.τ₂ ≫ psi.τ₂ ≫ eR.hom.τ₂ = phi.τ₂ := by
    calc
      eS.inv.τ₂ ≫ psi.τ₂ ≫ eR.hom.τ₂ =
          (eS.inv.τ₂ ≫ eS.hom.τ₂) ≫ phi.τ₂ ≫
            (eR.inv.τ₂ ≫ eR.hom.τ₂) := by
        simp only [psi, ShortComplex.comp_τ₂, Category.assoc]
      _ = phi.τ₂ := by
        rw [heS₂, heR₂, Category.id_comp, Category.comp_id]
  have heq₃ : eS.inv.τ₃ ≫ psi.τ₃ ≫ eR.hom.τ₃ = phi.τ₃ := by
    calc
      eS.inv.τ₃ ≫ psi.τ₃ ≫ eR.hom.τ₃ =
          (eS.inv.τ₃ ≫ eS.hom.τ₃) ≫ phi.τ₃ ≫
            (eR.inv.τ₃ ≫ eR.hom.τ₃) := by
        simp only [psi, ShortComplex.comp_τ₃, Category.assoc]
      _ = phi.τ₃ := by
        rw [heS₃, heR₃, Category.id_comp, Category.comp_id]
  exact ⟨heq₂ ▸ hback₂, heq₃ ▸ hback₃⟩

/-- Transport mixed split-epi lifting across displayed mesh
isomorphisms. -/
theorem splitEpi_components_of_displayed_steps
    (T : FiniteTauCategoryData C Ind)
    {X Y : C} {S R : ShortComplex C}
    (eS : T.leftMesh X ≅ S) (eR : T.rightMesh Y ≅ R)
    (phi : S ⟶ R) (hphi₃ : IsSplitEpi phi.τ₃) :
    IsSplitEpi phi.τ₁ ∧ IsSplitEpi phi.τ₂ := by
  letI : IsSplitEpi phi.τ₃ := hphi₃
  let psi : T.leftMesh X ⟶ T.rightMesh Y :=
    eS.hom ≫ phi ≫ eR.inv
  have hpsi₃ : IsSplitEpi psi.τ₃ := by
    change IsSplitEpi (eS.hom.τ₃ ≫ phi.τ₃ ≫ eR.inv.τ₃)
    infer_instance
  obtain ⟨hpsi₁, hpsi₂⟩ :=
    splitEpi_components_of_leftMesh_hom_rightMesh T X Y psi hpsi₃
  letI : IsSplitEpi psi.τ₁ := hpsi₁
  letI : IsSplitEpi psi.τ₂ := hpsi₂
  have hback₁ : IsSplitEpi
      (eS.inv.τ₁ ≫ psi.τ₁ ≫ eR.hom.τ₁) := by
    infer_instance
  have hback₂ : IsSplitEpi
      (eS.inv.τ₂ ≫ psi.τ₂ ≫ eR.hom.τ₂) := by
    infer_instance
  have heS₁ : eS.inv.τ₁ ≫ eS.hom.τ₁ = 𝟙 S.X₁ := by
    have h := congrArg ShortComplex.Hom.τ₁ eS.inv_hom_id
    change eS.inv.τ₁ ≫ eS.hom.τ₁ = 𝟙 S.X₁ at h
    exact h
  have heS₂ : eS.inv.τ₂ ≫ eS.hom.τ₂ = 𝟙 S.X₂ := by
    have h := congrArg ShortComplex.Hom.τ₂ eS.inv_hom_id
    change eS.inv.τ₂ ≫ eS.hom.τ₂ = 𝟙 S.X₂ at h
    exact h
  have heR₁ : eR.inv.τ₁ ≫ eR.hom.τ₁ = 𝟙 R.X₁ := by
    have h := congrArg ShortComplex.Hom.τ₁ eR.inv_hom_id
    change eR.inv.τ₁ ≫ eR.hom.τ₁ = 𝟙 R.X₁ at h
    exact h
  have heR₂ : eR.inv.τ₂ ≫ eR.hom.τ₂ = 𝟙 R.X₂ := by
    have h := congrArg ShortComplex.Hom.τ₂ eR.inv_hom_id
    change eR.inv.τ₂ ≫ eR.hom.τ₂ = 𝟙 R.X₂ at h
    exact h
  have heq₁ : eS.inv.τ₁ ≫ psi.τ₁ ≫ eR.hom.τ₁ = phi.τ₁ := by
    calc
      eS.inv.τ₁ ≫ psi.τ₁ ≫ eR.hom.τ₁ =
          (eS.inv.τ₁ ≫ eS.hom.τ₁) ≫ phi.τ₁ ≫
            (eR.inv.τ₁ ≫ eR.hom.τ₁) := by
        simp only [psi, ShortComplex.comp_τ₁, Category.assoc]
      _ = phi.τ₁ := by
        rw [heS₁, heR₁, Category.id_comp, Category.comp_id]
  have heq₂ : eS.inv.τ₂ ≫ psi.τ₂ ≫ eR.hom.τ₂ = phi.τ₂ := by
    calc
      eS.inv.τ₂ ≫ psi.τ₂ ≫ eR.hom.τ₂ =
          (eS.inv.τ₂ ≫ eS.hom.τ₂) ≫ phi.τ₂ ≫
            (eR.inv.τ₂ ≫ eR.hom.τ₂) := by
        simp only [psi, ShortComplex.comp_τ₂, Category.assoc]
      _ = phi.τ₂ := by
        rw [heS₂, heR₂, Category.id_comp, Category.comp_id]
  exact ⟨heq₁ ▸ hback₁, heq₂ ▸ hback₂⟩

/-- One reversed cross-ladder domination rung.

The input is a square from the current essential left arrow to the next
zero-padded right arrow, split monic on sources.  The output is a square from
the next zero-padded left arrow to the previous essential right arrow, split
monic on both components. -/
theorem exists_reversedStrongDomination_rung_data
    (T : FiniteTauCategoryData C Ind)
    {YLPrev ZLPrev YLNext ZLNext UL : C}
    {ZRPrev YRPrev ZRNext YRNext UR : C}
    (dPrev : YLPrev ⟶ ZLPrev) (dNext : YLNext ⟶ ZLNext)
    (lf : YLPrev ⟶ YLNext) (lg : ZLPrev ⟶ ZLNext)
    (lh : ZLPrev ⟶ UL)
    (lcomm : lf ≫ dNext = dPrev ≫ lg)
    (lhzero : dPrev ≫ lh = 0)
    (bPrev : ZRPrev ⟶ YRPrev) (bNext : ZRNext ⟶ YRNext)
    (rf : YRNext ⟶ YRPrev) (rg : ZRNext ⟶ ZRPrev)
    (rh : UR ⟶ ZRPrev)
    (rcomm : bNext ≫ rf = rg ≫ bPrev)
    (rhzero : rh ≫ bPrev = 0)
    (eLeft : Nonempty
      (T.leftMesh YLPrev ≅
        LeftLadder.stepComplex dPrev dNext lf lg lh lcomm lhzero))
    (eRight : Nonempty
      (T.rightMesh YRPrev ≅
        RightLadder.stepComplex bPrev bNext rf rg rh rcomm rhzero))
    (square : Arrow.mk dPrev ⟶
      Arrow.mk (biprod.desc bNext (0 : UR ⟶ YRNext)))
    (hsquare : IsSplitMono square.left) :
    ∃ phiStep :
        LeftLadder.stepComplex dPrev dNext lf lg lh lcomm lhzero ⟶
          RightLadder.stepComplex bPrev bNext rf rg rh rcomm rhzero,
      ∃ nextSquare :
        Arrow.mk (biprod.lift dNext (0 : YLNext ⟶ UL)) ⟶
          Arrow.mk bPrev,
        IsSplitMono phiStep.τ₁ ∧ IsSplitMono phiStep.τ₂ ∧
          IsSplitMono phiStep.τ₃ ∧
          IsSplitMono nextSquare.left ∧ IsSplitMono nextSquare.right ∧
          nextSquare.right = phiStep.τ₃ ∧
          square.left = phiStep.τ₁ ∧
          square.right =
            (biprod.inr : ZLPrev ⟶ YLNext ⊞ ZLPrev) ≫
              phiStep.τ₂ ≫
                (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) ∧
          (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫
              phiStep.τ₂ ≫
                (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) = 0 := by
  obtain ⟨eL⟩ := eLeft
  obtain ⟨eR⟩ := eRight
  let source : YLPrev ⟶ ZRNext ⊞ UR := square.left
  let target : ZLPrev ⟶ YRNext := square.right
  have hsource : IsSplitMono source := hsquare
  have hsquareComm :
      source ≫ biprod.desc bNext (0 : UR ⟶ YRNext) =
        dPrev ≫ target := square.w
  let leftFirst : YLPrev ⟶ YLNext ⊞ ZLPrev :=
    biprod.lift lf dPrev
  let leftSecond : YLNext ⊞ ZLPrev ⟶ ZLNext ⊞ UL :=
    biprod.lift (biprod.desc dNext (-lg)) (biprod.desc 0 lh)
  let rightFirst : ZRNext ⊞ UR ⟶ YRNext ⊞ ZRPrev :=
    biprod.desc (biprod.lift bNext (-rg)) (biprod.lift 0 rh)
  let rightSecond : YRNext ⊞ ZRPrev ⟶ YRPrev :=
    biprod.desc rf bPrev
  have hrightFirst : IsRadicalMorphism rightFirst := by
    have h := (T.rightTau YRPrev).toTauApproximation.f_radical_of_iso eR
    change IsRadicalMorphism rightFirst at h
    exact h
  let rightSourceComponent : ZRNext ⊞ UR ⟶ ZRPrev :=
    rightFirst ≫ biprod.snd
  have hrightSourceComponent : IsRadicalMorphism rightSourceComponent :=
    isRadicalMorphism_postcomp biprod.snd hrightFirst
  let factorInput : YLPrev ⟶ ZRPrev := source ≫ rightSourceComponent
  have hfactorInput : IsRadicalMorphism factorInput :=
    isRadicalMorphism_precomp source hrightSourceComponent
  let eLHom₁ : (T.leftMesh YLPrev).X₁ ⟶ YLPrev := eL.hom.τ₁
  let eLInv₁ : YLPrev ⟶ (T.leftMesh YLPrev).X₁ := eL.inv.τ₁
  let eLInv₂ : YLNext ⊞ ZLPrev ⟶ (T.leftMesh YLPrev).X₂ :=
    eL.inv.τ₂
  have htoMesh : IsRadicalMorphism (eLHom₁ ≫ factorInput) :=
    isRadicalMorphism_precomp eLHom₁ hfactorInput
  obtain ⟨q, hq⟩ :=
    (T.leftTau YLPrev).factors_from_left
      (eLHom₁ ≫ factorInput) htoMesh
  let secondComponent : YLNext ⊞ ZLPrev ⟶ ZRPrev := eLInv₂ ≫ q
  have heL₁ : eLInv₁ ≫ eLHom₁ = 𝟙 YLPrev := by
    have h := congrArg ShortComplex.Hom.τ₁ eL.inv_hom_id
    change eLInv₁ ≫ eLHom₁ = 𝟙 YLPrev at h
    exact h
  have heLcomm :
      leftFirst ≫ eLInv₂ = eLInv₁ ≫ (T.leftMesh YLPrev).f := by
    have h := eL.inv.comm₁₂
    change eLInv₁ ≫ (T.leftMesh YLPrev).f =
      leftFirst ≫ eLInv₂ at h
    exact h.symm
  have hsecondComponent : leftFirst ≫ secondComponent = factorInput := by
    calc
      leftFirst ≫ secondComponent =
          (leftFirst ≫ eLInv₂) ≫ q := by
        simp only [secondComponent, Category.assoc]
      _ = (eLInv₁ ≫ (T.leftMesh YLPrev).f) ≫ q := by
        rw [heLcomm]
      _ = eLInv₁ ≫ ((T.leftMesh YLPrev).f ≫ q) :=
        Category.assoc _ _ _
      _ = eLInv₁ ≫ (eLHom₁ ≫ factorInput) := by rw [hq]
      _ = (eLInv₁ ≫ eLHom₁) ≫ factorInput :=
        (Category.assoc _ _ _).symm
      _ = factorInput := by rw [heL₁, Category.id_comp]
  let firstComponent : YLNext ⊞ ZLPrev ⟶ YRNext :=
    biprod.desc 0 target
  let middle : YLNext ⊞ ZLPrev ⟶ YRNext ⊞ ZRPrev :=
    biprod.lift firstComponent secondComponent
  have hrightFirstFst :
      rightFirst ≫ (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) =
        biprod.desc bNext (0 : UR ⟶ YRNext) := by
    apply biprod.hom_ext' <;> simp [rightFirst]
  have hmiddleFst :
      middle ≫ (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) =
        firstComponent := by
    simp [middle]
  have hmiddle : source ≫ rightFirst = leftFirst ≫ middle := by
    apply biprod.hom_ext
    · calc
        (source ≫ rightFirst) ≫
            (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) =
          source ≫ (rightFirst ≫ biprod.fst) := Category.assoc _ _ _
        _ = source ≫ biprod.desc bNext (0 : UR ⟶ YRNext) := by
          rw [hrightFirstFst]
        _ = dPrev ≫ target := hsquareComm
        _ = leftFirst ≫ firstComponent := by
          simp [leftFirst, firstComponent]
        _ = leftFirst ≫ (middle ≫ biprod.fst) := by rw [hmiddleFst]
        _ = (leftFirst ≫ middle) ≫ biprod.fst :=
          (Category.assoc _ _ _).symm
    · simpa [rightSourceComponent, factorInput, middle,
        Category.assoc] using hsecondComponent.symm
  have hweakLeft : ShortComplex.IsWeakCokernel
      (LeftLadder.stepComplex dPrev dNext lf lg lh lcomm lhzero) :=
    (T.leftTau YLPrev).minimalWeakCokernel.1.of_iso eL
  have hrightZero : rightFirst ≫ rightSecond = 0 :=
    (RightLadder.stepComplex bPrev bNext rf rg rh rcomm rhzero).zero
  have hcokernel : leftFirst ≫ (middle ≫ rightSecond) = 0 := by
    calc
      leftFirst ≫ (middle ≫ rightSecond) =
          (leftFirst ≫ middle) ≫ rightSecond :=
        (Category.assoc _ _ _).symm
      _ = (source ≫ rightFirst) ≫ rightSecond := by rw [hmiddle]
      _ = source ≫ (rightFirst ≫ rightSecond) :=
        Category.assoc _ _ _
      _ = 0 := by rw [hrightZero, comp_zero]
  obtain ⟨targetNext, htargetNext⟩ :=
    (ShortComplex.isWeakCokernel_iff
      (LeftLadder.stepComplex dPrev dNext lf lg lh lcomm lhzero)).mp
      hweakLeft (middle ≫ rightSecond) hcokernel
  let targetMap : ZLNext ⊞ UL ⟶ YRPrev := targetNext
  have htargetMap :
      leftSecond ≫ targetMap = middle ≫ rightSecond := by
    change leftSecond ≫ targetMap = middle ≫ rightSecond at htargetNext
    exact htargetNext
  let phiStep :
      LeftLadder.stepComplex dPrev dNext lf lg lh lcomm lhzero ⟶
        RightLadder.stepComplex bPrev bNext rf rg rh rcomm rhzero :=
    { τ₁ := source
      τ₂ := middle
      τ₃ := targetMap
      comm₁₂ := hmiddle
      comm₂₃ := htargetMap.symm }
  have hsplit := splitMono_components_of_displayed_steps
    T eL eR phiStep hsource
  have hmiddleSplit : IsSplitMono middle := by
    have h := hsplit.1
    change IsSplitMono middle at h
    exact h
  have htargetSplit : IsSplitMono targetMap := by
    have h := hsplit.2
    change IsSplitMono targetMap at h
    exact h
  let sourceNext : YLNext ⟶ ZRPrev :=
    biprod.inl ≫ middle ≫ biprod.snd
  have hinlMiddle :
      (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫ middle =
        biprod.lift (0 : YLNext ⟶ YRNext) sourceNext := by
    apply biprod.hom_ext
    · simp [middle, firstComponent, sourceNext, Category.assoc]
    · simp [middle, firstComponent, sourceNext, Category.assoc]
  have hsourceInr :
      sourceNext ≫ (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev) =
        biprod.lift (0 : YLNext ⟶ YRNext) sourceNext := by
    apply biprod.hom_ext <;> simp
  letI : IsSplitMono middle := hmiddleSplit
  have hinlMiddleSplit : IsSplitMono
      ((biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫ middle) := by
    infer_instance
  have hliftSplit : IsSplitMono
      (biprod.lift (0 : YLNext ⟶ YRNext) sourceNext) := by
    rw [← hinlMiddle]
    exact hinlMiddleSplit
  have hsourceInrSplit : IsSplitMono
      (sourceNext ≫ (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev)) := by
    rw [hsourceInr]
    exact hliftSplit
  letI : IsSplitMono
      (sourceNext ≫ (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev)) :=
    hsourceInrSplit
  have hsourceNextSplit : IsSplitMono sourceNext :=
    isSplitMono_of_isSplitMono_postcomp sourceNext
      (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev)
  have hinlMiddle' :
      (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫ middle =
        sourceNext ≫ (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev) :=
    hinlMiddle.trans hsourceInr.symm
  have hleftInl :
      (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫ leftSecond =
        biprod.lift dNext (0 : YLNext ⟶ UL) := by
    apply biprod.hom_ext <;> simp [leftSecond]
  have hrightInr :
      (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev) ≫ rightSecond =
        bPrev := by
    simp [rightSecond]
  have hnextComm :
      sourceNext ≫ bPrev =
        biprod.lift dNext (0 : YLNext ⟶ UL) ≫ targetMap := by
    calc
      sourceNext ≫ bPrev =
          sourceNext ≫
            ((biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev) ≫
              rightSecond) := by rw [hrightInr]
      _ = (sourceNext ≫
            (biprod.inr : ZRPrev ⟶ YRNext ⊞ ZRPrev)) ≫
              rightSecond := (Category.assoc _ _ _).symm
      _ = ((biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫ middle) ≫
          rightSecond := by rw [hinlMiddle']
      _ = (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫
          (middle ≫ rightSecond) := Category.assoc _ _ _
      _ = (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫
          (leftSecond ≫ targetMap) := by rw [htargetMap]
      _ = ((biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫ leftSecond) ≫
          targetMap := (Category.assoc _ _ _).symm
      _ = biprod.lift dNext (0 : YLNext ⟶ UL) ≫ targetMap := by
        rw [hleftInl]
  let nextSquare :
      Arrow.mk (biprod.lift dNext (0 : YLNext ⟶ UL)) ⟶
        Arrow.mk bPrev :=
    { left := sourceNext
      right := targetMap
      w := hnextComm }
  have hinputTargetBlock : square.right =
      (biprod.inr : ZLPrev ⟶ YLNext ⊞ ZLPrev) ≫
        phiStep.τ₂ ≫
          (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) := by
    change target = biprod.inr ≫ middle ≫ biprod.fst
    simp [middle, firstComponent, target]
  have hzeroBlock :
      (biprod.inl : YLNext ⟶ YLNext ⊞ ZLPrev) ≫
          phiStep.τ₂ ≫
            (biprod.fst : YRNext ⊞ ZRPrev ⟶ YRNext) = 0 := by
    change biprod.inl ≫ middle ≫ biprod.fst = 0
    simp [middle, firstComponent]
  exact ⟨phiStep, nextSquare, hsource, hmiddleSplit, htargetSplit,
    hsourceNextSplit, htargetSplit, rfl, rfl, hinputTargetBlock, hzeroBlock⟩

/-- The split-monic output-square projection of the full reversed-rung
comparison data. -/
theorem exists_reversedStrongDomination_rung
    (T : FiniteTauCategoryData C Ind)
    {YLPrev ZLPrev YLNext ZLNext UL : C}
    {ZRPrev YRPrev ZRNext YRNext UR : C}
    (dPrev : YLPrev ⟶ ZLPrev) (dNext : YLNext ⟶ ZLNext)
    (lf : YLPrev ⟶ YLNext) (lg : ZLPrev ⟶ ZLNext)
    (lh : ZLPrev ⟶ UL)
    (lcomm : lf ≫ dNext = dPrev ≫ lg)
    (lhzero : dPrev ≫ lh = 0)
    (bPrev : ZRPrev ⟶ YRPrev) (bNext : ZRNext ⟶ YRNext)
    (rf : YRNext ⟶ YRPrev) (rg : ZRNext ⟶ ZRPrev)
    (rh : UR ⟶ ZRPrev)
    (rcomm : bNext ≫ rf = rg ≫ bPrev)
    (rhzero : rh ≫ bPrev = 0)
    (eLeft : Nonempty
      (T.leftMesh YLPrev ≅
        LeftLadder.stepComplex dPrev dNext lf lg lh lcomm lhzero))
    (eRight : Nonempty
      (T.rightMesh YRPrev ≅
        RightLadder.stepComplex bPrev bNext rf rg rh rcomm rhzero))
    (square : Arrow.mk dPrev ⟶
      Arrow.mk (biprod.desc bNext (0 : UR ⟶ YRNext)))
    (hsquare : IsSplitMono square.left) :
    ∃ nextSquare :
        Arrow.mk (biprod.lift dNext (0 : YLNext ⟶ UL)) ⟶
          Arrow.mk bPrev,
      IsSplitMono nextSquare.left ∧ IsSplitMono nextSquare.right := by
  obtain ⟨_, nextSquare, _, _, _, hleft, hright, _, _, _, _⟩ :=
    exists_reversedStrongDomination_rung_data T
      dPrev dNext lf lg lh lcomm lhzero
      bPrev bNext rf rg rh rcomm rhzero
      eLeft eRight square hsquare
  exact ⟨nextSquare, hleft, hright⟩

/-! ## Global reversed propagation -/

/-- A right-ladder prefix whose indexing has already been reversed, so its
rung `i` runs from the arrow at `i.castSucc` to the arrow at `i.succ`.
This removes all subtraction arithmetic from the propagation theorem. -/
structure ReversedRightPrefix
    (T : FiniteTauCategoryData C Ind) (n : ℕ) where
  Z : Fin (n + 1) → C
  Y : Fin (n + 1) → C
  U : Fin (n + 1) → C
  b : ∀ i, Z i ⟶ Y i
  f : ∀ i : Fin n, Y i.castSucc ⟶ Y i.succ
  g : ∀ i : Fin n, Z i.castSucc ⟶ Z i.succ
  h : ∀ i : Fin n, U i.castSucc ⟶ Z i.succ
  comm : ∀ i : Fin n, b i.castSucc ≫ f i = g i ≫ b i.succ
  hzero : ∀ i : Fin n, h i ≫ b i.succ = 0
  meshIso : ∀ i : Fin n, Nonempty
    (T.rightMesh (Y i.succ) ≅
      RightLadder.stepComplex (b i.succ) (b i.castSucc)
        (f i) (g i) (h i) (comm i) (hzero i))

def ReversedRightPrefix.paddedArrow
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (i : Fin (n + 1)) :
    R.Z i ⊞ R.U i ⟶ R.Y i :=
  biprod.desc (R.b i) 0

/-- A chosen split-monic piece of the complementary object at the reversed
boundary.  Taking a chosen indecomposable summand here is sufficient for the
comparison and avoids any indecomposability hypothesis on the whole
complement. -/
structure BoundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (U₀ : C) where
  hom : U₀ ⟶ R.U 0
  isSplitMono : IsSplitMono hom

/-- The original whole-boundary comparison is the identity special case. -/
def BoundaryEmbedding.identity
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) : BoundaryEmbedding R (R.U 0) where
  hom := 𝟙 _
  isSplitMono := inferInstance

/-- The split-monic comparison state along an aligned reversed prefix. -/
def DiagonalComparisonAt
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) : Prop :=
  ∃ q : Arrow.mk (L.b i) ⟶ Arrow.mk (R.paddedArrow i),
    IsSplitMono q.left ∧ IsSplitMono q.right

/-- A split-monic boundary piece gives the first diagonal comparison
square. -/
theorem diagonalComparisonAt_zero_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding R U₀) :
    DiagonalComparisonAt R L 0 := by
  let source : L.Y 0 ⟶ R.Z 0 ⊞ R.U 0 :=
    L.initialSourceIso.inv ≫ E.hom ≫ biprod.inr
  let target : L.Z 0 ⟶ R.Y 0 := 0
  have hcomm : source ≫ R.paddedArrow 0 = L.b 0 ≫ target := by
    simp [source, target, ReversedRightPrefix.paddedArrow, Category.assoc]
  let q : Arrow.mk (L.b 0) ⟶ Arrow.mk (R.paddedArrow 0) :=
    { left := source
      right := target
      w := hcomm }
  have hsource : IsSplitMono source := by
    dsimp only [source]
    have hfirst : IsSplitMono (L.initialSourceIso.inv ≫ E.hom) :=
      isSplitMono_comp_of_isSplitMono L.initialSourceIso.inv E.hom
        (by infer_instance) E.isSplitMono
    simpa only [Category.assoc] using
      (isSplitMono_comp_of_isSplitMono
        (L.initialSourceIso.inv ≫ E.hom)
        (biprod.inr : R.U 0 ⟶ R.Z 0 ⊞ R.U 0)
        hfirst (by infer_instance))
  have htarget : IsSplitMono target := by
    apply IsSplitMono.mk'
    exact
      { retraction := 0
        id := L.initialTargetZero.eq_of_src _ _ }
  exact ⟨q, hsource, htarget⟩

/-- The zero boundary gives the first diagonal comparison square when the
whole complementary object is used. -/
theorem diagonalComparisonAt_zero
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n) :
    DiagonalComparisonAt R L 0 :=
  diagonalComparisonAt_zero_of_boundaryEmbedding R L
    (BoundaryEmbedding.identity R)

/-- One aligned diagonal propagation step. -/
theorem diagonalComparisonAt_succ
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin n) (h : DiagonalComparisonAt R L i.castSucc) :
    DiagonalComparisonAt R L i.succ := by
  obtain ⟨inputSquare, hinputSource, _⟩ := h
  obtain ⟨rungSquare, hrungSource, hrungTarget⟩ :=
    exists_reversedStrongDomination_rung T
      (L.b i.castSucc) (L.b i.succ)
      (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i)
      (R.b i.succ) (R.b i.castSucc)
      (R.f i) (R.g i) (R.h i) (R.comm i) (R.hzero i)
      (L.meshIso i) (R.meshIso i) inputSquare hinputSource
  let leftPadding : Arrow.mk (L.b i.succ) ⟶
      Arrow.mk (L.paddedArrow i.succ) :=
    { left := 𝟙 _
      right := biprod.inl
      w := by
        change 𝟙 _ ≫ biprod.lift (L.b i.succ) 0 =
          L.b i.succ ≫ biprod.inl
        rw [Category.id_comp]
        apply biprod.hom_ext <;> simp }
  let rightPadding : Arrow.mk (R.b i.succ) ⟶
      Arrow.mk (R.paddedArrow i.succ) :=
    { left := biprod.inl
      right := 𝟙 _
      w := by
        change biprod.inl ≫ biprod.desc (R.b i.succ) 0 =
          R.b i.succ ≫ 𝟙 _
        rw [biprod.inl_desc, Category.comp_id] }
  let nextSquare : Arrow.mk (L.b i.succ) ⟶
      Arrow.mk (R.paddedArrow i.succ) :=
    leftPadding ≫ rungSquare ≫ rightPadding
  have hnextSource : IsSplitMono nextSquare.left := by
    change IsSplitMono
      ((𝟙 (L.Y i.succ)) ≫ rungSquare.left ≫
        (biprod.inl : R.Z i.succ ⟶ R.Z i.succ ⊞ R.U i.succ))
    have hsecond := isSplitMono_comp_of_isSplitMono rungSquare.left
      (biprod.inl : R.Z i.succ ⟶ R.Z i.succ ⊞ R.U i.succ)
      hrungSource (by infer_instance)
    exact isSplitMono_comp_of_isSplitMono
      (𝟙 (L.Y i.succ))
      (rungSquare.left ≫
        (biprod.inl : R.Z i.succ ⟶ R.Z i.succ ⊞ R.U i.succ))
      (by infer_instance) hsecond
  have hnextTarget : IsSplitMono nextSquare.right := by
    change IsSplitMono
      ((biprod.inl : L.Z i.succ ⟶ L.Z i.succ ⊞ L.U i.succ) ≫
        rungSquare.right ≫ 𝟙 (R.Y i.succ))
    have hid : IsSplitMono (𝟙 (R.Y i.succ)) := by
      apply IsSplitMono.mk'
      exact { retraction := 𝟙 _ }
    have hsecond := isSplitMono_comp_of_isSplitMono rungSquare.right
      (𝟙 (R.Y i.succ)) hrungTarget hid
    exact isSplitMono_comp_of_isSplitMono
      (biprod.inl : L.Z i.succ ⟶ L.Z i.succ ⊞ L.U i.succ)
      (rungSquare.right ≫ 𝟙 (R.Y i.succ))
      (by infer_instance) hsecond
  exact ⟨nextSquare, hnextSource, hnextTarget⟩

/-- The comparison propagates across every rung of an aligned finite
window. -/
theorem diagonalComparisonAt_all_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding R U₀) :
    ∀ i : Fin (n + 1), DiagonalComparisonAt R L i := by
  intro i
  induction i using Fin.induction with
  | zero => exact diagonalComparisonAt_zero_of_boundaryEmbedding R L E
  | succ i ih => exact diagonalComparisonAt_succ R L i ih

/-- Whole-boundary specialization of global propagation. -/
theorem diagonalComparisonAt_all
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n) :
    ∀ i : Fin (n + 1), DiagonalComparisonAt R L i := by
  exact diagonalComparisonAt_all_of_boundaryEmbedding R L
    (BoundaryEmbedding.identity R)

/-! ## The terminal four-cycle -/

/-- The literal inclusion of a right-ladder essential arrow into its
zero-padded arrow. -/
def ReversedRightPrefix.essentialToPaddedSquare
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (i : Fin (n + 1)) :
    Arrow.mk (R.b i) ⟶ Arrow.mk (R.paddedArrow i) :=
  { left := biprod.inl
    right := 𝟙 _
    w := by
      change biprod.inl ≫ biprod.desc (R.b i) 0 = R.b i ≫ 𝟙 _
      rw [biprod.inl_desc, Category.comp_id] }

/-- Both components of the right zero-padding square are split monic. -/
theorem ReversedRightPrefix.essentialToPaddedSquare_components
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n) (i : Fin (n + 1)) :
    IsSplitMono (R.essentialToPaddedSquare i).left ∧
      IsSplitMono (R.essentialToPaddedSquare i).right := by
  constructor
  · change IsSplitMono
      (biprod.inl : R.Z i ⟶ R.Z i ⊞ R.U i)
    infer_instance
  · change IsSplitMono (𝟙 (R.Y i))
    infer_instance

/-- The literal inclusion of a left-ladder essential arrow into its
zero-padded arrow. -/
def leftEssentialToPaddedSquare
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) :
    Arrow.mk (L.b i) ⟶ Arrow.mk (L.paddedArrow i) :=
  { left := 𝟙 _
    right := biprod.inl
    w := by
      change 𝟙 _ ≫ biprod.lift (L.b i) 0 = L.b i ≫ biprod.inl
      rw [Category.id_comp]
      apply biprod.hom_ext <;> simp }

/-- Both components of the left zero-padding square are split monic. -/
theorem leftEssentialToPaddedSquare_components
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin (n + 1)) :
    IsSplitMono (leftEssentialToPaddedSquare L i).left ∧
      IsSplitMono (leftEssentialToPaddedSquare L i).right := by
  constructor
  · change IsSplitMono (𝟙 (L.Y i))
    infer_instance
  · change IsSplitMono
      (biprod.inl : L.Z i ⟶ L.Z i ⊞ L.U i)
    infer_instance

/-- The middle edge of the domination chain produced by one reversed rung:
the previous essential right arrow contains the next padded left arrow. -/
def CrossComparisonAt
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (i : Fin n) : Prop :=
  ∃ q : Arrow.mk (L.paddedArrow i.succ) ⟶ Arrow.mk (R.b i.succ),
    IsSplitMono q.left ∧ IsSplitMono q.right

/-- Extract the middle edge before composing it with the two padding
inclusions. -/
theorem crossComparisonAt_succ
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (i : Fin n) (h : DiagonalComparisonAt R L i.castSucc) :
    CrossComparisonAt R L i := by
  obtain ⟨inputSquare, hinputSource, _⟩ := h
  exact exists_reversedStrongDomination_rung T
    (L.b i.castSucc) (L.b i.succ)
    (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i)
    (R.b i.succ) (R.b i.castSucc)
    (R.f i) (R.g i) (R.h i) (R.comm i) (R.hzero i)
    (L.meshIso i) (R.meshIso i) inputSquare hinputSource

/-- Every rung of an aligned finite window supplies its uncomposed middle
domination edge. -/
theorem crossComparisonAt_all
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n) :
    ∀ i : Fin n, CrossComparisonAt R L i := by
  intro i
  exact crossComparisonAt_succ R L i
    (diagonalComparisonAt_all R L i.castSucc)

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Two split-monic arrow squares in opposite directions are inverse up to
arrow isomorphism when endomorphisms of the receiving endpoints are directly
finite. -/
theorem nonempty_arrow_iso_of_mutual_splitMono_squares
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (d : Arrow.mk b ⟶ Arrow.mk a)
    (hdleft : IsSplitMono d.left) (hdright : IsSplitMono d.right)
    (e : Arrow.mk a ⟶ Arrow.mk b)
    (heleft : IsSplitMono e.left) (heright : IsSplitMono e.right) :
    Nonempty (Arrow.mk a ≅ Arrow.mk b) := by
  letI : IsSplitMono d.left := hdleft
  letI : IsSplitMono d.right := hdright
  letI : IsSplitMono e.left := heleft
  letI : IsSplitMono e.right := heright
  have hleftCompSplit : IsSplitMono (e.left ≫ d.left) := inferInstance
  have hrightCompSplit : IsSplitMono (e.right ≫ d.right) := inferInstance
  haveI hleftCompIso : IsIso (e.left ≫ d.left) :=
    hfinite Xa _ hleftCompSplit
  haveI hrightCompIso : IsIso (e.right ≫ d.right) :=
    hfinite Ya _ hrightCompSplit
  have hdleftEpi : IsSplitEpi d.left := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.left ≫ d.left) ≫ e.left
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  have hdrightEpi : IsSplitEpi d.right := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.right ≫ d.right) ≫ e.right
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi d.left := hdleftEpi
  letI : IsSplitEpi d.right := hdrightEpi
  have hdleftIso : IsIso d.left :=
    isIso_of_mono_of_isSplitEpi d.left
  have hdrightIso : IsIso d.right :=
    isIso_of_mono_of_isSplitEpi d.right
  letI : IsIso d.left := hdleftIso
  letI : IsIso d.right := hdrightIso
  have hdIso : IsIso d :=
    Arrow.isIso_of_isIso_left_of_isIso_right d
  letI : IsIso d := hdIso
  exact ⟨(asIso d).symm⟩

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The forward square itself is componentwise invertible under the same
mutual-domination and direct-finiteness hypotheses. -/
theorem isIso_components_of_mutual_splitMono_squares
    (hfinite : ∀ (X : C) (f : X ⟶ X), IsSplitMono f → IsIso f)
    {Xa Ya Xb Yb : C} {a : Xa ⟶ Ya} {b : Xb ⟶ Yb}
    (d : Arrow.mk b ⟶ Arrow.mk a)
    (hdleft : IsSplitMono d.left) (hdright : IsSplitMono d.right)
    (e : Arrow.mk a ⟶ Arrow.mk b)
    (heleft : IsSplitMono e.left) (heright : IsSplitMono e.right) :
    IsIso d.left ∧ IsIso d.right := by
  letI : IsSplitMono d.left := hdleft
  letI : IsSplitMono d.right := hdright
  letI : IsSplitMono e.left := heleft
  letI : IsSplitMono e.right := heright
  have hleftCompSplit : IsSplitMono (e.left ≫ d.left) := inferInstance
  have hrightCompSplit : IsSplitMono (e.right ≫ d.right) := inferInstance
  haveI hleftCompIso : IsIso (e.left ≫ d.left) :=
    hfinite Xa _ hleftCompSplit
  haveI hrightCompIso : IsIso (e.right ≫ d.right) :=
    hfinite Ya _ hrightCompSplit
  have hdleftEpi : IsSplitEpi d.left := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.left ≫ d.left) ≫ e.left
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  have hdrightEpi : IsSplitEpi d.right := by
    apply IsSplitEpi.mk'
    exact
      { section_ := inv (e.right ≫ d.right) ≫ e.right
        id := by rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi d.left := hdleftEpi
  letI : IsSplitEpi d.right := hdrightEpi
  exact ⟨isIso_of_mono_of_isSplitEpi d.left,
    isIso_of_mono_of_isSplitEpi d.right⟩

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- In an invertible biproduct matrix with zero upper-left block, the
upper-right block is split epic.  Its section is the lower-left block of the
inverse matrix. -/
theorem isSplitEpi_biprod_inr_comp_fst_of_isIso
    {A B D E : C} (m : A ⊞ B ⟶ D ⊞ E) (hm : IsIso m)
    (hzero :
      (biprod.inl : A ⟶ A ⊞ B) ≫ m ≫
        (biprod.fst : D ⊞ E ⟶ D) = 0) :
    IsSplitEpi
      ((biprod.inr : B ⟶ A ⊞ B) ≫ m ≫
        (biprod.fst : D ⊞ E ⟶ D)) := by
  letI : IsIso m := hm
  apply IsSplitEpi.mk'
  let s : D ⟶ B :=
    (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫ biprod.snd
  refine { section_ := s, id := ?_ }
  have hfirst :
      (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
          (biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl ≫ m ≫
            (biprod.fst : D ⊞ E ⟶ D) = 0 := by
    rw [hzero, comp_zero, comp_zero, comp_zero]
  calc
    s ≫ biprod.inr ≫ m ≫ biprod.fst =
        0 + s ≫ biprod.inr ≫ m ≫ biprod.fst := by simp
    _ =
        (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
            (biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl ≫ m ≫
              (biprod.fst : D ⊞ E ⟶ D) +
          s ≫ biprod.inr ≫ m ≫ biprod.fst := by rw [hfirst]
    _ =
        (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
          ((biprod.fst : A ⊞ B ⟶ A) ≫ biprod.inl +
            (biprod.snd : A ⊞ B ⟶ B) ≫ biprod.inr) ≫
              m ≫ (biprod.fst : D ⊞ E ⟶ D) := by
        simp only [s, Preadditive.comp_add, Preadditive.add_comp,
          Category.assoc]
    _ =
        (biprod.inl : D ⟶ D ⊞ E) ≫ inv m ≫
          𝟙 (A ⊞ B) ≫ m ≫
            (biprod.fst : D ⊞ E ⟶ D) := by rw [biprod.total]
    _ = 𝟙 D := by simp

omit [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Four split-monic arrow squares which close to a cycle make every edge an
arrow isomorphism under direct finiteness. -/
theorem nonempty_adjacent_arrow_isos_of_splitMono_four_cycle
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    {X₀ Y₀ X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    {a₀ : X₀ ⟶ Y₀} {a₁ : X₁ ⟶ Y₁}
    {a₂ : X₂ ⟶ Y₂} {a₃ : X₃ ⟶ Y₃}
    (q₀₁ : Arrow.mk a₁ ⟶ Arrow.mk a₀)
    (h₀₁l : IsSplitMono q₀₁.left)
    (h₀₁r : IsSplitMono q₀₁.right)
    (q₁₂ : Arrow.mk a₂ ⟶ Arrow.mk a₁)
    (h₁₂l : IsSplitMono q₁₂.left)
    (h₁₂r : IsSplitMono q₁₂.right)
    (q₂₃ : Arrow.mk a₃ ⟶ Arrow.mk a₂)
    (h₂₃l : IsSplitMono q₂₃.left)
    (h₂₃r : IsSplitMono q₂₃.right)
    (q₃₀ : Arrow.mk a₀ ⟶ Arrow.mk a₃)
    (h₃₀l : IsSplitMono q₃₀.left)
    (h₃₀r : IsSplitMono q₃₀.right) :
    Nonempty (Arrow.mk a₀ ≅ Arrow.mk a₁) ∧
      Nonempty (Arrow.mk a₁ ≅ Arrow.mk a₂) ∧
      Nonempty (Arrow.mk a₂ ≅ Arrow.mk a₃) ∧
      Nonempty (Arrow.mk a₃ ≅ Arrow.mk a₀) := by
  have hcomp₁₀l : IsSplitMono
      (q₃₀.left ≫ q₂₃.left ≫ q₁₂.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₃₀l (isSplitMono_comp_of_isSplitMono _ _ h₂₃l h₁₂l)
  have hcomp₁₀r : IsSplitMono
      (q₃₀.right ≫ q₂₃.right ≫ q₁₂.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₃₀r (isSplitMono_comp_of_isSplitMono _ _ h₂₃r h₁₂r)
  have hcomp₂₁l : IsSplitMono
      (q₀₁.left ≫ q₃₀.left ≫ q₂₃.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₀₁l (isSplitMono_comp_of_isSplitMono _ _ h₃₀l h₂₃l)
  have hcomp₂₁r : IsSplitMono
      (q₀₁.right ≫ q₃₀.right ≫ q₂₃.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₀₁r (isSplitMono_comp_of_isSplitMono _ _ h₃₀r h₂₃r)
  have hcomp₃₂l : IsSplitMono
      (q₁₂.left ≫ q₀₁.left ≫ q₃₀.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₁₂l (isSplitMono_comp_of_isSplitMono _ _ h₀₁l h₃₀l)
  have hcomp₃₂r : IsSplitMono
      (q₁₂.right ≫ q₀₁.right ≫ q₃₀.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₁₂r (isSplitMono_comp_of_isSplitMono _ _ h₀₁r h₃₀r)
  have hcomp₀₃l : IsSplitMono
      (q₂₃.left ≫ q₁₂.left ≫ q₀₁.left) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₂₃l (isSplitMono_comp_of_isSplitMono _ _ h₁₂l h₀₁l)
  have hcomp₀₃r : IsSplitMono
      (q₂₃.right ≫ q₁₂.right ≫ q₀₁.right) := by
    exact isSplitMono_comp_of_isSplitMono _ _
      h₂₃r (isSplitMono_comp_of_isSplitMono _ _ h₁₂r h₀₁r)
  let q₁₀ : Arrow.mk a₀ ⟶ Arrow.mk a₁ :=
    q₃₀ ≫ q₂₃ ≫ q₁₂
  let q₂₁ : Arrow.mk a₁ ⟶ Arrow.mk a₂ :=
    q₀₁ ≫ q₃₀ ≫ q₂₃
  let q₃₂ : Arrow.mk a₂ ⟶ Arrow.mk a₃ :=
    q₁₂ ≫ q₀₁ ≫ q₃₀
  let q₀₃ : Arrow.mk a₃ ⟶ Arrow.mk a₀ :=
    q₂₃ ≫ q₁₂ ≫ q₀₁
  refine ⟨
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₀₁ h₀₁l h₀₁r q₁₀ hcomp₁₀l hcomp₁₀r,
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₁₂ h₁₂l h₁₂r q₂₁ hcomp₂₁l hcomp₂₁r,
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₂₃ h₂₃l h₂₃r q₃₂ hcomp₃₂l hcomp₃₂r,
    nonempty_arrow_iso_of_mutual_splitMono_squares hfinite
      q₃₀ h₃₀l h₃₀r q₀₃ hcomp₀₃l hcomp₀₃r⟩

/-- Closing one propagated reversed rung by an endpoint isomorphism yields
all three cancellation isomorphisms in the terminal diagonal.  The first is
exactly the previous-right-arrow cancellation needed by the finite ladder
certificate. -/
theorem terminal_four_cycle_adjacent_isos
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (i : Fin n)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hterminal : Nonempty
      (Arrow.mk (L.b i.succ) ≅ Arrow.mk (R.paddedArrow i.succ))) :
    Nonempty
        (Arrow.mk (R.paddedArrow i.succ) ≅ Arrow.mk (R.b i.succ)) ∧
      Nonempty
        (Arrow.mk (R.b i.succ) ≅ Arrow.mk (L.paddedArrow i.succ)) ∧
      Nonempty
        (Arrow.mk (L.paddedArrow i.succ) ≅ Arrow.mk (L.b i.succ)) ∧
      Nonempty
        (Arrow.mk (L.b i.succ) ≅ Arrow.mk (R.paddedArrow i.succ)) := by
  obtain ⟨q₁₂, hq₁₂l, hq₁₂r⟩ := crossComparisonAt_all R L i
  obtain ⟨e₃₀⟩ := hterminal
  let q₀₁ : Arrow.mk (R.b i.succ) ⟶
      Arrow.mk (R.paddedArrow i.succ) :=
    R.essentialToPaddedSquare i.succ
  let q₂₃ : Arrow.mk (L.b i.succ) ⟶
      Arrow.mk (L.paddedArrow i.succ) :=
    leftEssentialToPaddedSquare L i.succ
  let q₃₀ : Arrow.mk (R.paddedArrow i.succ) ⟶
      Arrow.mk (L.b i.succ) := e₃₀.inv
  obtain ⟨hq₀₁l, hq₀₁r⟩ :=
    R.essentialToPaddedSquare_components i.succ
  obtain ⟨hq₂₃l, hq₂₃r⟩ :=
    leftEssentialToPaddedSquare_components L i.succ
  have hq₃₀l : IsSplitMono q₃₀.left := by
    dsimp only [q₃₀]
    infer_instance
  have hq₃₀r : IsSplitMono q₃₀.right := by
    dsimp only [q₃₀]
    infer_instance
  exact nonempty_adjacent_arrow_isos_of_splitMono_four_cycle hfinite
    q₀₁ hq₀₁l hq₀₁r
    q₁₂ hq₁₂l hq₁₂r
    q₂₃ hq₂₃l hq₂₃r
    q₃₀ hq₃₀l hq₃₀r

/-- The load-bearing terminal comparison theorem.  The endpoint isomorphism
closes the four-cycle, making the exact output square of the chosen rung
componentwise invertible.  Its third component is therefore split epic;
mixed split-epi lifting propagates this backwards, so the full displayed
left-to-right mesh comparison is an isomorphism. -/
theorem terminal_reversed_rung_step_iso
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (i : Fin n)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hdiag : DiagonalComparisonAt R L i.castSucc)
    (hterminal : Nonempty
      (Arrow.mk (L.b i.succ) ≅ Arrow.mk (R.paddedArrow i.succ))) :
    Nonempty
        (LeftLadder.stepComplex
            (L.b i.castSucc) (L.b i.succ)
            (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i) ≅
          RightLadder.stepComplex
            (R.b i.succ) (R.b i.castSucc)
            (R.f i) (R.g i) (R.h i) (R.comm i) (R.hzero i)) ∧
      Nonempty
        (Arrow.mk (L.b i.castSucc) ≅
          Arrow.mk (R.paddedArrow i.castSucc)) ∧
      Nonempty
        (Arrow.mk (R.paddedArrow i.succ) ≅ Arrow.mk (R.b i.succ)) ∧
      Nonempty
        (Arrow.mk (R.b i.succ) ≅ Arrow.mk (L.paddedArrow i.succ)) ∧
      Nonempty
        (Arrow.mk (L.paddedArrow i.succ) ≅ Arrow.mk (L.b i.succ)) ∧
      Nonempty
        (Arrow.mk (L.b i.succ) ≅ Arrow.mk (R.paddedArrow i.succ)) := by
  obtain ⟨inputSquare, hinputSource, hinputTarget⟩ := hdiag
  obtain ⟨eL⟩ := L.meshIso i
  obtain ⟨eR⟩ := R.meshIso i
  obtain ⟨phi, q₁₂, hphi₁, hphi₂, hphi₃,
      hq₁₂l, hq₁₂r, hq₁₂right,
      hinputSourceEq, hinputTargetBlock, hzeroBlock⟩ :=
    exists_reversedStrongDomination_rung_data T
      (L.b i.castSucc) (L.b i.succ)
      (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i)
      (R.b i.succ) (R.b i.castSucc)
      (R.f i) (R.g i) (R.h i) (R.comm i) (R.hzero i)
      ⟨eL⟩ ⟨eR⟩ inputSquare hinputSource
  obtain ⟨e₃₀⟩ := hterminal
  let q₀₁ : Arrow.mk (R.b i.succ) ⟶
      Arrow.mk (R.paddedArrow i.succ) :=
    R.essentialToPaddedSquare i.succ
  let q₂₃ : Arrow.mk (L.b i.succ) ⟶
      Arrow.mk (L.paddedArrow i.succ) :=
    leftEssentialToPaddedSquare L i.succ
  let q₃₀ : Arrow.mk (R.paddedArrow i.succ) ⟶
      Arrow.mk (L.b i.succ) := e₃₀.inv
  obtain ⟨hq₀₁l, hq₀₁r⟩ :=
    R.essentialToPaddedSquare_components i.succ
  obtain ⟨hq₂₃l, hq₂₃r⟩ :=
    leftEssentialToPaddedSquare_components L i.succ
  have hq₃₀l : IsSplitMono q₃₀.left := by
    dsimp only [q₃₀]
    infer_instance
  have hq₃₀r : IsSplitMono q₃₀.right := by
    dsimp only [q₃₀]
    infer_instance
  have hadjacent :=
    nonempty_adjacent_arrow_isos_of_splitMono_four_cycle hfinite
      q₀₁ hq₀₁l hq₀₁r
      q₁₂ hq₁₂l hq₁₂r
      q₂₃ hq₂₃l hq₂₃r
      q₃₀ hq₃₀l hq₃₀r
  let q₂₁ : Arrow.mk (R.b i.succ) ⟶
      Arrow.mk (L.paddedArrow i.succ) :=
    q₀₁ ≫ q₃₀ ≫ q₂₃
  have hq₂₁l : IsSplitMono q₂₁.left := by
    change IsSplitMono
      (q₀₁.left ≫ q₃₀.left ≫ q₂₃.left)
    exact isSplitMono_comp_of_isSplitMono _ _ hq₀₁l
      (isSplitMono_comp_of_isSplitMono _ _ hq₃₀l hq₂₃l)
  have hq₂₁r : IsSplitMono q₂₁.right := by
    change IsSplitMono
      (q₀₁.right ≫ q₃₀.right ≫ q₂₃.right)
    exact isSplitMono_comp_of_isSplitMono _ _ hq₀₁r
      (isSplitMono_comp_of_isSplitMono _ _ hq₃₀r hq₂₃r)
  obtain ⟨hq₁₂leftIso, hq₁₂rightIso⟩ :=
    isIso_components_of_mutual_splitMono_squares hfinite
      q₁₂ hq₁₂l hq₁₂r q₂₁ hq₂₁l hq₂₁r
  have hphi₃Iso : IsIso phi.τ₃ := by
    rw [← hq₁₂right]
    exact hq₁₂rightIso
  letI : IsIso phi.τ₃ := hphi₃Iso
  have hphi₃Epi : IsSplitEpi phi.τ₃ := by infer_instance
  obtain ⟨hphi₁Epi, hphi₂Epi⟩ :=
    splitEpi_components_of_displayed_steps T eL eR phi hphi₃Epi
  letI : IsSplitMono phi.τ₁ := hphi₁
  letI : IsSplitMono phi.τ₂ := hphi₂
  letI : IsSplitEpi phi.τ₁ := hphi₁Epi
  letI : IsSplitEpi phi.τ₂ := hphi₂Epi
  have hphi₁Iso : IsIso phi.τ₁ :=
    isIso_of_mono_of_isSplitEpi phi.τ₁
  have hphi₂Iso : IsIso phi.τ₂ :=
    isIso_of_mono_of_isSplitEpi phi.τ₂
  letI : IsIso phi.τ₁ := hphi₁Iso
  letI : IsIso phi.τ₂ := hphi₂Iso
  have hphiIso : IsIso phi :=
    (ShortComplex.isIso_iff phi).2 ⟨hphi₁Iso, hphi₂Iso, hphi₃Iso⟩
  letI : IsIso phi := hphiIso
  have hinputLeftIso : IsIso inputSquare.left := by
    rw [hinputSourceEq]
    exact hphi₁Iso
  have hblockEpi : IsSplitEpi
      ((biprod.inr : L.Z i.castSucc ⟶
          L.Y i.succ ⊞ L.Z i.castSucc) ≫ phi.τ₂ ≫
        (biprod.fst : R.Y i.castSucc ⊞ R.Z i.succ ⟶
          R.Y i.castSucc)) := by
    letI : IsIso phi.τ₂ := hphi₂Iso
    exact isSplitEpi_biprod_inr_comp_fst_of_isIso phi.τ₂
      hphi₂Iso hzeroBlock
  have hinputRightEpi : IsSplitEpi inputSquare.right := by
    rw [hinputTargetBlock]
    exact hblockEpi
  letI : IsSplitMono inputSquare.right := hinputTarget
  letI : IsSplitEpi inputSquare.right := hinputRightEpi
  have hinputRightIso : IsIso inputSquare.right :=
    isIso_of_mono_of_isSplitEpi inputSquare.right
  letI : IsIso inputSquare.left := hinputLeftIso
  letI : IsIso inputSquare.right := hinputRightIso
  have hinputIso : IsIso inputSquare :=
    Arrow.isIso_of_isIso_left_of_isIso_right inputSquare
  letI : IsIso inputSquare := hinputIso
  exact ⟨⟨asIso phi⟩, ⟨asIso inputSquare⟩, hadjacent⟩

/-- A terminal arrow isomorphism propagates backwards across the entire
aligned finite window. -/
theorem terminalArrowIsoAt_all_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding R U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk (R.paddedArrow (Fin.last n)))) :
    ∀ j : Fin (n + 1),
      Nonempty (Arrow.mk (L.b j) ≅ Arrow.mk (R.paddedArrow j)) := by
  intro j
  induction j using Fin.reverseInduction with
  | last => exact hlast
  | cast i ih =>
      exact
        (terminal_reversed_rung_step_iso R L i hfinite
          (diagonalComparisonAt_all_of_boundaryEmbedding R L E i.castSucc)
          ih).2.1

/-- Whole-boundary specialization of backward terminal propagation. -/
theorem terminalArrowIsoAt_all
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk (R.paddedArrow (Fin.last n)))) :
    ∀ j : Fin (n + 1),
      Nonempty (Arrow.mk (L.b j) ≅ Arrow.mk (R.paddedArrow j)) :=
  terminalArrowIsoAt_all_of_boundaryEmbedding R L
    (BoundaryEmbedding.identity R) hfinite hlast

/-- Every aligned pair of reversed left/right rungs is isomorphic once the
terminal diagonal closes. -/
theorem reversedStepIso_all_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding R U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk (R.paddedArrow (Fin.last n))))
    (i : Fin n) :
    Nonempty
      (LeftLadder.stepComplex
          (L.b i.castSucc) (L.b i.succ)
          (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i) ≅
        RightLadder.stepComplex
          (R.b i.succ) (R.b i.castSucc)
          (R.f i) (R.g i) (R.h i) (R.comm i) (R.hzero i)) := by
  exact
    (terminal_reversed_rung_step_iso R L i hfinite
      (diagonalComparisonAt_all_of_boundaryEmbedding R L E i.castSucc)
      (terminalArrowIsoAt_all_of_boundaryEmbedding R L E hfinite hlast
        i.succ)).1

/-- Whole-boundary specialization of the rung isomorphisms. -/
theorem reversedStepIso_all
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk (R.paddedArrow (Fin.last n))))
    (i : Fin n) :
    Nonempty
      (LeftLadder.stepComplex
          (L.b i.castSucc) (L.b i.succ)
          (L.f i) (L.g i) (L.h i) (L.comm i) (L.hzero i) ≅
        RightLadder.stepComplex
          (R.b i.succ) (R.b i.castSucc)
          (R.f i) (R.g i) (R.h i) (R.comm i) (R.hzero i)) :=
  reversedStepIso_all_of_boundaryEmbedding R L
    (BoundaryEmbedding.identity R) hfinite hlast i

/-- Every previous essential right arrow cancels its zero padding along the
closed reversed window. -/
theorem reversedPreviousCancellationIso_all_of_boundaryEmbedding
    {T : FiniteTauCategoryData C Ind} {U₀ : C} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T U₀ n)
    (E : BoundaryEmbedding R U₀)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk (R.paddedArrow (Fin.last n))))
    (i : Fin n) :
    Nonempty
      (Arrow.mk (R.paddedArrow i.succ) ≅ Arrow.mk (R.b i.succ)) := by
  exact
    (terminal_reversed_rung_step_iso R L i hfinite
      (diagonalComparisonAt_all_of_boundaryEmbedding R L E i.castSucc)
      (terminalArrowIsoAt_all_of_boundaryEmbedding R L E hfinite hlast
        i.succ)).2.2.1

/-- Whole-boundary specialization of previous-arrow cancellation. -/
theorem reversedPreviousCancellationIso_all
    {T : FiniteTauCategoryData C Ind} {n : ℕ}
    (R : ReversedRightPrefix T n)
    (L : LeftLadder.FiniteSpecialLeftLadderFromZero T (R.U 0) n)
    (hfinite : ∀ (X : C) (e : X ⟶ X), IsSplitMono e → IsIso e)
    (hlast : Nonempty
      (Arrow.mk (L.b (Fin.last n)) ≅
        Arrow.mk (R.paddedArrow (Fin.last n))))
    (i : Fin n) :
    Nonempty
      (Arrow.mk (R.paddedArrow i.succ) ≅ Arrow.mk (R.b i.succ)) :=
  reversedPreviousCancellationIso_all_of_boundaryEmbedding R L
    (BoundaryEmbedding.identity R) hfinite hlast i

end MBDVendor.QSE.Iyama.TauSequenceComparison
