module

public import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderPropagation
public import MBDVendor.QSE.CategoryTheory.IyamaRightLadderConstruction
public import MBDVendor.QSE.CategoryTheory.SplitMorphismComplement

/-!
# Basic normalized states and rungs for special left ladders

This file contains the invariant split-epimorphic rung construction and the
normalized state records used in the left-ladder half of Iyama,
*Tau-categories I*, Lemma 6.4.1(1)(ii).  The two-field builder interface
separates target normalization from complementary-successor specialness;
subsequent modules construct both fields categorically.

No concrete algebra or module classification occurs in this file.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MBDVendor.QSE.Iyama.LeftLadder

open CategoricalIdeal CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-! ## The invariant split-epimorphic left rung -/

/-- A split epimorphism, after replacing its complementary object by an
isomorphic object, identifies its source with `biprod Y Z`. -/
def transportedComplementTargetIso
    {M Z Y : C} {p : M ⟶ Z} [IsSplitEpi p]
    (d : SplitEpiComplement p) (e : d.complement ≅ Y) :
    M ≅ biprod Y Z where
  hom := biprod.lift (d.projection ≫ e.hom) p
  inv := biprod.desc (e.inv ≫ d.inclusion) (section_ p)
  hom_inv_id := by
    rw [biprod.lift_desc]
    simp only [Category.assoc, e.hom_inv_id_assoc]
    exact d.total
  inv_hom_id := by
    ext <;> simp [Category.assoc]
    calc
      e.inv ≫ d.inclusion ≫ d.projection ≫ e.hom =
          e.inv ≫ (d.inclusion ≫ d.projection) ≫ e.hom := by
            simp only [Category.assoc]
      _ = e.inv ≫ CategoryStruct.id d.complement ≫ e.hom := by
        rw [d.inclusion_projection]
      _ = CategoryStruct.id Y := by simp

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Dual of the invariant split-complement right-rung theorem.

`p` is the split-epimorphic factor of the current essential arrow through
`S.f`.  Its complementary successor is `d.inclusion ≫ S.g`.  An arrow
isomorphism from that successor to `(bNext,0)` determines the entire explicit
left-ladder rung and identifies it with `S`. -/
theorem exists_stepComplex_iso_of_split_cofactor_and_padded_next
    (S : ShortComplex C) {YPrev ZPrev YNext ZNext U : C}
    (ePrev : S.X₁ ≅ YPrev)
    (p : S.X₂ ⟶ ZPrev) [IsSplitEpi p]
    (d : SplitEpiComplement p)
    (bNext : YNext ⟶ ZNext)
    (eY : d.complement ≅ YNext)
    (eX : S.X₃ ≅ biprod ZNext U)
    (heNext :
      (d.inclusion ≫ S.g) ≫ eX.hom =
        eY.hom ≫ biprod.lift bNext (0 : YNext ⟶ U)) :
    let bPrev : YPrev ⟶ ZPrev := ePrev.inv ≫ S.f ≫ p
    ∃ (f : YPrev ⟶ YNext) (g : ZPrev ⟶ ZNext)
      (h : ZPrev ⟶ U)
      (comm : f ≫ bNext = bPrev ≫ g)
      (hzero : bPrev ≫ h = 0),
        Nonempty
          (S ≅ stepComplex bPrev bNext f g h comm hzero) := by
  dsimp only
  let bPrev : YPrev ⟶ ZPrev := ePrev.inv ≫ S.f ≫ p
  let f : YPrev ⟶ YNext :=
    ePrev.inv ≫ S.f ≫ d.projection ≫ eY.hom
  let q : ZPrev ⟶ biprod ZNext U :=
    section_ p ≫ S.g ≫ eX.hom
  let g : ZPrev ⟶ ZNext := -(q ≫ biprod.fst)
  let h : ZPrev ⟶ U := q ≫ biprod.snd
  let eM : S.X₂ ≅ biprod YNext ZPrev :=
    transportedComplementTargetIso d eY

  have hq : q = biprod.lift (-g) h := by
    apply biprod.hom_ext
    · simp [g, q]
    · simp [h, q]

  have hfirst :
      ePrev.hom ≫ biprod.lift f bPrev = S.f ≫ eM.hom := by
    apply biprod.hom_ext
    · simp [f, eM, transportedComplementTargetIso,
        Category.assoc]
    · simp [bPrev, eM, transportedComplementTargetIso,
        Category.assoc]

  let second : biprod YNext ZPrev ⟶ biprod ZNext U :=
    biprod.lift (biprod.desc bNext (-g)) (biprod.desc 0 h)
  have hsecond : eM.hom ≫ second = S.g ≫ eX.hom := by
    rw [← cancel_epi eM.inv]
    simp only [eM.inv_hom_id_assoc]
    apply biprod.hom_ext'
    · have hcomponent :
          biprod.inl ≫ second =
            biprod.lift bNext (0 : YNext ⟶ U) := by
        apply biprod.hom_ext <;> simp [second, Category.assoc]
      rw [hcomponent]
      have hs :
          eY.inv ≫ d.inclusion ≫ S.g ≫ eX.hom =
            biprod.lift bNext (0 : YNext ⟶ U) := by
        rw [← cancel_epi eY.hom]
        simpa only [eY.hom_inv_id_assoc, Category.assoc] using heNext
      simpa [eM, transportedComplementTargetIso,
        Category.assoc] using hs.symm
    · have hcomponent :
          biprod.inr ≫ second = biprod.lift (-g) h := by
        apply biprod.hom_ext <;> simp [second, Category.assoc]
      rw [hcomponent]
      have hs :
          section_ p ≫ S.g ≫ eX.hom =
            biprod.lift (-g) h := hq
      simpa [eM, transportedComplementTargetIso,
        Category.assoc] using hs.symm

  let first : YPrev ⟶ biprod YNext ZPrev := biprod.lift f bPrev
  have hzero : first ≫ second = 0 := by
    rw [← cancel_epi ePrev.hom]
    calc
      ePrev.hom ≫ (first ≫ second) =
          (ePrev.hom ≫ first) ≫ second :=
        (Category.assoc _ _ _).symm
      _ = (S.f ≫ eM.hom) ≫ second := by
        simpa only [first] using congrArg (fun k ↦ k ≫ second) hfirst
      _ = S.f ≫ (eM.hom ≫ second) := Category.assoc _ _ _
      _ = S.f ≫ (S.g ≫ eX.hom) := by
        rw [hsecond]
      _ = 0 := by rw [← Category.assoc, S.zero, zero_comp]
      _ = ePrev.hom ≫ 0 := by simp

  have hcomm : f ≫ bNext = bPrev ≫ g := by
    have hz := congrArg (fun k ↦ k ≫ biprod.fst) hzero
    apply sub_eq_zero.mp
    simpa [first, second, biprod.lift_eq, Category.assoc,
      sub_eq_add_neg] using hz

  have hhzero : bPrev ≫ h = 0 := by
    have hz := congrArg (fun k ↦ k ≫ biprod.snd) hzero
    dsimp only [first, second] at hz
    simpa [Category.assoc] using hz

  refine ⟨f, g, h, hcomm, hhzero, ⟨?_⟩⟩
  exact ShortComplex.isoMk ePrev eM eX hfirst hsecond


/-! ## Normalized left states and the dual-special interface -/

/-- A normalized special arrow obtained by postcomposing the first map of a
chosen left mesh with a split epimorphism. The field U records the zero-padded
target summand discarded from the essential arrow. -/
structure SpecialCosplitState
    (T : FiniteTauCategoryData C Ind) (Y : C) where
  Z : C
  U : C
  p : (T.leftMesh Y).X₂ ⟶ Z
  [p_split : IsSplitEpi p]
  special : IsSpecial T.radical
    ((T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ p)

instance {T : FiniteTauCategoryData C Ind} {Y : C}
    (s : SpecialCosplitState T Y) : IsSplitEpi s.p :=
  s.p_split

namespace SpecialCosplitState

variable {T : FiniteTauCategoryData C Ind} {Y : C}

def b (s : SpecialCosplitState T Y) : Y ⟶ s.Z :=
  (T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ s.p

theorem b_special (s : SpecialCosplitState T Y) :
    IsSpecial T.radical s.b :=
  s.special

def rawSuccessor (s : SpecialCosplitState T Y) :
    (splitEpiComplement s.p).complement ⟶ (T.leftMesh Y).X₃ :=
  (splitEpiComplement s.p).inclusion ≫ (T.leftMesh Y).g

end SpecialCosplitState

structure SpecialConormalization
    (T : FiniteTauCategoryData C Ind) {X Y : C} (a : X ⟶ Y) where
  state : SpecialCosplitState T X
  arrowIso : Nonempty
    (Arrow.mk a ≅
      Arrow.mk
        (biprod.lift state.b (0 : X ⟶ state.U)))

/-- The two dual-special operations used by the dependent recursion: target
split--radical normalization and specialness of the complementary left
successor. -/
structure SpecialLeftLadderBuilder
    (T : FiniteTauCategoryData C Ind) where
  normalize :
    ∀ {X Y : C} (a : X ⟶ Y), IsSpecial T.radical a →
      SpecialConormalization T a
  rawSuccessor_special :
    ∀ {Y : C} (s : SpecialCosplitState T Y),
      IsSpecial T.radical s.rawSuccessor


end MBDVendor.QSE.Iyama.LeftLadder
