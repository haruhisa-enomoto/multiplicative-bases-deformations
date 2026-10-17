import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Preadditive.Biproducts
import MBDVendor.QSE.CategoryTheory.IyamaTauSequence
import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Special morphisms in Iyama tau-categories

Iyama calls a radical morphism special when every perturbation by the square
of the categorical radical is isomorphic to it.  This file gives that
invariant arrow-category definition and proves the basic seed result used in
the right-ladder construction: the first map of every tau-approximation is
special.  In particular, every left mesh first map is special.

The nilpotence field of `NilpotentRadicalData` is not used here; the structure
currently provides the project's chosen Hom-ideal realization of the
categorical radical.
-/

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

open CategoricalIdeal CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A radical morphism is special when every perturbation by a
radical-square morphism is isomorphic to it in the arrow category. -/
def IsSpecial (R : NilpotentRadicalData C)
    {X Y : C} (a : X ⟶ Y) : Prop :=
  IsRadicalMorphism a ∧
    ∀ (r : X ⟶ Y),
      r ∈ (R.ideal.pow 2).hom X Y →
        Nonempty (Arrow.mk a ≅ Arrow.mk (a + r))

/-- Specialness is invariant under isomorphism in the arrow category. -/
theorem IsSpecial.of_iso (R : NilpotentRadicalData C)
    {A B : Arrow C} (ha : IsSpecial R A.hom) (e : A ≅ B) :
    IsSpecial R B.hom := by
  constructor
  · rw [Arrow.iso_w e]
    simpa only [Category.assoc] using
      isRadicalMorphism_postcomp e.hom.right
        (isRadicalMorphism_precomp e.inv.left ha.1)
  · intro s hs
    let r : A.left ⟶ A.right := e.hom.left ≫ s ≫ e.inv.right
    have hr : r ∈ (R.ideal.pow 2).hom A.left A.right := by
      simpa only [r, Category.assoc] using
        (R.ideal.pow 2).postcomp e.inv.right
          ((R.ideal.pow 2).precomp e.hom.left hs)
    obtain ⟨q⟩ := ha.2 r hr
    let eL : A.left ≅ B.left :=
      { hom := e.hom.left
        inv := e.inv.left
        hom_inv_id := by
          have h := congrArg Arrow.Hom.left e.hom_inv_id
          simpa only [Arrow.comp_left, Arrow.id_left] using h
        inv_hom_id := by
          have h := congrArg Arrow.Hom.left e.inv_hom_id
          simpa only [Arrow.comp_left, Arrow.id_left] using h }
    let eR : A.right ≅ B.right :=
      { hom := e.hom.right
        inv := e.inv.right
        hom_inv_id := by
          have h := congrArg Arrow.Hom.right e.hom_inv_id
          simpa only [Arrow.comp_right, Arrow.id_right] using h
        inv_hom_id := by
          have h := congrArg Arrow.Hom.right e.inv_hom_id
          simpa only [Arrow.comp_right, Arrow.id_right] using h }
    have hsq : eL.hom ≫ (B.hom + s) = (A.hom + r) ≫ eR.hom := by
      dsimp only [eL, eR, r]
      rw [Preadditive.comp_add, Preadditive.add_comp, e.hom.w]
      simp only [Category.assoc]
      have hri : e.inv.right ≫ e.hom.right = 𝟙 B.right := by
        have h := congrArg Arrow.Hom.right e.inv_hom_id
        simpa only [Arrow.comp_right, Arrow.id_right] using h
      rw [hri, Category.comp_id]
    let q' : Arrow.mk (A.hom + r) ≅ Arrow.mk (B.hom + s) :=
      Arrow.isoMk' (A.hom + r) (B.hom + s) eL eR hsq
    exact ⟨e.symm.trans (q.trans q')⟩

/-- A special padded arrow absorbs a radical-square complementary
component.  This is the perturbation step in Iyama's special-arrow normal
form; cancellation of the zero source summand is a separate theorem. -/
theorem IsSpecial.nonempty_iso_biprod_desc_zero
    [HasBinaryBiproducts C]
    (R : NilpotentRadicalData C)
    {Z U Y : C} {b : Z ⟶ Y} {q : U ⟶ Y}
    (ha : IsSpecial R (biprod.desc b q))
    (hq : q ∈ (R.ideal.pow 2).hom U Y) :
    Nonempty
      (Arrow.mk (biprod.desc b q) ≅
        Arrow.mk (biprod.desc b (0 : U ⟶ Y))) := by
  let t : Z ⊞ U ⟶ Y := biprod.desc 0 (-q)
  have ht : t ∈ (R.ideal.pow 2).hom (Z ⊞ U) Y := by
    have hqneg : -q ∈ (R.ideal.pow 2).hom U Y := neg_mem hq
    have hpre := (R.ideal.pow 2).precomp
      (biprod.snd : Z ⊞ U ⟶ U) hqneg
    simpa [t, biprod.desc_eq] using hpre
  obtain ⟨e⟩ := ha.2 t ht
  refine ⟨e.trans (eqToIso ?_)⟩
  congr 1
  dsimp only [t]
  ext <;> simp

/-- Isomorphism-invariant form of complementary radical-square absorption. -/
theorem IsSpecial.nonempty_iso_biprod_desc_zero_of_iso
    [HasBinaryBiproducts C]
    (R : NilpotentRadicalData C)
    {X Y Z U : C} {a : X ⟶ Y} {b : Z ⟶ Y} {q : U ⟶ Y}
    (ha : IsSpecial R a)
    (e : Arrow.mk a ≅ Arrow.mk (biprod.desc b q))
    (hq : q ∈ (R.ideal.pow 2).hom U Y) :
    Nonempty
      (Arrow.mk a ≅
        Arrow.mk (biprod.desc b (0 : U ⟶ Y))) := by
  obtain ⟨e'⟩ := (ha.of_iso R e).nonempty_iso_biprod_desc_zero R hq
  exact ⟨e.trans e'⟩

/-- Zero-padded right-minimal arrows cancel their padded source summands.
This is the categorical cancellation used in Iyama's special-arrow
construction. -/
theorem nonempty_arrow_iso_of_biprod_desc_zero_iso
    [HasBinaryBiproducts C]
    {Z U Y Z' U' Y' : C} {b : Z ⟶ Y} {b' : Z' ⟶ Y'}
    (hb : IsRightMinimal b) (hb' : IsRightMinimal b')
    (e :
      Arrow.mk (biprod.desc b (0 : U ⟶ Y)) ≅
        Arrow.mk (biprod.desc b' (0 : U' ⟶ Y'))) :
    Nonempty (Arrow.mk b ≅ Arrow.mk b') := by
  let eL : Z ⊞ U ≅ Z' ⊞ U' :=
    by simpa using Arrow.leftFunc.mapIso e
  let eR : Y ≅ Y' :=
    by simpa using Arrow.rightFunc.mapIso e
  have he :
      eL.hom ≫ biprod.desc b' (0 : U' ⟶ Y') =
        biprod.desc b (0 : U ⟶ Y) ≫ eR.hom := by
    exact e.hom.w
  have heInv :
      eL.inv ≫ biprod.desc b (0 : U ⟶ Y) =
        biprod.desc b' (0 : U' ⟶ Y') ≫ eR.inv := by
    exact e.inv.w
  let c : Z ⟶ Z' := biprod.inl ≫ eL.hom ≫ biprod.fst
  let d : Z' ⟶ Z := biprod.inl ≫ eL.inv ≫ biprod.fst
  have hc : c ≫ b' = b ≫ eR.hom := by
    have h := congrArg
      (fun q ↦ (biprod.inl : Z ⟶ Z ⊞ U) ≫ q) he
    have hdesc :
        biprod.desc b' (0 : U' ⟶ Y') = biprod.fst ≫ b' := by
      ext <;> simp
    rw [hdesc] at h
    simpa [c, Category.assoc] using h
  have hd : d ≫ b = b' ≫ eR.inv := by
    have h := congrArg
      (fun q ↦ (biprod.inl : Z' ⟶ Z' ⊞ U') ≫ q) heInv
    have hdesc :
        biprod.desc b (0 : U ⟶ Y) = biprod.fst ≫ b := by
      ext <;> simp
    rw [hdesc] at h
    simpa [d, Category.assoc] using h
  have hcd : (c ≫ d) ≫ b = b := by
    calc
      (c ≫ d) ≫ b = c ≫ (d ≫ b) := Category.assoc _ _ _
      _ = c ≫ (b' ≫ eR.inv) := by rw [hd]
      _ = (c ≫ b') ≫ eR.inv := (Category.assoc _ _ _).symm
      _ = (b ≫ eR.hom) ≫ eR.inv := by rw [hc]
      _ = b := by simp
  have hdc : (d ≫ c) ≫ b' = b' := by
    calc
      (d ≫ c) ≫ b' = d ≫ (c ≫ b') := Category.assoc _ _ _
      _ = d ≫ (b ≫ eR.hom) := by rw [hc]
      _ = (d ≫ b) ≫ eR.hom := (Category.assoc _ _ _).symm
      _ = (b' ≫ eR.inv) ≫ eR.hom := by rw [hd]
      _ = b' := by simp
  letI : IsIso (c ≫ d) := hb (c ≫ d) hcd
  letI : IsIso (d ≫ c) := hb' (d ≫ c) hdc
  letI : IsIso c := isIso_of_isIso_comp_both c d
  exact ⟨Arrow.isoMk' b b' (asIso c) eR hc⟩

/-- Specialness of a zero-padded arrow descends to its right-minimal
essential component, provided all its radical-square perturbations remain
right minimal. -/
theorem IsSpecial.cancel_biprod_desc_zero
    [HasBinaryBiproducts C]
    (R : NilpotentRadicalData C)
    {Z U Y : C} {b : Z ⟶ Y}
    (hpadded : IsSpecial R (biprod.desc b (0 : U ⟶ Y)))
    (hb : IsRightMinimal b)
    (hpert : ∀ (r : Z ⟶ Y),
      r ∈ (R.ideal.pow 2).hom Z Y → IsRightMinimal (b + r)) :
    IsSpecial R b := by
  constructor
  · have hcomponent :=
      isRadicalMorphism_precomp
        (biprod.inl : Z ⟶ Z ⊞ U) hpadded.1
    simpa using hcomponent
  · intro r hr
    let t : Z ⊞ U ⟶ Y := biprod.desc r 0
    have ht : t ∈ (R.ideal.pow 2).hom (Z ⊞ U) Y := by
      have hpre := (R.ideal.pow 2).precomp
        (biprod.fst : Z ⊞ U ⟶ Z) hr
      simpa [t, biprod.desc_eq] using hpre
    obtain ⟨e⟩ := hpadded.2 t ht
    have heq :
        Arrow.mk (biprod.desc b (0 : U ⟶ Y) + t) =
          Arrow.mk (biprod.desc (b + r) (0 : U ⟶ Y)) := by
      congr 1
      dsimp only [t]
      ext <;> simp
    let e' :
        Arrow.mk (biprod.desc b (0 : U ⟶ Y)) ≅
          Arrow.mk (biprod.desc (b + r) (0 : U ⟶ Y)) :=
      e.trans (eqToIso heq)
    exact nonempty_arrow_iso_of_biprod_desc_zero_iso
      hb (hpert r hr) e'

/-- Every radical-square perturbation of the first map of a
tau-approximation factors through that first map with a radical endomorphism
of the middle term. -/
theorem TauApproximation.exists_radical_factor_of_mem_square
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : TauApproximation S)
    {r : S.X₁ ⟶ S.X₂}
    (hr : r ∈ (R.ideal.pow 2).hom S.X₁ S.X₂) :
    ∃ b : S.X₂ ⟶ S.X₂,
      b ∈ R.ideal.hom S.X₂ S.X₂ ∧ S.f ≫ b = r := by
  have hr' : r ∈ (R.ideal ⋆ᵢ R.ideal).hom S.X₁ S.X₂ := by
    simpa using hr
  change r ∈ AddSubgroup.closure
    (CategoricalIdeal.HomIdeal.compositeGenerators
      R.ideal R.ideal S.X₁ S.X₂) at hr'
  clear hr
  induction hr' using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨W, u, v, hu, hv, rfl⟩ := hr
      obtain ⟨b, hb⟩ :=
        hS.factors_from_left u ((R.mem_ideal_iff u).mp hu)
      refine ⟨b ≫ v, R.ideal.precomp b hv, ?_⟩
      rw [← Category.assoc, hb]
  | zero =>
      exact ⟨0, zero_mem _, by simp⟩
  | add r s _ _ hr hs =>
      obtain ⟨b, hb, hbr⟩ := hr
      obtain ⟨c, hc, hcs⟩ := hs
      refine ⟨b + c, add_mem hb hc, ?_⟩
      rw [Preadditive.comp_add, hbr, hcs]
  | neg r _ hr =>
      obtain ⟨b, hb, hbr⟩ := hr
      refine ⟨-b, neg_mem hb, ?_⟩
      rw [Preadditive.comp_neg, hbr]

/-- Dually, every radical-square arrow into the right endpoint of a
tau-approximation factors through its second map with a radical morphism. -/
theorem TauApproximation.exists_radical_factor_into_of_mem_square
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : TauApproximation S)
    {W : C} {r : W ⟶ S.X₃}
    (hr : r ∈ (R.ideal.pow 2).hom W S.X₃) :
    ∃ b : W ⟶ S.X₂,
      b ∈ R.ideal.hom W S.X₂ ∧ b ≫ S.g = r := by
  have hr' : r ∈ (R.ideal ⋆ᵢ R.ideal).hom W S.X₃ := by
    simpa using hr
  change r ∈ AddSubgroup.closure
    (CategoricalIdeal.HomIdeal.compositeGenerators
      R.ideal R.ideal W S.X₃) at hr'
  clear hr
  induction hr' using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨V, u, v, hu, hv, rfl⟩ := hr
      obtain ⟨b, hb⟩ :=
        hS.factors_into_right v ((R.mem_ideal_iff v).mp hv)
      refine ⟨u ≫ b, R.ideal.postcomp b hu, ?_⟩
      rw [Category.assoc, hb]
  | zero =>
      exact ⟨0, zero_mem _, by simp⟩
  | add r s _ _ hr hs =>
      obtain ⟨b, hb, hbr⟩ := hr
      obtain ⟨c, hc, hcs⟩ := hs
      refine ⟨b + c, add_mem hb hc, ?_⟩
      rw [Preadditive.add_comp, hbr, hcs]
  | neg r _ hr =>
      obtain ⟨b, hb, hbr⟩ := hr
      refine ⟨-b, neg_mem hb, ?_⟩
      rw [Preadditive.neg_comp, hbr]

private theorem isIso_id_add_of_mem_radical
    (R : NilpotentRadicalData C)
    {X : C} (b : X ⟶ X)
    (hb : b ∈ R.ideal.hom X X) :
    IsIso (𝟙 X + b) := by
  have hb' : IsRadicalMorphism b := (R.mem_ideal_iff b).mp hb
  have hi : IsIso (𝟙 X - b ≫ (-𝟙 X)) := hb' (-𝟙 X)
  simpa using hi

/-- The first map of every tau-approximation is special. -/
theorem TauApproximation.isSpecial_f
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : TauApproximation S) :
    IsSpecial R S.f := by
  refine ⟨hS.f_radical, ?_⟩
  intro r hr
  obtain ⟨b, hb, hfb⟩ :=
    hS.exists_radical_factor_of_mem_square R hr
  haveI hbI : IsIso (𝟙 S.X₂ + b) :=
    isIso_id_add_of_mem_radical R b hb
  let e₂ : S.X₂ ≅ S.X₂ := asIso (𝟙 S.X₂ + b)
  refine ⟨Arrow.isoMk' S.f (S.f + r) (Iso.refl S.X₁) e₂ ?_⟩
  dsimp only [e₂]
  rw [asIso_hom, Iso.refl_hom, Category.id_comp,
    Preadditive.comp_add, Category.comp_id, hfb]

/-- The first map of every left tau-sequence is special.  This is the
abstract seed `μ⁻` used in Iyama's right-ladder existence theorem. -/
theorem LeftTauSequence.isSpecial_f
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : LeftTauSequence S) :
    IsSpecial R S.f :=
  hS.toTauApproximation.isSpecial_f R

end MBDVendor.QSE.Iyama
