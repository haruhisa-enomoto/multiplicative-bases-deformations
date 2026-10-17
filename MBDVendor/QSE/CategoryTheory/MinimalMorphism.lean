import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Minimal morphisms

The standard right- and left-minimal predicates are useful both for
almost-split morphisms and for minimal weak kernels and cokernels.
-/

open CategoryTheory

namespace MBDVendor.QSE

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism is right minimal when every endomorphism of its source which
fixes it is invertible. -/
def IsRightMinimal {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ (e : X ⟶ X), e ≫ f = f → IsIso e

/-- A morphism is left minimal when every endomorphism of its target which
fixes it is invertible. -/
def IsLeftMinimal {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ (e : Y ⟶ Y), f ≫ e = f → IsIso e

/-- A morphism whose composites with one reverse morphism are invertible in
both orders is itself invertible. -/
theorem isIso_of_isIso_comp_both
    {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    [IsIso (a ≫ b)] [IsIso (b ≫ a)] : IsIso a := by
  let r : Y ⟶ X := b ≫ inv (a ≫ b)
  let l : Y ⟶ X := inv (b ≫ a) ≫ b
  have hr : a ≫ r = 𝟙 X := by
    dsimp only [r]
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hl : l ≫ a = 𝟙 Y := by
    dsimp only [l]
    rw [Category.assoc, IsIso.inv_hom_id]
  have hrl : r = l := by
    calc
      r = 𝟙 Y ≫ r := by simp
      _ = (l ≫ a) ≫ r := by rw [hl]
      _ = l ≫ (a ≫ r) := by rw [Category.assoc]
      _ = l ≫ 𝟙 X := by rw [hr]
      _ = l := by simp
  exact ⟨⟨r, hr, hrl ▸ hl⟩⟩

variable [Preadditive C]

/-- Every nonzero morphism out of an object with local endomorphism ring is
right minimal. -/
theorem isRightMinimal_of_localEnd_of_ne_zero
    {X Y : C} [IsLocalRing (End X)] (f : X ⟶ Y) (hf : f ≠ 0) :
    IsRightMinimal f := by
  intro e he
  have hsum : IsUnit (End.of e + (1 - End.of e)) := by
    rw [add_sub_cancel]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with
      heUnit | hsubUnit
  · exact (isUnit_iff_isIso (End.of e)).1 heUnit
  · have hsubIso : IsIso (𝟙 X - e) :=
      (isUnit_iff_isIso (1 - End.of e)).1 hsubUnit
    letI : IsIso (𝟙 X - e) := hsubIso
    have hzero : (𝟙 X - e) ≫ f = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
    exfalso
    apply hf
    apply (cancel_epi (𝟙 X - e)).1
    simpa using hzero

omit [Preadditive C] in
/-- Postcomposing by an isomorphism preserves right minimality. -/
theorem IsRightMinimal.postcomp_iso
    {X Y Z : C} {g : X ⟶ Y}
    (e : Y ≅ Z) (hg : IsRightMinimal g) :
    IsRightMinimal (g ≫ e.hom) := by
  intro a ha
  apply hg a
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc] using ha

/-- Precomposing a right-minimal morphism by a split monomorphism preserves
right minimality. -/
theorem IsRightMinimal.precomp_splitMono
    {Z X Y : C} {g : X ⟶ Y}
    (hg : IsRightMinimal g) (j : Z ⟶ X) [IsSplitMono j] :
    IsRightMinimal (j ≫ g) := by
  intro e he
  let E : X ⟶ X :=
    retraction j ≫ e ≫ j +
      (𝟙 X - retraction j ≫ j)
  have hmain :
      retraction j ≫ e ≫ j ≫ g =
        retraction j ≫ j ≫ g := by
    simpa only [Category.assoc] using
      congrArg (fun q ↦ retraction j ≫ q) he
  have hEg : E ≫ g = g := by
    dsimp only [E]
    simp only [Preadditive.add_comp, Preadditive.sub_comp,
      Category.id_comp, Category.assoc]
    rw [hmain]
    simp [sub_eq_add_neg, add_left_comm]
  letI : IsIso E := hg E hEg
  have hjE : j ≫ E = e ≫ j := by
    dsimp only [E]
    simp only [Preadditive.comp_add, Preadditive.comp_sub,
      Category.comp_id]
    rw [IsSplitMono.id_assoc]
    simp
  have hEr : E ≫ retraction j = retraction j ≫ e := by
    simp [E, Category.assoc]
  apply IsIso.mk
  refine ⟨j ≫ inv E ≫ retraction j, ?_, ?_⟩
  · calc
      e ≫ (j ≫ inv E ≫ retraction j) =
          (e ≫ j) ≫ inv E ≫ retraction j := by
            simp only [Category.assoc]
      _ = (j ≫ E) ≫ inv E ≫ retraction j := by rw [hjE]
      _ = 𝟙 Z := by simp
  · calc
      (j ≫ inv E ≫ retraction j) ≫ e =
          j ≫ inv E ≫ (retraction j ≫ e) := by
            simp only [Category.assoc]
      _ = j ≫ inv E ≫ (E ≫ retraction j) := by rw [hEr]
      _ = 𝟙 Z := by simp

end

end MBDVendor.QSE
