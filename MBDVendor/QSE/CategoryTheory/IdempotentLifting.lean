import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Idempotents

/-!
# Idempotent completeness from nilpotent functor kernels

An idempotent lifts along a surjective ring homomorphism when every element
of its kernel is nilpotent.  Applied to endomorphism rings, this shows that a
full, essentially surjective additive functor out of an idempotent-complete
category has idempotent-complete target as soon as its endomorphism kernels
are elementwise nilpotent.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MBDVendor.QSE.CategoryTheory.IdempotentLifting

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- The kernel ideal of an additive functor is square-zero: any composite of
two composable morphisms killed by the functor vanishes. -/
def FunctorKernelSquareZero (F : C ⥤ D) : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    F.map f = 0 → F.map g = 0 → f ≫ g = 0

/-- A full additive functor with square-zero kernel reflects
isomorphisms.  This is the categorical inverse-lifting argument used for
separated representations. -/
theorem reflectsIso_of_kernelSquareZero
    (F : C ⥤ D) [F.Additive] [F.Full]
    (hF : FunctorKernelSquareZero F)
    {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f := by
  let g : Y ⟶ X := F.preimage (inv (F.map f))
  let nX : X ⟶ X := 𝟙 X - f ≫ g
  let nY : Y ⟶ Y := 𝟙 Y - g ≫ f
  have hnXmap : F.map nX = 0 := by
    simp [nX, g]
  have hnYmap : F.map nY = 0 := by
    simp [nY, g]
  have hnXsq : nX ≫ nX = 0 := hF nX nX hnXmap hnXmap
  have hnYsq : nY ≫ nY = 0 := hF nY nY hnYmap hnYmap
  have hleft : f ≫ (g ≫ (𝟙 X + nX)) = 𝟙 X := by
    rw [← Category.assoc]
    simp only [Preadditive.comp_add, Category.comp_id]
    have hfg : f ≫ g = 𝟙 X - nX := by
      simp [nX]
    rw [hfg, Preadditive.sub_comp, Category.id_comp, hnXsq, sub_zero]
    abel
  have hright : ((𝟙 Y + nY) ≫ g) ≫ f = 𝟙 Y := by
    rw [Category.assoc]
    simp only [Preadditive.add_comp, Category.id_comp]
    have hgf : g ≫ f = 𝟙 Y - nY := by
      simp [nY]
    rw [hgf, Preadditive.comp_sub, Category.comp_id, hnYsq, sub_zero]
    abel
  let leftInv : Y ⟶ X := g ≫ (𝟙 X + nX)
  let rightInv : Y ⟶ X := (𝟙 Y + nY) ≫ g
  have hEq : leftInv = rightInv := by
    calc
      leftInv = 𝟙 Y ≫ leftInv := by rw [Category.id_comp]
      _ = (rightInv ≫ f) ≫ leftInv := by rw [hright]
      _ = rightInv ≫ (f ≫ leftInv) := by rw [Category.assoc]
      _ = rightInv ≫ 𝟙 X := by rw [hleft]
      _ = rightInv := by rw [Category.comp_id]
  exact IsIso.mk ⟨leftInv, hleft, hEq.symm ▸ hright⟩

/-- Package inverse lifting as the standard categorical reflection
property. -/
theorem reflectsIsomorphisms_of_kernelSquareZero
    (F : C ⥤ D) [F.Additive] [F.Full]
    (hF : FunctorKernelSquareZero F) : F.ReflectsIsomorphisms where
  reflects f _ := reflectsIso_of_kernelSquareZero F hF f

/-- Any isomorphism between two functor images lifts to an isomorphism
between the source objects. -/
def isoOfMapIsoOfKernelSquareZero
    (F : C ⥤ D) [F.Additive] [F.Full]
    (hF : FunctorKernelSquareZero F)
    {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y := by
  let f : X ⟶ Y := F.preimage e.hom
  haveI : IsIso (F.map f) := by
    rw [show F.map f = e.hom from F.map_preimage e.hom]
    infer_instance
  haveI : IsIso f := reflectsIso_of_kernelSquareZero F hF f
  exact asIso f

/-- An idempotent on the image of an object splits when the endomorphism map
is surjective, its kernel is elementwise nilpotent, and idempotents split in
the source category. -/
theorem image_idempotent_splits
    (F : C ⥤ D) [F.Additive] [IsIdempotentComplete C]
    (X : C)
    (hsurjective : Function.Surjective
      (fun f : End X ↦ F.map f))
    (hker : ∀ f : End X, F.map f = 0 → IsNilpotent f)
    (p : End (F.obj X)) (hp : p ≫ p = p) :
    ∃ (Y : D) (i : Y ⟶ F.obj X) (e : F.obj X ⟶ Y),
      i ≫ e = 𝟙 Y ∧ e ≫ i = p := by
  let φ : End X →+* End (F.obj X) :=
    { F.mapEnd X with
      map_zero' := F.map_zero X X
      map_add' := fun _ _ ↦ by exact F.map_add }
  have hφsurjective : Function.Surjective φ := hsurjective
  have hφker : ∀ f ∈ RingHom.ker φ, IsNilpotent f := by
    intro f hf
    exact hker f hf
  have hp' : IsIdempotentElem p := hp
  obtain ⟨q, hq, hφq⟩ :=
    exists_isIdempotentElem_eq_of_ker_isNilpotent
      φ hφker p (Set.mem_range.mpr (hφsurjective p)) hp'
  obtain ⟨Y, i, e, hi, he⟩ :=
    IsIdempotentComplete.idempotents_split X q hq
  refine ⟨F.obj Y, F.map i, F.map e, ?_, ?_⟩
  · rw [← F.map_comp, hi, F.map_id]
  · rw [← F.map_comp, he]
    exact hφq

/-- A full, essentially surjective additive functor with elementwise
nilpotent endomorphism kernels transports idempotent completeness to its
target. -/
theorem isIdempotentComplete_of_ker_mapEnd_isNilpotent
    (F : C ⥤ D) [F.Additive] [F.Full] [F.EssSurj]
    [IsIdempotentComplete C]
    (hker : ∀ (X : C) (f : End X),
      F.map f = 0 → IsNilpotent f) :
    IsIdempotentComplete D := by
  refine ⟨?_⟩
  intro Y p hp
  obtain ⟨X, ⟨ε⟩⟩ := Functor.EssSurj.mem_essImage (F := F) Y
  let q : End (F.obj X) := ε.hom ≫ p ≫ ε.inv
  have hq : q ≫ q = q := by
    dsimp only [q]
    simp only [Category.assoc, ε.inv_hom_id_assoc]
    rw [← Category.assoc p p ε.inv, hp]
  have hsplitq :
      ∃ (Z : D) (i : Z ⟶ F.obj X) (e : F.obj X ⟶ Z),
        i ≫ e = 𝟙 Z ∧ e ≫ i = q := by
    apply image_idempotent_splits F X
      (F.map_surjective (X := X) (Y := X))
      (hker X) q hq
  apply (CategoryTheory.Idempotents.split_iff_of_iso
    ε q p (by simp [q])).mp
  exact hsplitq

/-- It suffices to have, for each target object, one isomorphic functor image
on whose endomorphism ring the functor kernel is elementwise nilpotent.  This
form permits discarding direct summands which the functor sends to zero. -/
theorem isIdempotentComplete_of_objectwise_nilpotent_kernel
    (F : C ⥤ D) [F.Additive] [F.Full]
    [IsIdempotentComplete C]
    (hcover : ∀ Y : D,
      ∃ (X : C) (_ : F.obj X ≅ Y),
        ∀ f : End X, F.map f = 0 → IsNilpotent f) :
    IsIdempotentComplete D := by
  refine ⟨?_⟩
  intro Y p hp
  obtain ⟨X, ε, hker⟩ := hcover Y
  let q : End (F.obj X) := ε.hom ≫ p ≫ ε.inv
  have hq : q ≫ q = q := by
    dsimp only [q]
    simp only [Category.assoc, ε.inv_hom_id_assoc]
    rw [← Category.assoc p p ε.inv, hp]
  have hsplitq :
      ∃ (Z : D) (i : Z ⟶ F.obj X) (e : F.obj X ⟶ Z),
        i ≫ e = 𝟙 Z ∧ e ≫ i = q := by
    apply image_idempotent_splits F X
      (F.map_surjective (X := X) (Y := X)) hker q hq
  apply (CategoryTheory.Idempotents.split_iff_of_iso
    ε q p (by simp [q])).mp
  exact hsplitq

end MBDVendor.QSE.CategoryTheory.IdempotentLifting
