module

public import MultiplicativeBasisDeformations.Foundations.ProjectiveIdempotents

/-!
# The exchange step of Krull–Schmidt

An object with local endomorphism ring which is a retract of a finite
biproduct is a retract of one of the summands; a retract with nonzero source
of an object with local endomorphism ring is an isomorphism. These are used
in Lemma 4.6 ("Decomposing the latter over the finitely many indecomposable
`B`-modules shows that only finitely many isomorphism classes can occur",
`scalar-normalization.tex`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem isIso_of_isUnit_end {X : C} {f : End X} (hf : IsUnit f) : IsIso (show X ⟶ X from f) := by
  obtain ⟨w, rfl⟩ := hf
  exact ⟨⟨w.inv, w.inv_val, w.val_inv⟩⟩

/-- **Exchange**: a retract with local endomorphism ring of a finite biproduct
is a retract of one summand. -/
theorem exists_retract_summand {M : C} [IsLocalRing (End M)] {ι : Type} [Fintype ι]
    (Y : ι → C) [HasBiproduct Y] (i : M ⟶ ⨁ Y) (p : (⨁ Y) ⟶ M) (h : i ≫ p = 𝟙 M) :
    ∃ (j : ι) (i' : M ⟶ Y j) (p' : Y j ⟶ M), i' ≫ p' = 𝟙 M := by
  classical
  let f : ι → End M := fun j ↦ i ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ p
  have hsum : (1 : End M) = ∑ j, f j := by
    change 𝟙 M = _
    calc 𝟙 M = i ≫ p := h.symm
      _ = i ≫ (∑ j, biproduct.π Y j ≫ biproduct.ι Y j) ≫ p := by
          rw [biproduct.total, Category.id_comp]
      _ = _ := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
          simp only [Category.assoc]
          rfl
  obtain ⟨j, -, hj⟩ := exists_isUnit_of_sum Finset.univ f (hsum ▸ isUnit_one)
  haveI : IsIso (i ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ p) := isIso_of_isUnit_end hj
  refine ⟨j, i ≫ biproduct.π Y j, biproduct.ι Y j ≫ p ≫
    inv (i ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ p), ?_⟩
  have e : (i ≫ biproduct.π Y j) ≫ biproduct.ι Y j ≫ p ≫
      inv (i ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ p) =
      (i ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ p) ≫
        inv (i ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ p) := by
    simp only [Category.assoc]
  rw [e, IsIso.hom_inv_id]

/-- A retract with nonzero source of an object with local endomorphism ring
is an isomorphism. -/
theorem isIso_of_retract {M Y : C} [IsLocalRing (End Y)] (hM : ¬ IsZero M) (i : M ⟶ Y)
    (p : Y ⟶ M) (h : i ≫ p = 𝟙 M) : IsIso i := by
  have hidem : IsIdempotentElem (show End Y from p ≫ i) := by
    change (p ≫ i) ≫ (p ≫ i) = p ≫ i
    rw [Category.assoc, ← Category.assoc i, h, Category.id_comp]
  rcases idem_eq_zero_or_one hidem with h0 | h1
  · exfalso
    apply hM
    rw [IsZero.iff_id_eq_zero]
    have h2 : i ≫ (p ≫ i) ≫ p = 𝟙 M := by
      rw [← Category.assoc, ← Category.assoc, h, Category.id_comp, h]
    have h3 : p ≫ i = 0 := h0
    rw [← h2, h3, Limits.zero_comp, Limits.comp_zero]
  · exact ⟨⟨p, h, h1⟩⟩

end MultiplicativeBasisDeformations
