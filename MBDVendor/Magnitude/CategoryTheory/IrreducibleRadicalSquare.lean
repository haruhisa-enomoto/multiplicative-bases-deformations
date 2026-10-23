module

public import MBDVendor.QSE.CategoryTheory.IyamaLadderRadical
public import MBDVendor.QSE.RepresentationTheory.IrreducibleCofinite

/-!
# Irreducible morphisms do not lie in the categorical radical square

In a finite Krull--Schmidt category, a finite sum of composites of radical
morphisms can be consolidated into one factorization through a finite
biproduct.  Both consolidated factors remain radical.  Hence a morphism in
the square of the categorical radical cannot be irreducible.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.Iyama

namespace MBDVendor.Magnitude.FiniteTauMatrix

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteRightTauCategoryData C Ind)

/-- Membership in the product of the categorical radical with itself can be
represented by one composite of two radical morphisms. -/
theorem exists_radical_factorization_of_mem_mul
    {x y : Ind} {f : T.obj x ⟶ T.obj y}
    (hf : f ∈ (T.radical.ideal ⋆ᵢ T.radical.ideal).hom
      (T.obj x) (T.obj y)) :
    ∃ (M : C) (g : T.obj x ⟶ M) (h : M ⟶ T.obj y),
      g ∈ T.radical.ideal.hom (T.obj x) M ∧
      h ∈ T.radical.ideal.hom M (T.obj y) ∧ g ≫ h = f := by
  classical
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
      exact hf
  | zero =>
      let F : Fin 0 → C := fun i ↦ Fin.elim0 i
      refine ⟨⨁ F, 0, 0, zero_mem _, zero_mem _, by simp⟩
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      obtain ⟨M₁, g₁, h₁, hg₁, hh₁, hcomp₁⟩ := hf₁
      obtain ⟨M₂, g₂, h₂, hg₂, hh₂, hcomp₂⟩ := hf₂
      let g : T.obj x ⟶ M₁ ⊞ M₂ := biprod.lift g₁ g₂
      let h : M₁ ⊞ M₂ ⟶ T.obj y := biprod.desc h₁ h₂
      have hg : g ∈ T.radical.ideal.hom (T.obj x) (M₁ ⊞ M₂) := by
        have hg₁' := T.radical.ideal.postcomp
          (biprod.inl : M₁ ⟶ M₁ ⊞ M₂) hg₁
        have hg₂' := T.radical.ideal.postcomp
          (biprod.inr : M₂ ⟶ M₁ ⊞ M₂) hg₂
        have hsum := add_mem hg₁' hg₂'
        have hgeq :
            g = g₁ ≫ (biprod.inl : M₁ ⟶ M₁ ⊞ M₂) +
              g₂ ≫ (biprod.inr : M₂ ⟶ M₁ ⊞ M₂) := by
          apply biprod.hom_ext
          · simp [g]
          · simp [g]
        rw [hgeq]
        exact hsum
      have hh : h ∈ T.radical.ideal.hom (M₁ ⊞ M₂) (T.obj y) := by
        have hh₁' := T.radical.ideal.precomp
          (biprod.fst : M₁ ⊞ M₂ ⟶ M₁) hh₁
        have hh₂' := T.radical.ideal.precomp
          (biprod.snd : M₁ ⊞ M₂ ⟶ M₂) hh₂
        have hsum := add_mem hh₁' hh₂'
        have hheq :
            h = (biprod.fst : M₁ ⊞ M₂ ⟶ M₁) ≫ h₁ +
              (biprod.snd : M₁ ⊞ M₂ ⟶ M₂) ≫ h₂ := by
          apply biprod.hom_ext'
          · simp [h]
          · simp [h]
        rw [hheq]
        exact hsum
      refine ⟨M₁ ⊞ M₂, g, h, hg, hh, ?_⟩
      simp [g, h, hcomp₁, hcomp₂]
  | neg f _ hf =>
      obtain ⟨M, g, h, hg, hh, hcomp⟩ := hf
      refine ⟨M, g, -h, hg, neg_mem hh, ?_⟩
      rw [Preadditive.comp_neg, hcomp]

/-- A morphism in the square of the categorical radical between chosen
indecomposables is not irreducible. -/
theorem not_isIrreducibleMorphism_of_mem_radical_mul
    {x y : Ind} {f : T.obj x ⟶ T.obj y}
    (hf : f ∈ (T.radical.ideal ⋆ᵢ T.radical.ideal).hom
      (T.obj x) (T.obj y)) :
    ¬ IsIrreducibleMorphism f := by
  intro hirr
  obtain ⟨M, g, h, hg, hh, hcomp⟩ :=
    exists_radical_factorization_of_mem_mul T hf
  rcases hirr.factorization g h hcomp with hsplit | hsplit
  · exact ((T.isRadicalMorphism_iff_not_isSplitMono_from_obj g).1
      ((T.radical.mem_ideal_iff g).1 hg)) hsplit
  · exact ((T.isRadicalMorphism_iff_not_isSplitEpi_to_obj h).1
      ((T.radical.mem_ideal_iff h).1 hh)) hsplit

end MBDVendor.Magnitude.FiniteTauMatrix
