import MBDVendor.Magnitude.CategoryTheory.FiniteKrullSchmidtMatrix
import MBDVendor.Magnitude.CategoryTheory.IrreducibleAbelian

/-!
# Irreducible components of minimal almost-split morphisms

This leaf module keeps the finite Krull--Schmidt matrix dependency out of the
widely imported elementary irreducible-morphism API.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A component cut out by an indecomposable split summand from a minimal
right almost-split morphism to an indecomposable target is irreducible. -/
theorem IsRightAlmostSplit.irreducible_comp_of_splitSummand
    {X E Z : C} (g : E ⟶ Z) (hg : IsRightAlmostSplit g)
    (hgmin : IsRightMinimal g)
    (inc : X ⟶ E) (proj : E ⟶ X)
    (hinc : inc ≫ proj = 𝟙 X)
    (hX : Indecomposable X) (hZ : Indecomposable Z) :
    IsIrreducibleMorphism (inc ≫ g) := by
  let f : X ⟶ Z := inc ≫ g
  have hnotepi : ¬ IsSplitEpi f := by
    intro hf
    obtain ⟨se⟩ := hf.exists_splitEpi
    apply hg.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := se.section_ ≫ inc
        id := by simpa only [f, Category.assoc] using se.id }
  have hnotmono : ¬ IsSplitMono f := by
    intro hf
    letI : IsSplitMono f := hf
    letI : IsIso f :=
      MBDVendor.Magnitude.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        hZ f hX.1
    exact hnotepi inferInstance
  change IsIrreducibleMorphism f
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  obtain ⟨q, hq⟩ := hg.factors b hb
  let e : E ⟶ E := 𝟙 E + proj ≫ (a ≫ q - inc)
  have hefix : e ≫ g = g := by
    dsimp only [e]
    rw [Preadditive.add_comp, Category.id_comp,
      Category.assoc, Preadditive.sub_comp]
    have haq : (a ≫ q) ≫ g = f := by
      rw [Category.assoc, hq, hab]
    rw [haq]
    change g + proj ≫ (f - f) = g
    simp
  have hence : inc ≫ e = a ≫ q := by
    dsimp only [e]
    rw [Preadditive.comp_add, Category.comp_id,
      ← Category.assoc, hinc, Category.id_comp]
    abel
  letI : IsIso e := hgmin e hefix
  exact Or.inl (IsSplitMono.mk'
    { retraction := q ≫ inv e ≫ proj
      id := by
        calc
          a ≫ (q ≫ inv e ≫ proj) =
              (a ≫ q) ≫ inv e ≫ proj := by
                simp only [Category.assoc]
          _ = (inc ≫ e) ≫ inv e ≫ proj := by rw [hence]
          _ = 𝟙 X := by
                simp only [Category.assoc,
                  IsIso.hom_inv_id_assoc, hinc] })

/-- A component cut out by an indecomposable split quotient of the target of
a minimal left almost-split morphism from an indecomposable source is
irreducible. -/
theorem IsLeftAlmostSplit.comp_irreducible_of_splitSummand
    {X E Y : C} (f : X ⟶ E) (hf : IsLeftAlmostSplit f)
    (hfmin : IsLeftMinimal f)
    (proj : E ⟶ Y) (inc : Y ⟶ E)
    (hinc : inc ≫ proj = 𝟙 Y)
    (hX : Indecomposable X) (hY : Indecomposable Y) :
    IsIrreducibleMorphism (f ≫ proj) := by
  let g : X ⟶ Y := f ≫ proj
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    obtain ⟨sm⟩ := hg.exists_splitMono
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := proj ≫ sm.retraction
        id := by simpa only [g, Category.assoc] using sm.id }
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    letI : IsSplitEpi g := hg
    letI : IsIso g :=
      MBDVendor.Magnitude.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
        hX g hY.1
    exact hnotmono inferInstance
  change IsIrreducibleMorphism g
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M p q hpq
  by_cases hp : IsSplitMono p
  · exact Or.inl hp
  obtain ⟨r, hr⟩ := hf.factors p hp
  let v : E ⟶ E := 𝟙 E + (r ≫ q - proj) ≫ inc
  have hfv : f ≫ v = f := by
    dsimp only [v]
    rw [Preadditive.comp_add, Category.comp_id,
      ← Category.assoc, Preadditive.comp_sub]
    have hrq : f ≫ (r ≫ q) = g := by
      rw [← Category.assoc, hr, hpq]
    rw [hrq]
    change f + (g - g) ≫ inc = f
    simp
  have hvproj : v ≫ proj = r ≫ q := by
    dsimp only [v]
    rw [Preadditive.add_comp, Category.id_comp,
      Category.assoc, hinc, Category.comp_id]
    abel
  letI : IsIso v := hfmin v hfv
  exact Or.inr (IsSplitEpi.mk'
    { section_ := inc ≫ inv v ≫ r
      id := by
        calc
          (inc ≫ inv v ≫ r) ≫ q =
              inc ≫ inv v ≫ (r ≫ q) := by
                simp only [Category.assoc]
          _ = inc ≫ inv v ≫ (v ≫ proj) := by rw [← hvproj]
          _ = 𝟙 Y := by
                simp only [IsIso.inv_hom_id_assoc, hinc] })

end MBDVendor.QSE
