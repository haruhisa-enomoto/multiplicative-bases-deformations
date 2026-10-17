import MultiplicativeBasisDeformations.Foundations.StrictLayers
import MBDVendor.Magnitude.Algebra.RightModuleLeftTau
import MBDVendor.Magnitude.Algebra.RightModuleFactorStrict

/-!
# Lemma 2.5 for `mod A`

The hypotheses of the abstract Lemma 2.5 (`StrictLayers.strict`) hold in
`mod A = FGModuleCat Aᵐᵒᵖ` for a representation-finite algebra:

* the right radical approximation of a module `Y` is the right mesh of `Y`:
  the biproduct of the minimal right almost split maps of the indecomposable
  summands of `Y` (with `rad P → P` at projective summands) and its kernel, a
  biproduct of left almost split maps (`graded-category.tex:238–258`);
* the Krull–Schmidt split–radical normal form.

Both are supplied by the vendored Auslander--Reiten library
(`moduleRightMesh`, `moduleRightTau`, `labelRightMesh_f_mono`,
`exists_splitMono_radical_normalForm`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

include S in
/-- The Krull–Schmidt split–radical normal form in `mod A`. -/
theorem hasSplitRadicalNormalForm : StrictLayers.HasSplitRadicalNormalForm (ModCat A) :=
  fun u ↦ MBDVendor.QSE.Iyama.FiniteRightTauCategoryData.exists_splitMono_radical_normalForm
    S.toVendor.finiteTauCategoryData.toFiniteRightTauCategoryData u

/-- The first map of the right mesh of a module is a monomorphism. -/
theorem moduleRightMesh_f_mono (Y : ModCat A) : Mono (S.toVendor.moduleRightMesh Y).f := by
  let d := S.toVendor.chosenLabelDecomposition Y
  change Mono (biproduct.map fun i : Fin d.n ↦ (S.toVendor.labelRightMesh (d.label i)).f)
  have : ∀ i : Fin d.n, Mono (S.toVendor.labelRightMesh (d.label i)).f :=
    fun i ↦ S.toVendor.labelRightMesh_f_mono (d.label i)
  apply Preadditive.mono_of_cancel_zero
  intro W t ht
  apply biproduct.hom_ext
  intro j
  have h := congrArg (· ≫ biproduct.π _ j) ht
  simp only [Category.assoc, biproduct.map_π, zero_comp] at h
  rw [zero_comp]
  exact (cancel_mono (S.toVendor.labelRightMesh (d.label j)).f).1 (by simpa using h)

/-- The right radical approximation of a module, from its right mesh. -/
def rightRadicalApprox (Y : ModCat A) : StrictLayers.RightRadicalApprox Y where
  E := (S.toVendor.moduleRightMesh Y).X₂
  p := (S.toVendor.moduleRightMesh Y).g ≫ (S.toVendor.moduleRightTermIso Y).hom
  T := (S.toVendor.moduleRightMesh Y).X₁
  i := (S.toVendor.moduleRightMesh Y).f
  p_rad := isRadicalMorphism_postcomp _ (S.toVendor.moduleRightTau Y).g_radical
  factors := by
    intro W g hg
    obtain ⟨b, hb⟩ := (S.toVendor.moduleRightTau Y).factors_into_right
      (g ≫ (S.toVendor.moduleRightTermIso Y).inv) (isRadicalMorphism_postcomp _ hg)
    exact ⟨b, by rw [← Category.assoc, hb]; simp⟩
  i_p := by simp
  lift := by
    intro W w hw
    have hw' : w ≫ (S.toVendor.moduleRightMesh Y).g = 0 := by
      rw [← cancel_mono (S.toVendor.moduleRightTermIso Y).hom]
      simpa using hw
    have hK := (S.toVendor.moduleRightTau Y).minimalWeakKernel.1
    exact ⟨hK.lift w hw', hK.lift_f w hw'⟩
  i_mono := S.moduleRightMesh_f_mono Y
  i_rad := (S.toVendor.moduleRightTau Y).f_radical
  sq := by
    intro Z g hg
    rw [StrictLayers.Ipow, HomIdeal.pow_succ] at hg
    induction hg using AddSubgroup.closure_induction with
    | mem h hh =>
        obtain ⟨M, u, v, hu, hv, rfl⟩ := hh
        rw [HomIdeal.pow_one, mem_homIdeal_iff] at hu
        obtain ⟨b, hb⟩ := (S.toVendor.moduleRightTau Y).factors_from_left u hu
        exact ⟨b ≫ v, isRadicalMorphism_precomp b ((mem_homIdeal_iff v).1 hv),
          by rw [← Category.assoc, hb]⟩
    | zero => exact ⟨0, isRadicalMorphism_zero, by simp⟩
    | add a b _ _ ha hb =>
        obtain ⟨q₁, hq₁, rfl⟩ := ha
        obtain ⟨q₂, hq₂, rfl⟩ := hb
        exact ⟨q₁ + q₂, isRadicalMorphism_add hq₁ hq₂, by rw [Preadditive.comp_add]⟩
    | neg a _ ha =>
        obtain ⟨q, hq, rfl⟩ := ha
        exact ⟨-q, isRadicalMorphism_neg hq, by rw [Preadditive.comp_neg]⟩

include S in
/-- **Lemma 2.5** (`lem:strict-radical-layers`) in `mod A`. -/
theorem strict_radical_layers (n : ℕ) {U Y : ModCat A} (a : U ⟶ Y) (ha : IsRadicalMorphism a)
    (hpert : ∀ h ∈ (StrictLayers.Ipow 2 : HomIdeal (ModCat A)).hom U Y, Mono (a + h))
    {W : ModCat A} (z : W ⟶ U)
    (hz : z ≫ a ∈ (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).hom W Y) :
    z ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom W U :=
  StrictLayers.strict S.hasSplitRadicalNormalForm S.rightRadicalApprox n a ha hpert z hz

end MultiplicativeBasisDeformations.IndSkeleton
