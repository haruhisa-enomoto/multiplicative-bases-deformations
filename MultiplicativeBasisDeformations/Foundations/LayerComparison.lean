import MultiplicativeBasisDeformations.Foundations.StrictLayersModules

/-!
# Radical powers of `ind(mod A)` and of `mod A`

For morphisms between indecomposables, the manuscript-literal radical power
`J^n` of `ind(mod A)` (composites of `n` radical maps through indecomposable
modules) coincides with the `n`-th power of the categorical radical of
`mod A` (composites through arbitrary finitely generated modules). This is
the general form of `mem_radPow_two_iff`: an intermediate module is
decomposed into indecomposable summands, and the components of radical maps
are radical.
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

variable {k A : Type w} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- `J^n` of `ind(mod A)` is the `n`-th power of the radical of `mod A`, on
indecomposables. -/
theorem mem_radPow_iff (n : ℕ) {X Y : S.Ind} (f : X ⟶ Y) :
    f ∈ S.radPow n X Y ↔
      S.toFG.map f ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _ := by
  induction n generalizing X Y with
  | zero => exact ⟨fun _ ↦ trivial, fun _ ↦ Submodule.mem_top⟩
  | succ n ih =>
      constructor
      · intro hf
        change f ∈ Submodule.span k _ at hf
        induction hf using Submodule.span_induction with
        | mem h hh =>
            obtain ⟨Z, f₁, g, hf₁, hg, rfl⟩ := hh
            rw [Functor.map_comp]
            exact StrictLayers.rad_comp_mem ((S.isRadical_iff f₁).1 hf₁) ((ih g).1 hg)
        | zero => rw [Functor.map_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [Functor.map_add]; exact add_mem ha hb
        | smul c a _ ha =>
            have h : S.toFG.map (c • a) = (c • 𝟙 _) ≫ S.toFG.map a := by
              simp [Functor.map_smul]
            rw [h]
            exact (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).precomp _ ha
      · intro hf
        suffices H : ∀ h ∈ (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).hom
            (S.toFG.obj X) (S.toFG.obj Y), (S.homEquivFG X Y).symm h ∈ S.radPow (n + 1) X Y by
          have h := H _ hf
          rwa [← homEquivFG_apply, LinearEquiv.symm_apply_apply] at h
        intro h hh
        rw [StrictLayers.Ipow, HomIdeal.pow_succ_eq_mul_pow] at hh
        induction hh using AddSubgroup.closure_induction with
        | mem h hh =>
            obtain ⟨M, a, b, ha, hb, rfl⟩ := hh
            obtain ⟨m, label, ⟨e⟩⟩ := S.toVendor.fgObj_decomposition (k := k) M
            rw [comp_eq_sum_biproduct e a b, map_sum]
            refine Submodule.sum_mem _ fun i _ ↦ ?_
            let a' : X ⟶ S.ind (label i) :=
              (S.homEquivFG X (S.ind (label i))).symm
                (a ≫ e.hom ≫ biproduct.π (fun j ↦ S.toVendor.fgObj (label j)) i)
            let b' : S.ind (label i) ⟶ Y :=
              (S.homEquivFG (S.ind (label i)) Y).symm
                (biproduct.ι (fun j ↦ S.toVendor.fgObj (label j)) i ≫ e.inv ≫ b)
            have ha' : S.toFG.map a' =
                a ≫ e.hom ≫ biproduct.π (fun j ↦ S.toVendor.fgObj (label j)) i :=
              S.map_homEquivFG_symm _
            have hb' : S.toFG.map b' =
                biproduct.ι (fun j ↦ S.toVendor.fgObj (label j)) i ≫ e.inv ≫ b :=
              S.map_homEquivFG_symm _
            have hterm : (a ≫ e.hom ≫ biproduct.π (fun j ↦ S.toVendor.fgObj (label j)) i) ≫
                (biproduct.ι (fun j ↦ S.toVendor.fgObj (label j)) i ≫ e.inv ≫ b) =
                  S.homEquivFG X Y (a' ≫ b') := by
              rw [homEquivFG_apply, Functor.map_comp, ha', hb']
            rw [hterm, LinearEquiv.symm_apply_apply]
            apply Submodule.subset_span
            refine ⟨S.ind (label i), a', b', ?_, ?_, rfl⟩
            · rw [isRadical_iff, ha']
              exact isRadicalMorphism_postcomp _ ((mem_homIdeal_iff a).1 ha)
            · rw [ih, hb']
              exact (StrictLayers.Ipow n : HomIdeal (ModCat A)).precomp _
                ((StrictLayers.Ipow n : HomIdeal (ModCat A)).precomp _ hb)
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | neg a _ ha => rw [map_neg]; exact neg_mem ha

end MultiplicativeBasisDeformations.IndSkeleton
