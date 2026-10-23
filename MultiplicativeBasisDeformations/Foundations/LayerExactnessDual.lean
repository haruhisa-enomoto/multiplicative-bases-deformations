module

public import MultiplicativeBasisDeformations.Foundations.LayerExactness
public import MultiplicativeBasisDeformations.Foundations.ARQuiver
public import MultiplicativeBasisDeformations.Foundations.StrictLayersDual

/-!
# Exactness of the second sequence of Proposition 2.6(1)

`graded-category.tex`: "Applying these arguments to the opposite module
category proves exactness of the second sequence in (1)." In `(mod A)ᵒᵖ` the
right radical approximations are the left meshes of `mod A` (biproducts of the
left almost split maps of the summands, with `I → I/soc I` at injective
summands), and the Krull–Schmidt normal form is the target normal form of
`mod A`; so the abstract Lemma 2.5 holds in `(mod A)ᵒᵖ`.

At a nonprojective vertex `x` the almost split sequence `τx → E_x → x` is also
the left mesh of `τx`. Its dual radical approximation gives, for a family
`v_i : E_i → W` out of the summands:

* (lowest degree) `∑ α_i v_i ∈ J²` implies every `v_i ∈ J`;
* (exactness at the middle) if every `v_i ∈ J^{n+1}` and
  `∑ α_i v_i ∈ J^{n+3}`, then `v_i ≡ β_i u` modulo `J^{n+2}` for one
  `u ∈ J^n(x, W)`;
* (injectivity) if every `β_i u ∈ J^{n+2}`, then `u ∈ J^{n+1}`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

include S in
/-- The Krull–Schmidt target normal form in `mod A`. -/
theorem hasSplitRadicalConormalForm : StrictLayers.HasSplitRadicalConormalForm (ModCat A) :=
  fun u ↦ MBDVendor.QSE.Iyama.LeftLadder.FiniteTauCategoryData.exists_splitEpi_radical_normalForm
    S.toVendor.finiteTauCategoryData u

/-- The second map of the left mesh of a module is an epimorphism. -/
theorem moduleLeftMesh_g_epi (Y : ModCat A) : Epi (S.toVendor.moduleLeftMesh Y).g := by
  let d := S.toVendor.chosenLabelDecomposition Y
  change Epi (biproduct.map fun i : Fin d.n ↦ (S.toVendor.labelLeftMesh (d.label i)).g)
  have : ∀ i : Fin d.n, Epi (S.toVendor.labelLeftMesh (d.label i)).g :=
    fun i ↦ S.toVendor.labelLeftMesh_g_epi (d.label i)
  apply Preadditive.epi_of_cancel_zero
  intro W t ht
  apply biproduct.hom_ext'
  intro j
  have h := congrArg (biproduct.ι _ j ≫ ·) ht
  simp only [biproduct.ι_map_assoc, comp_zero] at h
  rw [comp_zero]
  exact (cancel_epi (S.toVendor.labelLeftMesh (d.label j)).g).1 (by simpa using h)

/-- The right radical approximation of a module in `(mod A)ᵒᵖ`, from its left
mesh. -/
def opApprox (Y : (ModCat A)ᵒᵖ) : StrictLayers.RightRadicalApprox Y :=
  StrictLayers.approxOfLeftTau (S.toVendor.moduleLeftMesh Y.unop)
    (S.toVendor.moduleLeftTau Y.unop).toTauApproximation
    (StrictLayers.isWeakCok_of_left _ (S.toVendor.moduleLeftTau Y.unop))
    (S.moduleLeftMesh_g_epi Y.unop) (S.toVendor.moduleLeftTermIso Y.unop)

include S in
theorem hasSplitRadicalNormalForm_op : StrictLayers.HasSplitRadicalNormalForm (ModCat A)ᵒᵖ :=
  StrictLayers.hasSplitRadicalNormalForm_op S.hasSplitRadicalConormalForm

/-- At a nonprojective vertex, the second map of the almost split sequence is a
weak cokernel of the first: the sequence is also the left mesh of `τx`. -/
theorem rightMesh_isWeakCok (y : S.nonprojectiveVertices) :
    StrictLayers.IsWeakCok (S.rightMesh (S.index y.1)) :=
  StrictLayers.isWeakCok_of_iso (S.tau.rightLeftMeshIso (S.vendorNonprojective y))
    (StrictLayers.isWeakCok_of_left _ (S.tau.leftTau _))

theorem rightMesh_g_epi (y : S.nonprojectiveVertices) : Epi (S.rightMesh (S.index y.1)).g := by
  haveI : Epi (S.tau.leftMesh
      (S.tau.obj ((S.tau.tauPlusEquiv (S.vendorNonprojective y)).1))).g := by
    change Epi (S.toVendor.canonicalLeftMesh (S.toVendor.fgObj _)).g
    rw [S.toVendor.canonicalLeftMesh_at_label]
    exact S.toVendor.labelLeftMesh_g_epi _
  exact StrictLayers.epi_g_of_iso (S.tau.rightLeftMeshIso (S.vendorNonprojective y))

/-- The dual radical approximation of `τx` in `(mod A)ᵒᵖ`, from the almost
split sequence ending at the nonprojective vertex `x`. -/
def coApprox (y : S.nonprojectiveVertices) :
    StrictLayers.RightRadicalApprox (op (S.rightMesh (S.index y.1)).X₁) :=
  StrictLayers.approxOfLeftTau (S.rightMesh _) (S.tau.rightTau _).toTauApproximation
    (S.rightMesh_isWeakCok y) (S.rightMesh_g_epi y) (Iso.refl _)

/-- The map out of the middle term with components `v_i`. -/
def midDesc {W : ModCat A} (x : Fin S.n) (v : ∀ i, S.fg (S.midLabel x i) ⟶ W) :
    (S.rightMesh x).X₂ ⟶ W :=
  ∑ i, S.midProj x i ≫ v i

theorem midInc_midDesc {W : ModCat A} (x : Fin S.n) (v : ∀ i, S.fg (S.midLabel x i) ⟶ W)
    (j : Fin (S.arity x)) : S.midInc x j ≫ S.midDesc x v = v j := by
  simp only [midDesc, Preadditive.comp_sum, ← Category.assoc]
  rw [Finset.sum_eq_single j]
  · rw [midInc_midProj_self, Category.id_comp]
  · intro i _ hij
    rw [midInc_midProj_ne _ _ (Ne.symm hij), zero_comp]
  · simp

theorem midDesc_mem {W : ModCat A} (x : Fin S.n) (v : ∀ i, S.fg (S.midLabel x i) ⟶ W) {n : ℕ}
    (hv : ∀ i, v i ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _) :
    S.midDesc x v ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _ :=
  Submodule.sum_mem (HomIdeal.homSubmodule (k := k) _ _ _) fun i _ ↦
    (StrictLayers.Ipow n : HomIdeal (ModCat A)).precomp _ (hv i)

theorem f_midDesc {W : ModCat A} (x : Fin S.n) (v : ∀ i, S.fg (S.midLabel x i) ⟶ W) :
    (S.rightMesh x).f ≫ S.midDesc x v = ∑ i, ((S.rightMesh x).f ≫ S.midProj x i) ≫ v i := by
  simp [midDesc, Preadditive.comp_sum]

/-- **Proposition 2.6(1)**, second sequence, lowest degree: `∑ α_i v_i ∈ J²`
implies `v_i ∈ J` for every summand. -/
theorem colayer_exact_zero {W : ModCat A} (y : S.nonprojectiveVertices)
    (v : ∀ i, S.fg (S.midLabel (S.index y.1) i) ⟶ W)
    (hsum : ∑ i, ((S.rightMesh (S.index y.1)).f ≫ S.midProj (S.index y.1) i) ≫ v i ∈
      (StrictLayers.Ipow 2 : HomIdeal (ModCat A)).hom _ W)
    (i : Fin (S.arity (S.index y.1))) :
    v i ∈ (StrictLayers.Ipow 1 : HomIdeal (ModCat A)).hom _ W := by
  have h := (S.coApprox y).layer_exact_zero (S.midDesc _ v).op (by
    rw [← StrictLayers.mem_Ipow_unop_iff]
    change (Iso.refl _).inv ≫ (S.rightMesh (S.index y.1)).f ≫ S.midDesc _ v ∈ _
    rw [Iso.refl_inv, Category.id_comp, f_midDesc]
    exact hsum)
  rw [← StrictLayers.mem_Ipow_unop_iff] at h
  rw [← S.midInc_midDesc _ v i]
  exact (StrictLayers.Ipow 1 : HomIdeal (ModCat A)).precomp _ h

/-- **Proposition 2.6(1)**, second sequence, exactness at the middle term: if
every `v_i ∈ J^{n+1}` and `∑ α_i v_i ∈ J^{n+3}`, then there is
`u ∈ J^n(x, W)` with `v_i - β_i u ∈ J^{n+2}` for every summand. -/
theorem colayer_exact {W : ModCat A} (y : S.nonprojectiveVertices)
    (v : ∀ i, S.fg (S.midLabel (S.index y.1) i) ⟶ W) {n : ℕ}
    (hv : ∀ i, v i ∈ (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).hom _ W)
    (hsum : ∑ i, ((S.rightMesh (S.index y.1)).f ≫ S.midProj (S.index y.1) i) ≫ v i ∈
      (StrictLayers.Ipow (n + 3) : HomIdeal (ModCat A)).hom _ W) :
    ∃ u : S.fg (S.index y.1) ⟶ W, u ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _ ∧
      ∀ i, v i - S.beta (S.index y.1) i ≫ u ∈
        (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).hom _ W := by
  obtain ⟨z, hz, hwz⟩ := (S.coApprox y).layer_exact S.hasSplitRadicalNormalForm_op S.opApprox
    (S.midDesc _ v).op
    (by rw [← StrictLayers.mem_Ipow_unop_iff]; exact S.midDesc_mem _ v hv)
    (by
      rw [← StrictLayers.mem_Ipow_unop_iff]
      change (Iso.refl _).inv ≫ (S.rightMesh (S.index y.1)).f ≫ S.midDesc _ v ∈ _
      rw [Iso.refl_inv, Category.id_comp, f_midDesc]
      exact hsum)
  rw [← StrictLayers.mem_Ipow_unop_iff] at hz hwz
  refine ⟨(S.tau.rightTermIso (S.tau.obj (S.index y.1))).inv ≫ z.unop,
    (StrictLayers.Ipow n : HomIdeal (ModCat A)).precomp _ hz, fun i ↦ ?_⟩
  have h := (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).precomp
    (S.midInc (S.index y.1) i) hwz
  change S.midInc _ i ≫ (S.midDesc _ v - (S.rightMesh (S.index y.1)).g ≫ z.unop) ∈ _ at h
  rw [Preadditive.comp_sub, S.midInc_midDesc] at h
  have e : S.beta _ i ≫ (S.tau.rightTermIso (S.tau.obj (S.index y.1))).inv ≫ z.unop =
      S.midInc _ i ≫ (S.rightMesh (S.index y.1)).g ≫ z.unop := by
    rw [beta_eq, vertexApprox_p]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [e]
  exact h

/-- **Proposition 2.6(1)**, second sequence, injectivity: if every
`β_i u ∈ J^{n+2}`, then `u ∈ J^{n+1}`. -/
theorem colayer_injective {W : ModCat A} (y : S.nonprojectiveVertices) {n : ℕ}
    (u : S.fg (S.index y.1) ⟶ W)
    (hu : ∀ i, S.beta (S.index y.1) i ≫ u ∈
      (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).hom _ W) :
    u ∈ (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).hom _ W := by
  have h := (S.coApprox y).layer_injective S.hasSplitRadicalNormalForm_op S.opApprox
    ((S.tau.rightTermIso (S.tau.obj (S.index y.1))).hom ≫ u).op (by
      rw [← StrictLayers.mem_Ipow_unop_iff]
      change (S.rightMesh (S.index y.1)).g ≫ (S.tau.rightTermIso (S.tau.obj (S.index y.1))).hom ≫ u ∈ _
      have e : (S.rightMesh (S.index y.1)).g ≫ (S.tau.rightTermIso (S.tau.obj (S.index y.1))).hom ≫ u =
          ∑ i, S.midProj (S.index y.1) i ≫ S.beta (S.index y.1) i ≫ u := by
        calc (S.rightMesh (S.index y.1)).g ≫ (S.tau.rightTermIso (S.tau.obj (S.index y.1))).hom ≫ u
            = (∑ i, S.midProj (S.index y.1) i ≫ S.midInc (S.index y.1) i) ≫
                (S.rightMesh (S.index y.1)).g ≫ (S.tau.rightTermIso (S.tau.obj (S.index y.1))).hom ≫ u := by
              rw [S.sum_midProj_midInc, Category.id_comp]
          _ = _ := by
              rw [Preadditive.sum_comp]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [beta_eq, vertexApprox_p]
              simp only [Category.assoc]
      rw [e]
      exact sum_mem fun i _ ↦
        (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).precomp _ (hu i))
  rw [← StrictLayers.mem_Ipow_unop_iff] at h
  have := (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).precomp (S.tau.rightTermIso (S.tau.obj (S.index y.1))).inv h
  rwa [Quiver.Hom.unop_op, Iso.inv_hom_id_assoc] at this

end MultiplicativeBasisDeformations.IndSkeleton
