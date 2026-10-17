import MultiplicativeBasisDeformations.Foundations.LayerComparison
import MBDVendor.Magnitude.CategoryTheory.FiniteTauIrreducible

/-!
# Exactness of almost split sequences on radical layers

Proposition 2.6(1)(2) (`prop:graded-realization`, `graded-category.tex`),
in filtered form, at the canonical right mesh of a vertex `x` of `Γ_A`: the
minimal right almost split map `E_x → x` (with `E_x` decomposed into chosen
indecomposables, and `rad P → P` at a projective vertex) and its kernel `τx`
(zero at a projective vertex). For a family `w_i : W → E_i` of maps into the
summands:

* (lowest degree) `∑ w_i β_i ∈ J²` implies every `w_i ∈ J`;
* (exactness at the middle) if every `w_i ∈ J^{n+1}` and
  `∑ w_i β_i ∈ J^{n+3}`, then `w_i ≡ z α_i` modulo `J^{n+2}` for one
  `z ∈ J^n(W, τx)`;
* (injectivity) if every `z α_i ∈ J^{n+2}`, then `z ∈ J^{n+1}`.

Here `α_i : τx → E_i` and `β_i : E_i → x` are the components of the two maps.
At a projective vertex the left term is zero, which gives Proposition 2.6(2).
The statements are proved in `mod A`, from Lemma 2.5, and hold for every
finitely generated `W`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

namespace StrictLayers

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A right tau-sequence with monic first map is a right radical
approximation of its right term. -/
def approxOfRightTau {Y : C} (M : ShortComplex C) (hM : MBDVendor.QSE.Iyama.RightTauSequence M)
    (hmono : Mono M.f) (e : M.X₃ ≅ Y) : RightRadicalApprox Y where
  E := M.X₂
  p := M.g ≫ e.hom
  T := M.X₁
  i := M.f
  p_rad := isRadicalMorphism_postcomp _ hM.g_radical
  factors := by
    intro W g hg
    obtain ⟨b, hb⟩ := hM.factors_into_right (g ≫ e.inv) (isRadicalMorphism_postcomp _ hg)
    exact ⟨b, by rw [← Category.assoc, hb]; simp⟩
  i_p := by simp
  lift := by
    intro W w hw
    have hw' : w ≫ M.g = 0 := by
      rw [← cancel_mono e.hom]
      simpa using hw
    have hK := hM.minimalWeakKernel.1
    exact ⟨hK.lift w hw', hK.lift_f w hw'⟩
  i_mono := hmono
  i_rad := hM.f_radical
  sq := by
    intro Z g hg
    rw [Ipow, HomIdeal.pow_succ] at hg
    induction hg using AddSubgroup.closure_induction with
    | mem h hh =>
        obtain ⟨N, u, v, hu, hv, rfl⟩ := hh
        rw [HomIdeal.pow_one, mem_homIdeal_iff] at hu
        obtain ⟨b, hb⟩ := hM.factors_from_left u hu
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

end StrictLayers

namespace IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

/-- The vendored tau-category data of `mod A`. -/
abbrev tau := S.toVendor.finiteTauCategoryData

/-- The canonical right mesh ending at the vertex `x`. -/
abbrev rightMesh (x : Fin S.n) : ShortComplex (ModCat A) :=
  S.tau.rightMesh (S.tau.obj x)

/-- The number of summands of the middle term of the right mesh at `x`. -/
abbrev arity (x : Fin S.n) : ℕ :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleArity S.tau.toFiniteRightTauCategoryData x

/-- The label of a summand of the middle term. -/
abbrev midLabel (x : Fin S.n) (i : Fin (S.arity x)) : Fin S.n :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleLabel S.tau.toFiniteRightTauCategoryData x i

/-- Inclusion of a summand into the middle term. -/
abbrev midInc (x : Fin S.n) (i : Fin (S.arity x)) : S.fg (S.midLabel x i) ⟶ (S.rightMesh x).X₂ :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleInclusion S.tau x i

/-- Projection from the middle term onto a summand. -/
abbrev midProj (x : Fin S.n) (i : Fin (S.arity x)) : (S.rightMesh x).X₂ ⟶ S.fg (S.midLabel x i) :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleProjection S.tau x i

/-- The component `β_i : E_i → x` of the right almost split map. -/
abbrev beta (x : Fin S.n) (i : Fin (S.arity x)) : S.fg (S.midLabel x i) ⟶ S.fg x :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleComponent S.tau x i

theorem midInc_midProj_self (x : Fin S.n) (i : Fin (S.arity x)) :
    S.midInc x i ≫ S.midProj x i = 𝟙 _ :=
  MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleInclusion_projection S.tau x i

theorem midInc_midProj_ne (x : Fin S.n) {i j : Fin (S.arity x)} (h : i ≠ j) :
    S.midInc x i ≫ S.midProj x j = 0 := by
  unfold midInc midProj MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleInclusion
    MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleProjection
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact biproduct.ι_π_ne _ h

theorem sum_midProj_midInc (x : Fin S.n) :
    ∑ i, S.midProj x i ≫ S.midInc x i = 𝟙 _ := by
  let D := MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleDecompositionIso S.tau x
  let F := fun j ↦ S.tau.obj
    (MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleLabel S.tau.toFiniteRightTauCategoryData x j)
  calc ∑ i, S.midProj x i ≫ S.midInc x i
      = D.hom ≫ (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫ D.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        rfl
    _ = 𝟙 _ := by rw [biproduct.total, Category.id_comp, Iso.hom_inv_id]

/-- The first map of the right mesh is monic. -/
theorem rightMesh_f_mono (x : Fin S.n) : Mono (S.rightMesh x).f := by
  change Mono (S.toVendor.canonicalRightMesh (S.toVendor.fgObj x)).f
  rw [S.toVendor.canonicalRightMesh_at_label x]
  exact S.toVendor.labelRightMesh_f_mono x

/-- The right radical approximation of the vertex `x`, from its canonical
right mesh. -/
def vertexApprox (x : Fin S.n) : StrictLayers.RightRadicalApprox (S.fg x) :=
  StrictLayers.approxOfRightTau (S.rightMesh x) (S.tau.rightTau _) (S.rightMesh_f_mono x)
    (S.tau.rightTermIso _)

theorem vertexApprox_p (x : Fin S.n) :
    (S.vertexApprox x).p = (S.rightMesh x).g ≫ (S.tau.rightTermIso _).hom := rfl

theorem beta_eq (x : Fin S.n) (i : Fin (S.arity x)) :
    S.beta x i = S.midInc x i ≫ (S.vertexApprox x).p := rfl

/-- The map into the middle term with components `w_i`. -/
def midLift {W : ModCat A} (x : Fin S.n) (w : ∀ i, W ⟶ S.fg (S.midLabel x i)) :
    W ⟶ (S.rightMesh x).X₂ :=
  ∑ i, w i ≫ S.midInc x i

theorem midLift_midProj {W : ModCat A} (x : Fin S.n) (w : ∀ i, W ⟶ S.fg (S.midLabel x i))
    (j : Fin (S.arity x)) : S.midLift x w ≫ S.midProj x j = w j := by
  simp only [midLift, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_eq_single j]
  · rw [midInc_midProj_self, Category.comp_id]
  · intro i _ hij
    rw [midInc_midProj_ne _ _ hij, comp_zero]
  · simp

theorem midLift_p {W : ModCat A} (x : Fin S.n) (w : ∀ i, W ⟶ S.fg (S.midLabel x i)) :
    S.midLift x w ≫ (S.vertexApprox x).p = ∑ i, w i ≫ S.beta x i := by
  simp [midLift, Preadditive.sum_comp, beta_eq]

theorem midLift_mem {W : ModCat A} (x : Fin S.n) (w : ∀ i, W ⟶ S.fg (S.midLabel x i)) {n : ℕ}
    (hw : ∀ i, w i ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _) :
    S.midLift x w ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _ :=
  Submodule.sum_mem (HomIdeal.homSubmodule (k := k) _ _ _) fun i _ ↦
    (StrictLayers.Ipow n : HomIdeal (ModCat A)).postcomp _ (hw i)

/-- **Proposition 2.6(1)(2)**, lowest degree: `∑ w_i β_i ∈ J²` implies
`w_i ∈ J` for every summand. -/
theorem layer_exact_zero {W : ModCat A} (x : Fin S.n) (w : ∀ i, W ⟶ S.fg (S.midLabel x i))
    (hsum : ∑ i, w i ≫ S.beta x i ∈ (StrictLayers.Ipow 2 : HomIdeal (ModCat A)).hom W (S.fg x))
    (i : Fin (S.arity x)) :
    w i ∈ (StrictLayers.Ipow 1 : HomIdeal (ModCat A)).hom W _ := by
  have h := (S.vertexApprox x).layer_exact_zero (S.midLift x w) (by rw [midLift_p]; exact hsum)
  rw [← S.midLift_midProj x w i]
  exact (StrictLayers.Ipow 1 : HomIdeal (ModCat A)).postcomp _ h

/-- **Proposition 2.6(1)(2)**, exactness at the middle term: if every
`w_i ∈ J^{n+1}` and `∑ w_i β_i ∈ J^{n+3}`, then there is `z ∈ J^n(W, τx)` with
`w_i - z α_i ∈ J^{n+2}` for every summand. Here `α_i = f ≫ π_i` are the
components of the first map `f` of the mesh. -/
theorem layer_exact {W : ModCat A} (x : Fin S.n) (w : ∀ i, W ⟶ S.fg (S.midLabel x i)) {n : ℕ}
    (hw : ∀ i, w i ∈ (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).hom W _)
    (hsum : ∑ i, w i ≫ S.beta x i ∈
      (StrictLayers.Ipow (n + 3) : HomIdeal (ModCat A)).hom W (S.fg x)) :
    ∃ z : W ⟶ (S.rightMesh x).X₁, z ∈ (StrictLayers.Ipow n : HomIdeal (ModCat A)).hom _ _ ∧
      ∀ i, w i - z ≫ (S.rightMesh x).f ≫ S.midProj x i ∈
        (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).hom W _ := by
  obtain ⟨z, hz, hwz⟩ := (S.vertexApprox x).layer_exact S.hasSplitRadicalNormalForm
    S.rightRadicalApprox (S.midLift x w) (S.midLift_mem x w hw) (by rw [midLift_p]; exact hsum)
  refine ⟨z, hz, fun i ↦ ?_⟩
  have h := (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).postcomp (S.midProj x i) hwz
  rw [Preadditive.sub_comp, S.midLift_midProj, Category.assoc] at h
  exact h

/-- **Proposition 2.6(1)**, injectivity of the first map on layers. -/
theorem layer_injective {W : ModCat A} (x : Fin S.n) {n : ℕ} (z : W ⟶ (S.rightMesh x).X₁)
    (hz : ∀ i, z ≫ (S.rightMesh x).f ≫ S.midProj x i ∈
      (StrictLayers.Ipow (n + 2) : HomIdeal (ModCat A)).hom W _) :
    z ∈ (StrictLayers.Ipow (n + 1) : HomIdeal (ModCat A)).hom _ _ := by
  apply (S.vertexApprox x).layer_injective S.hasSplitRadicalNormalForm S.rightRadicalApprox z
  have : z ≫ (S.vertexApprox x).i = S.midLift x (fun i ↦ z ≫ (S.rightMesh x).f ≫ S.midProj x i) := by
    change z ≫ (S.rightMesh x).f = _
    simp only [midLift, ← Preadditive.comp_sum, Category.assoc]
    rw [sum_midProj_midInc, Category.comp_id]
  rw [this]
  exact S.midLift_mem x _ hz

end IndSkeleton

end MultiplicativeBasisDeformations
