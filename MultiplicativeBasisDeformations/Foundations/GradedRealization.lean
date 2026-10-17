import MultiplicativeBasisDeformations.Foundations.ARQuiver
import MultiplicativeBasisDeformations.Foundations.PathGrading
import MultiplicativeBasisDeformations.Foundations.LayerExactness

/-!
# Proposition 2.6(3): `k(Γ_A)` is the radical grading of `ind(mod A)`

`graded-category.tex:349–367`. Sending each arrow to its chosen class in
`C_1 = Irr` defines a functor from the path category; it kills each mesh
relation, because the degree-two part of `p ∘ i = 0` is the image of `r_Y`;
the resulting graded functor `k(Γ_A) → gr_J ind(mod A)` is surjective because
the radical layers are generated in degree one, and injective by induction on
the degree, using the exactness of Proposition 2.6(1).

Formally, choose for each arrow `a : x → y` a representative `rep a ∈ J(x, y)`
of the chosen basis vector of `Irr(x, y)`. A path is realized by the composite
of the representatives (`pathMap`), and a morphism of `kQ` by linear extension
(`realize`). A path of length `d` lands in `J^d`, so a homogeneous morphism of
degree `d` has a class in the radical layer `J^d/J^{d+1}`.
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
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- A representative in `J(x, y)` of the basis vector of `Irr(x, y)` indexed by
the arrow `a`. -/
def rep {x y : S.ARVertex} (a : x ⟶ y) : S.label x ⟶ S.label y :=
  (Classical.choose (Submodule.Quotient.mk_surjective _ (b x y a))).1

theorem rep_mem {x y : S.ARVertex} (a : x ⟶ y) : S.rep b a ∈ S.radPow 1 (S.label x) (S.label y) :=
  (Classical.choose (Submodule.Quotient.mk_surjective _ (b x y a))).2

theorem irrClass_rep {x y : S.ARVertex} (a : x ⟶ y) :
    S.irrClass (S.rep b a) (S.rep_mem b a) = b x y a :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ (b x y a))

/-- The realization of a path: the composite of the representatives of its
arrows. -/
def pathMap {x : S.ARVertex} : ∀ {y : S.ARVertex}, Quiver.Path x y → (S.label x ⟶ S.label y)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p a => pathMap p ≫ S.rep b a

@[simp] theorem pathMap_nil {x : S.ARVertex} : S.pathMap b (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ :=
  rfl

@[simp] theorem pathMap_cons {x y z : S.ARVertex} (p : Quiver.Path x y) (a : y ⟶ z) :
    S.pathMap b (p.cons a) = S.pathMap b p ≫ S.rep b a := rfl

theorem pathMap_comp {x y z : S.ARVertex} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    S.pathMap b (p.comp q) = S.pathMap b p ≫ S.pathMap b q := by
  induction q with
  | nil => simp
  | cons q a ih => simp [Quiver.Path.comp_cons, ih, Category.assoc]

theorem pathMap_mem {x y : S.ARVertex} (p : Quiver.Path x y) :
    S.pathMap b p ∈ S.radPow p.length (S.label x) (S.label y) := by
  induction p with
  | nil => exact Submodule.mem_top
  | cons p a ih =>
      rw [pathMap_cons, Quiver.Path.length_cons]
      exact S.comp_mem_radPow ih (S.rep_mem b a)

/-- The realization of a morphism of `kQ`, by linear extension. -/
def realize (x y : S.ARVertex) :
    (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj (k := k) y) →ₗ[k] (S.label x ⟶ S.label y) :=
  (Finsupp.linearCombination k (S.pathMap b (x := x) (y := y))).comp
    (LinearPaths.finsuppEquiv (k := k) x y).toLinearMap

theorem realize_path {x y : S.ARVertex} (p : Quiver.Path x y) :
    S.realize b x y (LinearPaths.path p) = S.pathMap b p := by
  change Finsupp.linearCombination k (S.pathMap b) (Finsupp.single p 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

theorem realize_comp {x y z : S.ARVertex} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y)
    (g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    S.realize b x z (f ≫ g) = S.realize b x y f ≫ S.realize b y z g := by
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, Preadditive.add_comp]
  | hsingle p c =>
      induction g using LinearPaths.induction_on with
      | h0 => simp
      | hadd g₁ g₂ h₁ h₂ =>
          rw [Preadditive.comp_add, map_add, map_add, h₁, h₂, Preadditive.comp_add]
      | hsingle q c' =>
          rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path, map_smul, map_smul,
            map_smul, map_smul, realize_path, realize_path, realize_path, pathMap_comp,
            Linear.smul_comp, Linear.comp_smul]

theorem realize_mem {d : ℕ} {x y : S.ARVertex} {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hf : f ∈ LinearPaths.degreePart (k := k) d x y) :
    S.realize b x y f ∈ S.radPow d (S.label x) (S.label y) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, rfl, rfl⟩ := hg
      rw [realize_path]
      exact S.pathMap_mem b p
  | zero => simp
  | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- In `Irr(x, y)`, every vector is a multiple of the basis vector of the
(unique) arrow. -/
theorem eq_repr_smul_basis {x y : S.ARVertex} (a : x ⟶ y) (v : S.Irr (S.label x) (S.label y)) :
    v = (b x y).repr v a • b x y a := by
  have : Subsingleton (x ⟶ y) := S.hasAtMostOneArrow x y
  conv_lhs => rw [← (b x y).sum_repr v]
  rw [Finset.sum_eq_single a (fun a' _ h ↦ absurd (Subsingleton.elim a' a) h) (by simp)]

/-- A radical map agrees modulo `J²` with the corresponding multiple of the
representative of the arrow. -/
theorem sub_repr_smul_rep_mem {x y : S.ARVertex} (a : x ⟶ y) {f : S.label x ⟶ S.label y}
    (hf : f ∈ S.radPow 1 _ _) :
    f - (b x y).repr (S.irrClass f hf) a • S.rep b a ∈ S.radPow 2 (S.label x) (S.label y) := by
  have h := S.eq_repr_smul_basis b a (S.irrClass f hf)
  rw [← S.irrClass_rep b a] at h
  have hsm : (b x y).repr (S.irrClass f hf) a • S.rep b a ∈ S.radPow 1 _ _ :=
    Submodule.smul_mem _ _ (S.rep_mem b a)
  have h' : S.irrClass f hf = S.irrClass _ hsm := h.trans rfl
  have := (Submodule.Quotient.eq _).1 h'
  exact this

/-- The components of the canonical mesh at a nonprojective vertex compose to
zero: `∑_i α_i β_i = 0`. -/
theorem sum_source_beta (x : S.nonprojectiveVertices) :
    ∑ i, MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent S.tau
        (S.vendorNonprojective x) i ≫ S.beta (S.index x.1) i = 0 := by
  have h := S.sum_midProj_midInc (S.index x.1)
  simp only [MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent, beta,
    MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleComponent, Category.assoc]
  calc ∑ i, (S.tau.tauPlusIso (S.vendorNonprojective x)).inv ≫ (S.rightMesh (S.index x.1)).f ≫
        S.midProj (S.index x.1) i ≫ S.midInc (S.index x.1) i ≫ (S.rightMesh (S.index x.1)).g ≫
          (S.tau.rightTermIso (S.tau.obj (S.index x.1))).hom
      = (S.tau.tauPlusIso (S.vendorNonprojective x)).inv ≫ (S.rightMesh (S.index x.1)).f ≫
          (∑ i, S.midProj (S.index x.1) i ≫ S.midInc (S.index x.1) i) ≫
            (S.rightMesh (S.index x.1)).g ≫ (S.tau.rightTermIso _).hom := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = 0 := by
        rw [h, Category.id_comp]
        simp only [ShortComplex.zero_assoc, zero_comp, comp_zero]

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- Agreement modulo `J²` of two radical factors gives agreement modulo `J³`
of their composites. -/
theorem comp_sub_comp_mem_three {X Y Z : S.Ind} {f f₀ : X ⟶ Y} {g g₀ : Y ⟶ Z}
    (hf : f - f₀ ∈ S.radPow 2 X Y) (hf₀ : f₀ ∈ S.radPow 1 X Y)
    (hg : g - g₀ ∈ S.radPow 2 Y Z) (hg₀ : g₀ ∈ S.radPow 1 Y Z) :
    f ≫ g - f₀ ≫ g₀ ∈ S.radPow 3 X Z := by
  have hg1 : g ∈ S.radPow 1 Y Z := by
    have : g = (g - g₀) + g₀ := by abel
    rw [this]; exact add_mem (S.radPow_succ_le 1 Y Z hg) hg₀
  have e : f ≫ g - f₀ ≫ g₀ = (f - f₀) ≫ g + f₀ ≫ (g - g₀) := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub]; abel
  rw [e]
  exact add_mem (S.comp_mem_radPow hf hg1) (by simpa using S.comp_mem_radPow hf₀ hg)

/-- The component `τx → y` at an occurrence, in `ind(mod A)`. -/
def alphaInd (x : S.nonprojectiveVertices) (y : S.ARVertex)
    (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) :
    S.label (S.arTranslationQuiver.tau x).1 ⟶ S.label y :=
  (S.homEquivFG _ _).symm (S.sourceComponent x i)

/-- The component `y → x` at an occurrence, in `ind(mod A)`. -/
def betaInd (x : S.nonprojectiveVertices) (y : S.ARVertex)
    (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) :
    S.label y ⟶ S.label x.1 :=
  (S.homEquivFG _ _).symm (S.toVendor.occurrenceMap i)

theorem alphaInd_mem (x : S.nonprojectiveVertices) (y : S.ARVertex)
    (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) :
    S.alphaInd x y i ∈ S.radPow 1 _ _ := by
  rw [mem_radPow_one_iff, isRadical_iff, alphaInd, map_homEquivFG_symm]
  exact S.isRadicalMorphism_of_irreducible (S.sourceComponent_isIrreducible x i)

theorem betaInd_mem (x : S.nonprojectiveVertices) (y : S.ARVertex)
    (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) :
    S.betaInd x y i ∈ S.radPow 1 _ _ := by
  rw [mem_radPow_one_iff, isRadical_iff, betaInd, map_homEquivFG_symm]
  exact S.isRadicalMorphism_of_irreducible (S.toVendor.occurrenceMap_isIrreducible i)

/-- One occurrence contributes `u_i v_i (σ a) a` modulo `J³`. -/
theorem occurrence_term_mem (x : S.nonprojectiveVertices) (y : S.ARVertex) (a : y ⟶ x.1)
    (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) :
    S.alphaInd x y i ≫ S.betaInd x y i -
        S.occurrenceCoefficient b x y a i •
          (S.rep b (S.arTranslationQuiver.mate x y a) ≫ S.rep b a) ∈
      S.radPow 3 _ _ := by
  have hα := S.sub_repr_smul_rep_mem b (S.arTranslationQuiver.mate x y a) (S.alphaInd_mem x y i)
  have hβ := S.sub_repr_smul_rep_mem b a (S.betaInd_mem x y i)
  have h := S.comp_sub_comp_mem_three hα (Submodule.smul_mem _ _ (S.rep_mem b _)) hβ
    (Submodule.smul_mem _ _ (S.rep_mem b _))
  have e : ((b (S.arTranslationQuiver.tau x).1 y).repr (S.irrClass (S.alphaInd x y i) (S.alphaInd_mem x y i))
        (S.arTranslationQuiver.mate x y a) • S.rep b (S.arTranslationQuiver.mate x y a)) ≫
      ((b y x.1).repr (S.irrClass (S.betaInd x y i) (S.betaInd_mem x y i)) a • S.rep b a) =
      S.occurrenceCoefficient b x y a i •
        (S.rep b (S.arTranslationQuiver.mate x y a) ≫ S.rep b a) := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul]
    rfl
  rw [e] at h
  exact h

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

theorem sourceComponent_comp_occurrenceMap (x : S.nonprojectiveVertices) {y : Fin S.n}
    (i : S.toVendor.Occurrence y (S.index x.1)) :
    S.sourceComponent x i ≫ S.toVendor.occurrenceMap i =
      MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent S.tau
        (S.vendorNonprojective x) i.1 ≫ S.beta (S.index x.1) i.1 := by
  obtain ⟨j, rfl⟩ := i
  simp [sourceComponent, MBDVendor.Magnitude.RightModule.FiniteIndecomposableSkeleton.occurrenceMap]

theorem alphaInd_comp_betaInd (x : S.nonprojectiveVertices) (y : S.ARVertex)
    (i : S.toVendor.Occurrence (S.index y) (S.index x.1)) :
    S.alphaInd x y i ≫ S.betaInd x y i =
      (S.homEquivFG (S.ind (S.index (S.arTranslationQuiver.tau x).1)) (S.ind (S.index x.1))).symm
        (MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent S.tau
          (S.vendorNonprojective x) i.1 ≫ S.beta (S.index x.1) i.1) := by
  apply S.toFG.map_injective
  calc S.toFG.map (S.alphaInd x y i ≫ S.betaInd x y i)
      = S.toFG.map (S.alphaInd x y i) ≫ S.toFG.map (S.betaInd x y i) := Functor.map_comp _ _ _
    _ = S.sourceComponent x i ≫ S.toVendor.occurrenceMap i :=
        congrArg₂ (· ≫ ·) (S.map_homEquivFG_symm _) (S.map_homEquivFG_symm _)
    _ = _ := S.sourceComponent_comp_occurrenceMap x i
    _ = _ := (S.map_homEquivFG_symm _).symm

/-- The sum of the occurrence composites at a vertex vanishes. -/
theorem sum_alphaInd_betaInd (x : S.nonprojectiveVertices) :
    ∑ y : S.ARVertex, ∑ i : S.toVendor.Occurrence (S.index y) (S.index x.1),
      S.alphaInd x y i ≫ S.betaInd x y i = 0 := by
  let F : Fin (S.arity (S.index x.1)) → (S.fg (S.index (S.arTranslationQuiver.tau x).1) ⟶
      S.fg (S.index x.1)) := fun j ↦
    MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent S.tau
      (S.vendorNonprojective x) j ≫ S.beta (S.index x.1) j
  have key : ∑ y : Fin S.n, ∑ i : {j // S.midLabel (S.index x.1) j = y}, F i.1 = 0 := by
    rw [Fintype.sum_fiberwise (fun j ↦ S.midLabel (S.index x.1) j) F]
    exact S.sum_source_beta x
  calc ∑ y : S.ARVertex, ∑ i : S.toVendor.Occurrence (S.index y) (S.index x.1),
        S.alphaInd x y i ≫ S.betaInd x y i
      = ∑ y : S.ARVertex, ∑ i : S.toVendor.Occurrence (S.index y) (S.index x.1),
          (S.homEquivFG (S.ind (S.index (S.arTranslationQuiver.tau x).1))
            (S.ind (S.index x.1))).symm (F i.1) := by
        simp only [alphaInd_comp_betaInd]; rfl
    _ = (S.homEquivFG (S.ind (S.index (S.arTranslationQuiver.tau x).1))
            (S.ind (S.index x.1))).symm
          (∑ y : Fin S.n, ∑ i : {j // S.midLabel (S.index x.1) j = y}, F i.1) := by
        simp only [map_sum]; rfl
    _ = 0 := by rw [key, map_zero]

/-- The number of arrows `y → x` equals the number of occurrences of `y` in
the mesh ending at `x`. -/
theorem card_arrows_eq_card_occurrence (x y : S.ARVertex) :
    Fintype.card (y ⟶ x) = Fintype.card (S.toVendor.Occurrence (S.index y) (S.index x)) := by
  change Fintype.card (Fin (Module.finrank k (S.Irr (S.ind (S.index y)) (S.ind (S.index x))))) = _
  rw [Fintype.card_fin]
  exact (S.finrank_irr_eq_arrowMultiplicity (S.index y) (S.index x)).trans
    (S.toVendor.arrowMultiplicity_eq_card_occurrence _ _)

/-- **The mesh relations are realized in `J³`**: the degree-two part of
`p ∘ i = 0` is the image of `r_x`. -/
theorem realize_meshRelation_mem (x : S.nonprojectiveVertices) :
    S.realize b _ _ (meshRelation (S.arCoefficients b) x) ∈
      S.radPow 3 (S.label (S.arTranslationQuiver.tau x).1) (S.label x.1) := by
  classical
  have hreal : S.realize b _ _ (meshRelation (S.arCoefficients b) x) =
      ∑ a : Σ y : S.ARVertex, y ⟶ x.1, S.arCoefficient b x a.1 a.2 •
        (S.rep b (S.arTranslationQuiver.mate x a.1 a.2) ≫ S.rep b a.2) := by
    simp only [meshRelation, map_sum, map_smul, realize_path, pathMap_comp]
    rfl
  -- the occurrence composites, summed over arrows
  let T : S.label (S.arTranslationQuiver.tau x).1 ⟶ S.label x.1 :=
    ∑ a : Σ y : S.ARVertex, y ⟶ x.1,
      ∑ i : S.toVendor.Occurrence (S.index a.1) (S.index x.1),
        S.alphaInd x a.1 i ≫ S.betaInd x a.1 i
  have hT : T = 0 := by
    have e : T = ∑ y : S.ARVertex, Fintype.card (y ⟶ x.1) •
        ∑ i : S.toVendor.Occurrence (S.index y) (S.index x.1),
          S.alphaInd x y i ≫ S.betaInd x y i := by
      simp only [T, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      exact (Finset.sum_const (s := (Finset.univ : Finset (y ⟶ x.1)))
        (∑ i : S.toVendor.Occurrence (S.index y) (S.index x.1),
          S.alphaInd x y i ≫ S.betaInd x y i)).trans (by rw [Finset.card_univ])
    rw [e, ← S.sum_alphaInd_betaInd x]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hle : Fintype.card (y ⟶ x.1) ≤ 1 := by
      change Fintype.card (Fin _) ≤ 1
      rw [Fintype.card_fin]; exact S.finrank_irr_le_one _ _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
    · have hocc : IsEmpty (S.toVendor.Occurrence (S.index y) (S.index x.1)) := by
        rw [← Fintype.card_eq_zero_iff, ← card_arrows_eq_card_occurrence]; exact h0
      simp [h0]
    · rw [h1, one_smul]
  have hdiff : S.realize b _ _ (meshRelation (S.arCoefficients b) x) - T ∈ S.radPow 3 _ _ := by
    rw [hreal]
    simp only [T, arCoefficient, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.sum_mem _ fun i _ ↦ ?_
    have := S.occurrence_term_mem b x a.1 a.2 i
    rw [← neg_sub]
    exact neg_mem this
  rw [hT, sub_zero] at hdiff
  exact hdiff

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The degree-`d` component of an element of the mesh ideal is realized in
`J^{d+1}`. -/
theorem realize_proj_mem_of_mem_ideal (d : ℕ) {x y : S.ARVertex}
    {g : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hg : g ∈ (MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal.linearSpan k (meshRelations (S.arCoefficients b))).hom
      (LinearPaths.obj x) (LinearPaths.obj y)) :
    S.realize b x y (LinearPaths.proj d x y g) ∈ S.radPow (d + 1) (S.label x) (S.label y) := by
  change g ∈ MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal.generatedHomSubmodule k _ (LinearPaths.obj x) (LinearPaths.obj y) at hg
  induction hg using Submodule.span_induction with
  | mem h hh =>
      obtain ⟨P, R, r, hr, a, b', rfl⟩ := hh
      obtain ⟨P', rfl⟩ : ∃ P' : S.ARVertex, LinearPaths.obj (k := k) P' = P := ⟨P, rfl⟩
      obtain ⟨R', rfl⟩ : ∃ R' : S.ARVertex, LinearPaths.obj (k := k) R' = R := ⟨R, rfl⟩
      obtain ⟨x₀, hX, hY, rfl⟩ := hr
      change P' = (S.arTranslationQuiver.tau x₀).1 at hX
      change R' = x₀.1 at hY
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      have hr3 := S.realize_meshRelation_mem b x₀
      induction a using LinearPaths.induction_on with
      | h0 => simp
      | hadd a₁ a₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add]; exact add_mem h₁ h₂
      | hsingle p c =>
          induction b' using LinearPaths.induction_on with
          | h0 => simp
          | hadd b₁ b₂ h₁ h₂ =>
              rw [Preadditive.comp_add, Preadditive.comp_add, map_add, map_add]
              exact add_mem h₁ h₂
          | hsingle q c' =>
              have hdeg : LinearPaths.path (k := k) p ≫ meshRelation (S.arCoefficients b) x₀ ≫
                  LinearPaths.path q ∈
                  LinearPaths.degreePart (k := k) (p.length + 2 + q.length) x y := by
                have h2 : meshRelation (S.arCoefficients b) x₀ ∈
                    LinearPaths.degreePart (k := k) 2 _ _ := by
                  unfold meshRelation
                  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ ?_
                  have := LinearPaths.path_mem_degreePart (k := k)
                    ((S.arTranslationQuiver.mate x₀ a.1 a.2).toPath.comp a.2.toPath)
                  simpa using this
                simpa [Category.assoc] using LinearPaths.comp_mem_degreePart
                  (LinearPaths.comp_mem_degreePart (LinearPaths.path_mem_degreePart p) h2)
                  (LinearPaths.path_mem_degreePart q)
              have e : (c • LinearPaths.path (k := k) p) ≫ meshRelation (S.arCoefficients b) x₀ ≫
                  (c' • LinearPaths.path q) = (c * c') • (LinearPaths.path (k := k) p ≫
                    meshRelation (S.arCoefficients b) x₀ ≫ LinearPaths.path q) := by
                simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
              rw [e, map_smul, LinearPaths.proj_of_mem hdeg]
              split_ifs with hd
              · rw [map_smul]
                apply Submodule.smul_mem
                rw [S.realize_comp, S.realize_comp, realize_path, realize_path]
                have := S.comp_mem_radPow (S.comp_mem_radPow (S.pathMap_mem b p) hr3)
                  (S.pathMap_mem b q)
                rw [show d + 1 = p.length + 3 + q.length by omega]
                exact this
              · simp
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, map_add]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- Maps between distinct (hence nonisomorphic) indecomposables are radical. -/
theorem isRadical_of_ne {x y : Fin S.n} (hxy : x ≠ y) (f : S.ind x ⟶ S.ind y) : S.IsRadical f := by
  rw [isRadical_iff]
  apply (S.tau.toFiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
    (x := x) (S.toFG.map f)).2
  intro hsplit
  have : IsIso (S.toFG.map f) :=
    MBDVendor.Magnitude.FiniteTauMatrix.isIso_of_isSplitMono_obj_obj
      S.tau.toFiniteRightTauCategoryData (p := x) (q := y) (S.toFG.map f)
  apply hxy
  apply S.pairwise
  exact ⟨(forget₂ (ModCat A) (RightModuleCat A)).mapIso (asIso (S.toFG.map f))⟩

/-- An endomorphism of an indecomposable is a scalar plus a radical map. -/
theorem exists_sub_smul_id_isRadical (x : Fin S.n) (f : S.ind x ⟶ S.ind x) :
    ∃ c : k, S.IsRadical (f - c • 𝟙 _) := by
  let T := S.tau.toFiniteRightTauCategoryData
  let ρ := MBDVendor.Magnitude.FiniteTauMatrix.algebraicallyClosedResidueMap (k := k) T x
  have hker : ∀ g : T.obj x ⟶ T.obj x, ρ g = 0 ↔ IsRadicalMorphism g := by
    intro g
    have h := congrArg (g ∈ ·)
      (MBDVendor.Magnitude.FiniteTauMatrix.radicalSubmodule_eq_ker_algebraicallyClosedResidueMap
        (k := k) T x)
    simp only [LinearMap.mem_ker] at h
    exact h.symm.to_iff.trans Iff.rfl
  have h1 : ρ (𝟙 _) ≠ 0 := by
    rw [Ne, hker]
    intro hrad
    have h := hrad (𝟙 _)
    simp only [Category.comp_id, sub_self] at h
    have hid : 𝟙 (T.obj x) = 0 := by
      rw [← IsIso.inv_hom_id (0 : T.obj x ⟶ T.obj x), comp_zero]
    have hz : IsZero (T.obj x) := (IsZero.iff_id_eq_zero _).2 hid
    exact (S.isFiniteIndecomposable x).2.1
      (Functor.map_isZero (forget₂ (ModCat A) (RightModuleCat A)) hz)
  refine ⟨ρ (S.toFG.map f) / ρ (𝟙 _), ?_⟩
  rw [isRadical_iff, ← hker]
  let F : T.obj x ⟶ T.obj x := S.toFG.map f
  have e : S.toFG.map (f - (ρ (S.toFG.map f) / ρ (𝟙 _)) • 𝟙 (S.ind x)) =
      (F - (ρ F / ρ (𝟙 (T.obj x))) • 𝟙 (T.obj x) : T.obj x ⟶ T.obj x) := by
    rw [Functor.map_sub, Functor.map_smul, CategoryTheory.Functor.map_id]; rfl
  rw [e, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ h1, sub_self]

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Surjectivity** in Proposition 2.6(3): the radical layers are generated in
degree one. Every `f ∈ J^d` agrees modulo `J^{d+1}` with the realization of a
homogeneous morphism of degree `d` of the path category. -/
theorem exists_realize_sub_mem (d : ℕ) : ∀ {x y : S.ARVertex} (f : S.label x ⟶ S.label y),
    f ∈ S.radPow d _ _ → ∃ F ∈ LinearPaths.degreePart (k := k) d x y,
      f - S.realize b x y F ∈ S.radPow (d + 1) _ _ := by
  induction d with
  | zero =>
      intro x y f _
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨c, hc⟩ := S.exists_sub_smul_id_isRadical x f
        have hnil : LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path x x) ∈
            LinearPaths.degreePart (k := k) 0 x x :=
          LinearPaths.path_mem_degreePart (k := k) (Quiver.Path.nil : Quiver.Path x x)
        refine ⟨c • LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path x x),
          Submodule.smul_mem _ _ hnil, ?_⟩
        rw [map_smul, realize_path, pathMap_nil, Nat.zero_add]
        exact (S.mem_radPow_one_iff (f - c • 𝟙 (S.label x))).2 hc
      · refine ⟨0, zero_mem _, ?_⟩
        rw [map_zero, sub_zero, Nat.zero_add]
        exact (S.mem_radPow_one_iff f).2 (S.isRadical_of_ne hxy f)
  | succ d ih =>
      intro x y f hf
      change f ∈ Submodule.span k _ at hf
      induction hf using Submodule.span_induction with
      | mem h hh =>
          obtain ⟨Z, h₁, g, hh₁, hg, rfl⟩ := hh
          obtain ⟨z, rfl⟩ : ∃ z : S.ARVertex, S.label z = Z := ⟨Z, rfl⟩
          obtain ⟨G, hG, hgG⟩ := ih g hg
          have hh₁' : h₁ ∈ S.radPow 1 _ _ := (S.mem_radPow_one_iff h₁).2 hh₁
          by_cases harr : 0 < Module.finrank k (S.Irr (S.label x) (S.label z))
          · let a : x ⟶ z := ⟨0, harr⟩
            let c := (b x z).repr (S.irrClass h₁ hh₁') a
            refine ⟨(c • LinearPaths.path a.toPath) ≫ G, ?_, ?_⟩
            · have := LinearPaths.comp_mem_degreePart
                (Submodule.smul_mem _ c (LinearPaths.path_mem_degreePart (k := k) a.toPath)) hG
              simpa [add_comm] using this
            · rw [S.realize_comp, map_smul, realize_path]
              have e : h₁ ≫ g - (c • S.pathMap b a.toPath) ≫ S.realize b z y G =
                  (h₁ - c • S.rep b a) ≫ g + (c • S.rep b a) ≫ (g - S.realize b z y G) := by
                simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
                  Quiver.Hom.toPath, pathMap_cons, pathMap_nil, Category.id_comp]
                abel
              rw [e]
              refine add_mem ?_ ?_
              · have := S.comp_mem_radPow (S.sub_repr_smul_rep_mem b a hh₁') hg
                rwa [show 2 + d = d + 1 + 1 by omega] at this
              · have := S.comp_mem_radPow (Submodule.smul_mem _ c (S.rep_mem b a)) hgG
                rwa [show 1 + (d + 1) = d + 1 + 1 by omega] at this
          · refine ⟨0, zero_mem _, ?_⟩
            rw [map_zero, sub_zero]
            have hirr : S.irrClass h₁ hh₁' = 0 := by
              have : Module.finrank k (S.Irr (S.label x) (S.label z)) = 0 := by omega
              have : Subsingleton (S.Irr (S.label x) (S.label z)) :=
                (Module.finrank_eq_zero_iff_of_free k _).1 this
              exact Subsingleton.elim _ _
            have h2 : h₁ ∈ S.radPow 2 _ _ :=
              (Submodule.Quotient.mk_eq_zero
                ((S.radPow 2 _ _).comap (S.radPow 1 _ _).subtype)).1 hirr
            have := S.comp_mem_radPow h2 hg
            rwa [show 2 + d = d + 1 + 1 by omega] at this
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add f₁ f₂ _ _ h₁ h₂ =>
          obtain ⟨F₁, hF₁, e₁⟩ := h₁
          obtain ⟨F₂, hF₂, e₂⟩ := h₂
          refine ⟨F₁ + F₂, add_mem hF₁ hF₂, ?_⟩
          rw [map_add]
          have : f₁ + f₂ - (S.realize b x y F₁ + S.realize b x y F₂) =
              (f₁ - S.realize b x y F₁) + (f₂ - S.realize b x y F₂) := by abel
          rw [this]; exact add_mem e₁ e₂
      | smul c f₁ _ h₁ =>
          obtain ⟨F₁, hF₁, e₁⟩ := h₁
          refine ⟨c • F₁, Submodule.smul_mem _ c hF₁, ?_⟩
          rw [map_smul, ← smul_sub]
          exact Submodule.smul_mem _ c e₁

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- `dim Irr(x, y)` is the number of occurrences of `x` in the middle term of the
mesh ending at `y`. -/
theorem finrank_irr_eq_card_occurrence (x y : Fin S.n) :
    Module.finrank k (S.Irr (S.ind x) (S.ind y)) = Fintype.card (S.toVendor.Occurrence x y) :=
  (S.finrank_irr_eq_arrowMultiplicity x y).trans
    (S.toVendor.arrowMultiplicity_eq_card_occurrence x y)

/-- The arrow `E_i → Y` given by a summand `i` of the middle term of the mesh
ending at `Y`. -/
def occArrow (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) :
    (S.vertex (S.midLabel (S.index Y) i)) ⟶ Y :=
  ⟨0, by
    have h : 0 < Fintype.card (S.toVendor.Occurrence (S.midLabel (S.index Y) i) (S.index Y)) :=
      Fintype.card_pos_iff.2 ⟨⟨i, rfl⟩⟩
    rw [← S.finrank_irr_eq_card_occurrence] at h
    exact h⟩

/-- The summands of the middle term at `Y` correspond bijectively to the arrows
ending at `Y`. -/
def occEquiv (Y : S.ARVertex) : Fin (S.arity (S.index Y)) ≃ (Σ X : S.ARVertex, X ⟶ Y) :=
  Equiv.ofBijective (fun i ↦ ⟨S.midLabel (S.index Y) i, S.occArrow Y i⟩) (by
    constructor
    · intro i j hij
      have hlab : S.midLabel (S.index Y) i = S.midLabel (S.index Y) j := congrArg Sigma.fst hij
      have hle : Fintype.card (S.toVendor.Occurrence (S.midLabel (S.index Y) i) (S.index Y)) ≤ 1 := by
        rw [← S.finrank_irr_eq_card_occurrence]
        exact S.finrank_irr_le_one _ _
      have := Fintype.card_le_one_iff.1 hle ⟨i, rfl⟩ ⟨j, hlab.symm⟩
      exact congrArg Subtype.val this
    · rintro ⟨X, a⟩
      have hpos : 0 < Fintype.card (S.toVendor.Occurrence (S.index X) (S.index Y)) := by
        rw [← S.card_arrows_eq_card_occurrence]
        exact Fintype.card_pos_iff.2 ⟨a⟩
      obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 hpos
      refine ⟨i, ?_⟩
      have hX : (S.vertex (S.midLabel (S.index Y) i)) = X := hi
      subst hX
      have hs : Subsingleton ((S.vertex (S.midLabel (S.index Y) i)) ⟶ Y) :=
        S.hasAtMostOneArrow _ Y
      exact Sigma.ext rfl (heq_of_eq (hs.elim _ _)))

@[simp] theorem occEquiv_apply_fst (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) :
    (S.occEquiv Y i).1 = S.midLabel (S.index Y) i := rfl

/-- The component `β_i` of the right almost split map, in `ind(mod A)`. -/
def betaI (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) :
    S.label (S.vertex (S.midLabel (S.index Y) i)) ⟶ S.label Y :=
  (S.homEquivFG _ _).symm (S.beta (S.index Y) i)

theorem betaI_mem (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) :
    S.betaI Y i ∈ S.radPow 1 _ _ := by
  rw [mem_radPow_one_iff, isRadical_iff, betaI, map_homEquivFG_symm]
  exact S.isRadicalMorphism_of_irreducible
    (MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleComponent_isIrreducible S.tau _ i)

/-- The coordinate `v_i` of `β_i` in the arrow basis; it is nonzero. -/
def vCoeff (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) : k :=
  (b _ Y).repr (S.irrClass (S.betaI Y i) (S.betaI_mem Y i)) (S.occArrow Y i)

theorem vCoeff_ne_zero (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) : S.vCoeff b Y i ≠ 0 := by
  have := S.hasAtMostOneArrow (S.vertex (S.midLabel (S.index Y) i)) Y
  apply basis_repr_ne_zero
  exact S.irrClassFG_ne_zero
    (MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleComponent_isIrreducible S.tau _ i)

theorem betaI_sub_mem (Y : S.ARVertex) (i : Fin (S.arity (S.index Y))) :
    S.betaI Y i - S.vCoeff b Y i • S.rep b (S.occArrow Y i) ∈ S.radPow 2 _ _ :=
  S.sub_repr_smul_rep_mem b (S.occArrow Y i) (S.betaI_mem Y i)

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The component `α_i : τY → E_i` of the first map, in `ind(mod A)`. -/
def alphaI (y : S.nonprojectiveVertices) (i : Fin (S.arity (S.index y.1))) :
    S.label (S.arTranslationQuiver.tau y).1 ⟶ S.label (S.vertex (S.midLabel (S.index y.1) i)) :=
  S.alphaInd y (S.vertex (S.midLabel (S.index y.1) i)) ⟨i, rfl⟩

theorem alphaI_mem (y : S.nonprojectiveVertices) (i : Fin (S.arity (S.index y.1))) :
    S.alphaI y i ∈ S.radPow 1 _ _ :=
  S.alphaInd_mem y _ _

/-- The coordinate `u_i` of `α_i` in the arrow basis. -/
def uCoeff (y : S.nonprojectiveVertices) (i : Fin (S.arity (S.index y.1))) : k :=
  (b _ _).repr (S.irrClass (S.alphaI y i) (S.alphaI_mem y i))
    (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i))

theorem alphaI_sub_mem (y : S.nonprojectiveVertices) (i : Fin (S.arity (S.index y.1))) :
    S.alphaI y i - S.uCoeff b y i • S.rep b (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)) ∈
      S.radPow 2 _ _ :=
  S.sub_repr_smul_rep_mem b _ (S.alphaI_mem y i)

/-- The mesh coefficient of the arrow of the summand `i` is `u_i v_i`. -/
theorem arCoefficients_occArrow (y : S.nonprojectiveVertices) (i : Fin (S.arity (S.index y.1))) :
    ((S.arCoefficients b y _ (S.occArrow y.1 i) : kˣ) : k) = S.uCoeff b y i * S.vCoeff b y.1 i := by
  change S.arCoefficient b y _ (S.occArrow y.1 i) = _
  unfold arCoefficient
  have hle : Fintype.card (S.toVendor.Occurrence (S.midLabel (S.index y.1) i) (S.index y.1)) ≤ 1 := by
    rw [← S.finrank_irr_eq_card_occurrence]
    exact S.finrank_irr_le_one _ _
  refine (Fintype.sum_eq_single (⟨i, rfl⟩ : S.toVendor.Occurrence (S.midLabel (S.index y.1) i)
    (S.index y.1)) (fun j hj ↦ absurd (Fintype.card_le_one_iff.1 hle _ _) hj)).trans ?_
  unfold occurrenceCoefficient uCoeff vCoeff
  congr 2

/-- At a projective vertex the first term of the mesh is zero. -/
theorem isZero_rightMesh_X₁_of_not_mem (Y : S.ARVertex) (hY : Y ∉ S.nonprojectiveVertices) :
    IsZero (S.rightMesh (S.index Y)).X₁ := by
  by_contra h
  apply hY
  exact (S.toVendor.canonicalRightNonzeroEquivNonprojective ⟨S.index Y, h⟩).2

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The mesh ideal of `k(Γ_A)` in the linear path category. -/
abbrev meshIdeal : MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal (LinearPaths k S.ARVertex) :=
  MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal.linearSpan k
    (meshRelations (S.arCoefficients b))

/-- The identity of an indecomposable is not radical. -/
theorem not_isRadical_id (x : S.Ind) : ¬ S.IsRadical (𝟙 x) := by
  intro h
  have h' := h (𝟙 _)
  simp only [Category.comp_id, sub_self] at h'
  have hid : 𝟙 x = 0 := by rw [← IsIso.inv_hom_id (0 : x ⟶ x), comp_zero]
  have hz : IsZero (S.incl.obj x) := by
    rw [IsZero.iff_id_eq_zero, ← S.incl.map_id, hid, Functor.map_zero]
  exact (S.isFiniteIndecomposable x).2.1 hz

theorem realize_arrow {x y : S.ARVertex} (a : x ⟶ y) :
    S.realize b x y (LinearPaths.arrow a) = S.rep b a := by
  rw [LinearPaths.arrow, realize_path]
  simp [Quiver.Hom.toPath]

/-- Reindexing the last-arrow decomposition by the summands of the mesh. -/
theorem sum_lastArrow_eq {W Y : S.ARVertex} {M : Type*} [AddCommMonoid M]
    (Φ : (Σ X : S.ARVertex, X ⟶ Y) → M) :
    ∑ a, Φ a = ∑ i, Φ ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ :=
  (Equiv.sum_comp (S.occEquiv Y) Φ).symm

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem inv_smul_comp_sub_aux {X Y Z : S.Ind} (g : X ⟶ Y) (β r : Y ⟶ Z) {v : k} (hv : v ≠ 0) :
    (v⁻¹ • g) ≫ β - g ≫ r = (v⁻¹ • g) ≫ (β - v • r) := by
  rw [Preadditive.comp_sub, Linear.comp_smul, Linear.smul_comp, Linear.smul_comp, smul_smul,
    mul_inv_cancel₀ hv, one_smul]

/-- The estimate `∑_i v_i⁻¹ G_i β_i ∈ J^{N+2}` used in the injectivity step. -/
theorem sum_inv_v_betaI_mem {N : ℕ} {W Y : S.ARVertex}
    (G : ∀ a : Σ X : S.ARVertex, X ⟶ Y, LinearPaths.obj (k := k) W ⟶ LinearPaths.obj a.1)
    (hG : ∀ a, G a ∈ LinearPaths.degreePart (k := k) N W a.1)
    (hF : S.realize b W Y (∑ a, G a ≫ LinearPaths.arrow a.2) ∈ S.radPow (N + 2) _ _) :
    ∑ i, ((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)) ≫ S.betaI Y i ∈
      S.radPow (N + 2) (S.label W) (S.label Y) := by
  have hreal : S.realize b W Y (∑ a, G a ≫ LinearPaths.arrow a.2) =
      ∑ i, S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩) ≫ S.rep b (S.occArrow Y i) := by
    rw [map_sum, S.sum_lastArrow_eq (W := W)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [S.realize_comp, realize_arrow]
  rw [hreal] at hF
  have hdiff : ∑ i, ((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)) ≫ S.betaI Y i -
      ∑ i, S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩) ≫ S.rep b (S.occArrow Y i) =
      ∑ i, ((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)) ≫
        (S.betaI Y i - S.vCoeff b Y i • S.rep b (S.occArrow Y i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      S.inv_smul_comp_sub_aux _ _ _ (S.vCoeff_ne_zero b Y i)
  have hmem : ∑ i, ((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)) ≫
      (S.betaI Y i - S.vCoeff b Y i • S.rep b (S.occArrow Y i)) ∈ S.radPow (N + 2) _ _ :=
    Submodule.sum_mem _ fun i _ ↦ S.comp_mem_radPow
      (Submodule.smul_mem _ _ (S.realize_mem b (hG _))) (S.betaI_sub_mem b Y i)
  have := add_mem hmem hF
  rwa [← hdiff, sub_add_cancel] at this

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

theorem alphaI_map (y : S.nonprojectiveVertices) (i : Fin (S.arity (S.index y.1))) :
    S.toFG.map (S.alphaI y i) = (S.tau.tauPlusIso (S.vendorNonprojective y)).inv ≫
      (S.rightMesh (S.index y.1)).f ≫ S.midProj (S.index y.1) i := by
  rw [alphaI, alphaInd, map_homEquivFG_symm]
  simp [sourceComponent, MBDVendor.Magnitude.FiniteTauMatrix.rightMiddleSourceComponent]
  rfl

set_option maxHeartbeats 400000 in
/-- The corrected component `G_i - c_i H (σ a_i)` is realized in `J^{m+2}`. -/
theorem realize_corrected_mem {m : ℕ} {W : S.ARVertex} (y : S.nonprojectiveVertices)
    (i : Fin (S.arity (S.index y.1)))
    (Gi : LinearPaths.obj (k := k) W ⟶ LinearPaths.obj (S.vertex (S.midLabel (S.index y.1) i)))
    (H : LinearPaths.obj (k := k) W ⟶ LinearPaths.obj (S.arTranslationQuiver.tau y).1)
    (hH : H ∈ LinearPaths.degreePart (k := k) m W _)
    (hInd : S.label W ⟶ S.label (S.arTranslationQuiver.tau y).1)
    (hHdiff : hInd - S.realize b _ _ H ∈ S.radPow (m + 1) _ _)
    (h1 : (S.vCoeff b y.1 i)⁻¹ • S.realize b W _ Gi - hInd ≫ S.alphaI y i ∈
      S.radPow (m + 2) _ _) :
    S.realize b W _ (Gi - ((S.arCoefficients b y _ (S.occArrow y.1 i) : kˣ) : k) •
        (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)))) ∈
      S.radPow (m + 2) _ _ := by
  rw [map_sub, map_smul, S.realize_comp, realize_arrow, S.arCoefficients_occArrow]
  set σa := S.arTranslationQuiver.mate y _ (S.occArrow y.1 i)
  set v := S.vCoeff b y.1 i
  set u := S.uCoeff b y i
  set g := S.realize b W _ Gi
  have hv := S.vCoeff_ne_zero b y.1 i
  have h2 : hInd ≫ S.alphaI y i - S.realize b _ _ H ≫ (u • S.rep b σa) ∈
      S.radPow (m + 2) _ _ := by
    have e : hInd ≫ S.alphaI y i - S.realize b _ _ H ≫ (u • S.rep b σa) =
        (hInd - S.realize b _ _ H) ≫ S.alphaI y i +
          S.realize b _ _ H ≫ (S.alphaI y i - u • S.rep b σa) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub]; abel
    rw [e]
    exact add_mem (S.comp_mem_radPow (m := m + 1) (n := 1) hHdiff (S.alphaI_mem y i))
      (S.comp_mem_radPow (m := m) (n := 2) (S.realize_mem b hH) (S.alphaI_sub_mem b y i))
  have e : g - (u * v) • (S.realize b _ _ H ≫ S.rep b σa) =
      v • ((v⁻¹ • g - hInd ≫ S.alphaI y i) +
        (hInd ≫ S.alphaI y i - S.realize b _ _ H ≫ (u • S.rep b σa))) := by
    rw [sub_add_sub_cancel, smul_sub, smul_smul, mul_inv_cancel₀ hv, one_smul,
      Linear.comp_smul, smul_smul, mul_comm v u]
  rw [e]
  exact Submodule.smul_mem _ _ (add_mem h1 h2)

theorem lastArrow_sum_mem_of {W Y : S.ARVertex}
    (G : ∀ a : Σ X : S.ARVertex, X ⟶ Y, LinearPaths.obj (k := k) W ⟶ LinearPaths.obj a.1)
    (hG : ∀ i, G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ ∈ (S.meshIdeal b).hom _ _) :
    ∑ a, G a ≫ LinearPaths.arrow a.2 ∈ (S.meshIdeal b).hom _ _ := by
  rw [S.sum_lastArrow_eq (W := W)]
  exact sum_mem fun i _ ↦ (S.meshIdeal b).postcomp _ (hG i)

set_option maxHeartbeats 800000 in
/-- **Injectivity** in Proposition 2.6(3): a homogeneous morphism of degree `N`
of the path category whose realization lies in `J^{N+1}` belongs to the mesh
ideal. -/
theorem mem_meshIdeal_of_realize_mem (N : ℕ) : ∀ {W Y : S.ARVertex}
    {F : LinearPaths.obj (k := k) W ⟶ LinearPaths.obj Y},
    F ∈ LinearPaths.degreePart (k := k) N W Y → S.realize b W Y F ∈ S.radPow (N + 1) _ _ →
    F ∈ (S.meshIdeal b).hom _ _ := by
  induction N with
  | zero =>
      intro W Y F hF hreal
      by_cases hWY : W = Y
      · subst hWY
        rw [LinearPaths.degreePart_zero_self hF] at hreal ⊢
        by_cases hc : LinearPaths.toFinsupp F Quiver.Path.nil = 0
        · rw [hc, zero_smul]; exact zero_mem _
        · exfalso
          rw [map_smul, realize_path, pathMap_nil] at hreal
          have h1 : 𝟙 (S.label W) ∈ S.radPow 1 _ _ := by
            have := Submodule.smul_mem _ (LinearPaths.toFinsupp F Quiver.Path.nil)⁻¹ hreal
            rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
          exact S.not_isRadical_id _ ((S.mem_radPow_one_iff _).1 h1)
      · rw [LinearPaths.degreePart_zero_of_ne hWY hF]; exact zero_mem _
  | succ N ih =>
      intro W Y F hF hreal
      obtain ⟨G, hG, rfl⟩ := LinearPaths.exists_lastArrow_decomposition hF
      have hsumInd := S.sum_inv_v_betaI_mem b G hG hreal
      -- the components `w_i` in `mod A`
      let w : ∀ i, S.fg (S.index W) ⟶ S.fg (S.midLabel (S.index Y) i) := fun i ↦
        S.toFG.map ((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩))
      have hw : ∀ i, w i ∈ (StrictLayers.Ipow N : HomIdeal (ModCat A)).hom _ _ := by
        intro i
        have h0 := S.realize_mem b (hG ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)
        exact (S.mem_radPow_iff N _).1 (Submodule.smul_mem _ _ h0)
      have hsum : ∑ i, w i ≫ S.beta (S.index Y) i ∈
          (StrictLayers.Ipow (N + 2) : HomIdeal (ModCat A)).hom _ _ := by
        have e : ∀ i, w i ≫ S.beta (S.index Y) i = S.toFG.map
            (((S.vCoeff b Y i)⁻¹ • S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩)) ≫ S.betaI Y i) := by
          intro i
          rw [Functor.map_comp]
          congr 1
          exact (S.map_homEquivFG_symm _).symm
        rw [Finset.sum_congr rfl (fun i _ ↦ e i), ← Functor.map_sum]
        exact (S.mem_radPow_iff (N + 2) _).1 hsumInd
      -- from `w_i ∈ J^{N+1}` to `G_i` in the ideal, by the induction hypothesis
      have hstep : ∀ i, w i ∈ (StrictLayers.Ipow (N + 1) : HomIdeal (ModCat A)).hom _ _ →
          G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ ∈ (S.meshIdeal b).hom _ _ := by
        intro i hi
        apply ih (hG _)
        have h1 := (S.mem_radPow_iff (N + 1) _).2 hi
        have := Submodule.smul_mem _ (S.vCoeff b Y i) h1
        rwa [smul_smul, mul_inv_cancel₀ (S.vCoeff_ne_zero b Y i), one_smul] at this
      cases N with
      | zero =>
          apply S.lastArrow_sum_mem_of b G
          intro i
          exact hstep i (S.layer_exact_zero (S.index Y) w hsum i)
      | succ m =>
          obtain ⟨z, hz, hwz⟩ := S.layer_exact (S.index Y) w hw hsum
          by_cases hY : Y ∈ S.nonprojectiveVertices
          · let y : S.nonprojectiveVertices := ⟨Y, hY⟩
            let h : S.fg (S.index W) ⟶ S.fg (S.index (S.arTranslationQuiver.tau y).1) :=
              z ≫ (S.tau.tauPlusIso (S.vendorNonprojective y)).hom
            have hh : h ∈ (StrictLayers.Ipow m : HomIdeal (ModCat A)).hom _ _ :=
              (StrictLayers.Ipow m : HomIdeal (ModCat A)).postcomp _ hz
            let hInd : S.label W ⟶ S.label (S.arTranslationQuiver.tau y).1 :=
              (S.homEquivFG (S.ind (S.index W)) (S.ind (S.index (S.arTranslationQuiver.tau y).1))).symm h
            have hIndMap : S.toFG.map hInd = h := S.map_homEquivFG_symm _
            have hIndMem : hInd ∈ S.radPow m _ _ := by
              rw [S.mem_radPow_iff, hIndMap]; exact hh
            obtain ⟨H, hH, hHdiff⟩ := S.exists_realize_sub_mem b m hInd hIndMem
            -- the corrected components
            have hcorr : ∀ i, G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ -
                ((S.arCoefficients b y _ (S.occArrow Y i) : kˣ) : k) •
                  (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate y _ (S.occArrow Y i))) ∈
                (S.meshIdeal b).hom _ _ := by
              intro i
              apply ih
              · refine sub_mem (hG _) (Submodule.smul_mem _ _ ?_)
                exact LinearPaths.comp_arrow_mem_degreePart hH _
              · apply S.realize_corrected_mem b y i _ H hH hInd hHdiff
                have e : S.toFG.map ((S.vCoeff b y.1 i)⁻¹ •
                    S.realize b W _ (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩) -
                      hInd ≫ S.alphaI y i) =
                    w i - z ≫ (S.rightMesh (S.index Y)).f ≫ S.midProj (S.index Y) i := by
                  rw [Functor.map_sub, Functor.map_comp, hIndMap, S.alphaI_map]
                  simp only [h, Category.assoc, Iso.hom_inv_id_assoc]
                  rfl
                rw [S.mem_radPow_iff, e]
                exact hwz i
            -- the mesh relation at `Y`
            have hmesh : H ≫ meshRelation (S.arCoefficients b) y ∈ (S.meshIdeal b).hom _ _ := by
              apply (S.meshIdeal b).precomp
              exact MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal.relation_mem_linearSpan
                _ ⟨y, rfl, rfl, by simp⟩
            have hdecomp : ∑ a, G a ≫ LinearPaths.arrow a.2 - H ≫ meshRelation (S.arCoefficients b) y =
                ∑ i, (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ -
                  ((S.arCoefficients b y _ (S.occArrow Y i) : kˣ) : k) •
                    (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate y _ (S.occArrow Y i)))) ≫
                  LinearPaths.arrow (S.occArrow Y i) := by
              rw [meshRelation, Preadditive.comp_sum, S.sum_lastArrow_eq (W := W),
                S.sum_lastArrow_eq (W := W) (fun a ↦ H ≫ _), ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [Preadditive.sub_comp, Linear.smul_comp, Category.assoc, Linear.comp_smul,
                LinearPaths.arrow, LinearPaths.arrow, LinearPaths.path_comp_path]
            have hsumc : ∑ i, (G ⟨S.vertex (S.midLabel (S.index Y) i), S.occArrow Y i⟩ -
                ((S.arCoefficients b y _ (S.occArrow Y i) : kˣ) : k) •
                  (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate y _ (S.occArrow Y i)))) ≫
                LinearPaths.arrow (S.occArrow Y i) ∈ (S.meshIdeal b).hom _ _ :=
              sum_mem fun i _ ↦ (S.meshIdeal b).postcomp (LinearPaths.arrow (S.occArrow Y i)) (hcorr i)
            have := add_mem hsumc hmesh
            rwa [← hdecomp, sub_add_cancel] at this
          · have hz0 : z = 0 := (S.isZero_rightMesh_X₁_of_not_mem Y hY).eq_of_tgt _ _
            apply S.lastArrow_sum_mem_of b G
            intro i
            apply hstep i
            simpa [hz0] using hwz i

end MultiplicativeBasisDeformations.IndSkeleton
