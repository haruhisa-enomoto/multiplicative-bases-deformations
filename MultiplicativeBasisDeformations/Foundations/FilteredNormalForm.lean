import MultiplicativeBasisDeformations.Foundations.GradedRealizationIso
import MultiplicativeBasisDeformations.Foundations.MeshCorrections

/-!
# Proposition 5.4: successive correction of irreducible representatives

`mesh-deformations.tex`. Let `C = kQ/(r_1, …, r_t)` be a
finite-dimensional graded category with homogeneous quadratic relations such
that the derivatives `D_{q-1}` are surjective for `q ≥ 3`, and let `E` be a
finite filtered category with a graded identification `gr E = C`. Choose lifts
of the arrows; their relation errors lie in `F³E`. If the errors vanish in
degrees below `q`, their degree-`q` classes lie in the image of `D_{q-1}`, and a
parallel change of the arrows in degree `q - 1` cancels them; a term using two
corrections has degree at least `2q - 2 > q`. The filtration is finite, so the
process ends, and the resulting homomorphism `C → E` is an isomorphism.

This file proves the proposition in the case used by the manuscript
(Corollary 5.5): `E = ind(mod A)` filtered by the powers of its radical,
`C = k(Γ_A) = C(Γ_A, c)`, and the identification of Proposition 2.6(3). The
surjectivity of the derivatives is a hypothesis
(`ScalarMeshCategory.MeshDerivativeSurjective`), supplied outside
characteristic two by Proposition 5.3.

This file: lift families and their realizations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- A family of lifts of the arrows: morphisms congruent to the chosen
representatives modulo `J²`. -/
structure Lifts where
  L : ∀ {x y : S.ARVertex}, (x ⟶ y) → (S.label x ⟶ S.label y)
  sub_mem : ∀ {x y : S.ARVertex} (a : x ⟶ y), L a - S.rep b a ∈ S.radPow 2 _ _

namespace Lifts

variable {S b} (L : S.Lifts b)

/-- The chosen representatives form a lift family. -/
def ofRep : S.Lifts b where
  L a := S.rep b a
  sub_mem a := by rw [sub_self]; exact zero_mem _

theorem mem_one {x y : S.ARVertex} (a : x ⟶ y) : L.L a ∈ S.radPow 1 _ _ := by
  have : L.L a = (L.L a - S.rep b a) + S.rep b a := by abel
  rw [this]
  exact add_mem (S.radPow_succ_le 1 _ _ (L.sub_mem a)) (S.rep_mem b a)

/-- The realization of a path by the lifts. -/
def pathMap {x : S.ARVertex} : ∀ {y : S.ARVertex}, Quiver.Path x y → (S.label x ⟶ S.label y)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p a => pathMap p ≫ L.L a

@[simp] theorem pathMap_nil {x : S.ARVertex} :
    L.pathMap (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ := rfl

@[simp] theorem pathMap_cons {x y z : S.ARVertex} (p : Quiver.Path x y) (a : y ⟶ z) :
    L.pathMap (p.cons a) = L.pathMap p ≫ L.L a := rfl

theorem pathMap_comp {x y z : S.ARVertex} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    L.pathMap (p.comp q) = L.pathMap p ≫ L.pathMap q := by
  induction q with
  | nil => simp
  | cons q a ih => simp [Quiver.Path.comp_cons, ih, Category.assoc]

theorem pathMap_mem {x y : S.ARVertex} (p : Quiver.Path x y) :
    L.pathMap p ∈ S.radPow p.length (S.label x) (S.label y) := by
  induction p with
  | nil => exact Submodule.mem_top
  | cons p a ih =>
      rw [pathMap_cons, Quiver.Path.length_cons]
      exact S.comp_mem_radPow ih (L.mem_one a)

/-- The lifts agree with the chosen representatives on a path modulo one more
power of the radical. -/
theorem pathMap_sub_mem {x y : S.ARVertex} (p : Quiver.Path x y) :
    L.pathMap p - S.pathMap b p ∈ S.radPow (p.length + 1) (S.label x) (S.label y) := by
  induction p with
  | nil => simp
  | cons p a ih =>
      rw [pathMap_cons, IndSkeleton.pathMap_cons, Quiver.Path.length_cons]
      have e : L.pathMap p ≫ L.L a - S.pathMap b p ≫ S.rep b a =
          (L.pathMap p - S.pathMap b p) ≫ L.L a + S.pathMap b p ≫ (L.L a - S.rep b a) := by
        simp only [Preadditive.sub_comp, Preadditive.comp_sub]; abel
      rw [e]
      refine add_mem (S.comp_mem_radPow ih (L.mem_one a)) ?_
      have := S.comp_mem_radPow (S.pathMap_mem b p) (L.sub_mem a)
      rwa [show p.length + 2 = p.length + 1 + 1 by omega] at this

/-- The realization of a morphism of `kQ` by the lifts. -/
def realize (x y : S.ARVertex) :
    (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj (k := k) y) →ₗ[k] (S.label x ⟶ S.label y) :=
  (Finsupp.linearCombination k (L.pathMap (x := x) (y := y))).comp
    (LinearPaths.finsuppEquiv (k := k) x y).toLinearMap

theorem realize_path {x y : S.ARVertex} (p : Quiver.Path x y) :
    L.realize x y (LinearPaths.path p) = L.pathMap p := by
  change Finsupp.linearCombination k L.pathMap (Finsupp.single p 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

theorem realize_arrow {x y : S.ARVertex} (a : x ⟶ y) :
    L.realize x y (LinearPaths.arrow a) = L.L a := by
  rw [LinearPaths.arrow, realize_path]
  simp [Quiver.Hom.toPath]

theorem realize_comp {x y z : S.ARVertex} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y)
    (g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    L.realize x z (f ≫ g) = L.realize x y f ≫ L.realize y z g := by
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
    L.realize x y f ∈ S.radPow d (S.label x) (S.label y) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, rfl, rfl⟩ := hg
      rw [realize_path]
      exact L.pathMap_mem p
  | zero => simp
  | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- On homogeneous morphisms of degree `d`, the realizations by the lifts and by
the chosen representatives agree modulo `J^{d+1}`. -/
theorem realize_sub_mem {d : ℕ} {x y : S.ARVertex} {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hf : f ∈ LinearPaths.degreePart (k := k) d x y) :
    L.realize x y f - S.realize b x y f ∈ S.radPow (d + 1) (S.label x) (S.label y) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, rfl, rfl⟩ := hg
      rw [realize_path, IndSkeleton.realize_path]
      exact L.pathMap_sub_mem p
  | zero => simp
  | add a c _ _ ha hc =>
      rw [map_add, map_add]
      have : L.realize x y a + L.realize x y c - (S.realize b x y a + S.realize b x y c) =
          (L.realize x y a - S.realize b x y a) + (L.realize x y c - S.realize b x y c) := by abel
      rw [this]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul, map_smul, ← smul_sub]; exact Submodule.smul_mem _ c ha

/-- The relation error of the lifts at a nonprojective vertex. -/
def error (x : S.nonprojectiveVertices) : S.label (S.arTranslationQuiver.tau x).1 ⟶ S.label x.1 :=
  L.realize _ _ (meshRelation (S.arCoefficients b) x)

/-- The relation errors lie in `J³`. -/
theorem error_mem_three (x : S.nonprojectiveVertices) : L.error x ∈ S.radPow 3 _ _ := by
  have h1 := L.realize_sub_mem (meshRelation_mem_degreePart (S.arCoefficients b) x)
  have h2 := S.realize_meshRelation_mem b x
  have : L.error x = (L.error x - S.realize b _ _ (meshRelation (S.arCoefficients b) x)) +
      S.realize b _ _ (meshRelation (S.arCoefficients b) x) := by abel
  rw [this]
  exact add_mem h1 h2

end Lifts

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem layerClass_add {d : ℕ} {X Y : S.Ind} {f g : X ⟶ Y} (hf : f ∈ S.radPow d X Y)
    (hg : g ∈ S.radPow d X Y) :
    S.layerClass (f + g) (add_mem hf hg) = S.layerClass f hf + S.layerClass g hg := rfl

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem layerClass_smul {d : ℕ} {X Y : S.Ind} (c : k) {f : X ⟶ Y} (hf : f ∈ S.radPow d X Y) :
    S.layerClass (c • f) (Submodule.smul_mem _ c hf) = c • S.layerClass f hf := rfl

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem layerClass_eq_zero_iff {d : ℕ} {X Y : S.Ind} {f : X ⟶ Y} (hf : f ∈ S.radPow d X Y) :
    S.layerClass f hf = 0 ↔ f ∈ S.radPow (d + 1) X Y :=
  Submodule.Quotient.mk_eq_zero _

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem layerClass_eq_iff {d : ℕ} {X Y : S.Ind} {f g : X ⟶ Y} (hf : f ∈ S.radPow d X Y)
    (hg : g ∈ S.radPow d X Y) :
    S.layerClass f hf = S.layerClass g hg ↔ f - g ∈ S.radPow (d + 1) X Y :=
  Submodule.Quotient.eq _

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

namespace Lifts

variable {S b} (L : S.Lifts b)

theorem pathMap_two {x y z : S.ARVertex} (a : x ⟶ y) (a' : y ⟶ z) :
    L.pathMap (a.toPath.comp a'.toPath) = L.L a ≫ L.L a' := by
  rw [pathMap_comp]; simp [Quiver.Hom.toPath]

/-- The relation error, written out: `∑_a c_{x,a} L(σ a) L(a)`. -/
theorem error_eq (x : S.nonprojectiveVertices) :
    L.error x = ∑ a : Σ y : S.ARVertex, y ⟶ x.1,
      ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
        (L.L (S.arTranslationQuiver.mate x a.1 a.2) ≫ L.L a.2) := by
  simp only [error, meshRelation, map_sum, map_smul, realize_path, pathMap_two]

end Lifts

set_option maxHeartbeats 800000 in
/-- **The correction step** of Proposition 5.4: if the relation errors of a lift
family lie in `J^{m+1}` (`m ≥ 2`) and `D_m` is surjective, a change of the lifts
in degree `m` moves all errors into `J^{m+2}`. -/
theorem Lifts.exists_correction {m : ℕ} (hm : 2 ≤ m)
    (hD : ScalarMeshCategory.MeshDerivativeSurjective (S.arCoefficients b) m)
    (L : S.Lifts b) (hL : ∀ x, L.error x ∈ S.radPow (m + 1) _ _) :
    ∃ L' : S.Lifts b, ∀ x, L'.error x ∈ S.radPow (m + 2) _ _ := by
  classical
  -- the error classes, pulled back to `C_{m+1}`
  let g : ScalarMeshCategory.MeshFamily (S.arCoefficients b) := fun x ↦
    -((S.phi b (m + 1) _ _).symm (S.layerClass (L.error x) (hL x))).1
  have hg : ∀ x, g x ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) (m + 1)
      (S.arTranslationQuiver.tau x).1 x.1 := fun x ↦ neg_mem (Subtype.prop _)
  obtain ⟨f, hf, hDf⟩ := hD g hg
  -- lift the corrections to the path category and realize them
  have hex : ∀ a : Σ x y : S.ARVertex, x ⟶ y, ∃ F : LinearPaths.obj (k := k) a.1 ⟶
      LinearPaths.obj a.2.1, F ∈ LinearPaths.degreePart (k := k) m a.1 a.2.1 ∧
        (S.meshQuot b).map F = f a := by
    intro a
    obtain ⟨F, hF, h⟩ := hf a
    exact ⟨F, hF, h⟩
  choose Ft hFt hqFt using hex
  let F : ∀ {x y : S.ARVertex} (a : x ⟶ y), S.label x ⟶ S.label y :=
    fun {x y} a ↦ S.realize b x y (Ft ⟨x, y, a⟩)
  have hFm : ∀ {x y : S.ARVertex} (a : x ⟶ y), F a ∈ S.radPow m _ _ :=
    fun {x y} a ↦ S.realize_mem b (hFt ⟨x, y, a⟩)
  have hF2 : ∀ {x y : S.ARVertex} (a : x ⟶ y), F a ∈ S.radPow 2 _ _ :=
    fun a ↦ S.radPow_anti hm _ _ (hFm a)
  let L' : S.Lifts b :=
    { L := fun a ↦ L.L a + F a
      sub_mem := fun a ↦ by
        have : L.L a + F a - S.rep b a = (L.L a - S.rep b a) + F a := by abel
        rw [this]; exact add_mem (L.sub_mem a) (hF2 a) }
  refine ⟨L', fun x ↦ ?_⟩
  -- the derivative of the corrections, in the path category
  let T : LinearPaths.obj (k := k) (S.arTranslationQuiver.tau x).1 ⟶ LinearPaths.obj x.1 :=
    ∑ a : Σ y : S.ARVertex, y ⟶ x.1, ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
      (Ft ⟨_, a.1, S.arTranslationQuiver.mate x a.1 a.2⟩ ≫ LinearPaths.arrow a.2 +
        LinearPaths.arrow (S.arTranslationQuiver.mate x a.1 a.2) ≫ Ft ⟨a.1, x.1, a.2⟩)
  have hT : T ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := by
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem ?_ ?_)
    · exact LinearPaths.comp_arrow_mem_degreePart
        (hFt ⟨_, a.1, S.arTranslationQuiver.mate x a.1 a.2⟩) a.2
    · have := LinearPaths.comp_mem_degreePart
        (LinearPaths.arrow_mem_degreePart (k := k) (S.arTranslationQuiver.mate x a.1 a.2))
        (hFt ⟨a.1, x.1, a.2⟩)
      rwa [add_comm] at this
  have hqT : (S.meshQuot b).map T = g x := by
    rw [← congrFun hDf x]
    simp only [T, ScalarMeshCategory.meshDerivative, Functor.map_sum, Functor.map_smul,
      Functor.map_add, Functor.map_comp, hqFt]
    rfl
  -- the class of `realize T` is minus the class of the error
  have hclass : L.error x + S.realize b _ _ T ∈ S.radPow (m + 2) _ _ := by
    have h1 : S.phi b (m + 1) _ _ (S.qd b (m + 1) _ _ ⟨T, hT⟩) =
        -S.layerClass (L.error x) (hL x) := by
      have e : S.qd b (m + 1) _ _ ⟨T, hT⟩ =
          -((S.phi b (m + 1) _ _).symm (S.layerClass (L.error x) (hL x))) :=
        Subtype.ext hqT
      rw [e, map_neg, LinearEquiv.apply_symm_apply]
    rw [S.phi_qd] at h1
    have h2 : S.layerClass (L.error x + S.realize b _ _ T)
        (add_mem (hL x) (S.realize_mem b hT)) = 0 := by
      have e : S.layerClass (L.error x + S.realize b _ _ T)
          (add_mem (hL x) (S.realize_mem b hT)) =
          S.layerClass (L.error x) (hL x) + S.psi b (m + 1) _ _ ⟨T, hT⟩ := rfl
      rw [e, h1, add_neg_cancel]
    exact (S.layerClass_eq_zero_iff _).1 h2
  -- the new error differs from `error + realize T` by terms in `J^{m+2}`
  have hrealT : S.realize b _ _ T = ∑ a : Σ y : S.ARVertex, y ⟶ x.1,
      ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
        (F (S.arTranslationQuiver.mate x a.1 a.2) ≫ S.rep b a.2 +
          S.rep b (S.arTranslationQuiver.mate x a.1 a.2) ≫ F a.2) := by
    simp only [T, map_sum, map_smul, map_add, S.realize_comp, S.realize_arrow]
    rfl
  have hdiff : L'.error x - (L.error x + S.realize b _ _ T) =
      ∑ a : Σ y : S.ARVertex, y ⟶ x.1, ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
        (F (S.arTranslationQuiver.mate x a.1 a.2) ≫ (L.L a.2 - S.rep b a.2) +
          (L.L (S.arTranslationQuiver.mate x a.1 a.2) -
            S.rep b (S.arTranslationQuiver.mate x a.1 a.2)) ≫ F a.2 +
          F (S.arTranslationQuiver.mate x a.1 a.2) ≫ F a.2) := by
    rw [Lifts.error_eq, Lifts.error_eq, hrealT, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← smul_add, ← smul_sub]
    congr 1
    simp only [L', Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp,
      Preadditive.comp_sub]
    abel
  have hmem : L'.error x - (L.error x + S.realize b _ _ T) ∈ S.radPow (m + 2) _ _ := by
    rw [hdiff]
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem (add_mem ?_ ?_) ?_)
    · exact S.comp_mem_radPow (hFm (S.arTranslationQuiver.mate x a.1 a.2)) (L.sub_mem a.2)
    · have := S.comp_mem_radPow (L.sub_mem (S.arTranslationQuiver.mate x a.1 a.2)) (hFm a.2)
      rwa [add_comm] at this
    · exact S.radPow_anti (by omega) _ _
        (S.comp_mem_radPow (hFm (S.arTranslationQuiver.mate x a.1 a.2)) (hFm a.2))
  have := add_mem hmem hclass
  rwa [sub_add_cancel] at this

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The derivatives `D_{q-1}` of `k(Γ_A)` are surjective for all `q ≥ 3`. -/
def DerivativesSurjective : Prop :=
  ∀ m, 2 ≤ m → ScalarMeshCategory.MeshDerivativeSurjective (S.arCoefficients b) m

/-- Successive correction: lifts whose relation errors lie in `J^{n+3}`. -/
theorem exists_lifts_error_mem (hD : S.DerivativesSurjective b) :
    ∀ n : ℕ, ∃ L : S.Lifts b, ∀ x, L.error x ∈ S.radPow (n + 3) _ _ := by
  intro n
  induction n with
  | zero => exact ⟨Lifts.ofRep, fun x ↦ Lifts.ofRep.error_mem_three x⟩
  | succ n ih =>
      obtain ⟨L, hL⟩ := ih
      exact Lifts.exists_correction S b (m := n + 2) (by omega) (hD _ (by omega)) L hL

/-- The process terminates: lifts satisfying the mesh relations exactly. -/
theorem exists_lifts_error_eq_zero (hD : S.DerivativesSurjective b) :
    ∃ L : S.Lifts b, ∀ x, L.error x = 0 := by
  obtain ⟨N, hN⟩ := S.exists_radPow_eq_bot
  obtain ⟨L, hL⟩ := S.exists_lifts_error_mem b hD N
  refine ⟨L, fun x ↦ ?_⟩
  have := S.radPow_anti (show N ≤ N + 3 by omega) _ _ (hL x)
  rwa [hN, Submodule.mem_bot] at this

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

namespace Lifts

variable {S b} (L : S.Lifts b)

theorem realize_id (x : S.ARVertex) :
    L.realize x x (𝟙 (LinearPaths.obj (k := k) x)) = 𝟙 (S.label x) :=
  L.realize_path Quiver.Path.nil

/-- The functor `kQ → ind(mod A)` sending each arrow to its lift. -/
def pathFunctor : LinearPaths k S.ARVertex ⥤ S.Ind where
  obj X := S.label X
  map {X Y} f := L.realize X Y f
  map_id X := L.realize_id X
  map_comp f g := L.realize_comp f g

theorem pathFunctor_map {x y : S.ARVertex} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    L.pathFunctor.map f = L.realize x y f := rfl

/-- Lifts satisfying the mesh relations kill the mesh ideal. -/
theorem realize_eq_zero_of_mem (hL : ∀ x, L.error x = 0) {x y : S.ARVertex}
    {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y} (hf : f ∈ (S.meshIdeal b).hom _ _) :
    L.realize x y f = 0 := by
  change f ∈ MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal.generatedHomSubmodule k _
    (LinearPaths.obj x) (LinearPaths.obj y) at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨X, Y, r, hr, a, a', rfl⟩ := hg
      obtain ⟨x₀, hX, hY, rfl⟩ := hr
      change X = LinearPaths.obj (S.arTranslationQuiver.tau x₀).1 at hX
      change Y = LinearPaths.obj x₀.1 at hY
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [← pathFunctor_map, Functor.map_comp, Functor.map_comp, pathFunctor_map L
        (meshRelation (S.arCoefficients b) x₀)]
      change _ ≫ L.error x₀ ≫ _ = 0
      rw [hL, Limits.zero_comp, Limits.comp_zero]
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, ha, hc, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

end Lifts

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

namespace Lifts

variable {S b} (L : S.Lifts b) (hL : ∀ x, L.error x = 0)

/-- The homomorphism `k(Γ_A) → ind(mod A)` given by lifts satisfying the mesh
relations. -/
def functor : S.ARMeshCategory b ⥤ S.Ind :=
  CategoryTheory.Quotient.lift _ L.pathFunctor fun x y f₁ f₂ h ↦ by
    have h0 := L.realize_eq_zero_of_mem hL h
    rw [map_sub, sub_eq_zero] at h0
    exact h0

theorem functor_map {x y : S.ARVertex} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    (L.functor hL).map ((S.meshQuot b).map f) = L.realize x y f := rfl

/-- On homogeneous morphisms, the lifts realize the prescribed graded
identification. -/
theorem layerClass_functor_map {d : ℕ} {x y : S.ARVertex}
    (f : ScalarMeshCategory.degreePart (S.arCoefficients b) d x y) :
    ∃ hf : (L.functor hL).map f.1 ∈ S.radPow d _ _,
      S.layerClass _ hf = S.phi b d x y f := by
  obtain ⟨F, rfl⟩ := LinearMap.submoduleMap_surjective (S.meshQuotL b x y) _ f
  refine ⟨L.realize_mem F.2, ?_⟩
  rw [S.phi_qd]
  exact (S.layerClass_eq_iff _ _).2 (L.realize_sub_mem F.2)

include hL in
/-- Faithfulness: a morphism of `kQ` realized to zero lies in the mesh ideal. -/
theorem mem_meshIdeal_of_realize_eq_zero {x y : S.ARVertex}
    {G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y} (hG : L.realize x y G = 0) :
    G ∈ (S.meshIdeal b).hom _ _ := by
  classical
  obtain ⟨N, hN⟩ := LinearPaths.eq_sum_proj (k := k) G
  -- every homogeneous component lies in the mesh ideal, by induction on the degree
  have hd : ∀ n, ∀ d < n, LinearPaths.proj d x y G ∈ (S.meshIdeal b).hom _ _ := by
    intro n
    induction n with
    | zero => intro d hd; omega
    | succ n ih =>
        intro d hd
        rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
        · exact ih d hd
        by_cases hdN : d ∈ Finset.range N
        · -- the other components realize into `J^{d+1}`
          have hrest : ∀ e ∈ (Finset.range N).erase d,
              L.realize x y (LinearPaths.proj e x y G) ∈ S.radPow (d + 1) _ _ := by
            intro e he
            rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with hed | hed
            · rw [L.realize_eq_zero_of_mem hL (ih e hed)]; exact zero_mem _
            · exact S.radPow_anti hed _ _ (L.realize_mem (LinearPaths.proj_mem G))
          have hsum : L.realize x y G = L.realize x y (LinearPaths.proj d x y G) +
              ∑ e ∈ (Finset.range N).erase d, L.realize x y (LinearPaths.proj e x y G) := by
            conv_lhs => rw [hN]
            rw [map_sum, ← Finset.add_sum_erase _ _ hdN]
          have hL1 : L.realize x y (LinearPaths.proj d x y G) ∈ S.radPow (d + 1) _ _ := by
            have : L.realize x y (LinearPaths.proj d x y G) =
                -∑ e ∈ (Finset.range N).erase d, L.realize x y (LinearPaths.proj e x y G) := by
              rw [eq_neg_iff_add_eq_zero, ← hsum, hG]
            rw [this]
            exact neg_mem (sum_mem hrest)
          have hS : S.realize b x y (LinearPaths.proj d x y G) ∈ S.radPow (d + 1) _ _ := by
            have := _root_.sub_mem hL1 (L.realize_sub_mem (LinearPaths.proj_mem G))
            rwa [sub_sub_cancel] at this
          exact S.mem_meshIdeal_of_realize_mem b d (LinearPaths.proj_mem G) hS
        · have : LinearPaths.proj d x y G = 0 := by
            conv_lhs => rw [hN]
            rw [map_sum]
            refine Finset.sum_eq_zero fun e he ↦ ?_
            rw [LinearPaths.proj_of_mem (LinearPaths.proj_mem G), if_neg]
            rintro rfl; exact hdN he
          rw [this]; exact zero_mem _
  rw [hN]
  exact sum_mem fun d _ ↦ hd (d + 1) d (by omega)

/-- Fullness: every morphism of `ind(mod A)` is realized by the lifts. -/
theorem exists_realize_eq {x y : S.ARVertex} (f : S.label x ⟶ S.label y) :
    ∃ G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y, L.realize x y G = f := by
  obtain ⟨N, hN⟩ := S.exists_radPow_eq_bot
  have key : ∀ j n, N ≤ n + j → ∀ {x y : S.ARVertex} (f : S.label x ⟶ S.label y),
      f ∈ S.radPow n _ _ → ∃ G : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y,
        L.realize x y G = f := by
    intro j
    induction j with
    | zero =>
        intro n hn x y f hf
        have := S.radPow_anti (show N ≤ n by omega) _ _ hf
        rw [hN, Submodule.mem_bot] at this
        exact ⟨0, by rw [map_zero, this]⟩
    | succ j ih =>
        intro n hn x y f hf
        obtain ⟨F, hF, hfF⟩ := S.exists_realize_sub_mem b n f hf
        have h1 : f - L.realize x y F ∈ S.radPow (n + 1) _ _ := by
          have := _root_.sub_mem hfF (L.realize_sub_mem hF)
          rwa [show f - S.realize b x y F - (L.realize x y F - S.realize b x y F) =
            f - L.realize x y F by abel] at this
        obtain ⟨G, hG⟩ := ih (n + 1) (by omega) _ h1
        exact ⟨F + G, by rw [map_add, hG]; abel⟩
  exact key N 0 (by omega) f (by rw [S.radPow_zero]; exact Submodule.mem_top)

theorem functor_faithful : (L.functor hL).Faithful := by
  refine ⟨fun {a a'} f g h ↦ ?_⟩
  obtain ⟨F, rfl⟩ := (S.meshQuot b).map_surjective (X := a.as) (Y := a'.as) f
  obtain ⟨G, rfl⟩ := (S.meshQuot b).map_surjective (X := a.as) (Y := a'.as) g
  change L.realize a.as a'.as F = L.realize a.as a'.as G at h
  apply CategoryTheory.Quotient.sound
  change F - G ∈ (S.meshIdeal b).hom _ _
  exact L.mem_meshIdeal_of_realize_eq_zero hL (by rw [map_sub, h, sub_self])

theorem functor_full : (L.functor hL).Full := by
  refine ⟨fun {a a'} f ↦ ?_⟩
  obtain ⟨G, hG⟩ := L.exists_realize_eq (x := a.as) (y := a'.as) f
  exact ⟨(S.meshQuot b).map G, hG⟩

theorem functor_essSurj : (L.functor hL).EssSurj :=
  ⟨fun Y ↦ ⟨(S.meshQuot b).obj (LinearPaths.obj (S.vertex Y)), ⟨Iso.refl _⟩⟩⟩

theorem functor_isEquivalence : (L.functor hL).IsEquivalence where
  faithful := L.functor_faithful hL
  full := L.functor_full hL
  essSurj := L.functor_essSurj hL

theorem functor_isLinear : IsLinearFunctor (k := k) (L.functor hL) := by
  intro a a' c f g
  obtain ⟨F, rfl⟩ := (S.meshQuot b).map_surjective (X := a.as) (Y := a'.as) f
  obtain ⟨G, rfl⟩ := (S.meshQuot b).map_surjective (X := a.as) (Y := a'.as) g
  rw [← Functor.map_smul, ← Functor.map_add]
  change L.realize a.as a'.as (c • F + G) = c • L.realize a.as a'.as F + L.realize a.as a'.as G
  rw [map_add, map_smul]

end Lifts

end MultiplicativeBasisDeformations.IndSkeleton

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Proposition 5.4** for `E = ind(mod A)` filtered by the radical powers and
`C = k(Γ_A)` with the identification of Proposition 2.6(3): if the derivatives
`D_{q-1}` are surjective for `q ≥ 3`, there is a `k`-linear equivalence
`k(Γ_A) ≃ ind(mod A)` sending each vertex to its label and inducing the
prescribed identification on the radical layers. -/
theorem filteredNormalForm (hD : S.DerivativesSurjective b) :
    ∃ (L : S.Lifts b) (hL : ∀ x, L.error x = 0),
      (L.functor hL).IsEquivalence ∧ IsLinearFunctor (k := k) (L.functor hL) ∧
      ∀ (d : ℕ) (x y : S.ARVertex)
        (f : ScalarMeshCategory.degreePart (S.arCoefficients b) d x y),
        ∃ hf : (L.functor hL).map f.1 ∈ S.radPow d (S.label x) (S.label y),
          S.layerClass _ hf = S.phi b d x y f := by
  obtain ⟨L, hL⟩ := S.exists_lifts_error_eq_zero b hD
  exact ⟨L, hL, L.functor_isEquivalence hL, L.functor_isLinear hL,
    fun _ _ _ f ↦ L.layerClass_functor_map hL f⟩

/-- Standardness from the surjectivity of the mesh derivatives. -/
theorem isStandard_of_derivativesSurjective (hD : S.DerivativesSurjective b) : S.IsStandard := by
  obtain ⟨L, hL, hF, hlin, -⟩ := S.filteredNormalForm b hD
  exact ⟨b, L.functor hL, hF, hlin, fun x ↦ ⟨Iso.refl _⟩⟩

end MultiplicativeBasisDeformations.IndSkeleton
