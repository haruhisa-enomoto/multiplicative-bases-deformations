import MultiplicativeBasisDeformations.Foundations.PsiInjective

/-!
# Evaluation of linear paths and its first-order deformation, over any ring

Given modules `N_X` over a commutative ring `R` and maps `φ_a : N_y → N_x` for the arrows of a
translation quiver, a path evaluates to the composite of the arrow maps (`evP`), extended
linearly to `RQ` (`evL`). Arrow corrections `g_a` give the `ε`-part `δ` of the evaluation of
`φ + εg` (`δp`, `δL`), a derivation (`δL_comp`). When the mesh relations hold for `φ`
(`evL_ideal`), and also to first order (`δL_ideal`), both kill the mesh ideal.

This is the ring-generic part of the proof of Proposition 7.6 (`PsiInjective`), used over
`ℤ/4` for Lemma 10.2 (`integral-deformations.tex:144–171`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

namespace PathEval

open ScalarMeshCategory

variable {R : Type u} [CommRing R] {V : Type} [Quiver.{0} V]
  (N : V → Type v) [∀ X, AddCommGroup (N X)] [∀ X, Module R (N X)]
  (φ : ∀ {y x : V}, (y ⟶ x) → (N y →ₗ[R] N x))

/-- The evaluation of a path. -/
def evP : ∀ {Y X : V}, Quiver.Path Y X → (N Y →ₗ[R] N X)
  | _, _, Quiver.Path.nil => LinearMap.id
  | _, _, Quiver.Path.cons p a => φ a ∘ₗ evP p

theorem evP_nil (Y : V) : evP N φ (Quiver.Path.nil : Quiver.Path Y Y) = LinearMap.id := by
  rw [evP]

theorem evP_cons {Y X Z : V} (p : Quiver.Path Y X) (a : X ⟶ Z) :
    evP N φ (p.cons a) = φ a ∘ₗ evP N φ p := by
  rw [evP]

theorem evP_comp {Y X : V} (p : Quiver.Path Y X) : ∀ {Z : V} (p' : Quiver.Path X Z),
    evP N φ (p.comp p') = evP N φ p' ∘ₗ evP N φ p := by
  intro Z p'
  induction p' with
  | nil => rw [Quiver.Path.comp_nil, evP_nil, LinearMap.id_comp]
  | cons p' a ih => rw [Quiver.Path.comp_cons, evP_cons, ih, evP_cons, LinearMap.comp_assoc]

theorem evP_toPath {Y X : V} (a : Y ⟶ X) : evP N φ a.toPath = φ a := by
  change evP N φ (Quiver.Path.cons Quiver.Path.nil a) = _
  rw [evP_cons, evP_nil, LinearMap.comp_id]

/-- The linear extension of `evP` to the morphisms of `RQ`. -/
def evL {Y X : V} : (LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X) →ₗ[R]
    (N Y →ₗ[R] N X) :=
  (Finsupp.linearCombination R (fun p : Quiver.Path Y X ↦ evP N φ p)).comp
    (LinearPaths.finsuppEquiv (k := R) Y X).toLinearMap

theorem evL_path {Y X : V} (p : Quiver.Path Y X) :
    evL N φ (LinearPaths.path (k := R) p) = evP N φ p := by
  simp [evL, LinearPaths.finsuppEquiv]

theorem evL_id (Y : V) : evL N φ (𝟙 (LinearPaths.obj (k := R) Y)) = LinearMap.id := by
  change evL N φ (LinearPaths.path (k := R) Quiver.Path.nil) = _
  rw [evL_path, evP_nil]

theorem rq_induction {Y X : V}
    {P : (LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X) → Prop}
    (h0 : P 0) (hadd : ∀ F G, P F → P G → P (F + G)) (hsmul : ∀ (t : R) F, P F → P (t • F))
    (hpath : ∀ p, P (LinearPaths.path p)) (F) : P F := by
  have : F = LinearPaths.ofFinsupp (LinearPaths.toFinsupp F) := rfl
  rw [this]
  induction LinearPaths.toFinsupp F using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg => exact hadd _ _ hf hg
  | single p t =>
    have : LinearPaths.ofFinsupp (Finsupp.single p t) = t • LinearPaths.path (k := R) p := by
      change Finsupp.single p t = t • Finsupp.single p 1
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact hsmul _ _ (hpath p)

theorem evL_comp {Y X Z : V} (F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X)
    (G : LinearPaths.obj (k := R) X ⟶ LinearPaths.obj (k := R) Z) :
    evL N φ (F ≫ G) = evL N φ G ∘ₗ evL N φ F := by
  induction F using rq_induction with
  | h0 => rw [Limits.zero_comp, map_zero, map_zero, LinearMap.comp_zero]
  | hadd F F' hF hF' => rw [Preadditive.add_comp, map_add, hF, hF', map_add, LinearMap.comp_add]
  | hsmul t F hF => rw [Linear.smul_comp, map_smul, hF, map_smul, LinearMap.comp_smul]
  | hpath p =>
    induction G using rq_induction with
    | h0 => rw [Limits.comp_zero, map_zero, map_zero, LinearMap.zero_comp]
    | hadd G G' hG hG' =>
      rw [Preadditive.comp_add, map_add, hG, hG', map_add, LinearMap.add_comp]
    | hsmul t G hG => rw [Linear.comp_smul, map_smul, hG, map_smul, LinearMap.smul_comp]
    | hpath p' => rw [LinearPaths.path_comp_path, evL_path, evL_path, evL_path, evP_comp]

/-! ### The mesh ideal -/

variable {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (u : MeshCoefficients R Q)

theorem evL_meshRelation (x : Q.nonprojective) :
    evL N φ (meshRelation u x) = ∑ a : Σ y : V, y ⟶ x.1,
      ((u x a.1 a.2 : Rˣ) : R) • (φ a.2 ∘ₗ φ (Q.mate x a.1 a.2)) := by
  rw [meshRelation, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, evL_path, evP_comp, evP_toPath, evP_toPath]

/-- The ideal induction for the mesh ideal: a linear map killing the sandwiches of the mesh
relations kills the mesh ideal. -/
theorem mem_ideal_induction {Y X : V} {M : Type*} [AddCommGroup M] [Module R M]
    (T : (LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X) →ₗ[R] M)
    (hT : ∀ (x : Q.nonprojective)
      (a : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) (Q.tau x).1)
      (b : LinearPaths.obj (k := R) x.1 ⟶ LinearPaths.obj (k := R) X),
      T (a ≫ meshRelation u x ≫ b) = 0)
    {F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X}
    (hF : F ∈ (CategoricalIdeal.HomIdeal.linearSpan R (meshRelations u)).hom
      (LinearPaths.obj Y) (LinearPaths.obj X)) : T F = 0 := by
  rw [CategoricalIdeal.HomIdeal.linearSpan_hom] at hF
  change F ∈ CategoricalIdeal.HomIdeal.generatedHomSubmodule R (meshRelations u) _ _ at hF
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, B, r, hr, a, b, rfl⟩ := hf
    obtain ⟨x, hA, hB, rfl⟩ := hr
    change A = LinearPaths.obj (k := R) (Q.tau x).1 at hA
    change B = LinearPaths.obj (k := R) x.1 at hB
    subst hA hB
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact hT x a b
  | zero => exact map_zero _
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul t f _ hf => rw [map_smul, hf, smul_zero]

variable {N φ u}

/-- **When the mesh relations hold, the evaluation kills the mesh ideal.** -/
theorem evL_ideal (hmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
      ((u x a.1 a.2 : Rˣ) : R) • (φ a.2 ∘ₗ φ (Q.mate x a.1 a.2)) = 0) {Y X : V}
    {F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X}
    (hF : F ∈ (CategoricalIdeal.HomIdeal.linearSpan R (meshRelations u)).hom
      (LinearPaths.obj Y) (LinearPaths.obj X)) : evL N φ F = 0 :=
  mem_ideal_induction u (evL N φ) (fun x a b ↦ by
    rw [evL_comp, evL_comp, evL_meshRelation, hmesh, LinearMap.comp_zero, LinearMap.zero_comp])
    hF

/-! ### The first-order part -/

variable (N φ) (g : ∀ {y x : V}, (y ⟶ x) → (N y →ₗ[R] N x))

/-- The `ε`-part of the evaluation of `φ + εg` on a path: `δ(p a) = φ_a δ(p) + g_a ev(p)`. -/
def δp : ∀ {Y X : V}, Quiver.Path Y X → (N Y →ₗ[R] N X)
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p a => φ a ∘ₗ δp p + g a ∘ₗ evP N φ p

theorem δp_nil (Y : V) : δp N φ g (Quiver.Path.nil : Quiver.Path Y Y) = 0 := by
  rw [δp]

theorem δp_cons {Y X Z : V} (p : Quiver.Path Y X) (a : X ⟶ Z) :
    δp N φ g (p.cons a) = φ a ∘ₗ δp N φ g p + g a ∘ₗ evP N φ p := by
  rw [δp]

theorem δp_comp {Y X : V} (p : Quiver.Path Y X) : ∀ {Z : V} (p' : Quiver.Path X Z),
    δp N φ g (p.comp p') = evP N φ p' ∘ₗ δp N φ g p + δp N φ g p' ∘ₗ evP N φ p := by
  intro Z p'
  induction p' with
  | nil => rw [Quiver.Path.comp_nil, δp_nil, evP_nil, LinearMap.id_comp, LinearMap.zero_comp,
      add_zero]
  | cons p' a ih =>
    rw [Quiver.Path.comp_cons, δp_cons, ih, δp_cons, evP_cons, evP_comp]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc]
    abel

theorem δp_toPath {Y X : V} (a : Y ⟶ X) : δp N φ g a.toPath = g a := by
  change δp N φ g (Quiver.Path.cons Quiver.Path.nil a) = _
  rw [δp_cons, δp_nil, evP_nil, LinearMap.comp_zero, LinearMap.comp_id, zero_add]

/-- The linear extension of `δp`. -/
def δL {Y X : V} : (LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X) →ₗ[R]
    (N Y →ₗ[R] N X) :=
  (Finsupp.linearCombination R (fun p : Quiver.Path Y X ↦ δp N φ g p)).comp
    (LinearPaths.finsuppEquiv (k := R) Y X).toLinearMap

theorem δL_path {Y X : V} (p : Quiver.Path Y X) :
    δL N φ g (LinearPaths.path (k := R) p) = δp N φ g p := by
  simp [δL, LinearPaths.finsuppEquiv]

theorem δL_id (Y : V) : δL N φ g (𝟙 (LinearPaths.obj (k := R) Y)) = 0 := by
  change δL N φ g (LinearPaths.path (k := R) Quiver.Path.nil) = _
  rw [δL_path, δp_nil]

/-- **`δ` is a derivation.** -/
theorem δL_comp {Y X Z : V} (F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X)
    (G : LinearPaths.obj (k := R) X ⟶ LinearPaths.obj (k := R) Z) :
    δL N φ g (F ≫ G) = evL N φ G ∘ₗ δL N φ g F + δL N φ g G ∘ₗ evL N φ F := by
  induction F using rq_induction with
  | h0 => rw [Limits.zero_comp, map_zero, map_zero, map_zero, LinearMap.comp_zero,
      LinearMap.comp_zero, add_zero]
  | hadd F F' hF hF' =>
    rw [Preadditive.add_comp, map_add, hF, hF', map_add, map_add]
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    abel
  | hsmul t F hF =>
    rw [Linear.smul_comp, map_smul, hF, map_smul, map_smul]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, smul_add]
  | hpath p =>
    induction G using rq_induction with
    | h0 => rw [Limits.comp_zero, map_zero, map_zero, map_zero, LinearMap.zero_comp,
        LinearMap.zero_comp, add_zero]
    | hadd G G' hG hG' =>
      rw [Preadditive.comp_add, map_add, hG, hG', map_add, map_add]
      simp only [LinearMap.comp_add, LinearMap.add_comp]
      abel
    | hsmul t G hG =>
      rw [Linear.comp_smul, map_smul, hG, map_smul, map_smul]
      simp only [LinearMap.comp_smul, LinearMap.smul_comp, smul_add]
    | hpath p' =>
      rw [LinearPaths.path_comp_path, δL_path, δL_path, δL_path, evL_path, evL_path, δp_comp]

theorem δL_meshRelation (x : Q.nonprojective) :
    δL N φ g (meshRelation u x) = ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : Rˣ) : R) •
      (φ a.2 ∘ₗ g (Q.mate x a.1 a.2) + g a.2 ∘ₗ φ (Q.mate x a.1 a.2)) := by
  rw [meshRelation, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, δL_path, δp_comp, δp_toPath, δp_toPath, evP_toPath, evP_toPath]

variable {N φ g}

/-- **When the mesh relations hold to first order, `δ` kills the mesh ideal.** -/
theorem δL_ideal (hmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
      ((u x a.1 a.2 : Rˣ) : R) • (φ a.2 ∘ₗ φ (Q.mate x a.1 a.2)) = 0)
    (hz : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : Rˣ) : R) •
      (φ a.2 ∘ₗ g (Q.mate x a.1 a.2) + g a.2 ∘ₗ φ (Q.mate x a.1 a.2)) = 0) {Y X : V}
    {F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X}
    (hF : F ∈ (CategoricalIdeal.HomIdeal.linearSpan R (meshRelations u)).hom
      (LinearPaths.obj Y) (LinearPaths.obj X)) : δL N φ g F = 0 :=
  mem_ideal_induction u (δL N φ g) (fun x a b ↦ by
    rw [δL_comp, δL_comp, δL_meshRelation, hz, evL_comp, evL_meshRelation, hmesh]
    simp only [LinearMap.comp_zero, LinearMap.zero_comp, zero_add, add_zero]) hF

/-! ### Lifted maps -/

section Lift

open GExt

variable {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ} {μ : Λ →ₗ[R] Λ →ₗ[R] Λ}
  {q : ℤ} {MM : ∀ X, GMod GΛ (N X)} (Lf : ∀ X, ActLift μ q (MM X))

theorem isLiftHom_id' (Y : V) : IsLiftHom (Lf Y) (Lf Y) LinearMap.id 0 :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ by simp⟩

theorem isLiftHom_zero' {Y X : V} : IsLiftHom (Lf Y) (Lf X) 0 0 :=
  ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩

variable {Lf}

theorem δp_lift (hφ : ∀ {y x : V} (a : y ⟶ x), IsLiftHom (Lf y) (Lf x) (φ a) (g a))
    {Y X : V} (p : Quiver.Path Y X) : IsLiftHom (Lf Y) (Lf X) (evP N φ p) (δp N φ g p) := by
  induction p with
  | nil => rw [evP_nil, δp_nil]; exact isLiftHom_id' Lf _
  | cons p a ih => rw [evP_cons, δp_cons]; exact (hφ a).comp ih

theorem δL_lift (hφ : ∀ {y x : V} (a : y ⟶ x), IsLiftHom (Lf y) (Lf x) (φ a) (g a))
    {Y X : V} (F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X) :
    IsLiftHom (Lf Y) (Lf X) (evL N φ F) (δL N φ g F) := by
  induction F using rq_induction with
  | h0 => rw [map_zero, map_zero]; exact isLiftHom_zero' Lf
  | hadd F G hF hG => rw [map_add, map_add]; exact hF.add hG
  | hsmul t F hF => rw [map_smul, map_smul]; exact hF.smul t
  | hpath p => rw [evL_path, δL_path]; exact δp_lift hφ p

end Lift

end PathEval

end MultiplicativeBasisDeformations
