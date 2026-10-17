import MultiplicativeBasisDeformations.Foundations.CoveringIdeals

/-!
# Rescaling arrows and mesh relations

`graded-category.tex:174–190` and Appendix A
(`periodic-mesh-calculations.tex:65–79, 236–241`): "rescaling arrows and entire
mesh relations changes the mesh derivative by invertible diagonal maps". Given
arrow scalars `μ` and relation scalars `η` with
`c'_{x,a} = η_x c_{x,a} μ_{σ a} μ_a`, the linear functor `kQ → kQ` multiplying
each path by the product of the scalars of its arrows (`gaugeMap`) sends the
mesh relation `r_x(c)` to `η_x⁻¹ r_x(c')`, hence the mesh ideal of `c` into that
of `c'` (`gaugeMap_mem_ideal`). A single path therefore lies in one ideal iff it
lies in the other.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]

/-- The weight of a path: the product of the scalars of its arrows. -/
def pathWt (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) {x : V} : ∀ {y : V}, Quiver.Path x y → kˣ
  | _, Quiver.Path.nil => 1
  | _, Quiver.Path.cons p a => pathWt μ p * μ a

theorem pathWt_comp (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) {x y z : V} (p : Quiver.Path x y)
    (q : Quiver.Path y z) : pathWt μ (p.comp q) = pathWt μ p * pathWt μ q := by
  induction q with
  | nil => simp [pathWt]
  | cons q a ih => simp [pathWt, Quiver.Path.comp_cons, ih, mul_assoc]

theorem pathWt_toPath (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) {x y : V} (a : x ⟶ y) :
    pathWt μ a.toPath = μ a := by
  simp [pathWt, Quiver.Hom.toPath]

/-- Multiplying each path by its weight. -/
def gaugeMap (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (x y : V) :
    (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) →ₗ[k]
      (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :=
  LinearPaths.extend (k := k) fun p ↦ ((pathWt μ p : kˣ) : k) • LinearPaths.path p

theorem gaugeMap_path (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) {x y : V} (p : Quiver.Path x y) :
    gaugeMap (k := k) μ x y (LinearPaths.path p) = ((pathWt μ p : kˣ) : k) • LinearPaths.path p :=
  LinearPaths.extend_path _ _

theorem gaugeMap_comp (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) {x y z : V}
    (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y)
    (g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    gaugeMap μ x z (f ≫ g) = gaugeMap μ x y f ≫ gaugeMap μ y z g :=
  LinearPaths.extend_comp (D := LinearPaths k V) (fun x ↦ LinearPaths.obj x)
    (fun p ↦ ((pathWt μ p : kˣ) : k) • LinearPaths.path p)
    (fun p q ↦ by
      rw [pathWt_comp, Linear.smul_comp, Linear.comp_smul, smul_smul, LinearPaths.path_comp_path,
        Units.val_mul, mul_comm]) f g

variable {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- **Gauge transformations of mesh relations.** -/
theorem gaugeMap_meshRelation (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
    (c c' : MeshCoefficients k Q)
    (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a)
    (x : Q.nonprojective) :
    gaugeMap μ _ _ (meshRelation c x) = ((η x)⁻¹ : kˣ) • meshRelation c' x := by
  unfold meshRelation
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, gaugeMap_path, smul_smul, pathWt_comp, pathWt_toPath, pathWt_toPath,
    Units.smul_def, smul_smul]
  congr 1
  rw [h]
  have hη : ((η x)⁻¹ : kˣ).val * (η x).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Units.val_mul]
  linear_combination (-(↑(c x a.fst a.snd) * (↑(μ ((Q.mate x a.fst) a.snd)) * ↑(μ a.snd)) : k)) * hη

/-- A gauge transformation maps the mesh ideal of `c` into that of `c'`. -/
theorem gaugeMap_mem_ideal (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
    (c c' : MeshCoefficients k Q)
    (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a)
    {X Y : V} {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ (RelSystem.mesh c).ideal _ _) :
    gaugeMap μ X Y f ∈ (RelSystem.mesh c').ideal _ _ := by
  refine (RelSystem.mesh c).ideal_induction
    (P := fun f ↦ gaugeMap μ X Y f ∈ (RelSystem.mesh c').ideal _ _) (by simp)
    (fun f g hf hg ↦ by rw [map_add]; exact add_mem hf hg)
    (fun t f hf ↦ by rw [map_smul]; exact Submodule.smul_mem _ t hf) (fun i p p' ↦ ?_) hf
  rw [gaugeMap_comp, gaugeMap_comp, gaugeMap_path, gaugeMap_path, RelSystem.mesh_rel]
  erw [gaugeMap_meshRelation μ η c c' h i]
  rw [Units.smul_def, Linear.smul_comp, Linear.comp_smul,
    Linear.smul_comp, Linear.comp_smul, Linear.comp_smul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    ((RelSystem.mesh c').comp_rel_comp_mem i _ _)))

/-- A single path lies in the mesh ideal of `c'` if it lies in that of `c`. -/
theorem path_mem_of_gauge (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
    (c c' : MeshCoefficients k Q)
    (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a)
    {X Y : V} (P : Quiver.Path X Y)
    (hP : LinearPaths.path (k := k) P ∈ (RelSystem.mesh c).ideal _ _) :
    LinearPaths.path (k := k) P ∈ (RelSystem.mesh c').ideal _ _ := by
  have := gaugeMap_mem_ideal μ η c c' h hP
  rw [gaugeMap_path] at this
  have h2 := Submodule.smul_mem _ (((pathWt μ P)⁻¹ : kˣ) : k) this
  rwa [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h2

end MultiplicativeBasisDeformations
