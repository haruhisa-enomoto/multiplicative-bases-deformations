import MultiplicativeBasisDeformations.Foundations.SectionalCover

/-!
# Mesh relations along the covering `ℤΔ → Q`

Proof of Proposition 4.1, Step 1 (`periodic-mesh-calculations.tex`).
Pull the coefficients of `Q` back along `π`. The mesh relation of `ℤΔ` at `X`
maps to the mesh relation of `Q` at `π X`, so `π` preserves the mesh ideal; and
every mesh relation of `Q` starting at `π Z` lifts to one starting at `Z`, so
`π` reflects it (`RelSystem.mem_ideal_of_mapPaths_mem`). In particular, if
paths of length at least `N` vanish in `C(Q, c)`, they vanish upstairs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Function

namespace MultiplicativeBasisDeformations

universe u v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) {x₀ : V}

namespace SecPath

/-- The vertex `π X`, as a nonprojective vertex of `Q`. -/
def piNP (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) : Q.nonprojective :=
  ⟨piV hQ x₀ X, hQ.mem_nonprojective _⟩

variable {k : Type u} [Field k]

/-- The coefficients of `Q`, pulled back to `ℤΔ`. -/
def pullCoeff (c : MeshCoefficients k Q) :
    MeshCoefficients k (SecPath.tree (Q := Q) (x₀ := x₀)).zQuiver :=
  fun X Y a ↦ c (piNP hQ X.1) (piV hQ x₀ Y) ((piQ hQ (x₀ := x₀)).map a)

theorem toPath_eq_cast {u u' y : V} (e : u = u') (f : u ⟶ y) (g : u' ⟶ y) :
    f.toPath = g.toPath.cast e.symm rfl := by
  subst e
  rw [Subsingleton.elim f g]
  rfl

theorem path_two_eq {u u' y z : V} (e : u = u') (f : u ⟶ y) (g : u' ⟶ y) (h : y ⟶ z) :
    LinearPaths.path (k := k) (f.toPath.comp h.toPath) =
      eqToHom (by rw [e]) ≫ LinearPaths.path (g.toPath.comp h.toPath) := by
  subst e
  rw [Subsingleton.elim f g]
  simp

variable [Fintype (Q.SecPath x₀)] [DecidableEq (Q.SecPath x₀)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- The mesh relation of `ℤΔ` at `X` maps to the mesh relation of `Q` at `π X`. -/
theorem mapPaths_meshRelation (c : MeshCoefficients k Q)
    (X : (SecPath.tree (Q := Q) (x₀ := x₀)).zQuiver.nonprojective) :
    LinearPaths.mapPaths (k := k) (piQ hQ (x₀ := x₀)) _ _ (meshRelation (pullCoeff hQ c) X) =
      eqToHom (by rw [show (piQ hQ (x₀ := x₀)).obj
          ((SecPath.tree (Q := Q) (x₀ := x₀)).zQuiver.tau X).1 = (Q.tau (piNP hQ X.1)).1 from
          piV_ztau hQ X.1]) ≫ meshRelation c (piNP hQ X.1) := by
  unfold meshRelation
  rw [map_sum, Preadditive.comp_sum]
  refine Fintype.sum_bijective _ (piQ_costar_bijective hQ X.1) _ _ fun a ↦ ?_
  rw [map_smul, Linear.comp_smul, LinearPaths.mapPaths_path, Prefunctor.mapPath_comp,
    Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath]
  congr 1
  exact path_two_eq (piV_ztau hQ X.1) _ _ _

/-- `π` maps the mesh ideal of `ℤΔ` into that of `Q`. -/
theorem mapPaths_mem_mesh (c : MeshCoefficients k Q) {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert}
    {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ (RelSystem.mesh (pullCoeff hQ c)).ideal _ _) :
    LinearPaths.mapPaths (piQ hQ (x₀ := x₀)) X Y f ∈ (RelSystem.mesh c).ideal _ _ := by
  refine RelSystem.mapPaths_mem_ideal _ _ _ (fun i p p' ↦ ?_) hf
  have h1 := (RelSystem.mesh c).comp_rel_comp_mem (piNP hQ i.1)
    (LinearPaths.path ((piQ hQ (x₀ := x₀)).mapPath p) ≫
      eqToHom (congrArg (LinearPaths.obj (k := k)) (piV_ztau hQ (x₀ := x₀) i.1)))
    (LinearPaths.path ((piQ hQ (x₀ := x₀)).mapPath p'))
  have h2 : LinearPaths.mapPaths (k := k) (piQ hQ (x₀ := x₀)) _ _
      (LinearPaths.path p ≫ (RelSystem.mesh (pullCoeff hQ c)).rel i ≫ LinearPaths.path p') =
      (LinearPaths.path ((piQ hQ (x₀ := x₀)).mapPath p) ≫
        eqToHom (congrArg (LinearPaths.obj (k := k)) (piV_ztau hQ (x₀ := x₀) i.1))) ≫
        (RelSystem.mesh c).rel (piNP hQ i.1) ≫ LinearPaths.path ((piQ hQ (x₀ := x₀)).mapPath p') := by
    rw [LinearPaths.mapPaths_comp, LinearPaths.mapPaths_comp, LinearPaths.mapPaths_path,
      LinearPaths.mapPaths_path, RelSystem.mesh_rel, RelSystem.mesh_rel]
    erw [mapPaths_meshRelation hQ c i]
    simp only [Category.assoc]
  rw [h2]
  exact h1

/-- **`π` reflects the mesh ideal.** -/
theorem mem_mesh_of_mapPaths (c : MeshCoefficients k Q)
    {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert}
    {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : LinearPaths.mapPaths (piQ hQ (x₀ := x₀)) X Y f ∈ (RelSystem.mesh c).ideal _ _) :
    f ∈ (RelSystem.mesh (pullCoeff hQ c)).ideal _ _ := by
  refine RelSystem.mem_ideal_of_mapPaths_mem _ _ _ (piQ_isCovering hQ)
    (RelSystem.lift_condition _ (piQ_isCovering hQ) _ _ ?_) hf
  intro Z i' h
  have e : (SecPath.tree (Q := Q) (x₀ := x₀)).ztau
      ((SecPath.tree (Q := Q) (x₀ := x₀)).ztauInv Z) = Z := by
    ext <;> simp [OrientedTree.ztau, OrientedTree.ztauInv]
  have ht : i'.1 = piV hQ x₀ ((SecPath.tree (Q := Q) (x₀ := x₀)).ztauInv Z) := by
    apply hQ.tauE.injective
    rw [← piV_ztau, e]
    exact h
  have hi : i' = piNP hQ ((SecPath.tree (Q := Q) (x₀ := x₀)).ztauInv Z) := Subtype.ext ht
  subst hi
  refine ⟨⟨(SecPath.tree (Q := Q) (x₀ := x₀)).ztauInv Z, trivial⟩, e, rfl, ?_⟩
  change LinearPaths.mapPaths _ _ _ (meshRelation (pullCoeff hQ c) _) = _
  rw [mapPaths_meshRelation]
  simp

end SecPath

end TranslationQuiver

end MultiplicativeBasisDeformations
