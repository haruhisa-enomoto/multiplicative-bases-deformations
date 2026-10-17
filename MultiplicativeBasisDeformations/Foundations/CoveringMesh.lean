import MultiplicativeBasisDeformations.Foundations.TreeRepetition
import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows

/-!
# Mesh relations along a covering `ℤΔ → Q`

The general form of `SectionalMesh`: for any covering `π : ℤΔ → Q` commuting
with translation, pulling the coefficients of `Q` back along `π` makes `π` map
the mesh relation at `X` to the mesh relation at `π X`, so `π` preserves the
mesh ideal (`periodic-mesh-calculations.tex`). This is how the twisted
trace calculation (Lemma A.2) passes relations downstairs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v v' w

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D)
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)

/-- The vertex `π X`, as a nonprojective vertex of `Q`. -/
def piNP (X : T.ZVert) : Q.nonprojective := ⟨π.obj X, hQ.mem_nonprojective _⟩

variable {k : Type u} [CommRing k]

/-- The coefficients of `Q`, pulled back along `π`. -/
def pullCoeff (c : MeshCoefficients k Q) : MeshCoefficients k T.zQuiver :=
  fun X Y a ↦ c (T.piNP hQ π X.1) (π.obj Y) (π.map a)

variable [Fintype D] [DecidableEq D] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))

theorem path_two_eq {u u' y z : V} (e : u = u') (f : u ⟶ y) (g : u' ⟶ y) (h : y ⟶ z) :
    LinearPaths.path (k := k) (f.toPath.comp h.toPath) =
      eqToHom (by rw [e]) ≫ LinearPaths.path (g.toPath.comp h.toPath) := by
  subst e
  rw [Subsingleton.elim f g]
  simp

include hπ in
/-- The mesh relation of `ℤΔ` at `X` maps to the mesh relation of `Q` at `π X`. -/
theorem mapPaths_meshRelation (c : MeshCoefficients k Q) (X : T.zQuiver.nonprojective) :
    LinearPaths.mapPaths (k := k) π _ _ (meshRelation (T.pullCoeff hQ π c) X) =
      eqToHom (by rw [show π.obj (T.zQuiver.tau X).1 = (Q.tau (T.piNP hQ π X.1)).1 from
          hτ X.1]) ≫ meshRelation c (T.piNP hQ π X.1) := by
  unfold meshRelation
  rw [map_sum, Preadditive.comp_sum]
  refine Fintype.sum_bijective _ (hπ.costar_bijective X.1) _ _ fun a ↦ ?_
  rw [map_smul, Linear.comp_smul, LinearPaths.mapPaths_path, Prefunctor.mapPath_comp,
    Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath]
  congr 1
  exact path_two_eq (hτ X.1) _ _ _

include hπ hτ in
/-- `π` maps the mesh ideal of `ℤΔ` into that of `Q`. -/
theorem mapPaths_mem_mesh (c : MeshCoefficients k Q) {X Y : T.ZVert}
    {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ (RelSystem.mesh (T.pullCoeff hQ π c)).ideal _ _) :
    LinearPaths.mapPaths π X Y f ∈ (RelSystem.mesh c).ideal _ _ := by
  refine RelSystem.mapPaths_mem_ideal _ _ _ (fun i p p' ↦ ?_) hf
  have h1 := (RelSystem.mesh c).comp_rel_comp_mem (T.piNP hQ π i.1)
    (LinearPaths.path (π.mapPath p) ≫
      eqToHom (congrArg (LinearPaths.obj (k := k)) (hτ i.1)))
    (LinearPaths.path (π.mapPath p'))
  have h2 : LinearPaths.mapPaths (k := k) π _ _
      (LinearPaths.path p ≫ (RelSystem.mesh (T.pullCoeff hQ π c)).rel i ≫ LinearPaths.path p') =
      (LinearPaths.path (π.mapPath p) ≫
        eqToHom (congrArg (LinearPaths.obj (k := k)) (hτ i.1))) ≫
        (RelSystem.mesh c).rel (T.piNP hQ π i.1) ≫ LinearPaths.path (π.mapPath p') := by
    rw [LinearPaths.mapPaths_comp, LinearPaths.mapPaths_comp, LinearPaths.mapPaths_path,
      LinearPaths.mapPaths_path, RelSystem.mesh_rel, RelSystem.mesh_rel]
    erw [T.mapPaths_meshRelation hQ π hπ hτ c i]
    simp only [Category.assoc]
  rw [h2]
  exact h1

end OrientedTree

end MultiplicativeBasisDeformations
