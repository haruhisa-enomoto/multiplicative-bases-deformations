import MultiplicativeBasisDeformations.Foundations.PathGrading
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Linear maps out of path categories

A morphism of `kQ` is a finite linear combination of paths, so any function on
paths extends linearly (`LinearPaths.extend`); if the function is
multiplicative on paths, so is its extension (`extend_comp`). Two instances
are used repeatedly:

* a quiver morphism `φ` induces `LinearPaths.mapPaths φ : kQ → kQ'`, sending a
  path to its image;
* for a full subquiver, sending a path to its lift when all of its vertices lie
  in the subquiver, and to zero otherwise, is multiplicative (in
  `FullSubquiver.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w v' w' u₂ v₂

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]

namespace LinearPaths

section Extend

variable {M : Type u₂} [AddCommGroup M] [Module k M]

/-- The linear extension of a function on the paths from `x` to `y`. -/
def extend {x y : V} (g : Quiver.Path x y → M) : (obj (k := k) x ⟶ obj (k := k) y) →ₗ[k] M :=
  (Finsupp.linearCombination k g).comp (finsuppEquiv (k := k) x y).toLinearMap

@[simp] theorem extend_path {x y : V} (g : Quiver.Path x y → M) (p : Quiver.Path x y) :
    extend (k := k) g (path p) = g p := by
  change Finsupp.linearCombination k g (Finsupp.single p 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

end Extend

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- The linear extension of a multiplicative function on paths is
multiplicative. -/
theorem extend_comp (F : V → D) (g : ∀ {x y : V}, Quiver.Path x y → (F x ⟶ F y))
    (hg : ∀ {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z), g (p.comp q) = g p ≫ g q)
    {x y z : V} (f : obj (k := k) x ⟶ obj y) (f' : obj (k := k) y ⟶ obj z) :
    extend (k := k) g (f ≫ f') = extend (k := k) g f ≫ extend (k := k) g f' := by
  induction f using induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, Preadditive.add_comp]
  | hsingle p c =>
      induction f' using induction_on with
      | h0 => simp
      | hadd g₁ g₂ h₁ h₂ =>
          rw [Preadditive.comp_add, map_add, map_add, h₁, h₂, Preadditive.comp_add]
      | hsingle q c' =>
          rw [Linear.smul_comp, Linear.comp_smul, path_comp_path, map_smul, map_smul,
            map_smul, map_smul, extend_path, extend_path, extend_path, hg,
            Linear.smul_comp, Linear.comp_smul]

theorem extend_mem_of_forall {x y : V} {M : Type u₂} [AddCommGroup M] [Module k M]
    (g : Quiver.Path x y → M) (N : Submodule k M) {d : ℕ}
    (hg : ∀ p : Quiver.Path x y, p.length = d → g p ∈ N) {f : obj (k := k) x ⟶ obj y}
    (hf : f ∈ degreePart (k := k) d x y) : extend (k := k) g f ∈ N := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      rw [extend_path]; exact hg p hp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul t a _ ha => rw [map_smul]; exact N.smul_mem t ha

end LinearPaths

namespace LinearPaths

variable {W : Type v'} [Quiver.{w'} W] (φ : V ⥤q W)

theorem length_mapPath {x y : V} (p : Quiver.Path x y) : (φ.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => simp [Prefunctor.mapPath_cons, ih]

theorem vertices_mapPath {x y : V} (p : Quiver.Path x y) :
    (φ.mapPath p).vertices = p.vertices.map φ.obj := by
  induction p with
  | nil => rfl
  | cons p a ih => simp [Prefunctor.mapPath_cons, ih]

/-- The linear functor `kQ → kQ'` induced by a quiver morphism, on Hom spaces. -/
def mapPaths (x y : V) :
    (obj (k := k) x ⟶ obj (k := k) y) →ₗ[k] (obj (k := k) (φ.obj x) ⟶ obj (k := k) (φ.obj y)) :=
  extend (k := k) fun p ↦ path (φ.mapPath p)

@[simp] theorem mapPaths_path {x y : V} (p : Quiver.Path x y) :
    mapPaths (k := k) φ x y (path p) = path (φ.mapPath p) :=
  extend_path _ p

theorem mapPaths_comp {x y z : V} (f : obj (k := k) x ⟶ obj y) (f' : obj (k := k) y ⟶ obj z) :
    mapPaths (k := k) φ x z (f ≫ f') = mapPaths φ x y f ≫ mapPaths φ y z f' :=
  extend_comp (D := LinearPaths k W) (fun x ↦ obj (φ.obj x))
    (fun p ↦ path (φ.mapPath p))
    (fun p q ↦ by rw [Prefunctor.mapPath_comp, path_comp_path]) f f'

theorem mapPaths_arrow {x y : V} (a : x ⟶ y) :
    mapPaths (k := k) φ x y (arrow a) = arrow (φ.map a) := by
  rw [arrow, mapPaths_path, Prefunctor.mapPath_toPath]; rfl

theorem mapPaths_mem_degreePart {d : ℕ} {x y : V} {f : obj (k := k) x ⟶ obj y}
    (hf : f ∈ degreePart (k := k) d x y) :
    mapPaths (k := k) φ x y f ∈ degreePart (k := k) d (φ.obj x) (φ.obj y) :=
  extend_mem_of_forall _ _ (fun p hp ↦ by
    rw [← hp, ← length_mapPath φ p]; exact path_mem_degreePart _) hf

end LinearPaths

end MultiplicativeBasisDeformations
