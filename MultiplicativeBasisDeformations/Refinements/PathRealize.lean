import MultiplicativeBasisDeformations.Foundations.PathMaps

/-!
# Realizing the path category by chosen arrows (toward Proposition 12.8)

Given morphisms `g a : F y ⟶ F x` of a `k`-linear category for the arrows `a : y ⟶ x` of a
quiver, paths are realized by composition (`pathR`) and the `k`-linear path category `kQ` by
linear extension (`realizeR`); the realization is a functor (`realizeR_comp`). This is the
realization `kQ → ℳ` by lifted arrows of `deformation-refinements.tex`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace PathReal

variable {k : Type*} [Field k] {V : Type} [Quiver.{0} V] {𝒞 : Type*} [Category 𝒞]
  [Preadditive 𝒞] [Linear k 𝒞] {F : V → 𝒞} (g : ∀ {y x : V}, (y ⟶ x) → (F y ⟶ F x))

/-- The realization of a path. -/
def pathR {x : V} : ∀ {y : V}, Quiver.Path x y → (F x ⟶ F y)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p a => pathR p ≫ g a

@[simp] theorem pathR_nil {x : V} : pathR g (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ := rfl

@[simp] theorem pathR_cons {x y z : V} (p : Quiver.Path x y) (a : y ⟶ z) :
    pathR g (p.cons a) = pathR g p ≫ g a := rfl

theorem pathR_comp {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    pathR g (p.comp q) = pathR g p ≫ pathR g q := by
  induction q with
  | nil => simp
  | cons q a ih => simp [Quiver.Path.comp_cons, ih, Category.assoc]

theorem pathR_toPath {x y : V} (a : x ⟶ y) : pathR g a.toPath = g a := by
  simp [Quiver.Hom.toPath]

variable (k) in
/-- **The realization of the path category.** -/
def realizeR (x y : V) : (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj (k := k) y) →ₗ[k] (F x ⟶ F y) :=
  LinearPaths.extend (k := k) (pathR g (x := x) (y := y))

theorem realizeR_path {x y : V} (p : Quiver.Path x y) :
    realizeR k g x y (LinearPaths.path p) = pathR g p := by
  simp [realizeR]

theorem realizeR_arrow {x y : V} (a : x ⟶ y) :
    realizeR k g x y (LinearPaths.arrow a) = g a := by
  rw [LinearPaths.arrow, realizeR_path, pathR_toPath]

theorem realizeR_comp {x y z : V} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y)
    (h : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    realizeR k g x z (f ≫ h) = realizeR k g x y f ≫ realizeR k g y z h := by
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, Preadditive.add_comp]
  | hsingle p c =>
      induction h using LinearPaths.induction_on with
      | h0 => simp
      | hadd h₁' h₂' e₁ e₂ =>
          rw [Preadditive.comp_add, map_add, map_add, e₁, e₂, Preadditive.comp_add]
      | hsingle q c' =>
          rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path, map_smul, map_smul,
            map_smul, map_smul, realizeR_path, realizeR_path, realizeR_path, pathR_comp,
            Linear.smul_comp, Linear.comp_smul]

end PathReal

end MultiplicativeBasisDeformations
