import MultiplicativeBasisDeformations.Foundations.SectionalMesh
import MultiplicativeBasisDeformations.Foundations.ZDeltaGauge

/-!
# Long paths vanish in `Π(Δ)`

Proof of Proposition 4.1, Steps 1–2 (`periodic-mesh-calculations.tex:61–91`):
"In particular every upstairs path of length at least `N` is zero ... Forgetting
the integer coordinate identifies the lifted mesh relations with its relations,
and every path lifts. The uniform path bound makes `Π(Δ)` finite-dimensional."

A path of the doubled tree lifts to `ℤΔ` (`forget` is a covering), its image
under `π` is a long path of `Q`, hence zero; `π` reflects the mesh ideal, the
rescaling of Step 2 moves it to the signed mesh ideal, and forgetting heights
lands in the ideal of `Π(Δ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) {x₀ : V} {k : Type u} [Field k]
  [Fintype (Q.SecPath x₀)] [DecidableEq (Q.SecPath x₀)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

namespace SecPath

include hQ in
/-- **Every path of length at least `N` vanishes in `Π(Δ)`**, if every path of
length at least `N` vanishes in `C(Q, c)`. -/
theorem path_mem_preproj [DecidableRel (SecPath.tree (Q := Q) (x₀ := x₀)).orient]
    (c : MeshCoefficients k Q) (N : ℕ)
    (hN : ∀ (x y : V) (p : Quiver.Path x y), N ≤ p.length →
      LinearPaths.path (k := k) p ∈ (RelSystem.mesh c).ideal _ _)
    {v w : (SecPath.tree (Q := Q) (x₀ := x₀)).Dbl} (P : Quiver.Path v w) (hP : N ≤ P.length) :
    LinearPaths.path (k := k) P ∈ ((SecPath.tree (Q := Q) (x₀ := x₀)).preproj k).ideal _ _ := by
  let X₀ : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert := ⟨v, (v : Q.SecPath x₀).len, rfl⟩
  obtain ⟨Y, e, P', hP'⟩ := RelSystem.exists_lift (SecPath.tree (Q := Q) (x₀ := x₀)).forget
    (SecPath.tree (Q := Q) (x₀ := x₀)).forget_isCovering X₀
    (show Quiver.Path ((SecPath.tree (Q := Q) (x₀ := x₀)).forget.obj X₀) w from P)
  subst e
  have hlen : P'.length = P.length := by
    rw [← LinearPaths.length_mapPath (SecPath.tree (Q := Q) (x₀ := x₀)).forget P', hP']
    rfl
  -- the image in `Q` is long, hence zero
  have h1 : LinearPaths.mapPaths (k := k) (piQ hQ (x₀ := x₀)) _ _ (LinearPaths.path P') ∈
      (RelSystem.mesh c).ideal _ _ := by
    rw [LinearPaths.mapPaths_path]
    exact hN _ _ _ (by rw [LinearPaths.length_mapPath, hlen]; exact hP)
  have h2 := mem_mesh_of_mapPaths hQ c h1
  obtain ⟨μ, hμ⟩ := (SecPath.tree (Q := Q) (x₀ := x₀)).exists_gauge (pullCoeff hQ c)
  have h3 := path_mem_of_gauge μ (fun _ ↦ 1) (pullCoeff hQ c)
    ((SecPath.tree (Q := Q) (x₀ := x₀)).zSigned k) hμ P' h2
  have h4 := (SecPath.tree (Q := Q) (x₀ := x₀)).forget_mem_preproj k h3
  rw [LinearPaths.mapPaths_path, hP'] at h4
  simp only [Quiver.Path.cast_rfl_rfl] at h4
  exact h4

end SecPath

end TranslationQuiver

end MultiplicativeBasisDeformations
