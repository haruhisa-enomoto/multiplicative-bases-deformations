import MultiplicativeBasisDeformations.Foundations.DeletionTransfer

/-!
# Functionals on `Π(Δ)` modulo deleted vertices

Tools for the nonvanishing statements of Appendix A
(`periodic-mesh-calculations.tex:610–630`: "Assigning these values in `k` gives a
nonzero functional annihilating all the relations"). A function `g` on vertex
lists gives a functional on paths (`vfun`); it annihilates the ideal of `Π(Δ)`
modulo the deleted vertices when its values on the terms of each contextual
relation cancel and it vanishes on lists through deleted vertices
(`vfun_eq_zero_of_mem`). The constant term (`len0`) shows that the vertex
idempotents of retained vertices are nonzero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

theorem Quiver.Path.vertices_eq_cons {V : Type*} [Quiver V] {a b : V} (p : Quiver.Path a b) :
    p.vertices = a :: p.vertices.tail := by
  have h := p.vertices_head?
  cases hv : p.vertices with
  | nil => exact absurd hv p.vertices_ne_nil
  | cons x l => rw [hv] at h; simp at h; rw [h]; rfl

namespace MultiplicativeBasisDeformations

universe u v

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D) [Fintype D] [DecidableEq D] [DecidableRel T.orient]
  {k : Type u} [Field k]

/-- The functional of a function on vertex lists. -/
def vfun {x y : T.Dbl} (g : List T.Dbl → k) :
    (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) →ₗ[k] k :=
  LinearPaths.extend fun q ↦ g q.vertices

theorem vfun_path {x y : T.Dbl} (g : List T.Dbl → k) (q : Quiver.Path x y) :
    T.vfun g (LinearPaths.path q) = g q.vertices := LinearPaths.extend_path _ _

/-- The value on a contextual relation. -/
theorem vfun_rel (g : List T.Dbl → k) {x y u : T.Dbl} (p : Quiver.Path x u) (p' : Quiver.Path u y) :
    T.vfun g (LinearPaths.path p ≫ T.preprojRel k u ≫ LinearPaths.path p') =
      ∑ e : Σ w : T.Dbl, u ⟶ w, ((T.sgn k (u : D) (e.1 : D) : kˣ) : k) *
        g (p.vertices.dropLast ++ u :: e.1 :: u :: p'.vertices.tail) := by
  unfold preprojRel
  rw [Preadditive.sum_comp, Preadditive.comp_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Linear.smul_comp, Linear.comp_smul, map_smul, LinearPaths.path_comp_path,
    LinearPaths.path_comp_path, vfun_path, smul_eq_mul]
  congr 2
  rw [Quiver.Path.vertices_comp, Quiver.Path.vertices_comp, Quiver.Path.vertices_comp,
    Quiver.Path.vertices_toPath, Quiver.Path.vertices_toPath, p'.vertices_eq_cons]
  simp

/-- **A vertex-list functional annihilating the relations.** -/
theorem vfun_eq_zero_of_mem (Del : Set T.Dbl) (g : List T.Dbl → k)
    (hrel : ∀ (u : T.Dbl) (l₀ l₂ : List T.Dbl), ∑ e : Σ w : T.Dbl, u ⟶ w,
      ((T.sgn k (u : D) (e.1 : D) : kˣ) : k) * g (l₀ ++ u :: e.1 :: u :: l₂) = 0)
    (hdel : ∀ l : List T.Dbl, (∃ d ∈ l, d ∈ Del) → g l = 0) {x y : T.Dbl}
    {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y} (hf : f ∈ ((T.preproj k).del Del).ideal _ _) :
    T.vfun g f = 0 := by
  refine (T.preproj k).del_induction Del (P := fun f ↦ T.vfun g f = 0) (by simp)
    (fun f g hf hg ↦ by rw [map_add, hf, hg, add_zero])
    (fun c f hf ↦ by rw [map_smul, hf, smul_zero]) (fun i p p' ↦ ?_) (fun d hd p p' ↦ ?_) hf
  · exact (T.vfun_rel g (u := (i : T.Dbl)) p p').trans (hrel _ _ _)
  · rw [LinearPaths.path_comp_path, vfun_path]
    have hm : d ∈ (p.comp p').vertices := by
      rw [Quiver.Path.vertices_comp, List.mem_append]
      exact Or.inr (Quiver.Path.start_mem_vertices _)
    exact hdel _ ⟨d, hm, hd⟩

open Classical in
/-- The coefficient of the paths of length zero. -/
def len0 {x y : T.Dbl} : (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) →ₗ[k] k :=
  LinearPaths.extend fun q ↦ if q.length = 0 then 1 else 0

/-- **Retained vertex idempotents are nonzero** in `Π(Δ)` modulo deleted
vertices. -/
theorem nil_not_mem_del (Del : Set T.Dbl) {x : T.Dbl} (hx : x ∉ Del) :
    LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path x x) ∉ ((T.preproj k).del Del).ideal _ _ := by
  classical
  intro h
  have key : ∀ {y : T.Dbl} {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y},
      f ∈ ((T.preproj k).del Del).ideal _ _ → T.len0 f = 0 := by
    intro y f hf
    refine (T.preproj k).del_induction Del (P := fun f ↦ T.len0 f = 0) (by simp)
      (fun f g hf hg ↦ by rw [map_add, hf, hg, add_zero])
      (fun c f hf ↦ by rw [map_smul, hf, smul_zero]) (fun i p p' ↦ ?_) (fun d hd p p' ↦ ?_) hf
    · change T.len0 (LinearPaths.path p ≫ T.preprojRel k i ≫ LinearPaths.path p') = 0
      unfold preprojRel
      rw [Preadditive.sum_comp, Preadditive.comp_sum, map_sum]
      refine Finset.sum_eq_zero fun e _ ↦ ?_
      rw [Linear.smul_comp, Linear.comp_smul, map_smul, LinearPaths.path_comp_path,
        LinearPaths.path_comp_path, len0, LinearPaths.extend_path, if_neg, smul_zero]
      simp
    · rw [LinearPaths.path_comp_path, len0, LinearPaths.extend_path]
      split_ifs with hl
      · exfalso
        rw [Quiver.Path.length_comp] at hl
        have h1 : p.length = 0 := by omega
        obtain rfl := Quiver.Path.eq_of_length_zero p h1
        exact hx hd
      · rfl
  have := key h
  rw [len0, LinearPaths.extend_path] at this
  simp at this

end OrientedTree

end MultiplicativeBasisDeformations
