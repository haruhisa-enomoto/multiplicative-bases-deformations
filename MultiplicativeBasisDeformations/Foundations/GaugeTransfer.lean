module

public import MultiplicativeBasisDeformations.Foundations.MeshGauge
public import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows

/-!
# Gauge transformations preserve derivative surjectivity

Appendix A (`periodic-mesh-calculations.tex`): "rescaling arrows and
entire relations changes the mesh derivative by invertible diagonal maps, so it
changes neither its cokernel nor the brick property." For
`c'_{x,a} = η_x c_{x,a} μ_{σ a} μ_a`, the gauge functor `kQ → kQ` descends to a
functor `Φ : C(Q, c) → C(Q, c')` with `Φ(a) = μ_a a`; and for `f'_a = μ_a⁻¹ Φ(f_a)`,
`D'(f') = η Φ(D f)`. Hence each row of `C(Q, c')` lies in the image of `D'_m`
when the corresponding row of `C(Q, c)` lies in that of `D_m`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]

/-- The gauge functor on the linear path category. -/
def gaugeFunctor (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) : LinearPaths k V ⥤ LinearPaths k V where
  obj X := X
  map {X Y} f := gaugeMap μ X Y f
  map_id X := by
    change gaugeMap μ X X (LinearPaths.path Quiver.Path.nil) = LinearPaths.path Quiver.Path.nil
    rw [gaugeMap_path]; simp [pathWt]
  map_comp f g := gaugeMap_comp μ f g

variable {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

namespace ScalarMeshCategory

variable (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ) (c c' : MeshCoefficients k Q)
  (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
    c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a)

/-- The induced functor `C(Q, c) → C(Q, c')`. -/
def gaugeQ : ScalarMeshCategory k Q c ⥤ ScalarMeshCategory k Q c' :=
  CategoryTheory.Quotient.lift _ (gaugeFunctor μ ⋙ RelationCategory.functor k (meshRelations c'))
    fun X Y f₁ f₂ hf ↦ by
      change (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ X Y f₁) =
        (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ X Y f₂)
      rw [← sub_eq_zero, ← Functor.map_sub, ← map_sub,
        RelationCategory.functor_map_eq_zero_iff]
      exact gaugeMap_mem_ideal μ η c c' h hf

include h in
theorem gaugeQ_map (x y : V) (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    (gaugeQ μ η c c' h).map ((RelationCategory.functor k (meshRelations c)).map f) =
      (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ x y f) := rfl

theorem gaugeQ_obj (x : V) : (gaugeQ μ η c c' h).obj (obj c x) = obj c' x := rfl

theorem gaugeQ_pathMor {x y : V} (p : Quiver.Path x y) :
    (gaugeQ μ η c c' h).map (pathMor c p) = ((pathWt μ p : kˣ) : k) • pathMor c' p := by
  rw [pathMor, gaugeQ_map, gaugeMap_path, Functor.map_smul]; rfl

theorem gaugeQ_arrowMor {x y : V} (a : x ⟶ y) :
    (gaugeQ μ η c c' h).map (arrowMor c a) = ((μ a : kˣ) : k) • arrowMor c' a := by
  rw [← pathMor_toPath, gaugeQ_pathMor, pathWt_toPath]; rfl

theorem gaugeQ_map_add {x y : V} (f g : obj c x ⟶ obj c y) :
    (gaugeQ μ η c c' h).map (f + g) = (gaugeQ μ η c c' h).map f + (gaugeQ μ η c c' h).map g := by
  obtain ⟨f, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) f
  obtain ⟨g, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) g
  rw [← Functor.map_add]
  change (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ x y (f + g)) =
    (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ x y f) +
      (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ x y g)
  rw [map_add, Functor.map_add]

theorem gaugeQ_map_smul {x y : V} (t : k) (f : obj c x ⟶ obj c y) :
    (gaugeQ μ η c c' h).map (t • f) = t • (gaugeQ μ η c c' h).map f := by
  obtain ⟨f, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) f
  rw [← Functor.map_smul]
  change (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ x y (t • f)) =
    t • (RelationCategory.functor k (meshRelations c')).map (gaugeMap μ x y f)
  rw [map_smul, Functor.map_smul]

theorem gaugeQ_map_zero {x y : V} :
    (gaugeQ μ η c c' h).map (0 : obj c x ⟶ obj c y) = 0 := by
  have := gaugeQ_map_smul μ η c c' h (0 : k) (0 : obj c x ⟶ obj c y)
  rwa [zero_smul, zero_smul] at this

theorem gaugeQ_mem_degreePart {x y : V} {n : ℕ} {f : obj c x ⟶ obj c y}
    (hf : f ∈ degreePart c n x y) : (gaugeQ μ η c c' h).map f ∈ degreePart c' n x y := by
  rw [degreePart_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      rw [gaugeQ_pathMor, ← hp]
      exact Submodule.smul_mem _ _ (pathMor_mem_degreePart c' p)
  | zero => rw [gaugeQ_map_zero]; exact zero_mem _
  | add f g _ _ hf hg => rw [gaugeQ_map_add]; exact add_mem hf hg
  | smul t f _ hf => rw [gaugeQ_map_smul]; exact Submodule.smul_mem _ _ hf

theorem gaugeQ_map_sum {x y : V} {ι : Type*} (S : Finset ι) (f : ι → (obj c x ⟶ obj c y)) :
    (gaugeQ μ η c c' h).map (∑ i ∈ S, f i) = ∑ i ∈ S, (gaugeQ μ η c c' h).map (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact gaugeQ_map_zero μ η c c' h
  | insert i S hi ih => rw [Finset.sum_insert hi, gaugeQ_map_add, ih, Finset.sum_insert hi]

/-- The transported family `f'_a = μ_a⁻¹ Φ(f_a)`. -/
def gaugeFamily (f : ArrowFamily c) : ArrowFamily c' :=
  fun a ↦ (((μ a.2.2)⁻¹ : kˣ) : k) • (gaugeQ μ η c c' h).map (f a)

/-- **The derivative is changed by an invertible diagonal map**:
`D'(f') = η Φ(D f)`. -/
theorem meshDerivative_gauge (f : ArrowFamily c) (x : Q.nonprojective) :
    meshDerivative c' (gaugeFamily μ η c c' h f) x =
      ((η x : kˣ) : k) • (gaugeQ μ η c c' h).map (meshDerivative c f x) := by
  unfold meshDerivative gaugeFamily
  rw [gaugeQ_map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [gaugeQ_map_smul, gaugeQ_map_add, Functor.map_comp, Functor.map_comp, gaugeQ_arrowMor,
    gaugeQ_arrowMor, h]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_add, smul_smul, Units.val_mul]
  have hσ : (μ (Q.mate x a.1 a.2) : k) * ((μ (Q.mate x a.1 a.2))⁻¹ : kˣ) = 1 := Units.mul_inv _
  have ha : (μ a.2 : k) * ((μ a.2)⁻¹ : kˣ) = 1 := Units.mul_inv _
  congr 1 <;> congr 1
  · linear_combination ((η x : k) * (c x a.1 a.2 : k) * (μ a.2 : k)) * hσ
  · linear_combination ((η x : k) * (c x a.1 a.2 : k) * (μ (Q.mate x a.1 a.2) : k)) * ha

/-- The degree of the transported family. -/
theorem gaugeFamily_mem {m : ℕ} {f : ArrowFamily c} (hf : f ∈ familiesDeg c m) :
    gaugeFamily μ η c c' h f ∈ familiesDeg c' m := fun a ↦
  Submodule.smul_mem _ _ (gaugeQ_mem_degreePart μ η c c' h (hf a))

variable [DecidableEq V]

include h in
/-- **Rows transfer along a gauge transformation.** -/
theorem row_mem_imageD_gauge {m : ℕ} (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1)
    (hw : row c x w ∈ imageD c m) : row c' x w ∈ imageD c' m := by
  obtain ⟨f, hf, hDf⟩ := hw
  set e : kˣ := η x * pathWt μ w
  refine ⟨((e⁻¹ : kˣ) : k) • gaugeFamily μ η c c' h f,
    Submodule.smul_mem _ _ (gaugeFamily_mem μ η c c' h hf), ?_⟩
  rw [map_smul, meshDerivativeₗ_apply]
  funext x'
  rw [Pi.smul_apply, meshDerivative_gauge]
  change ((e⁻¹ : kˣ) : k) • ((η x' : k) • (gaugeQ μ η c c' h).map (meshDerivativeₗ c f x')) = _
  rw [hDf]
  by_cases hx : x' = x
  · subst hx
    simp only [row, Pi.single_eq_same, gaugeQ_pathMor, smul_smul]
    rw [show ((e⁻¹ : kˣ) : k) * ((η x' : k) * (pathWt μ w : k)) = 1 by
      rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]
  · simp only [row, Pi.single_eq_of_ne hx]
    rw [gaugeQ_map_zero, smul_zero, smul_zero]

include h in
/-- **Surjectivity of `D_m` is gauge invariant.** -/
theorem surjective_gauge [Fintype Q.nonprojective] [∀ x y : V, DecidableEq (x ⟶ y)]
    [DecidablePred (· ∈ Q.nonprojective)] {m : ℕ}
    (hS : MeshDerivativeSurjective c m) : MeshDerivativeSurjective c' m := by
  rw [surjective_iff_rows] at hS ⊢
  exact fun x w hw ↦ row_mem_imageD_gauge μ η c c' h x w (hS x w hw)

include h in
theorem gauge_symm (x : Q.nonprojective) (y : V) (a : y ⟶ x.1) :
    c x y a = (η x)⁻¹ * c' x y a * (μ (Q.mate x y a))⁻¹ * (μ a)⁻¹ := by
  rw [h]
  apply Units.ext
  simp only [Units.val_mul]
  have h1 : ((η x)⁻¹ : kˣ).val * (η x).val = 1 := Units.inv_mul _
  have h2 : (μ (Q.mate x y a) : k) * ((μ (Q.mate x y a))⁻¹ : kˣ) = 1 := Units.mul_inv _
  have h3 : (μ a : k) * ((μ a)⁻¹ : kˣ) = 1 := Units.mul_inv _
  linear_combination (-(c x y a : k) * ((μ (Q.mate x y a) : k) *
    ((μ (Q.mate x y a))⁻¹ : kˣ)) * ((μ a : k) * ((μ a)⁻¹ : kˣ))) * h1 -
    (c x y a : k) * ((μ a : k) * ((μ a)⁻¹ : kˣ)) * h2 - (c x y a : k) * h3

end ScalarMeshCategory

end MultiplicativeBasisDeformations
