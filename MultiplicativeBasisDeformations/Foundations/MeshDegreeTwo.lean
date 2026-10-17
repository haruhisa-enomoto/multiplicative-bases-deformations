import MultiplicativeBasisDeformations.Foundations.PathGradingComp
import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows

/-!
# The degree-two part of the mesh ideal

Lemma 4.13 (`scalar-normalization.tex:588–592`): "Since `Φ` preserves the mesh
ideal, whose degree-two part from `τX` to `X` is spanned by the mesh relation at
`X`, it multiplies that relation by some `ν_X ∈ k*`. Comparing coefficients
gives `w(σa) w(a) = ν_X` for every mate pair at that mesh."

The mesh ideal is spanned by composites `u r_Y v`; their degree-two parts from
`τX` to `X` are those with `u, v` of degree zero, hence `Y = X` and
`u, v` scalars (`proj_two_mem_span`). A linear relation among the composites
`(σa) a` in `C(Q, c)` is therefore proportional to the mesh coefficients
(`mesh_coeffs`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

namespace ScalarMeshCategory

variable (c : MeshCoefficients k Q)

open CategoricalIdeal LinearPaths

/-- The mesh relation vanishes in `C(Q, c)`. -/
theorem mesh_sum_zero (x : Q.nonprojective) :
    ∑ a : (Σ y : V, y ⟶ x.1), ((c x a.1 a.2 : kˣ) : k) •
      (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) = 0 := by
  have hrel : meshRelation c x ∈ (HomIdeal.linearSpan k (meshRelations c)).hom _ _ :=
    HomIdeal.relation_mem_linearSpan _ ⟨x, rfl, rfl, by simp⟩
  rw [← RelationCategory.functor_map_eq_zero_iff, meshRelation, Functor.map_sum] at hrel
  rw [← hrel]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Functor.map_smul, ← LinearPaths.path_comp_path, Functor.map_comp]
  rfl

/-- The degree-two part of a two-sided composite through a mesh relation. -/
theorem proj_two_comp (x z : Q.nonprojective)
    (u : LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj (Q.tau z).1)
    (w' : LinearPaths.obj (k := k) z.1 ⟶ LinearPaths.obj x.1) :
    proj 2 _ _ (u ≫ meshRelation c z ≫ w') =
      proj 0 _ _ u ≫ meshRelation c z ≫ proj 0 _ _ w' := by
  have hr := meshRelation_mem_degreePart c z
  obtain ⟨N, hN⟩ := eq_sum_proj_of_le (k := k) u
  conv_lhs => rw [hN (max N 1) (le_max_left _ _), Preadditive.sum_comp, map_sum]
  rw [Finset.sum_eq_single 0]
  · rw [show (2 : ℕ) = 0 + 2 from rfl, proj_of_mem_comp (LinearPaths.proj_mem (d := 0) u)]
    congr 1
    rw [show (2 : ℕ) = 2 + 0 from rfl, proj_of_mem_comp hr]
  · intro d _ hd
    by_cases hd2 : d ≤ 2
    · rw [show (2 : ℕ) = d + (2 - d) by omega]
      rw [proj_of_mem_comp (LinearPaths.proj_mem (d := d) u), proj_of_mem_comp_lt hr _ (by omega),
        Limits.comp_zero]
    · exact proj_of_mem_comp_lt (LinearPaths.proj_mem (d := d) u) _ (by omega)
  · intro h
    exact absurd (Finset.mem_range.2 (lt_of_lt_of_le zero_lt_one (le_max_right _ _))) h

/-- **The degree-two part of the mesh ideal from `τX` to `X` is spanned by the
mesh relation at `X`.** -/
theorem proj_two_mem_span (x : Q.nonprojective)
    {f : LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj x.1}
    (hf : f ∈ HomIdeal.generatedHomSubmodule k (meshRelations c) _ _) :
    proj 2 _ _ f ∈ k ∙ meshRelation c x := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨A, B, r, hr, u, w', rfl⟩ := hg
      obtain ⟨A', rfl⟩ : ∃ A' : V, LinearPaths.obj (k := k) A' = A := ⟨A, rfl⟩
      obtain ⟨B', rfl⟩ : ∃ B' : V, LinearPaths.obj (k := k) B' = B := ⟨B, rfl⟩
      obtain ⟨z, hX, hY, rfl⟩ := hr
      have e : u ≫ (eqToHom hX ≫ meshRelation c z ≫ eqToHom hY.symm) ≫ w' =
          (u ≫ eqToHom hX) ≫ meshRelation c z ≫ (eqToHom hY.symm ≫ w') := by
        simp only [Category.assoc]
      rw [e, proj_two_comp]
      generalize u ≫ eqToHom hX = u
      generalize eqToHom hY.symm ≫ w' = w'
      by_cases hzx : z = x
      · subst hzx
        rw [degreePart_zero_self (LinearPaths.proj_mem (d := 0) u), degreePart_zero_self (LinearPaths.proj_mem (d := 0) w')]
        simp only [Linear.smul_comp, Linear.comp_smul]
        rw [show LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path (Q.tau z).1 (Q.tau z).1) =
          𝟙 _ from rfl, show LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path z.1 z.1) =
          𝟙 _ from rfl, Category.id_comp, Category.comp_id]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · have hne : z.1 ≠ x.1 := fun h ↦ hzx (Subtype.ext h)
        rw [degreePart_zero_of_ne hne (LinearPaths.proj_mem (d := 0) w'), Limits.comp_zero, Limits.comp_zero]
        exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul t f _ hf => rw [map_smul]; exact Submodule.smul_mem _ t hf

/-- The two-arrow path `(σ a) a` of a mesh. -/
abbrev meshPath (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) : Quiver.Path (Q.tau x).1 x.1 :=
  (Q.mate x a.1 a.2).toPath.comp a.2.toPath

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] in
theorem meshPath_injective (x : Q.nonprojective) : Function.Injective (meshPath (Q := Q) x) := by
  intro e a h
  change ((Q.mate x e.1 e.2).toPath).cons e.2 = ((Q.mate x a.1 a.2).toPath).cons a.2 at h
  exact Sigma.ext (Quiver.Path.obj_eq_of_cons_eq_cons h) (Quiver.Path.hom_heq_of_cons_eq_cons h)

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] in
theorem coeff_meshPath (x : Q.nonprojective) [Fintype (Σ y : V, y ⟶ x.1)]
    (μ : (Σ y : V, y ⟶ x.1) → k) (a : Σ y : V, y ⟶ x.1) :
    toFinsupp (∑ e, μ e • LinearPaths.path (k := k) (meshPath x e)) (meshPath x a) = μ a := by
  classical
  rw [show ∀ g : LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj x.1,
    toFinsupp g = (finsuppEquiv (Q.tau x).1 x.1) g from fun _ ↦ rfl, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply]
  rw [Finset.sum_eq_single a]
  · change μ a • (Finsupp.single (meshPath x a) (1 : k)) (meshPath x a) = μ a
    rw [Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro e _ he
    change μ e • (Finsupp.single (meshPath x e) (1 : k)) (meshPath x a) = 0
    rw [Finsupp.single_eq_of_ne (fun h ↦ he (meshPath_injective x h.symm)), smul_zero]
  · simp

/-- **Comparing coefficients**: a linear relation among the composites `(σ a) a`
is proportional to the mesh relation. -/
theorem mesh_coeffs (x : Q.nonprojective) (lam : (Σ y : V, y ⟶ x.1) → k)
    (h : ∑ a : (Σ y : V, y ⟶ x.1), lam a • (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2) = 0) :
    ∃ ν : k, ∀ a, lam a = ν * ((c x a.1 a.2 : kˣ) : k) := by
  set R : LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj x.1 :=
    ∑ a, lam a • LinearPaths.path (meshPath x a)
  have hR0 : (RelationCategory.functor k (meshRelations c)).map R = 0 := by
    rw [Functor.map_sum, ← h]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Functor.map_smul, ← LinearPaths.path_comp_path, Functor.map_comp]
    rfl
  have hRmem : R ∈ HomIdeal.generatedHomSubmodule k (meshRelations c) _ _ :=
    (RelationCategory.functor_map_eq_zero_iff (k := k) _ R).1 hR0
  have hR2 : R ∈ LinearPaths.degreePart (k := k) 2 (Q.tau x).1 x.1 := by
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ ?_
    have := LinearPaths.path_mem_degreePart (k := k) (meshPath x a)
    simpa using this
  have hspan := proj_two_mem_span c x hRmem
  rw [proj_of_mem hR2, if_pos rfl] at hspan
  obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.1 hspan
  refine ⟨ν, fun a ↦ ?_⟩
  have := congrArg (fun f ↦ toFinsupp f (meshPath x a)) hν
  rw [coeff_meshPath x lam a, meshRelation, Finset.smul_sum] at this
  simp_rw [smul_smul] at this
  rw [coeff_meshPath x (fun e ↦ ν * ((c x e.1 e.2 : kˣ) : k)) a] at this
  exact this.symm

end ScalarMeshCategory

end MultiplicativeBasisDeformations
