module

public import MultiplicativeBasisDeformations.Foundations.ReductionMesh

/-!
# Base change of scalar mesh categories along a field extension

`integral-deformations.tex` (Section 10): "The all-one meshes […] define a graded category
`C⁽²⁾` with `k ⊗_{𝔽₂} C⁽²⁾ = C`. […] Evaluation identifies `C⁽²⁾` with their full Hom category,
since it does so after the faithful field extension to `k`."

For a field extension `K → k` and coefficients `u` over `K`, extension of coefficients
`redE : C(Q, u) → C(Q, ι ∘ u)` (`ReductionMesh`) is controlled by the *coefficient retractions*:
for every `K`-linear `θ : k → K`, applying `θ` to the coefficients of path combinations
(`retP`) maps the mesh ideal over `k` into the mesh ideal over `K`, so it descends to
`retE u θ : C(Q, ι ∘ u)(x, y) → C(Q, u)(x, y)`. It is a bimodule map over the morphisms coming
from `K` (`retE_comp_redE`, `retE_redE_comp`) and `retE u θ (λ • redE φ) = θ λ • φ`. Consequently
`redE` is injective, carries `K`-independent families to `k`-independent ones, its image spans,
and the Hom spaces over `K` and `k` have the same dimension (`finrank_redE`).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace LinearPaths

variable {K : Type} [Field K] {k : Type u} [Field k] [Algebra K k] {V : Type v} [Quiver.{w} V]
  (θ : k →ₗ[K] K)

/-- **The coefficient retraction** `kQ → KQ` along a `K`-linear map `θ : k → K`. -/
def retP {x y : V} : (obj (k := k) x ⟶ obj (k := k) y) →+ (obj (k := K) x ⟶ obj (k := K) y) where
  toFun f := ofFinsupp (Finsupp.mapRange θ (map_zero θ) (toFinsupp f))
  map_zero' := by simp; rfl
  map_add' f g := by
    change ofFinsupp (Finsupp.mapRange θ _ (toFinsupp f + toFinsupp g)) = _
    rw [Finsupp.mapRange_add (map_add θ)]; rfl

theorem retP_smul_path {x y : V} (t : k) (p : Quiver.Path x y) :
    retP θ (t • path (k := k) p) = θ t • path (k := K) p := by
  change ofFinsupp (Finsupp.mapRange θ (map_zero θ) (t • Finsupp.single p (1 : k))) =
    ofFinsupp (θ t • Finsupp.single p (1 : K))
  rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    Finsupp.mapRange_single]

theorem θ_mul_algebraMap (t : k) (a : K) : θ (t * algebraMap K k a) = a * θ t := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem retP_smul_redP {x y : V} (t : k) (f : obj (k := K) x ⟶ obj (k := K) y) :
    retP θ (t • redP (algebraMap K k) f) = θ t • f := by
  induction f using induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, smul_add, map_add, hf, hg, smul_add]
  | hsingle p a =>
      rw [redP_smul_path, smul_smul, retP_smul_path, θ_mul_algebraMap, smul_smul, mul_comm]

theorem retP_redP (h1 : θ 1 = 1) {x y : V} (f : obj (k := K) x ⟶ obj (k := K) y) :
    retP θ (redP (algebraMap K k) f) = f := by
  have := retP_smul_redP θ 1 f
  rwa [one_smul, h1, one_smul] at this

theorem retP_algSmul {x y : V} (a : K) (f : obj (k := k) x ⟶ obj (k := k) y) :
    retP θ (algebraMap K k a • f) = a • retP θ f := by
  induction f using induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [smul_add, map_add, hf, hg, map_add, smul_add]
  | hsingle p t =>
      rw [smul_smul, retP_smul_path, retP_smul_path, smul_smul, mul_comm, θ_mul_algebraMap]

theorem retP_comp_redP {x y z : V} (g : obj (k := k) x ⟶ obj (k := k) y)
    (f : obj (k := K) y ⟶ obj (k := K) z) :
    retP θ (g ≫ redP (algebraMap K k) f) = retP θ g ≫ f := by
  induction g using induction_on with
  | h0 => simp
  | hadd g₁ g₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Preadditive.add_comp]
  | hsingle q t =>
      induction f using induction_on with
      | h0 => simp
      | hadd f₁ f₂ h₁ h₂ =>
          rw [map_add, Preadditive.comp_add, map_add, h₁, h₂, Preadditive.comp_add]
      | hsingle p a =>
          rw [redP_smul_path, Linear.smul_comp, Linear.comp_smul, path_comp_path, smul_smul,
            retP_smul_path, retP_smul_path, Linear.smul_comp, Linear.comp_smul, path_comp_path,
            smul_smul, θ_mul_algebraMap, mul_comm]

theorem retP_redP_comp {x y z : V} (f : obj (k := K) x ⟶ obj (k := K) y)
    (g : obj (k := k) y ⟶ obj (k := k) z) :
    retP θ (redP (algebraMap K k) f ≫ g) = f ≫ retP θ g := by
  induction g using induction_on with
  | h0 => simp
  | hadd g₁ g₂ h₁ h₂ => rw [Preadditive.comp_add, map_add, h₁, h₂, map_add, Preadditive.comp_add]
  | hsingle q t =>
      induction f using induction_on with
      | h0 => simp
      | hadd f₁ f₂ h₁ h₂ =>
          rw [map_add, Preadditive.add_comp, map_add, h₁, h₂, Preadditive.add_comp]
      | hsingle p a =>
          rw [redP_smul_path, Linear.smul_comp, Linear.comp_smul, path_comp_path, smul_smul,
            retP_smul_path, retP_smul_path, Linear.smul_comp, Linear.comp_smul, path_comp_path,
            smul_smul, mul_comm, θ_mul_algebraMap]

end LinearPaths

namespace ScalarMeshCategory

open LinearPaths

variable {K : Type} [Field K] {k : Type u} [Field k] [Algebra K k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {u : MeshCoefficients K Q} {c : MeshCoefficients k Q}
  (hred : ∀ x y a, algebraMap K k (u x y a : K) = (c x y a : k)) (θ : k →ₗ[K] K)

include hred in
/-- **The retraction maps the mesh ideal over `k` into the mesh ideal over `K`.** -/
theorem retP_mem_ideal {X Y : V} {g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj (k := k) Y}
    (hg : g ∈ (RelSystem.mesh c).ideal _ _) (t : k) :
    retP θ (t • g) ∈ (RelSystem.mesh u).ideal _ _ := by
  revert t
  refine (RelSystem.mesh c).ideal_induction
    (P := fun g ↦ ∀ t : k, retP θ (t • g) ∈ (RelSystem.mesh u).ideal _ _)
    (fun t ↦ by rw [smul_zero, map_zero]; exact zero_mem _)
    (fun f g hf hg t ↦ by rw [smul_add, map_add]; exact add_mem (hf t) (hg t))
    (fun s f hf t ↦ by rw [smul_smul]; exact hf _) (fun i p p' t ↦ ?_) hg
  have e : LinearPaths.path (k := k) p ≫ (RelSystem.mesh c).rel i ≫ LinearPaths.path p' =
      redP (algebraMap K k) (LinearPaths.path p ≫ (RelSystem.mesh u).rel i ≫ LinearPaths.path p') := by
    rw [redP_comp, redP_comp, redP_path, redP_path]
    congr 2
    exact (redP_meshRelation hred (show Q.nonprojective from i)).symm
  rw [e, retP_smul_redP]
  exact Submodule.smul_mem _ _ ((RelSystem.mesh u).comp_rel_comp_mem i _ _)

variable (u) in
/-- **The retraction on the scalar mesh category.** -/
def retE {X Y : V} (φ : obj c X ⟶ obj c Y) : obj u X ⟶ obj u Y :=
  (RelationCategory.functor K (meshRelations u)).map
    (retP θ (Classical.choose (RelationCategory.functor_map_surjective (k := k) _ φ)))

include hred in
theorem retE_map {X Y : V} (Φ : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj (k := k) Y) :
    retE u θ ((RelationCategory.functor k (meshRelations c)).map Φ) =
      (RelationCategory.functor K (meshRelations u)).map (retP θ Φ) := by
  rw [retE, ← sub_eq_zero, ← Functor.map_sub, ← map_sub, RelationCategory.functor_map_eq_zero_iff]
  have h := Classical.choose_spec (RelationCategory.functor_map_surjective (k := k)
    (meshRelations c) ((RelationCategory.functor k (meshRelations c)).map Φ))
  rw [← sub_eq_zero, ← Functor.map_sub, RelationCategory.functor_map_eq_zero_iff] at h
  have := retP_mem_ideal hred θ h 1
  rwa [one_smul] at this

include hred in
theorem retE_add {X Y : V} (φ ψ : obj c X ⟶ obj c Y) : retE u θ (φ + ψ) = retE u θ φ + retE u θ ψ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ φ
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ ψ
  rw [← Functor.map_add, retE_map hred, retE_map hred, retE_map hred, map_add, Functor.map_add]

include hred in
theorem retE_zero {X Y : V} : retE u θ (0 : obj c X ⟶ obj c Y) = 0 := by
  rw [← Functor.map_zero (RelationCategory.functor k (meshRelations c)) (LinearPaths.obj X)
    (LinearPaths.obj Y), retE_map hred, map_zero, Functor.map_zero]

include hred in
theorem retE_sub {X Y : V} (φ ψ : obj c X ⟶ obj c Y) : retE u θ (φ - ψ) = retE u θ φ - retE u θ ψ := by
  rw [eq_sub_iff_add_eq, ← retE_add hred, sub_add_cancel]

include hred in
theorem retE_sum {X Y : V} {ι : Type*} (s : Finset ι) (φ : ι → (obj c X ⟶ obj c Y)) :
    retE u θ (∑ i ∈ s, φ i) = ∑ i ∈ s, retE u θ (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [retE_zero hred]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, retE_add hred, ih]

include hred in
theorem retE_algSmul {X Y : V} (a : K) (φ : obj c X ⟶ obj c Y) :
    retE u θ (algebraMap K k a • φ) = a • retE u θ φ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ φ
  rw [← Functor.map_smul, retE_map hred, retE_map hred, retP_algSmul, Functor.map_smul]

include hred in
theorem retE_smul_redE {X Y : V} (t : k) (φ : obj u X ⟶ obj u Y) :
    retE u θ (t • redE (algebraMap K k) u c φ) = θ t • φ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := K) _ φ
  rw [redE_map hred, ← Functor.map_smul, retE_map hred, retP_smul_redP, Functor.map_smul]

include hred in
theorem retE_redE (h1 : θ 1 = 1) {X Y : V} (φ : obj u X ⟶ obj u Y) :
    retE u θ (redE (algebraMap K k) u c φ) = φ := by
  have := retE_smul_redE hred θ 1 φ
  rwa [one_smul, h1, one_smul] at this

include hred in
theorem retE_comp_redE {X Y Z : V} (ψ : obj c X ⟶ obj c Y) (φ : obj u Y ⟶ obj u Z) :
    retE u θ (ψ ≫ redE (algebraMap K k) u c φ) = retE u θ ψ ≫ φ := by
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ ψ
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := K) _ φ
  rw [redE_map hred, ← Functor.map_comp, retE_map hred, retE_map hred, retP_comp_redP,
    Functor.map_comp]

include hred in
theorem retE_redE_comp {X Y Z : V} (φ : obj u X ⟶ obj u Y) (ψ : obj c Y ⟶ obj c Z) :
    retE u θ (redE (algebraMap K k) u c φ ≫ ψ) = φ ≫ retE u θ ψ := by
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ ψ
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := K) _ φ
  rw [redE_map hred, ← Functor.map_comp, retE_map hred, retE_map hred, retP_redP_comp,
    Functor.map_comp]

/-! ### Consequences: injectivity, independence, spanning, dimension -/

/-- A `K`-linear retraction `k → K` of the scalars. -/
theorem exists_retraction : ∃ θ : k →ₗ[K] K, θ 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K k)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap K k).injective)
  refine ⟨g, ?_⟩
  have := LinearMap.congr_fun hg 1
  simpa using this

include hred in
theorem redE_injective {X Y : V} : Function.Injective
    (redE (algebraMap K k) u c : (obj u X ⟶ obj u Y) → (obj c X ⟶ obj c Y)) := by
  obtain ⟨θ, h1⟩ := exists_retraction (K := K) (k := k)
  intro φ ψ h
  rw [← retE_redE hred θ h1 φ, h, retE_redE hred θ h1]

include hred in
/-- **`K`-independent families stay independent over `k`.** -/
theorem linearIndependent_redE {X Y : V} {ι : Type*} {f : ι → (obj u X ⟶ obj u Y)}
    (hf : LinearIndependent K f) : LinearIndependent k (fun i ↦ redE (algebraMap K k) u c (f i)) := by
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hg i hi
  have key : ∀ θ : k →ₗ[K] K, θ (g i) = 0 := by
    intro θ
    have h := congrArg (retE u θ) hg
    rw [retE_sum hred, retE_zero hred] at h
    simp only [retE_smul_redE hred] at h
    exact hf s (fun j ↦ θ (g j)) h i hi
  exact (Module.forall_dual_apply_eq_zero_iff K (g i)).1 key

include hred in
/-- **The image of `redE` spans.** -/
theorem span_redE {X Y : V} :
    Submodule.span k (Set.range (redE (algebraMap K k) u c : (obj u X ⟶ obj u Y) → _)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro φ
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ φ
  induction Φ using LinearPaths.induction_on with
  | h0 => rw [Functor.map_zero]; exact zero_mem _
  | hadd F G hF hG => rw [Functor.map_add]; exact add_mem hF hG
  | hsingle p t =>
      rw [Functor.map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨pathMor u p, ?_⟩)
      rw [pathMor, redE_map hred, redP_path]

include hred in
/-- **Equal dimensions**: `C(Q, u)(x, y)` over `K` and `C(Q, ι ∘ u)(x, y)` over `k`. -/
theorem finiteDimensional_finrank_redE {X Y : V} [FiniteDimensional k (obj c X ⟶ obj c Y)] :
    FiniteDimensional K (obj u X ⟶ obj u Y) ∧
      Module.finrank K (obj u X ⟶ obj u Y) = Module.finrank k (obj c X ⟶ obj c Y) := by
  classical
  let b := Module.Basis.ofVectorSpace K (obj u X ⟶ obj u Y)
  have hli := linearIndependent_redE hred b.linearIndependent
  have : Finite (Module.Basis.ofVectorSpaceIndex K (obj u X ⟶ obj u Y)) := hli.finite
  have : FiniteDimensional K (obj u X ⟶ obj u Y) := Module.Finite.of_basis b
  refine ⟨inferInstance, ?_⟩
  have hsp : Submodule.span k (Set.range fun i ↦ redE (algebraMap K k) u c (b i)) = ⊤ := by
    refine eq_top_iff.2 ((span_redE hred).ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨φ, rfl⟩
    rw [← b.sum_repr φ, redE_sum hred]
    · refine Submodule.sum_mem _ fun i _ ↦ ?_
      have : redE (algebraMap K k) u c (b.repr φ i • b i) =
          algebraMap K k (b.repr φ i) • redE (algebraMap K k) u c (b i) := by
        rw [redE_smul hred]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli (le_of_eq hsp.symm)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end ScalarMeshCategory

end MultiplicativeBasisDeformations
