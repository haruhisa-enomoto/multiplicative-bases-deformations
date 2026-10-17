import MultiplicativeBasisDeformations.Foundations.FormFunctor
import MultiplicativeBasisDeformations.Foundations.GradedLocal
import MultiplicativeBasisDeformations.Foundations.LocalMesh

/-!
# Exact meshes of a scalar mesh category and their descent to a prime field

The mesh data of a scalar mesh category `C(Q, c)` (`CatAlg.MeshData`): the right mesh maps are
the arrows into each vertex, the left ones the coefficient-scaled mates, and the mesh sequences
are exact (`MeshExact`). For `k(Γ_A)` this is Proposition 2.6(1)(2) (`IndSkeleton.arMeshData`).

`integral-deformations.tex:31–34`: the prime-field model `C⁽²⁾` inherits these properties
"since it does so after the faithful field extension to `k`". Here (`MeshExact.descend`):
exactness of the meshes of `C(Q, c)` over `k`, for a gauge `c = η · (ι ∘ u) · μ μ`, implies that of
`C(Q, u)` over the subfield `K`, through the form functor and its retractions (`FormFunctor`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u w

namespace ScalarMeshCategory

open LinearPaths

section Exact

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

/-- The coefficient-scaled mate arrow `c_{x,a} σa : τx → y`. -/
abbrev qArr (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) : obj c (Q.tau x).1 ⟶ obj c a.1 :=
  ((c x a.1 a.2 : kˣ) : k) • arrowMor c (Q.mate x a.1 a.2)

/-- The mesh relation holds in `C(Q, c)`. -/
theorem qArr_comp_zero (x : Q.nonprojective) :
    ∑ a : Σ y : V, y ⟶ x.1, qArr c x a ≫ arrowMor c a.2 = 0 := by
  have hrel : meshRelation c x ∈ (CategoricalIdeal.HomIdeal.linearSpan k (meshRelations c)).hom
      (LinearPaths.obj (Q.tau x).1) (LinearPaths.obj x.1) :=
    CategoricalIdeal.HomIdeal.relation_mem_linearSpan _ ⟨x, rfl, rfl, by simp⟩
  rw [← RelationCategory.functor_map_eq_zero_iff, meshRelation, Functor.map_sum] at hrel
  rw [← hrel]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Functor.map_smul, Linear.smul_comp, ← LinearPaths.path_comp_path, Functor.map_comp]
  rfl

/-- **Exact meshes** (Proposition 2.6(1)(2) for `k(Γ_A)`). -/
structure MeshExact : Prop where
  cov_exact : ∀ (x : Q.nonprojective) (w : V) (g : ∀ a : Σ y : V, y ⟶ x.1, obj c w ⟶ obj c a.1),
    ∑ a, g a ≫ arrowMor c a.2 = 0 →
      ∃ z : obj c w ⟶ obj c (Q.tau x).1, ∀ a, g a = z ≫ qArr c x a
  cov_mono : ∀ (x : Q.nonprojective) (w : V) (z : obj c w ⟶ obj c (Q.tau x).1),
    (∀ a, z ≫ qArr c x a = 0) → z = 0
  contra_exact : ∀ (x : Q.nonprojective) (w : V) (v : ∀ a : Σ y : V, y ⟶ x.1, obj c a.1 ⟶ obj c w),
    ∑ a, qArr c x a ≫ v a = 0 → ∃ u : obj c x.1 ⟶ obj c w, ∀ a, v a = arrowMor c a.2 ≫ u
  contra_mono : ∀ (x : Q.nonprojective) (w : V) (u : obj c x.1 ⟶ obj c w),
    (∀ a : Σ y : V, y ⟶ x.1, arrowMor c a.2 ≫ u = 0) → u = 0
  proj_mono : ∀ (x : V), x ∉ Q.nonprojective → ∀ (w : V)
    (g : ∀ a : Σ y : V, y ⟶ x, obj c w ⟶ obj c a.1), ∑ a, g a ≫ arrowMor c a.2 = 0 → ∀ a, g a = 0

variable {c}

open Classical in
/-- **The mesh data of a scalar mesh category with exact meshes.** -/
def meshDataOf (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) (hE : MeshExact c) :
    CatAlg.MeshData (fun x : V ↦ obj c x) (localFamily c hfin) where
  Mid x := Σ y : V, y ⟶ x
  fin _ := inferInstance
  decMid _ := Classical.decEq _
  mid _ a := a.1
  p _ a := arrowMor c a.2
  p_rad _ a := arrowMor_mem_radN c a.2
  image _ _ _ hf := exists_lastArrow c hf
  proj x := x ∉ Q.nonprojective
  decProj := Classical.decPred _
  tau x hx := (Q.tau ⟨x, not_not.1 hx⟩).1
  q x hx a := qArr c ⟨x, not_not.1 hx⟩ a
  comp_zero x hx := qArr_comp_zero c ⟨x, not_not.1 hx⟩
  cov_exact x hx w g hg := hE.cov_exact ⟨x, not_not.1 hx⟩ w g hg
  cov_mono x hx w z hz := hE.cov_mono ⟨x, not_not.1 hx⟩ w z hz
  contra_exact x hx w v hv := hE.contra_exact ⟨x, not_not.1 hx⟩ w v hv
  contra_mono x hx w u hu := hE.contra_mono ⟨x, not_not.1 hx⟩ w u hu
  proj_mono x hx w g hg := hE.proj_mono x hx w g hg

end Exact

/-! ### Descent along the form functor -/

section Descent

variable {K : Type} [Field K] {k : Type u} [Field k] [Algebra K k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (u : MeshCoefficients K Q) (c₁ c : MeshCoefficients k Q)
  (hred : ∀ x y a, algebraMap K k (u x y a : K) = (c₁ x y a : k))
  (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
  (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
    c x y a = η x * c₁ x y a * μ (Q.mate x y a) * μ a)

include hred in
theorem Fm_qArr (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) :
    Fm u c₁ c μ η h (qArr u x a) = (((η x * μ a.2)⁻¹ : kˣ) : k) • qArr c x a := by
  rw [qArr, Fm_smul u c₁ c hred, Fm_arrowMor u c₁ c hred, qArr, smul_smul, smul_smul, hred, h]
  congr 1
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

include hred h in
/-- **Exactness of the meshes descends to the subfield.** -/
theorem MeshExact.descend (hE : MeshExact c) : MeshExact u := by
  obtain ⟨θ, h1⟩ := exists_retraction (K := K) (k := k)
  have FmA : ∀ {x y : V} (a : x ⟶ y), Fm u c₁ c μ η h (arrowMor u a) =
      ((μ a : kˣ) : k) • arrowMor c a := fun a ↦ Fm_arrowMor u c₁ c hred μ η h a
  refine ⟨fun x w g hg ↦ ?_, fun x w z hz ↦ ?_, fun x w v hv ↦ ?_, fun x w v hv ↦ ?_,
    fun x hx w g hg a ↦ ?_⟩
  · -- covariant exactness
    have hk : ∑ a, (((μ a.2 : kˣ) : k) • Fm u c₁ c μ η h (g a)) ≫ arrowMor c a.2 = 0 := by
      have := congrArg (Fm u c₁ c μ η h) hg
      rw [Fm_sum u c₁ c hred, Fm_zero u c₁ c hred] at this
      rw [← this]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Fm_comp u c₁ c hred, FmA, Linear.smul_comp, Linear.comp_smul]
    obtain ⟨z, hz⟩ := hE.cov_exact x w _ hk
    refine ⟨retF u c₁ c μ η h θ (((η x : kˣ) : k) • z), fun a ↦ ?_⟩
    have e : Fm u c₁ c μ η h (g a) = (((η x : kˣ) : k) • z) ≫ Fm u c₁ c μ η h (qArr u x a) := by
      rw [Fm_qArr u c₁ c hred μ η h, Linear.comp_smul, Linear.smul_comp, smul_smul, ← hz a,
        smul_smul]
      have hs : (((η x * μ a.2)⁻¹ : kˣ) : k) * ((η x : kˣ) : k) * ((μ a.2 : kˣ) : k) = 1 := by
        simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
      rw [hs, one_smul]
    rw [← retF_Fm u c₁ c hred μ η h θ h1 (g a), e, retF_comp_Fm u c₁ c hred]
  · -- covariant injectivity
    apply Fm_injective u c₁ c hred μ η h
    rw [Fm_zero u c₁ c hred]
    apply hE.cov_mono x w
    intro a
    have := congrArg (Fm u c₁ c μ η h) (hz a)
    rw [Fm_comp u c₁ c hred, Fm_qArr u c₁ c hred μ η h, Fm_zero u c₁ c hred, Linear.comp_smul]
      at this
    have hu := (smul_eq_zero.1 this).resolve_left (Units.ne_zero _)
    exact hu
  · -- contravariant exactness
    have hk : ∑ a, qArr c x a ≫ ((((η x * μ a.2)⁻¹ : kˣ) : k) • Fm u c₁ c μ η h (v a)) = 0 := by
      have := congrArg (Fm u c₁ c μ η h) hv
      rw [Fm_sum u c₁ c hred, Fm_zero u c₁ c hred] at this
      rw [← this]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Fm_comp u c₁ c hred, Fm_qArr u c₁ c hred μ η h]
      simp only [Linear.smul_comp, Linear.comp_smul]
    obtain ⟨t, ht⟩ := hE.contra_exact x w _ hk
    refine ⟨retF u c₁ c μ η h θ (((η x : kˣ) : k) • t), fun a ↦ ?_⟩
    have e : Fm u c₁ c μ η h (v a) = Fm u c₁ c μ η h (arrowMor u a.2) ≫
        (((η x : kˣ) : k) • t) := by
      rw [FmA, Linear.comp_smul, Linear.smul_comp, smul_smul, ← ht a, smul_smul]
      have hs : ((η x : kˣ) : k) * ((μ a.2 : kˣ) : k) * (((η x * μ a.2)⁻¹ : kˣ) : k) = 1 := by
        simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
      rw [hs, one_smul]
    rw [← retF_Fm u c₁ c hred μ η h θ h1 (v a), e, retF_Fm_comp u c₁ c hred]
  · -- contravariant injectivity
    apply Fm_injective u c₁ c hred μ η h
    rw [Fm_zero u c₁ c hred]
    apply hE.contra_mono x w
    intro a
    have := congrArg (Fm u c₁ c μ η h) (hv a)
    rw [Fm_comp u c₁ c hred, FmA, Fm_zero u c₁ c hred, Linear.smul_comp] at this
    exact (smul_eq_zero.1 this).resolve_left (Units.ne_zero _)
  · -- projective injectivity
    have hk : ∑ a, (((μ a.2 : kˣ) : k) • Fm u c₁ c μ η h (g a)) ≫ arrowMor c a.2 = 0 := by
      have := congrArg (Fm u c₁ c μ η h) hg
      rw [Fm_sum u c₁ c hred, Fm_zero u c₁ c hred] at this
      rw [← this]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Fm_comp u c₁ c hred, FmA, Linear.smul_comp, Linear.comp_smul]
    have := hE.proj_mono x hx w _ hk a
    apply Fm_injective u c₁ c hred μ η h
    rw [Fm_zero u c₁ c hred]
    exact (smul_eq_zero.1 this).resolve_left (Units.ne_zero _)

end Descent

end ScalarMeshCategory

end MultiplicativeBasisDeformations
