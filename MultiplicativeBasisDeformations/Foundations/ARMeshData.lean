import MultiplicativeBasisDeformations.Foundations.ARMeshExactness
import MultiplicativeBasisDeformations.Foundations.ARMeshFinite
import MultiplicativeBasisDeformations.Foundations.GradedLocal
import MultiplicativeBasisDeformations.Foundations.PathGradingComp
import MultiplicativeBasisDeformations.Foundations.LocalMesh

/-!
# The mesh data of `k(Γ_A)`

Lemma 2.7 and Proposition 2.6(1)(2) for `C = k(Γ_A)` in the form used by the
proof of Proposition 2.10 (`graded-category.tex`): the categorical
radical of `C` is its positive-degree part (`ScalarMeshCategory.localFamily`),
the right mesh maps at `x` are the arrows ending at `x`, and at a nonprojective
`x` the sequences

`0 → C(W, τx) → ⊕_a C(W, E_a) → C(W, x)` and `0 → C(x, W) → ⊕_a C(E_a, W) → C(τx, W)`

are exact, with first map given by `c_{x,a} (σa)`; at a projective `x` the
right mesh map is a monomorphism. Exactness is reduced to homogeneous families
of paths (`ARMeshExactness.lean`) by the path-length grading.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The local structure of `k(Γ_A)`. -/
def arLocal : CatAlg.LocalFamily (k := k) (fun x : S.ARVertex ↦ S.meshObj b x) :=
  ScalarMeshCategory.localFamily (S.arCoefficients b) (S.finiteDimensional_meshHom b)

/-- The degree-`(e+1)` component of a sum over the arrows ending at `Y`. -/
theorem proj_sum_comp_arrow (e : ℕ) {W Y : S.ARVertex}
    (G : ∀ a : Σ X : S.ARVertex, X ⟶ Y, LinearPaths.obj (k := k) W ⟶ LinearPaths.obj a.1) :
    LinearPaths.proj (k := k) (e + 1) W Y (∑ a : (Σ X : S.ARVertex, X ⟶ Y), G a ≫ LinearPaths.arrow a.2) =
      ∑ a : (Σ X : S.ARVertex, X ⟶ Y), LinearPaths.proj (k := k) e W a.1 (G a) ≫ LinearPaths.arrow a.2 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact LinearPaths.proj_comp_of_mem (m := 1) (d := e) (G a)
    (LinearPaths.arrow_mem_degreePart (k := k) a.2)

theorem proj_mem_meshIdeal (e : ℕ) {X Y : S.ARVertex}
    {F : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y} (hF : F ∈ (S.meshIdeal b).hom _ _) :
    LinearPaths.proj (k := k) e X Y F ∈ (S.meshIdeal b).hom _ _ :=
  LinearPaths.proj_mem_linearSpan _
    (meshRelations_homogeneous (V := S.ARVertex) (Q := S.arTranslationQuiver)
      (S.arCoefficients b)) e hF

theorem map_eq_of_sub_mem {X Y : S.ARVertex} {F G : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (h : F - G ∈ (S.meshIdeal b).hom _ _) : (S.meshQuot b).map F = (S.meshQuot b).map G := by
  rw [← sub_eq_zero, ← Functor.map_sub, S.meshQuot_map_eq_zero_iff]
  exact h

theorem map_eq_sum_proj {X Y : S.ARVertex} {F : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    {N : ℕ} (hN : F = ∑ e ∈ Finset.range N, LinearPaths.proj (k := k) e X Y F) :
    (S.meshQuot b).map F = ∑ e ∈ Finset.range N, (S.meshQuot b).map (LinearPaths.proj (k := k) e X Y F) := by
  conv_lhs => rw [hN]
  rw [Functor.map_sum]

theorem proj_sum_arrow_comp (e : ℕ) {W : S.ARVertex} (y : S.nonprojectiveVertices)
    (V : ∀ a : Σ X : S.ARVertex, X ⟶ y.1, LinearPaths.obj (k := k) a.1 ⟶ LinearPaths.obj W) :
    LinearPaths.proj (k := k) (e + 1) _ W
      (∑ a : (Σ X : S.ARVertex, X ⟶ y.1), ((S.arCoefficients b y a.1 a.2 : kˣ) : k) •
        (LinearPaths.arrow (S.arTranslationQuiver.mate y a.1 a.2) ≫ V a)) =
      ∑ a : (Σ X : S.ARVertex, X ⟶ y.1), ((S.arCoefficients b y a.1 a.2 : kˣ) : k) •
        (LinearPaths.arrow (S.arTranslationQuiver.mate y a.1 a.2) ≫
          LinearPaths.proj (k := k) e a.1 W (V a)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, add_comm]
  congr 1
  exact LinearPaths.proj_of_mem_comp (m := 1) (d := e)
    (LinearPaths.arrow_mem_degreePart (k := k) _) (V a)

/-- `map` of an arrow is the arrow morphism. -/
theorem map_arrow {X Y : S.ARVertex} (a : X ⟶ Y) :
    (S.meshQuot b).map (LinearPaths.arrow (k := k) a) =
      ScalarMeshCategory.arrowMor (S.arCoefficients b) a := rfl

theorem mem_of_proj_mem {X Y : S.ARVertex} {F : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (h : ∀ e, LinearPaths.proj (k := k) e X Y F ∈ (S.meshIdeal b).hom _ _) :
    F ∈ (S.meshIdeal b).hom _ _ := by
  obtain ⟨N, hN⟩ := LinearPaths.eq_sum_proj (k := k) F
  rw [hN]
  exact sum_mem fun e _ ↦ h e

/-- Covariant exactness at a nonprojective vertex. -/
theorem ar_cov_exact (x : S.ARVertex) (hx : x ∈ S.nonprojectiveVertices) (w : S.ARVertex)
    (g : ∀ a : Σ y : S.ARVertex, y ⟶ x, S.meshObj b w ⟶ S.meshObj b a.1)
    (hg : ∑ a : (Σ y : S.ARVertex, y ⟶ x),
      g a ≫ ScalarMeshCategory.arrowMor (S.arCoefficients b) a.2 = 0) :
    ∃ z : S.meshObj b w ⟶ S.meshObj b (S.arTranslationQuiver.tau ⟨x, hx⟩).1,
      ∀ a, g a = z ≫ (((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
        ScalarMeshCategory.arrowMor (S.arCoefficients b)
          (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2)) := by
  choose G hG using fun a ↦ (S.meshQuot b).map_surjective (g a)
  have hsum : ∑ a : (Σ y : S.ARVertex, y ⟶ x), G a ≫ LinearPaths.arrow a.2 ∈
      (S.meshIdeal b).hom _ _ := by
    rw [← S.meshQuot_map_eq_zero_iff, Functor.map_sum, ← hg]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Functor.map_comp, hG]; rfl
  obtain ⟨N, hN⟩ := LinearPaths.exists_sum_proj_family (k := k) (x := fun _ ↦ w)
    (y := fun a : (Σ y : S.ARVertex, y ⟶ x) ↦ a.1) G
  have hcomp : ∀ e, ∃ H : LinearPaths.obj (k := k) w ⟶
      LinearPaths.obj (S.arTranslationQuiver.tau ⟨x, hx⟩).1,
      ∀ a, LinearPaths.proj (k := k) e w a.1 (G a) -
        ((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
          (H ≫ LinearPaths.arrow (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2)) ∈
        (S.meshIdeal b).hom _ _ := fun e ↦
    (S.cov_homog b e (fun a ↦ LinearPaths.proj (k := k) e w a.1 (G a))
      (fun a ↦ LinearPaths.proj_mem _)
      (by rw [← proj_sum_comp_arrow]; exact S.proj_mem_meshIdeal b _ hsum)).2 hx
  choose H hH using hcomp
  refine ⟨(S.meshQuot b).map (∑ e ∈ Finset.range N, H e), fun a ↦ ?_⟩
  rw [← hG a, S.map_eq_sum_proj b (hN a), Functor.map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [S.map_eq_of_sub_mem b (hH e a), Functor.map_smul, Functor.map_comp, map_arrow,
    Linear.comp_smul]

/-- Covariant injectivity at a nonprojective vertex. -/
theorem ar_cov_mono (x : S.ARVertex) (hx : x ∈ S.nonprojectiveVertices) (w : S.ARVertex)
    (z : S.meshObj b w ⟶ S.meshObj b (S.arTranslationQuiver.tau ⟨x, hx⟩).1)
    (hz : ∀ a : Σ y : S.ARVertex, y ⟶ x, z ≫ (((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
        ScalarMeshCategory.arrowMor (S.arCoefficients b)
          (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2)) = 0) : z = 0 := by
  obtain ⟨Z, rfl⟩ := (S.meshQuot b).map_surjective z
  rw [S.meshQuot_map_eq_zero_iff]
  have h1 : ∀ a : Σ y : S.ARVertex, y ⟶ x,
      Z ≫ LinearPaths.arrow (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2) ∈
        (S.meshIdeal b).hom _ _ := by
    intro a
    have := hz a
    rw [Linear.comp_smul, ← map_arrow, ← Functor.map_comp, ← Functor.map_smul,
      S.meshQuot_map_eq_zero_iff] at this
    have h2 := Submodule.smul_mem _
      ((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ)⁻¹ : kˣ).1 this
    rwa [smul_smul, Units.inv_mul, one_smul] at h2
  apply S.mem_of_proj_mem b
  intro e
  apply S.cov_mono_homog b e ⟨x, hx⟩ _ (LinearPaths.proj_mem _)
  intro a
  rw [← LinearPaths.proj_comp_of_mem (m := 1) _ (LinearPaths.arrow_mem_degreePart (k := k) _)]
  exact S.proj_mem_meshIdeal b _ (h1 a)

/-- At a projective vertex the right mesh map is a monomorphism. -/
theorem ar_proj_mono (x : S.ARVertex) (hx : x ∉ S.nonprojectiveVertices) (w : S.ARVertex)
    (g : ∀ a : Σ y : S.ARVertex, y ⟶ x, S.meshObj b w ⟶ S.meshObj b a.1)
    (hg : ∑ a : (Σ y : S.ARVertex, y ⟶ x),
      g a ≫ ScalarMeshCategory.arrowMor (S.arCoefficients b) a.2 = 0) (a : Σ y : S.ARVertex, y ⟶ x) :
    g a = 0 := by
  choose G hG using fun a ↦ (S.meshQuot b).map_surjective (g a)
  have hsum : ∑ a : (Σ y : S.ARVertex, y ⟶ x), G a ≫ LinearPaths.arrow a.2 ∈
      (S.meshIdeal b).hom _ _ := by
    rw [← S.meshQuot_map_eq_zero_iff, Functor.map_sum, ← hg]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Functor.map_comp, hG]; rfl
  rw [← hG a, S.meshQuot_map_eq_zero_iff]
  apply S.mem_of_proj_mem b
  intro e
  exact (S.cov_homog b e (fun a ↦ LinearPaths.proj (k := k) e w a.1 (G a))
    (fun a ↦ LinearPaths.proj_mem _)
    (by rw [← proj_sum_comp_arrow]; exact S.proj_mem_meshIdeal b _ hsum)).1 hx a

set_option maxHeartbeats 1600000 in
/-- Contravariant exactness at a nonprojective vertex. -/
theorem ar_contra_exact (x : S.ARVertex) (hx : x ∈ S.nonprojectiveVertices) (w : S.ARVertex)
    (v : ∀ a : Σ y : S.ARVertex, y ⟶ x, S.meshObj b a.1 ⟶ S.meshObj b w)
    (hv : ∑ a : (Σ y : S.ARVertex, y ⟶ x), (((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
        ScalarMeshCategory.arrowMor (S.arCoefficients b)
          (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2)) ≫ v a = 0) :
    ∃ u : S.meshObj b x ⟶ S.meshObj b w,
      ∀ a, v a = ScalarMeshCategory.arrowMor (S.arCoefficients b) a.2 ≫ u := by
  choose V hV using fun a ↦ (S.meshQuot b).map_surjective (v a)
  have hsum : ∑ a : (Σ X : S.ARVertex, X ⟶ x), ((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
      (LinearPaths.arrow (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2) ≫ V a) ∈
      (S.meshIdeal b).hom _ _ := by
    rw [← S.meshQuot_map_eq_zero_iff, Functor.map_sum, ← hv]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Functor.map_smul, Functor.map_comp, hV, Linear.smul_comp]
    rfl
  obtain ⟨N, hN⟩ := LinearPaths.exists_sum_proj_family (k := k)
    (x := fun a : (Σ X : S.ARVertex, X ⟶ x) ↦ a.1) (y := fun _ ↦ w) V
  have hcomp : ∀ e, ∃ U : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj w,
      ∀ a : (Σ X : S.ARVertex, X ⟶ x),
        LinearPaths.proj (k := k) e a.1 w (V a) - LinearPaths.arrow a.2 ≫ U ∈
          (S.meshIdeal b).hom _ _ := fun e ↦
    S.contra_homog b e ⟨x, hx⟩ (fun a ↦ LinearPaths.proj (k := k) e a.1 w (V a))
      (fun a ↦ LinearPaths.proj_mem _)
      (by rw [← S.proj_sum_arrow_comp b e ⟨x, hx⟩ V]; exact S.proj_mem_meshIdeal b _ hsum)
  choose U hU using hcomp
  refine ⟨(S.meshQuot b).map (∑ e ∈ Finset.range N, U e), fun a ↦ ?_⟩
  rw [← hV a, S.map_eq_sum_proj b (hN a), Functor.map_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [S.map_eq_of_sub_mem b (hU e a), Functor.map_comp, map_arrow]

/-- Contravariant injectivity at a nonprojective vertex. -/
theorem ar_contra_mono (x : S.ARVertex) (hx : x ∈ S.nonprojectiveVertices) (w : S.ARVertex)
    (u : S.meshObj b x ⟶ S.meshObj b w)
    (hu : ∀ a : Σ y : S.ARVertex, y ⟶ x,
      ScalarMeshCategory.arrowMor (S.arCoefficients b) a.2 ≫ u = 0) : u = 0 := by
  obtain ⟨U, rfl⟩ := (S.meshQuot b).map_surjective u
  rw [S.meshQuot_map_eq_zero_iff]
  have h1 : ∀ a : Σ y : S.ARVertex, y ⟶ x, LinearPaths.arrow a.2 ≫ U ∈ (S.meshIdeal b).hom _ _ := by
    intro a
    have := hu a
    rwa [← map_arrow, ← Functor.map_comp, S.meshQuot_map_eq_zero_iff] at this
  apply S.mem_of_proj_mem b
  intro e
  apply S.contra_mono_homog b e ⟨x, hx⟩ _ (LinearPaths.proj_mem _)
  intro a
  have := S.proj_mem_meshIdeal b (1 + e) (h1 a)
  rwa [LinearPaths.proj_of_mem_comp (m := 1) (LinearPaths.arrow_mem_degreePart (k := k) _)] at this

/-- The mesh relation at a nonprojective vertex holds in `k(Γ_A)`. -/
theorem ar_comp_zero (x : S.ARVertex) (hx : x ∈ S.nonprojectiveVertices) :
    ∑ a : (Σ y : S.ARVertex, y ⟶ x), (((S.arCoefficients b ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
        ScalarMeshCategory.arrowMor (S.arCoefficients b)
          (S.arTranslationQuiver.mate ⟨x, hx⟩ a.1 a.2)) ≫
      ScalarMeshCategory.arrowMor (S.arCoefficients b) a.2 = 0 := by
  have hrel : meshRelation (S.arCoefficients b) ⟨x, hx⟩ ∈ (S.meshIdeal b).hom _ _ :=
    MultiplicativeBasisDeformations.CategoricalIdeal.HomIdeal.relation_mem_linearSpan _
      ⟨⟨x, hx⟩, rfl, rfl, by simp⟩
  rw [← S.meshQuot_map_eq_zero_iff, meshRelation, Functor.map_sum] at hrel
  rw [← hrel]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Functor.map_smul, Linear.smul_comp, ← LinearPaths.path_comp_path, Functor.map_comp]
  rfl

/-- **The mesh data of `k(Γ_A)`**: the right mesh maps are the arrows ending at
each vertex, with the exact mesh sequences of Proposition 2.6(1)(2). -/
def arMeshData : CatAlg.MeshData (fun x : S.ARVertex ↦ S.meshObj b x) (S.arLocal b) where
  Mid x := Σ y : S.ARVertex, y ⟶ x
  fin _ := inferInstance
  decMid _ := Classical.decEq _
  mid _ a := a.1
  p _ a := ScalarMeshCategory.arrowMor (S.arCoefficients b) a.2
  p_rad _ a := ScalarMeshCategory.arrowMor_mem_radN _ a.2
  image _ _ _ hf := ScalarMeshCategory.exists_lastArrow _ hf
  proj x := x ∉ S.nonprojectiveVertices
  decProj := Classical.decPred _
  tau x hx := (S.arTranslationQuiver.tau ⟨x, not_not.1 hx⟩).1
  q x hx a := ((S.arCoefficients b ⟨x, not_not.1 hx⟩ a.1 a.2 : kˣ) : k) •
    ScalarMeshCategory.arrowMor (S.arCoefficients b)
      (S.arTranslationQuiver.mate ⟨x, not_not.1 hx⟩ a.1 a.2)
  comp_zero x hx := S.ar_comp_zero b x (not_not.1 hx)
  cov_exact x hx w g hg := S.ar_cov_exact b x (not_not.1 hx) w g hg
  cov_mono x hx w z hz := S.ar_cov_mono b x (not_not.1 hx) w z hz
  contra_exact x hx w v hv := S.ar_contra_exact b x (not_not.1 hx) w v hv
  contra_mono x hx w u hu := S.ar_contra_mono b x (not_not.1 hx) w u hu
  proj_mono x hx w g hg := S.ar_proj_mono b x hx w g hg

/-- **Lemma 2.7** (`lem:mesh-simple-tops`): at every label `X` of `C = k(Γ_A)`, projective or
not, the right mesh map `⊕_a C(-, mid a) → C(-, X)` (at a projective label, the initial forms of
the components of `rad P → P`, the arrows into `P`) has image the radical of the representable
`C(-, X)`, and its cokernel is the simple top of `C(-, X)`. -/
theorem meshSimpleTops (x : S.ARVertex) :
    LinearMap.range ((S.arMeshData b).meshMap x) = (S.arLocal b).radRep x ∧
      IsSimpleModule (CatAlg.Alg fun x : S.ARVertex ↦ S.meshObj b x)
        (CatAlg.Rep _ (S.meshObj b x) ⧸ LinearMap.range ((S.arMeshData b).meshMap x)) := by
  refine ⟨(S.arMeshData b).range_meshMap x, ?_⟩
  rw [(S.arMeshData b).range_meshMap x]
  exact inferInstanceAs (IsSimpleModule _ ((S.arLocal b).Top x))

end MultiplicativeBasisDeformations.IndSkeleton
