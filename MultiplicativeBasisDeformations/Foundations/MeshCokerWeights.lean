module

public import MultiplicativeBasisDeformations.Foundations.WeightGrading
public import MultiplicativeBasisDeformations.Foundations.IntegralCokerIso

/-!
# Weight gradings of the mesh derivative cokernels

`weights-and-parameters.tex`: "a mesh weight `w` grades `V_{m+1}(C)` by giving a path at
row `v` the weight `w(path) − ν_v`, and grades `U_m(C)` by giving a path parallel to an arrow
`a` the weight `w(path) − w(a)`. The map `D_m` preserves these gradings, because each term
`(σa)a` of the mesh at `v` has weight `ν_v`. Hence `coker D_m` is graded by `L`, and the line
`k[p_i]` has degree `χ_i`."

Over any commutative coefficient ring: for an integer mesh weight `W` (`IntWt`), the weight
projections of families (`projW`, `projWA`) commute with `D_m` (`D_projWA`), so the image of
`D_m` is graded (`projW_mem_imageD`), and a row is homogeneous of degree `W(p) − ν_v`
(`projW_row`). This gives the labels `χ_i` of Lemma B.2 (`integralMeshCokernels_graded`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

variable {V : Type v} [Quiver.{w} V]

/-- **An integer mesh weight**: arrow weights `w` and row weights `ν` with
`w(σa) + w(a) = ν_v`. -/
structure IntWt (Q : TranslationQuiver V) where
  w : ∀ {y x : V}, (y ⟶ x) → ℤ
  ν : Q.nonprojective → ℤ
  mesh : ∀ (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1), w (Q.mate x a.1 a.2) + w a.2 = ν x

variable {Q : TranslationQuiver V}

/-- The weight of a path. -/
def IntWt.pw (W : IntWt Q) : ∀ {y x : V}, Quiver.Path y x → ℤ
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p a => W.pw p + W.w a

theorem IntWt.pw_comp (W : IntWt Q) {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    W.pw (p.comp q) = W.pw p + W.pw q := by
  induction q with
  | nil => simp [IntWt.pw]
  | cons q a ih => rw [Quiver.Path.comp_cons, IntWt.pw, IntWt.pw, ih, add_assoc]

/-- The path weight of `W`, multiplicatively. -/
def IntWt.pathWeight (W : IntWt Q) : PathWeight V (Multiplicative ℤ) where
  deg p := Multiplicative.ofAdd (W.pw p)
  deg_nil _ := by simp [IntWt.pw]
  deg_comp p q := by rw [W.pw_comp, ofAdd_add]

@[simp] theorem IntWt.pathWeight_deg (W : IntWt Q) {x y : V} (p : Quiver.Path x y) :
    W.pathWeight.deg p = Multiplicative.ofAdd (W.pw p) := rfl

theorem IntWt.pw_toPath (W : IntWt Q) {y x : V} (a : y ⟶ x) : W.pw a.toPath = W.w a := by
  simp [IntWt.pw, Quiver.Hom.toPath]

theorem IntWt.homog (W : IntWt Q) [∀ x : V, Fintype (Σ y : V, y ⟶ x)] :
    MeshHomogeneous (Q := Q) W.pathWeight := by
  intro x a b
  rw [IntWt.pathWeight_deg, IntWt.pathWeight_deg, W.pw_comp, W.pw_comp, W.pw_toPath, W.pw_toPath, W.pw_toPath, W.pw_toPath, W.mesh, W.mesh]

variable {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  (W : IntWt Q)

/-- The weight projection on Hom spaces. -/
abbrev wP (g : ℤ) (x y : V) : (obj c x ⟶ obj c y) →ₗ[k] (obj c x ⟶ obj c y) :=
  wProj c W.pathWeight W.homog (Multiplicative.ofAdd g) x y

theorem arrowMor_mem_wPart {y x : V} (a : y ⟶ x) :
    arrowMor c a ∈ wPart c W.pathWeight (Multiplicative.ofAdd (W.w a)) y x := by
  have := pathMor_mem_wPart (c := c) (wt := W.pathWeight) a.toPath
  change pathMor c a.toPath ∈ _ at this
  rw [show W.pathWeight.deg a.toPath = Multiplicative.ofAdd (W.w a) by
    rw [IntWt.pathWeight_deg, W.pw_toPath]] at this
  exact this

theorem wP_comp_hom {x y z : V} (φ : obj c x ⟶ obj c y) {α : obj c y ⟶ obj c z} {h : ℤ}
    (hα : α ∈ wPart c W.pathWeight (Multiplicative.ofAdd h) y z) (g : ℤ) :
    wP c W g x z (φ ≫ α) = wP c W (g - h) x y φ ≫ α := by
  classical
  obtain ⟨s, hs⟩ := eq_sum_wProj (c := c) W.homog φ
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  rw [Preadditive.sum_comp, map_sum, map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hm := comp_mem_wPart (wProj_mem (c := c) W.homog e φ) hα
  rw [wProj_of_mem W.homog hm, wProj_of_mem W.homog (wProj_mem (c := c) W.homog e φ)]
  by_cases he : e = Multiplicative.ofAdd (g - h)
  · subst he
    rw [if_pos (by rw [← ofAdd_add]; congr 1; ring), if_pos rfl]
  · rw [if_neg (fun h' ↦ he (by
      have := congrArg Multiplicative.toAdd h'
      simp only [toAdd_mul, toAdd_ofAdd] at this
      rw [show e = Multiplicative.ofAdd (Multiplicative.toAdd e) from rfl, ← this]
      congr 1; ring)), if_neg he, Limits.zero_comp]

theorem wP_hom_comp {x y z : V} {α : obj c x ⟶ obj c y} (φ : obj c y ⟶ obj c z) {h : ℤ}
    (hα : α ∈ wPart c W.pathWeight (Multiplicative.ofAdd h) x y) (g : ℤ) :
    wP c W g x z (α ≫ φ) = α ≫ wP c W (g - h) y z φ := by
  classical
  obtain ⟨s, hs⟩ := eq_sum_wProj (c := c) W.homog φ
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  rw [Preadditive.comp_sum, map_sum, map_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hm := comp_mem_wPart hα (wProj_mem (c := c) W.homog e φ)
  rw [wProj_of_mem W.homog hm, wProj_of_mem W.homog (wProj_mem (c := c) W.homog e φ)]
  by_cases he : e = Multiplicative.ofAdd (g - h)
  · subst he
    rw [if_pos (by rw [← ofAdd_add]; congr 1; ring), if_pos rfl]
  · rw [if_neg (fun h' ↦ he (by
      have := congrArg Multiplicative.toAdd h'
      simp only [toAdd_mul, toAdd_ofAdd] at this
      rw [show e = Multiplicative.ofAdd (Multiplicative.toAdd e) from rfl, ← this]
      congr 1; ring)), if_neg he, Limits.comp_zero]

/-- The weight-`λ` part of a mesh family: degree `W(path) − ν_v` at the row `v`. -/
def projW (l : ℤ) (g : MeshFamily c) : MeshFamily c := fun x ↦ wP c W (l + W.ν x) _ _ (g x)

/-- The weight-`λ` part of an arrow family: degree `W(path) − W(a)` at the arrow `a`. -/
def projWA (l : ℤ) (f : ArrowFamily c) : ArrowFamily c := fun a ↦ wP c W (l + W.w a.2.2) _ _ (f a)

/-- **`D_m` preserves the weight gradings.** -/
theorem D_projWA (l : ℤ) (f : ArrowFamily c) :
    meshDerivative c (projWA c W l f) = projW c W l (meshDerivative c f) := by
  funext x
  simp only [meshDerivative, projWA, projW, map_sum, map_smul, map_add]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  rw [wP_comp_hom c W _ (arrowMor_mem_wPart c W a.2), wP_hom_comp c W _ (arrowMor_mem_wPart c W _)]
  have hm := W.mesh x a
  rw [show l + W.ν x - W.w a.2 = l + W.w (Q.mate x a.1 a.2) by omega,
    show l + W.ν x - W.w (Q.mate x a.1 a.2) = l + W.w a.2 by omega]

theorem wP_degreePart {g : ℤ} {d : ℕ} {x y : V} {φ : obj c x ⟶ obj c y}
    (hφ : φ ∈ degreePart c d x y) : wP c W g x y φ ∈ degreePart c d x y := by
  rw [degreePart_eq_span] at hφ
  induction hφ using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      rw [wProj_of_mem W.homog (pathMor_mem_wPart p)]
      split_ifs
      · rw [← hp]; exact pathMor_mem_degreePart c p
      · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul t a _ ha => rw [map_smul]; exact Submodule.smul_mem _ t ha

/-- **The image of `D_m` is graded by `W`.** -/
theorem projW_mem_imageD (l : ℤ) {m : ℕ} {g : MeshFamily c} (hg : g ∈ imageD c m) :
    projW c W l g ∈ imageD c m := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨projWA c W l f, fun a ↦ wP_degreePart c W (hf a), by
    rw [meshDerivativeₗ_apply, meshDerivativeₗ_apply, D_projWA]⟩

/-- **A row is homogeneous of degree `W(p) − ν_v`.** -/
theorem projW_row [DecidableEq V] [DecidablePred (· ∈ Q.nonprojective)] (l : ℤ)
    (x : Q.nonprojective) (p : Quiver.Path (Q.tau x).1 x.1) :
    projW c W l (row c x p) = if W.pw p - W.ν x = l then row c x p else 0 := by
  funext y
  simp only [projW, row]
  by_cases hy : y = x
  · subst hy
    rw [Pi.single_eq_same, wProj_of_mem W.homog (pathMor_mem_wPart p)]
    split_ifs with h1 h2 h2
    · rw [Pi.single_eq_same]
    · exfalso; apply h2
      rw [IntWt.pathWeight_deg] at h1
      have := congrArg Multiplicative.toAdd h1
      simp only [toAdd_ofAdd] at this
      omega
    · exfalso; apply h1
      rw [IntWt.pathWeight_deg]
      congr 1; omega
    · rw [Pi.zero_apply]
  · rw [Pi.single_eq_of_ne hy, map_zero]
    split_ifs
    · rw [Pi.single_eq_of_ne hy]
    · rfl

/-- **The weight labels of Lemma B.2**: over `𝒪 = ℤ/4` (or any coefficient ring), for every
integer mesh weight `W` the cokernel of `D_m` is `W`-graded (the image of `D_m` is graded), and
the class of a row `p_i` at `v_i` is homogeneous of degree `χ_i(W) = W(p_i) − ν_{v_i}`
(`eq:parameter-character`). With `integralMeshCokernels` this is
`⊕_{m≥2} coker D_m(E₄) ≅ ⊕_{i∈I} (𝒪/(2))_{χ_i}`. -/
theorem integralMeshCokernels_weights [DecidableEq V] [DecidablePred (· ∈ Q.nonprojective)]
    {m : ℕ} (l : ℤ) :
    (∀ g, g ∈ imageD c m → projW c W l g ∈ imageD c m) ∧
    ∀ (x : Q.nonprojective) (p : Quiver.Path (Q.tau x).1 x.1),
      projW c W l (row c x p) = if W.pw p - W.ν x = l then row c x p else 0 :=
  ⟨fun _ hg ↦ projW_mem_imageD c W l hg, projW_row c W l⟩

end ScalarMeshCategory

end MultiplicativeBasisDeformations
