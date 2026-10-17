import MultiplicativeBasisDeformations.Foundations.MeshCorrections
import MultiplicativeBasisDeformations.Foundations.PathGrading

/-!
# Rows and columns of the mesh derivative

Subsection 5.1 of the frozen manuscript (`mesh-deformations.tex:24–162`).

For a scalar mesh category `C = C(Q, c)` the derivative `D_m` of
`eq:mesh-derivative` is linear. Its target `V_{m+1}` is spanned by the *rows*
`(x, w)`: a nonprojective vertex `x` and a path `w : τ x → x` of length
`m + 1`, placed in the `x`-th component. A *correction column* is an arrow `b`
together with a parallel path `p`; by `eq:mesh-derivative` its image has at most
two entries (`column_eq`). This file sets up these objects:

* `meshDerivativeₗ`, the derivative as a linear map;
* `imageD c m`, the image of the degree-`m` families;
* `row c x w`, the row of a path, and `surjective_iff_rows`: `D_m` is
  surjective exactly when every row of length `m + 1` lies in the image;
* `column_eq`, the two entries of a correction column.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)

/-- The image of a path in the scalar mesh category. -/
def pathMor {x y : V} (p : Quiver.Path x y) : obj c x ⟶ obj c y :=
  (RelationCategory.functor k (meshRelations c)).map (LinearPaths.path p)

theorem pathMor_comp {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    pathMor c (p.comp q) = pathMor c p ≫ pathMor c q := by
  rw [pathMor, pathMor, pathMor, ← Functor.map_comp, LinearPaths.path_comp_path]

theorem pathMor_toPath {x y : V} (a : x ⟶ y) : pathMor c a.toPath = arrowMor c a := rfl

theorem pathMor_cons {x y z : V} (p : Quiver.Path x y) (a : y ⟶ z) :
    pathMor c (p.cons a) = pathMor c p ≫ arrowMor c a := by
  rw [← pathMor_toPath, ← pathMor_comp]; rfl

theorem pathMor_mem_degreePart {x y : V} (p : Quiver.Path x y) :
    pathMor c p ∈ degreePart c p.length x y :=
  ⟨_, LinearPaths.path_mem_degreePart p, rfl⟩

/-- The degree-`n` part is spanned by the images of the paths of length `n`. -/
theorem degreePart_eq_span (n : ℕ) (x y : V) :
    degreePart c n x y = Submodule.span k {f | ∃ p : Quiver.Path x y, p.length = n ∧
      f = pathMor c p} := by
  rw [degreePart, LinearPaths.degreePart, Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩

/-- The mesh derivative is linear. -/
def meshDerivativeₗ : ArrowFamily c →ₗ[k] MeshFamily c where
  toFun := meshDerivative c
  map_add' f g := by
    funext x
    simp only [meshDerivative, Pi.add_apply, Preadditive.add_comp, Preadditive.comp_add,
      ← Finset.sum_add_distrib, ← smul_add]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    abel
  map_smul' t f := by
    funext x
    simp only [meshDerivative, Pi.smul_apply, Linear.smul_comp, Linear.comp_smul,
      RingHom.id_apply, Finset.smul_sum, ← smul_add, smul_comm t]

@[simp] theorem meshDerivativeₗ_apply (f : ArrowFamily c) :
    meshDerivativeₗ c f = meshDerivative c f := rfl

/-- The families of path degree `m`. -/
def familiesDeg (m : ℕ) : Submodule k (ArrowFamily c) where
  carrier := {f | ∀ a, f a ∈ degreePart c m a.1 a.2.1}
  add_mem' hf hg a := add_mem (hf a) (hg a)
  zero_mem' a := zero_mem _
  smul_mem' t f hf a := Submodule.smul_mem _ t (hf a)

/-- The image of `D_m`. -/
def imageD (m : ℕ) : Submodule k (MeshFamily c) :=
  (familiesDeg c m).map (meshDerivativeₗ c)

variable [DecidableEq V]

/-- The row of a path `w : τ x → x`: the family with `w` at `x` and zero
elsewhere. -/
def row (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) : MeshFamily c :=
  Pi.single x (pathMor c w)

variable [Fintype Q.nonprojective]

/-- `D_m` is surjective exactly when every row of length `m + 1` lies in its
image. -/
theorem surjective_iff_rows (m : ℕ) :
    MeshDerivativeSurjective c m ↔
      ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
        row c x w ∈ imageD c m := by
  constructor
  · intro h x w hw
    obtain ⟨f, hf, hDf⟩ := h (row c x w) fun x' ↦ by
      by_cases hx : x' = x
      · subst hx
        simp only [row, Pi.single_eq_same]
        rw [← hw]; exact pathMor_mem_degreePart c w
      · simp only [row, Pi.single_eq_of_ne hx]; exact zero_mem _
    exact ⟨f, hf, hDf⟩
  · intro h g hg
    have hsingle : ∀ x (e : obj c (Q.tau x).1 ⟶ obj c x.1),
        e ∈ degreePart c (m + 1) (Q.tau x).1 x.1 → Pi.single x e ∈ imageD c m := by
      intro x e he
      rw [degreePart_eq_span] at he
      induction he using Submodule.span_induction with
      | mem e he =>
          obtain ⟨w, hw, rfl⟩ := he
          exact h x w hw
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | add e₁ e₂ _ _ h₁ h₂ => rw [Pi.single_add]; exact add_mem h₁ h₂
      | smul t e _ he => rw [Pi.single_smul]; exact Submodule.smul_mem _ t he
    have hg' : g = ∑ x, Pi.single x (g x) := (Finset.univ_sum_single g).symm
    have : g ∈ imageD c m := by
      rw [hg']
      exact sum_mem fun x _ ↦ hsingle x (g x) (hg x)
    obtain ⟨f, hf, hDf⟩ := this
    exact ⟨f, hf, hDf⟩

omit [Fintype Q.nonprojective] in
theorem meshDerivative_apply_eq (f : ArrowFamily c) (x : Q.nonprojective) :
    meshDerivative c f x =
      (∑ b : Σ y : V, y ⟶ x.1, ((c x b.1 b.2 : kˣ) : k) •
        (f ⟨(Q.tau x).1, b.1, Q.mate x b.1 b.2⟩ ≫ arrowMor c b.2)) +
      ∑ b : Σ y : V, y ⟶ x.1, ((c x b.1 b.2 : kˣ) : k) •
        (arrowMor c (Q.mate x b.1 b.2) ≫ f ⟨b.1, x.1, b.2⟩) := by
  simp only [meshDerivative, smul_add, Finset.sum_add_distrib]

variable [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]

omit [Fintype Q.nonprojective] in
theorem sigma3_eq_iff {u v u' v' : V} (a : u ⟶ v) (a' : u' ⟶ v') :
    (⟨u, v, a⟩ : Σ u v : V, u ⟶ v) = ⟨u', v', a'⟩ ↔ u = u' ∧ v = v' ∧ a ≍ a' := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, HEq.rfl⟩
  · rintro ⟨rfl, rfl, h⟩; cases h; rfl

omit [Fintype Q.nonprojective] in
/-- **A correction column has at most two entries** (proof of
`prop:periodic-localization`). Correcting the arrow `σ a : τ x → y` (for
`a : y → x`) by a parallel path `p` contributes `c_{x,a} p a` to the mesh at
`x` and, if `y` is nonprojective, `c_{y,σ a} (σ σ a) p` to the mesh at `y`. -/
theorem column_eq (x : Q.nonprojective) {y : V} (a : y ⟶ x.1) (p : Quiver.Path (Q.tau x).1 y) :
    meshDerivative c (Pi.single (⟨(Q.tau x).1, y, Q.mate x y a⟩ : Σ u v : V, u ⟶ v)
        (pathMor c p)) =
      ((c x y a : kˣ) : k) • row c x (p.cons a) +
        if hy : y ∈ Q.nonprojective then
          ((c ⟨y, hy⟩ (Q.tau x).1 (Q.mate x y a) : kˣ) : k) •
            row c ⟨y, hy⟩ ((Q.mate ⟨y, hy⟩ (Q.tau x).1 (Q.mate x y a)).toPath.comp p)
        else 0 := by
  funext x'
  rw [meshDerivative_apply_eq, Pi.add_apply, Pi.smul_apply]
  congr 1
  · -- the occurrence of `σ a` as a first factor
    by_cases hx : x' = x
    · subst hx
      rw [Finset.sum_eq_single (⟨y, a⟩ : Σ y : V, y ⟶ x'.1)]
      · simp only [Pi.single_eq_same, row, pathMor_cons]
      · rintro ⟨b1, b2⟩ _ hb
        rw [Pi.single_eq_of_ne, Limits.zero_comp]
        · exact smul_zero _
        · intro h
          obtain ⟨-, rfl, h2⟩ := (sigma3_eq_iff _ _).1 h
          exact hb (Sigma.ext rfl (heq_of_eq ((Q.mate x' _).injective (eq_of_heq h2))))
      · simp
    · rw [row, Pi.single_eq_of_ne hx]
      refine (Finset.sum_eq_zero fun b _ ↦ ?_).trans (smul_zero _).symm
      rw [Pi.single_eq_of_ne, Limits.zero_comp]
      · exact smul_zero _
      · intro h
        obtain ⟨h1, -, -⟩ := (sigma3_eq_iff _ _).1 h
        exact hx (Q.tau.injective (Subtype.ext h1))
  · -- the occurrence of `σ a` as a last factor
    by_cases hy : y ∈ Q.nonprojective
    · rw [dif_pos hy, Pi.smul_apply]
      by_cases hx : x' = ⟨y, hy⟩
      · subst hx
        rw [Finset.sum_eq_single (⟨(Q.tau x).1, Q.mate x y a⟩ : Σ y' : V, y' ⟶ y)]
        · simp only [Pi.single_eq_same, row, pathMor_comp, pathMor_toPath]
        · rintro ⟨b1, b2⟩ _ hb
          rw [Pi.single_eq_of_ne, Limits.comp_zero]
          · exact smul_zero _
          · intro h
            obtain ⟨rfl, -, h2⟩ := (sigma3_eq_iff _ _).1 h
            exact hb (Sigma.ext rfl h2)
        · simp
      · rw [row, Pi.single_eq_of_ne hx]
        refine (Finset.sum_eq_zero fun b _ ↦ ?_).trans (smul_zero _).symm
        rw [Pi.single_eq_of_ne, Limits.comp_zero]
        · exact smul_zero _
        · intro h
          obtain ⟨-, h1, -⟩ := (sigma3_eq_iff _ _).1 h
          exact hx (Subtype.ext h1)
    · rw [dif_neg hy, Pi.zero_apply]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [Pi.single_eq_of_ne, Limits.comp_zero]
      · exact smul_zero _
      · intro h
        obtain ⟨-, h1, -⟩ := (sigma3_eq_iff _ _).1 h
        exact hy (h1 ▸ x'.2)

end ScalarMeshCategory

end MultiplicativeBasisDeformations
