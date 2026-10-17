import MultiplicativeBasisDeformations.Foundations.MeshCategory

/-!
# The path-length grading of a linear path category

The linear path category `kQ = Free k (Paths Q)` is graded by path length:
every morphism is the finite sum of its homogeneous components, and
composition adds degrees (`graded-category.tex:156–157`: "The quotient is
graded by path length").
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]

namespace LinearPaths

/-- A morphism of `kQ`, as a finitely supported function on paths. -/
def toFinsupp {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) : Quiver.Path x y →₀ k := f

/-- A finitely supported function on paths, as a morphism of `kQ`. -/
def ofFinsupp {x y : V} (F : Quiver.Path x y →₀ k) : obj (k := k) x ⟶ obj (k := k) y := F

@[simp] theorem ofFinsupp_toFinsupp {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    ofFinsupp (toFinsupp f) = f := rfl

@[simp] theorem toFinsupp_add {x y : V} (f g : obj (k := k) x ⟶ obj (k := k) y) :
    toFinsupp (f + g) = toFinsupp f + toFinsupp g := rfl

@[simp] theorem toFinsupp_smul {x y : V} (c : k) (f : obj (k := k) x ⟶ obj (k := k) y) :
    toFinsupp (c • f) = c • toFinsupp f := rfl

@[simp] theorem toFinsupp_zero {x y : V} :
    toFinsupp (0 : obj (k := k) x ⟶ obj (k := k) y) = 0 := rfl

@[simp] theorem toFinsupp_path {x y : V} (p : Quiver.Path x y) :
    toFinsupp (path (k := k) p) = Finsupp.single p 1 := rfl

/-- Morphisms of `kQ` are finitely supported functions on paths. -/
def finsuppEquiv (x y : V) : (obj (k := k) x ⟶ obj (k := k) y) ≃ₗ[k] (Quiver.Path x y →₀ k) where
  toFun := toFinsupp
  invFun := ofFinsupp
  map_add' f g := toFinsupp_add f g
  map_smul' c f := toFinsupp_smul c f
  left_inv _ := rfl
  right_inv _ := rfl

/-- The homogeneous component of degree `d` of a morphism of `kQ`. -/
def proj (d : ℕ) (x y : V) :
    (obj (k := k) x ⟶ obj (k := k) y) →ₗ[k] (obj (k := k) x ⟶ obj (k := k) y) where
  toFun f := ofFinsupp (Finsupp.filter (fun p : Quiver.Path x y ↦ p.length = d) (toFinsupp f))
  map_add' f g := by
    change Finsupp.filter _ (toFinsupp f + toFinsupp g) = _
    rw [Finsupp.filter_add]; rfl
  map_smul' c f := by
    change Finsupp.filter _ (c • toFinsupp f) = _
    rw [Finsupp.filter_smul]; rfl

theorem path_comp_path {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    path (k := k) p ≫ path q = path (p.comp q) := by
  have h := Free.single_comp_single (R := k) (C := Paths V) (X := x) (Y := y) (Z := z)
    p q 1 1
  rw [one_mul] at h
  exact h

theorem path_mem_degreePart {x y : V} (p : Quiver.Path x y) :
    path (k := k) p ∈ degreePart (k := k) p.length x y :=
  Submodule.subset_span ⟨p, rfl, rfl⟩

theorem proj_path {x y : V} (d : ℕ) (p : Quiver.Path x y) :
    proj (k := k) d x y (path p) = if p.length = d then path p else 0 := by
  change ofFinsupp (Finsupp.filter _ (Finsupp.single p 1)) = _
  split_ifs with h
  · rw [Finsupp.filter_single_of_pos (fun p : Quiver.Path x y ↦ p.length = d) h]; rfl
  · rw [Finsupp.filter_single_of_neg (fun p : Quiver.Path x y ↦ p.length = d) h]; rfl

/-- Every morphism of `kQ` is a finite linear combination of paths. -/
theorem induction_on {x y : V} {P : (obj (k := k) x ⟶ obj (k := k) y) → Prop}
    (f : obj (k := k) x ⟶ obj (k := k) y) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g))
    (hsingle : ∀ (p : Quiver.Path x y) (c : k), P (c • path p)) : P f := by
  rw [← ofFinsupp_toFinsupp f]
  induction toFinsupp f using Finsupp.induction_linear with
  | zero => exact h0
  | add F G hF hG => exact hadd _ _ hF hG
  | single p c =>
      have : ofFinsupp (Finsupp.single p c) = c • path (k := k) p := by
        change Finsupp.single p c = c • Finsupp.single p (1 : k)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [this]
      exact hsingle p c

theorem mem_degreePart_iff {d : ℕ} {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    f ∈ degreePart (k := k) d x y ↔ proj (k := k) d x y f = f := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨p, hp, rfl⟩ := hg
        rw [proj_path, if_pos hp]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  · intro hf
    rw [← hf]
    clear hf
    induction f using induction_on with
    | h0 => simp
    | hadd f g hf hg => rw [map_add]; exact add_mem hf hg
    | hsingle p c =>
        rw [map_smul, proj_path]
        split_ifs with h
        · exact Submodule.smul_mem _ c (h ▸ path_mem_degreePart p)
        · simp

theorem proj_mem {d : ℕ} {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    proj (k := k) d x y f ∈ degreePart (k := k) d x y := by
  rw [mem_degreePart_iff]
  change ofFinsupp (Finsupp.filter _ (Finsupp.filter _ (toFinsupp f))) =
    ofFinsupp (Finsupp.filter _ (toFinsupp f))
  congr 1
  ext p
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl

theorem proj_of_mem {d e : ℕ} {x y : V} {f : obj (k := k) x ⟶ obj (k := k) y}
    (hf : f ∈ degreePart (k := k) e x y) : proj (k := k) d x y f = if e = d then f else 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, hp, rfl⟩ := hg
      rw [proj_path, hp]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]; split_ifs <;> simp
  | smul c a _ ha => rw [map_smul, ha]; split_ifs <;> simp

/-- A morphism is the finite sum of its homogeneous components. -/
theorem eq_sum_proj {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    ∃ N : ℕ, f = ∑ d ∈ Finset.range N, proj (k := k) d x y f := by
  classical
  refine ⟨(toFinsupp f).support.sup Quiver.Path.length + 1, ?_⟩
  apply_fun toFinsupp using fun _ _ h ↦ h
  ext p
  change toFinsupp f p = (∑ d ∈ _, Finsupp.filter (fun p : Quiver.Path x y ↦ p.length = d)
    (toFinsupp f) : Quiver.Path x y →₀ k) p
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.filter_apply]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := Quiver.Path.length) (Finsupp.mem_support_iff.2 hne)

theorem comp_mem_degreePart {d e : ℕ} {x y z : V} {f : obj (k := k) x ⟶ obj (k := k) y}
    {g : obj (k := k) y ⟶ obj (k := k) z} (hf : f ∈ degreePart (k := k) d x y)
    (hg : g ∈ degreePart (k := k) e y z) : f ≫ g ∈ degreePart (k := k) (d + e) x z := by
  induction hf using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨p, rfl, rfl⟩ := ha
      induction hg using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨q, rfl, rfl⟩ := hb
          rw [path_comp_path, ← Quiver.Path.length_comp]
          exact path_mem_degreePart _
      | zero => simp
      | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact add_mem ha hb
      | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | smul c a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c ha

open CategoricalIdeal in
/-- An ideal generated by homogeneous relations is graded: it is stable under
the homogeneous projections. -/
theorem proj_mem_linearSpan (R : ∀ X Y : LinearPaths k V, Set (X ⟶ Y))
    (hR : ∀ (X Y : V) (r : obj (k := k) X ⟶ obj (k := k) Y), r ∈ R X Y →
      ∃ e, r ∈ degreePart (k := k) e X Y)
    (d : ℕ) {X Y : V} {f : obj (k := k) X ⟶ obj (k := k) Y}
    (hf : f ∈ (HomIdeal.linearSpan k R).hom (obj X) (obj Y)) :
    proj (k := k) d X Y f ∈ (HomIdeal.linearSpan k R).hom (obj X) (obj Y) := by
  change f ∈ HomIdeal.generatedHomSubmodule k R (obj X) (obj Y) at hf
  change _ ∈ HomIdeal.generatedHomSubmodule k R (obj X) (obj Y)
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨A, B, r, hr, a, b, rfl⟩ := hg
      obtain ⟨A', rfl⟩ : ∃ A' : V, obj (k := k) A' = A := ⟨A, rfl⟩
      obtain ⟨B', rfl⟩ : ∃ B' : V, obj (k := k) B' = B := ⟨B, rfl⟩
      obtain ⟨e, he⟩ := hR A' B' r hr
      induction a using induction_on with
      | h0 => simp
      | hadd a₁ a₂ h₁ h₂ => rw [Preadditive.add_comp, map_add]; exact add_mem h₁ h₂
      | hsingle p c =>
          induction b using induction_on with
          | h0 => simp
          | hadd b₁ b₂ h₁ h₂ =>
              rw [Preadditive.comp_add, Preadditive.comp_add, map_add]; exact add_mem h₁ h₂
          | hsingle q c' =>
              have hdeg : path (k := k) p ≫ r ≫ path q ∈
                  degreePart (k := k) (p.length + e + q.length) X Y :=
                comp_mem_degreePart (comp_mem_degreePart (path_mem_degreePart p) he)
                  (path_mem_degreePart q) |> fun h ↦ by simpa [Category.assoc] using h
              have hgen : path (k := k) p ≫ r ≫ path q ∈
                  HomIdeal.generatedHomSubmodule k R (obj X) (obj Y) :=
                Submodule.subset_span ⟨obj A', obj B', r, hr, path p, path q, rfl⟩
              have : (c • path (k := k) p) ≫ r ≫ (c' • path q) =
                  (c * c') • (path (k := k) p ≫ r ≫ path q) := by
                simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
              rw [this, map_smul, proj_of_mem hdeg]
              split_ifs
              · exact Submodule.smul_mem _ _ hgen
              · simp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end LinearPaths

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.LinearPaths

open CategoryTheory

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]

/-- A homogeneous morphism of positive degree is a sum over the arrows ending
at its target: `F = ∑_a G_a a` with `G_a` homogeneous of one degree less. -/
theorem exists_lastArrow_decomposition [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
    {N : ℕ} {W Y : V} [Fintype (Σ X : V, X ⟶ Y)]
    {F : obj (k := k) W ⟶ obj (k := k) Y} (hF : F ∈ degreePart (k := k) (N + 1) W Y) :
    ∃ G : ∀ a : Σ X : V, X ⟶ Y, obj (k := k) W ⟶ obj (k := k) a.1,
      (∀ a, G a ∈ degreePart (k := k) N W a.1) ∧ F = ∑ a, G a ≫ arrow a.2 := by
  classical
  induction hF using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      cases p with
      | nil => simp at hp
      | cons p' α =>
          rename_i X
          simp only [Quiver.Path.length_cons, Nat.add_right_cancel_iff] at hp
          let a₀ : Σ X : V, X ⟶ Y := ⟨X, α⟩
          refine ⟨Function.update (fun _ ↦ 0) a₀ (path p'), ?_, ?_⟩
          · intro a
            by_cases ha : a = a₀
            · subst ha; rw [Function.update_self, ← hp]; exact path_mem_degreePart p'
            · rw [Function.update_of_ne ha]; exact zero_mem _
          · rw [Finset.sum_eq_single a₀]
            · rw [Function.update_self, arrow, path_comp_path]; rfl
            · intro a _ ha; rw [Function.update_of_ne ha, Limits.zero_comp]
            · simp
  | zero => exact ⟨fun _ ↦ 0, fun _ ↦ zero_mem _, by simp⟩
  | add f g _ _ hf hg =>
      obtain ⟨G₁, hG₁, rfl⟩ := hf
      obtain ⟨G₂, hG₂, rfl⟩ := hg
      exact ⟨fun a ↦ G₁ a + G₂ a, fun a ↦ add_mem (hG₁ a) (hG₂ a), by
        simp only [Preadditive.add_comp, Finset.sum_add_distrib]⟩
  | smul c f _ hf =>
      obtain ⟨G, hG, rfl⟩ := hf
      exact ⟨fun a ↦ c • G a, fun a ↦ Submodule.smul_mem _ c (hG a), by
        simp only [Linear.smul_comp, Finset.smul_sum]⟩

/-- A homogeneous morphism of degree zero between distinct vertices vanishes. -/
theorem degreePart_zero_of_ne {x y : V} (hxy : x ≠ y) {F : obj (k := k) x ⟶ obj (k := k) y}
    (hF : F ∈ degreePart (k := k) 0 x y) : F = 0 := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      exact absurd (p.eq_of_length_zero hp) hxy
  | zero => rfl
  | add f g _ _ hf hg => rw [hf, hg, add_zero]
  | smul c f _ hf => rw [hf, smul_zero]

/-- A homogeneous endomorphism of degree zero is a multiple of the trivial
path. -/
theorem degreePart_zero_self {x : V} {F : obj (k := k) x ⟶ obj (k := k) x}
    (hF : F ∈ degreePart (k := k) 0 x x) :
    F = toFinsupp F Quiver.Path.nil • path (k := k) (Quiver.Path.nil : Quiver.Path x x) := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      rw [p.eq_nil_of_length_zero hp, toFinsupp_path, Finsupp.single_eq_same, one_smul]
  | zero => simp
  | add f g _ _ hf hg =>
      rw [toFinsupp_add, Finsupp.add_apply, add_smul, ← hf, ← hg]
  | smul c f _ hf =>
      rw [toFinsupp_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul, ← hf]

end MultiplicativeBasisDeformations.LinearPaths

namespace MultiplicativeBasisDeformations.LinearPaths

open CategoryTheory

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]

theorem arrow_mem_degreePart {x y : V} (a : x ⟶ y) : arrow (k := k) a ∈ degreePart (k := k) 1 x y :=
  path_mem_degreePart (k := k) a.toPath

theorem comp_arrow_mem_degreePart {m : ℕ} {x y z : V} {H : obj (k := k) x ⟶ obj (k := k) y}
    (hH : H ∈ degreePart (k := k) m x y) (a : y ⟶ z) :
    H ≫ arrow (k := k) a ∈ degreePart (k := k) (m + 1) x z :=
  comp_mem_degreePart hH (arrow_mem_degreePart a)

end MultiplicativeBasisDeformations.LinearPaths

namespace MultiplicativeBasisDeformations

open CategoryTheory

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- The mesh relations are homogeneous of degree two. -/
theorem meshRelation_mem_degreePart (c : MeshCoefficients k Q) (x : Q.nonprojective) :
    meshRelation c x ∈ LinearPaths.degreePart (k := k) 2 (Q.tau x).1 x.1 := by
  unfold meshRelation
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ ?_
  have := LinearPaths.path_mem_degreePart (k := k) ((Q.mate x a.1 a.2).toPath.comp a.2.toPath)
  simpa using this

theorem meshRelations_homogeneous (c : MeshCoefficients k Q) (X Y : V)
    (r : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y)
    (hr : r ∈ meshRelations c (LinearPaths.obj X) (LinearPaths.obj Y)) :
    ∃ e, r ∈ LinearPaths.degreePart (k := k) e X Y := by
  obtain ⟨x, hX, hY, rfl⟩ := hr
  change X = (Q.tau x).1 at hX
  change Y = x.1 at hY
  subst hX hY
  refine ⟨2, ?_⟩
  have e : eqToHom (rfl : LinearPaths.obj (k := k) (Q.tau x).1 = _) ≫ meshRelation c x ≫
      eqToHom (rfl : LinearPaths.obj (k := k) x.1 = _) = meshRelation c x := by
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  convert meshRelation_mem_degreePart c x

end MultiplicativeBasisDeformations
