module

public import MultiplicativeBasisDeformations.Foundations.FullSubquiver
public import MultiplicativeBasisDeformations.Foundations.PeriodicLocalization

/-!
# Transfer of the mesh derivative to a `τ`-closed full subquiver

Proof of Proposition 5.1 (`prop:periodic-localization`), last paragraph, and
`eq:mesh-object-quotient`. For a `τ`-closed set `S`, the inclusion
`kQ_S → kQ` sends the mesh relation of `Q_S` at `x` to the mesh relation of
`Q` at `x` minus its terms through middle vertices outside `S`
(`inclL_meshRelation_sub_mem`). Hence the inclusion maps the mesh ideal of
`Q_S` into the mesh ideal of `Q` plus the paths through vertices outside `S`
(`inclL_mem_ideal_sup_outside`).

Consequently, if `D_m(C(Q_S))` is surjective and the rows through vertices
outside `S` are already in the image of `D_m(C(Q))`, then every row at a vertex
of `S` is in that image (`row_mem_imageD_of_restrict`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

open CategoricalIdeal

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- The mesh ideal of `C(Q, c)`, as a submodule of the Hom spaces of `kQ`. -/
abbrev meshIdealSub (c : MeshCoefficients k Q) (X Y : LinearPaths k V) :=
  HomIdeal.generatedHomSubmodule k (meshRelations c) X Y

theorem meshRelation_mem_meshIdealSub (c : MeshCoefficients k Q) (x : Q.nonprojective) :
    meshRelation c x ∈ meshIdealSub c _ _ :=
  Submodule.subset_span ⟨_, _, meshRelation c x, ⟨x, rfl, rfl, by simp⟩, 𝟙 _, 𝟙 _, by simp⟩

variable {S : Set V} (hS : Q.IsTauClosed S) (c : MeshCoefficients k Q)

theorem path_mem_outside {x y : V} (p : Quiver.Path x y) {v : V} (hv : v ∈ p.vertices)
    (hvS : v ∉ S) : LinearPaths.path (k := k) p ∈ FullSub.outside k S x y :=
  Submodule.subset_span ⟨p, ⟨v, hv, hvS⟩, rfl⟩

/-- The image in `kQ` of the mesh relation of `Q_S` at `x`. -/
def inclMesh (x : (TranslationQuiver.restrict hS).nonprojective) :
    LinearPaths.obj (k := k) (Q.tau (TranslationQuiver.restrictNonproj hS x)).1 ⟶
      LinearPaths.obj (TranslationQuiver.restrictNonproj hS x).1 :=
  FullSub.inclL k _ _ (meshRelation (c.restrict hS) x)

/-- The mesh relation of `Q_S` maps to the mesh relation of `Q`, up to the terms
with middle vertex outside `S`. -/
theorem inclL_meshRelation_sub_mem (x : (TranslationQuiver.restrict hS).nonprojective) :
    inclMesh hS c x - meshRelation c (TranslationQuiver.restrictNonproj hS x) ∈
      FullSub.outside k S _ _ := by
  classical
  set x' := TranslationQuiver.restrictNonproj hS x
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Σ y : V, y ⟶ x'.1))
    (fun a ↦ a.1 ∈ S) fun a ↦ ((c x' a.1 a.2 : kˣ) : k) •
      LinearPaths.path (k := k) ((Q.mate x' a.1 a.2).toPath.comp a.2.toPath)
  have hS' : inclMesh hS c x =
      ∑ a ∈ Finset.univ.filter (fun a : Σ y : V, y ⟶ x'.1 ↦ a.1 ∈ S),
        ((c x' a.1 a.2 : kˣ) : k) •
          LinearPaths.path (k := k) ((Q.mate x' a.1 a.2).toPath.comp a.2.toPath) := by
    unfold inclMesh meshRelation
    rw [map_sum]
    refine Finset.sum_bij' (fun b _ ↦ ⟨b.1.val, b.2⟩)
      (fun a ha ↦ ⟨FullSub.mk a.1 (Finset.mem_filter.1 ha).2, a.2⟩) ?_ ?_ ?_ ?_ ?_
    · intro b _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact b.1.val_mem
    · intro a _; exact Finset.mem_univ _
    · intro b _; rfl
    · intro a _; rfl
    · intro b _
      rw [map_smul, LinearPaths.mapPaths_path, Prefunctor.mapPath_comp,
        Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath]
      rfl
  unfold meshRelation at hsplit ⊢
  rw [hS']
  erw [← hsplit]
  rw [sub_add_cancel_left]
  refine neg_mem (sum_mem fun a ha ↦ Submodule.smul_mem _ _ ?_)
  refine path_mem_outside _ (v := a.1) ?_ (Finset.mem_filter.1 ha).2
  rw [Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath, List.mem_append]
  exact Or.inr (by simp)

/-- The inclusion maps the mesh ideal of `Q_S` into the mesh ideal of `Q` plus
the paths through vertices outside `S`. -/
theorem inclL_mem_ideal_sup_outside {a b : FullSub S}
    {f : LinearPaths.obj (k := k) a ⟶ LinearPaths.obj b}
    (hf : f ∈ meshIdealSub (c.restrict hS) (LinearPaths.obj a) (LinearPaths.obj b)) :
    FullSub.inclL k a b f ∈ meshIdealSub c _ _ ⊔ FullSub.outside k S a.val b.val := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨A, B, r, hr, u, w', rfl⟩ := hg
      obtain ⟨A', rfl⟩ : ∃ A' : FullSub S, LinearPaths.obj (k := k) A' = A := ⟨A, rfl⟩
      obtain ⟨B', rfl⟩ : ∃ B' : FullSub S, LinearPaths.obj (k := k) B' = B := ⟨B, rfl⟩
      obtain ⟨x, hX, hY, rfl⟩ := hr
      change A' = ((TranslationQuiver.restrict hS).tau x).1 at hX
      change B' = x.1 at hY
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [LinearPaths.mapPaths_comp, LinearPaths.mapPaths_comp]
      have hrel := inclL_meshRelation_sub_mem hS c x
      have e : inclMesh hS c x = meshRelation c (TranslationQuiver.restrictNonproj hS x) +
          (inclMesh hS c x - meshRelation c (TranslationQuiver.restrictNonproj hS x)) := by abel
      change _ ≫ inclMesh hS c x ≫ _ ∈ _
      rw [e, Preadditive.add_comp, Preadditive.comp_add]
      refine Submodule.add_mem_sup ?_ ?_
      · exact Submodule.subset_span ⟨_, _, _, ⟨TranslationQuiver.restrictNonproj hS x, rfl, rfl,
          by simp⟩, _, _, rfl⟩
      · exact FullSub.comp_outside_mem k _ (FullSub.outside_comp_mem k hrel _)
  | zero => simp
  | add g g' _ _ hg hg' => rw [map_add]; exact add_mem hg hg'
  | smul t g _ hg => rw [map_smul]; exact Submodule.smul_mem _ t hg

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

theorem proj_mem_span_outside {S : Set V} {x y : V} (d : ℕ)
    {o : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y} (ho : o ∈ FullSub.outside k S x y) :
    LinearPaths.proj d x y o ∈ Submodule.span k {f | ∃ p : Quiver.Path x y, p.length = d ∧
      (∃ v ∈ p.vertices, v ∉ S) ∧ f = LinearPaths.path p} := by
  induction ho using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      rw [LinearPaths.proj_path]
      split_ifs with h
      · exact Submodule.subset_span ⟨p, h, hp, rfl⟩
      · exact zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul t a _ ha => rw [map_smul]; exact Submodule.smul_mem _ t ha

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u v w

open ScalarMeshCategory

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {S : Set V} (hS : Q.IsTauClosed S)
  (c : MeshCoefficients k Q) [DecidablePred (· ∈ S)]

/-- A family of morphisms of `kQ_S` parallel to the arrows of `Q_S`. -/
abbrev PathFamily (S : Set V) :=
  ∀ b : Σ u v : FullSub S, u ⟶ v, LinearPaths.obj (k := k) b.1 ⟶ LinearPaths.obj (k := k) b.2.1

/-- Extend a family on `Q_S` by zero to a family on `Q`. -/
def liftFamily (F : PathFamily (k := k) S) : ArrowFamily c := fun b ↦
  if h : b.1 ∈ S ∧ b.2.1 ∈ S then
    (RelationCategory.functor k (meshRelations c)).map
      (FullSub.inclL k (FullSub.mk b.1 h.1) (FullSub.mk b.2.1 h.2)
        (F ⟨FullSub.mk b.1 h.1, FullSub.mk b.2.1 h.2, b.2.2⟩))
  else 0

theorem liftFamily_mem {m : ℕ} (F : PathFamily (k := k) S)
    (hF : ∀ b, F b ∈ LinearPaths.degreePart (k := k) m b.1 b.2.1) :
    liftFamily c F ∈ familiesDeg c m := by
  intro b
  unfold liftFamily
  split_ifs with h
  · exact ⟨_, LinearPaths.mapPaths_mem_degreePart (FullSub.incl S)
      (hF ⟨FullSub.mk b.1 h.1, FullSub.mk b.2.1 h.2, b.2.2⟩), rfl⟩
  · exact zero_mem _

/-- The derivative of a family on `Q_S`, computed in `kQ_S`. -/
def derivPath (F : PathFamily (k := k) S) (x : (TranslationQuiver.restrict hS).nonprojective) :
    LinearPaths.obj (k := k) ((TranslationQuiver.restrict hS).tau x).1 ⟶ LinearPaths.obj x.1 :=
  ∑ b : Σ y : FullSub S, y ⟶ x.1, ((c.restrict hS x b.1 b.2 : kˣ) : k) •
    (F ⟨_, b.1, (TranslationQuiver.restrict hS).mate x b.1 b.2⟩ ≫ LinearPaths.arrow b.2 +
      LinearPaths.arrow ((TranslationQuiver.restrict hS).mate x b.1 b.2) ≫ F ⟨b.1, x.1, b.2⟩)

theorem map_derivPath (F : PathFamily (k := k) S)
    (x : (TranslationQuiver.restrict hS).nonprojective) :
    (RelationCategory.functor k (meshRelations (c.restrict hS))).map (derivPath hS c F x) =
      meshDerivative (c.restrict hS)
        (fun b ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map (F b)) x := by
  simp only [derivPath, meshDerivative, Functor.map_sum, Functor.map_smul, Functor.map_add,
    Functor.map_comp]
  rfl

/-- The image in `kQ` of `derivPath`. -/
def inclDeriv (F : PathFamily (k := k) S) (x : (TranslationQuiver.restrict hS).nonprojective) :
    LinearPaths.obj (k := k) (Q.tau (TranslationQuiver.restrictNonproj hS x)).1 ⟶
      LinearPaths.obj (TranslationQuiver.restrictNonproj hS x).1 :=
  FullSub.inclL k _ _ (derivPath hS c F x)

theorem meshDerivative_liftFamily (F : PathFamily (k := k) S)
    (x : (TranslationQuiver.restrict hS).nonprojective) :
    meshDerivative c (liftFamily c F) (TranslationQuiver.restrictNonproj hS x) =
      (RelationCategory.functor k (meshRelations c)).map (inclDeriv hS c F x) := by
  classical
  set x' := TranslationQuiver.restrictNonproj hS x
  have hτ : (Q.tau x').1 ∈ S := (hS x'.1 x'.2).1 x.1.val_mem
  unfold meshDerivative
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Σ y : V, y ⟶ x'.1 ↦ a.1 ∈ S)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun a : Σ y : V, y ⟶ x'.1 ↦ a.1 ∉ S),
    add_zero]
  swap
  · intro a ha
    have ha' := (Finset.mem_filter.1 ha).2
    unfold liftFamily
    rw [dif_neg (fun h ↦ ha' h.2), dif_neg (fun h ↦ ha' h.1), Limits.zero_comp,
      Limits.comp_zero, add_zero]
    exact smul_zero _
  unfold inclDeriv derivPath
  rw [map_sum, Functor.map_sum]
  symm
  refine Finset.sum_bij' (fun b _ ↦ ⟨b.1.val, b.2⟩)
    (fun a ha ↦ ⟨FullSub.mk a.1 (Finset.mem_filter.1 ha).2, a.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro b _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact b.1.val_mem
  · intro a _; exact Finset.mem_univ _
  · intro b _; rfl
  · intro a _; rfl
  · intro b _
    unfold liftFamily
    rw [dif_pos ⟨hτ, b.1.val_mem⟩, dif_pos ⟨b.1.val_mem, x.1.val_mem⟩]
    rw [map_smul, Functor.map_smul, map_add, Functor.map_add, LinearPaths.mapPaths_comp,
      LinearPaths.mapPaths_comp, Functor.map_comp, Functor.map_comp, LinearPaths.mapPaths_arrow,
      LinearPaths.mapPaths_arrow]
    rfl

include hS in
theorem meshDerivative_liftFamily_of_not_mem (F : PathFamily (k := k) S) (x : Q.nonprojective)
    (hx : x.1 ∉ S) : meshDerivative c (liftFamily c F) x = 0 := by
  have hτ : (Q.tau x).1 ∉ S := fun h ↦ hx ((hS x.1 x.2).2 h)
  unfold meshDerivative
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  unfold liftFamily
  rw [dif_neg (fun h ↦ hτ h.1), dif_neg (fun h ↦ hx h.2), Limits.zero_comp, Limits.comp_zero,
    add_zero]
  exact smul_zero _

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u v w

open ScalarMeshCategory

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {S : Set V} (hS : Q.IsTauClosed S)
  (c : MeshCoefficients k Q) [DecidablePred (· ∈ S)]

theorem derivPath_mem {m : ℕ} (F : PathFamily (k := k) S)
    (hF : ∀ b, F b ∈ LinearPaths.degreePart (k := k) m b.1 b.2.1)
    (x : (TranslationQuiver.restrict hS).nonprojective) :
    derivPath hS c F x ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := by
  refine sum_mem fun b _ ↦ Submodule.smul_mem _ _ (add_mem ?_ ?_)
  · exact LinearPaths.comp_arrow_mem_degreePart
      (hF ⟨_, b.1, (TranslationQuiver.restrict hS).mate x b.1 b.2⟩) b.2
  · have := LinearPaths.comp_mem_degreePart
      (LinearPaths.arrow_mem_degreePart (k := k) ((TranslationQuiver.restrict hS).mate x b.1 b.2))
      (hF ⟨b.1, x.1, b.2⟩)
    rwa [add_comm] at this

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]

/-- A degree-`(m+1)` element of the mesh ideal of `Q` plus the paths outside `S`
gives a combination of rows through vertices outside `S`. -/
theorem single_mem_imageD_of_mem_sup {m : ℕ}
    (hout : ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
      x.1 ∈ S → (∃ v ∈ w.vertices, v ∉ S) → row c x w ∈ imageD c m)
    (x : Q.nonprojective) (hx : x.1 ∈ S)
    {G : LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj x.1}
    (hG : G ∈ meshIdealSub c _ _ ⊔ FullSub.outside k S _ _)
    (hGd : G ∈ LinearPaths.degreePart (k := k) (m + 1) _ _) :
    Pi.single x ((RelationCategory.functor k (meshRelations c)).map G) ∈ imageD c m := by
  obtain ⟨i, hi, o, ho, hio⟩ := Submodule.mem_sup.1 hG
  have hproj : G = LinearPaths.proj (m + 1) _ _ i + LinearPaths.proj (m + 1) _ _ o := by
    rw [← map_add, hio, LinearPaths.proj_of_mem hGd, if_pos rfl]
  have hi' : (RelationCategory.functor k (meshRelations c)).map
      (LinearPaths.proj (m + 1) _ _ i) = 0 := by
    rw [RelationCategory.functor_map_eq_zero_iff]
    exact LinearPaths.proj_mem_linearSpan _ (meshRelations_homogeneous c) _ hi
  rw [hproj, Functor.map_add, hi', zero_add]
  have hspan := proj_mem_span_outside (k := k) (m + 1) ho
  generalize LinearPaths.proj (m + 1) _ _ o = o' at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, hp, hpS, rfl⟩ := hg
      exact hout x p hp hx hpS
  | zero => rw [Functor.map_zero, Pi.single_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Functor.map_add, Pi.single_add]; exact add_mem ha hb
  | smul t a _ ha => rw [Functor.map_smul, Pi.single_smul]; exact Submodule.smul_mem _ t ha

variable [Fintype V]

set_option maxHeartbeats 800000 in
/-- **Proposition 5.1, transfer to a `τ`-closed subquiver**
(`prop:periodic-localization`, last paragraph). If `D_m(C(Q_S))` is surjective
and every row through a vertex outside `S` is in the image of `D_m(C(Q))`, then
every row at a vertex of `S` is in that image. -/
theorem row_mem_imageD_of_restrict {m : ℕ}
    (hsurj : MeshDerivativeSurjective (c.restrict hS) m)
    (hout : ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
      x.1 ∈ S → (∃ v ∈ w.vertices, v ∉ S) → row c x w ∈ imageD c m)
    (x : Q.nonprojective) (hx : x.1 ∈ S) (w : Quiver.Path (Q.tau x).1 x.1)
    (hw : w.length = m + 1) : row c x w ∈ imageD c m := by
  by_cases hin : ∀ v ∈ w.vertices, v ∈ S
  swap
  · push_neg at hin; exact hout x w hw hx hin
  let xS : (TranslationQuiver.restrict hS).nonprojective := ⟨FullSub.mk x.1 hx, x.2⟩
  let wS : Quiver.Path ((TranslationQuiver.restrict hS).tau xS).1 xS.1 :=
    FullSub.liftPath _ _ w hin
  have hwS : wS.length = m + 1 := by rw [FullSub.length_liftPath, hw]
  obtain ⟨f, hf, hDf⟩ := hsurj (row (c.restrict hS) xS wS) fun x'' ↦ by
    by_cases h : x'' = xS
    · subst h; rw [row, Pi.single_eq_same, ← hwS]; exact pathMor_mem_degreePart _ wS
    · rw [row, Pi.single_eq_of_ne h]; exact zero_mem _
  choose F hF hFf using fun b ↦ hf b
  have hFf' : f = fun b ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map
      (F b) := funext fun b ↦ (hFf b).symm
  have hlift := liftFamily_mem c F hF
  suffices h : meshDerivative c (liftFamily c F) - row c x w ∈ imageD c m by
    have := sub_mem (Submodule.mem_map.2 ⟨liftFamily c F, hlift, rfl⟩ :
      meshDerivative c (liftFamily c F) ∈ imageD c m) h
    rwa [sub_sub_cancel] at this
  rw [← Finset.univ_sum_single (meshDerivative c (liftFamily c F) - row c x w)]
  refine sum_mem fun x' _ ↦ ?_
  by_cases hx' : x'.1 ∈ S
  · let x'S : (TranslationQuiver.restrict hS).nonprojective := ⟨FullSub.mk x'.1 hx', x'.2⟩
    have hD := meshDerivative_liftFamily hS c F x'S
    have hDS := congrFun hDf x'S
    rw [hFf', ← map_derivPath] at hDS
    by_cases hxx : x' = x
    · subst hxx
      have e1 : (meshDerivative c (liftFamily c F) - row c x' w) x' =
          (RelationCategory.functor k (meshRelations c)).map
            (inclDeriv hS c F x'S - LinearPaths.path w) := by
        rw [Pi.sub_apply, row, Pi.single_eq_same, Functor.map_sub, ← hD]
        rfl
      rw [e1]
      refine single_mem_imageD_of_mem_sup c hout x' hx' ?_ ?_
      · have hw' : LinearPaths.path (k := k) w = FullSub.inclL k _ _ (LinearPaths.path wS) := by
          rw [LinearPaths.mapPaths_path, FullSub.incl_mapPath_liftPath]
        have hE : derivPath hS c F x'S - LinearPaths.path wS ∈
            meshIdealSub (c.restrict hS) _ _ := by
          rw [row, Pi.single_eq_same] at hDS
          have := (RelationCategory.functor_map_eq_zero_iff (k := k) _ _).1
            (show (RelationCategory.functor k (meshRelations (c.restrict hS))).map
              (derivPath hS c F x'S - LinearPaths.path wS) = 0 by
                rw [Functor.map_sub, hDS]; exact sub_self _)
          exact this
        have := inclL_mem_ideal_sup_outside hS c hE
        rw [map_sub] at this
        unfold inclDeriv
        rw [hw']
        exact this
      · unfold inclDeriv
        refine sub_mem (LinearPaths.mapPaths_mem_degreePart (FullSub.incl S)
          (derivPath_mem hS c F hF x'S)) ?_
        rw [← hw]; exact LinearPaths.path_mem_degreePart w
    · have e1 : (meshDerivative c (liftFamily c F) - row c x w) x' =
          (RelationCategory.functor k (meshRelations c)).map (inclDeriv hS c F x'S) := by
        rw [Pi.sub_apply, row, Pi.single_eq_of_ne hxx, sub_zero, ← hD]
      rw [e1]
      refine single_mem_imageD_of_mem_sup c hout x' hx' ?_ ?_
      · have hne : x'S ≠ xS := fun h ↦ hxx (Subtype.ext (by
          have := congrArg (fun z : (TranslationQuiver.restrict hS).nonprojective ↦ z.1.val) h
          exact this))
        rw [row, Pi.single_eq_of_ne hne] at hDS
        have hE : derivPath hS c F x'S ∈ meshIdealSub (c.restrict hS) _ _ :=
          (RelationCategory.functor_map_eq_zero_iff (k := k) _ _).1 hDS
        exact inclL_mem_ideal_sup_outside hS c hE
      · exact LinearPaths.mapPaths_mem_degreePart (FullSub.incl S) (derivPath_mem hS c F hF x'S)
  · have hne : x' ≠ x := fun h ↦ hx' (h ▸ hx)
    rw [Pi.sub_apply, meshDerivative_liftFamily_of_not_mem hS c F x' hx', row,
      Pi.single_eq_of_ne hne, sub_zero, Pi.single_zero]
    exact zero_mem _

end MultiplicativeBasisDeformations
