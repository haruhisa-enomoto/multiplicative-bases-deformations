import MultiplicativeBasisDeformations.Foundations.MeshGrading

/-!
# Gradings of mesh categories by path weights

For the covering formula `eq:walk-hom-sum` (`scalar-normalization.tex:203–209`):
"Paths lift uniquely from a chosen starting vertex. Contextual mesh relations
lift uniquely as well: all terms of a mesh have the same lifted endpoints […]
The relation ideal therefore decomposes by lifted endpoints, just as the path
spaces do."

A *path weight* assigns to each path an element of a monoid, multiplicatively.
When all terms of each mesh relation have the same weight, the mesh ideal is
homogeneous and the Hom spaces of `C(Q, c)` are the internal direct sums of
their weight parts (`iSupIndep_wPart`, `iSup_wPart`), compatibly with
composition (`comp_mem_wPart`). For the walk-class weight of the cover
(`DeckGrading.lean`) the weight part of degree `g` is the space
`C̃(X̃, gỸ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w u'

/-- A multiplicative weight on the paths of a quiver. -/
structure PathWeight (V : Type v) [Quiver.{w} V] (G : Type u') [Monoid G] where
  deg : ∀ {x y : V}, Quiver.Path x y → G
  deg_nil : ∀ x : V, deg (Quiver.Path.nil : Quiver.Path x x) = 1
  deg_comp : ∀ {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z),
    deg (p.comp q) = deg p * deg q

namespace LinearPaths

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {G : Type u'} [Monoid G]
  [DecidableEq G] (wt : PathWeight V G)

/-- The weight-`g` part of `kQ(x, y)`. -/
def wpart (g : G) (x y : V) : Submodule k (obj (k := k) x ⟶ obj (k := k) y) :=
  Submodule.span k {f | ∃ p : Quiver.Path x y, wt.deg p = g ∧ path p = f}

/-- The projection onto the weight-`g` part. -/
def wproj (g : G) (x y : V) :
    (obj (k := k) x ⟶ obj (k := k) y) →ₗ[k] (obj (k := k) x ⟶ obj (k := k) y) where
  toFun f := ofFinsupp (Finsupp.filter (fun p : Quiver.Path x y ↦ wt.deg p = g) (toFinsupp f))
  map_add' f g := by
    change Finsupp.filter _ (toFinsupp f + toFinsupp g) = _
    rw [Finsupp.filter_add]; rfl
  map_smul' c f := by
    change Finsupp.filter _ (c • toFinsupp f) = _
    rw [Finsupp.filter_smul]; rfl

variable {wt}

theorem path_mem_wpart {x y : V} (p : Quiver.Path x y) :
    path (k := k) p ∈ wpart (k := k) wt (wt.deg p) x y :=
  Submodule.subset_span ⟨p, rfl, rfl⟩

theorem wproj_path {x y : V} (g : G) (p : Quiver.Path x y) :
    wproj (k := k) wt g x y (path p) = if wt.deg p = g then path p else 0 := by
  change ofFinsupp (Finsupp.filter _ (Finsupp.single p 1)) = _
  split_ifs with h
  · rw [Finsupp.filter_single_of_pos (fun p : Quiver.Path x y ↦ wt.deg p = g) h]; rfl
  · rw [Finsupp.filter_single_of_neg (fun p : Quiver.Path x y ↦ wt.deg p = g) h]; rfl

theorem wproj_of_mem {g h : G} {x y : V} {f : obj (k := k) x ⟶ obj (k := k) y}
    (hf : f ∈ wpart (k := k) wt h x y) : wproj (k := k) wt g x y f = if h = g then f else 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      rw [wproj_path, hp]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]; split_ifs <;> simp
  | smul c a _ ha => rw [map_smul, ha]; split_ifs <;> simp

theorem wproj_mem {g : G} {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    wproj (k := k) wt g x y f ∈ wpart (k := k) wt g x y := by
  induction f using induction_on with
  | h0 => simp
  | hadd f f' hf hf' => rw [map_add]; exact add_mem hf hf'
  | hsingle p c =>
      rw [map_smul, wproj_path]
      split_ifs with h
      · exact Submodule.smul_mem _ c (h ▸ path_mem_wpart p)
      · simp

/-- A morphism of `kQ` is the sum of its weight components, over a finite set of
weights. -/
theorem eq_sum_wproj {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    ∃ s : Finset G, f = ∑ g ∈ s, wproj (k := k) wt g x y f := by
  refine ⟨(toFinsupp f).support.image wt.deg, ?_⟩
  apply_fun toFinsupp using fun _ _ h ↦ h
  ext p
  change toFinsupp f p = (∑ g ∈ _, Finsupp.filter (fun p : Quiver.Path x y ↦ wt.deg p = g)
    (toFinsupp f) : Quiver.Path x y →₀ k) p
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.filter_apply]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (Finset.mem_image.2 ⟨p, Finsupp.mem_support_iff.2 hne, rfl⟩)

theorem comp_mem_wpart {g h : G} {x y z : V} {f : obj (k := k) x ⟶ obj (k := k) y}
    {f' : obj (k := k) y ⟶ obj (k := k) z} (hf : f ∈ wpart (k := k) wt g x y)
    (hf' : f' ∈ wpart (k := k) wt h y z) : f ≫ f' ∈ wpart (k := k) wt (g * h) x z := by
  induction hf using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨p, rfl, rfl⟩ := ha
      induction hf' using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨q, rfl, rfl⟩ := hb
          rw [path_comp_path, ← wt.deg_comp]
          exact path_mem_wpart _
      | zero => simp
      | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact add_mem ha hb
      | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | smul c a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c ha

open CategoricalIdeal in
/-- An ideal generated by weight-homogeneous relations is stable under the
weight projections. -/
theorem wproj_mem_linearSpan (R : ∀ X Y : LinearPaths k V, Set (X ⟶ Y))
    (hR : ∀ (X Y : V) (r : obj (k := k) X ⟶ obj (k := k) Y), r ∈ R X Y →
      ∃ e, r ∈ wpart (k := k) wt e X Y)
    (g : G) {X Y : V} {f : obj (k := k) X ⟶ obj (k := k) Y}
    (hf : f ∈ (HomIdeal.linearSpan k R).hom (obj X) (obj Y)) :
    wproj (k := k) wt g X Y f ∈ (HomIdeal.linearSpan k R).hom (obj X) (obj Y) := by
  change f ∈ HomIdeal.generatedHomSubmodule k R (obj X) (obj Y) at hf
  change _ ∈ HomIdeal.generatedHomSubmodule k R (obj X) (obj Y)
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨A, B, r, hr, a, b, rfl⟩ := hf
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
                  wpart (k := k) wt (wt.deg p * e * wt.deg q) X Y := by
                have := comp_mem_wpart (comp_mem_wpart (path_mem_wpart p) he) (path_mem_wpart q)
                simpa [Category.assoc] using this
              have hgen : path (k := k) p ≫ r ≫ path q ∈
                  HomIdeal.generatedHomSubmodule k R (obj X) (obj Y) :=
                Submodule.subset_span ⟨obj A', obj B', r, hr, path p, path q, rfl⟩
              have : (c • path (k := k) p) ≫ r ≫ (c' • path q) =
                  (c * c') • (path (k := k) p ≫ r ≫ path q) := by
                simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
              rw [this, map_smul, wproj_of_mem hdeg]
              split_ifs
              · exact Submodule.smul_mem _ _ hgen
              · simp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end LinearPaths

namespace ScalarMeshCategory

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q) {G : Type u'} [Monoid G] [DecidableEq G] (wt : PathWeight V G)

/-- All terms of every mesh have the same weight. -/
def MeshHomogeneous : Prop :=
  ∀ (x : Q.nonprojective) (a b : Σ y : V, y ⟶ x.1),
    wt.deg ((Q.mate x a.1 a.2).toPath.comp a.2.toPath) =
      wt.deg ((Q.mate x b.1 b.2).toPath.comp b.2.toPath)

variable {c wt}

theorem meshRelation_mem_wpart (hw : MeshHomogeneous (Q := Q) wt) (x : Q.nonprojective) :
    ∃ e, meshRelation c x ∈ LinearPaths.wpart (k := k) wt e (Q.tau x).1 x.1 := by
  by_cases hne : Nonempty (Σ y : V, y ⟶ x.1)
  · obtain ⟨a₀⟩ := hne
    refine ⟨wt.deg ((Q.mate x a₀.1 a₀.2).toPath.comp a₀.2.toPath), ?_⟩
    unfold meshRelation
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ ?_
    rw [hw x a₀ a]
    exact LinearPaths.path_mem_wpart _
  · refine ⟨1, ?_⟩
    unfold meshRelation
    rw [Finset.sum_eq_zero fun a _ ↦ absurd ⟨a⟩ hne]
    exact Submodule.zero_mem _

theorem meshRelations_wHomogeneous (hw : MeshHomogeneous (Q := Q) wt) (X Y : V)
    (r : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y)
    (hr : r ∈ meshRelations c (LinearPaths.obj X) (LinearPaths.obj Y)) :
    ∃ e, r ∈ LinearPaths.wpart (k := k) wt e X Y := by
  obtain ⟨x, hX, hY, rfl⟩ := hr
  change X = (Q.tau x).1 at hX
  change Y = x.1 at hY
  subst hX hY
  obtain ⟨e, he⟩ := meshRelation_mem_wpart (c := c) hw x
  refine ⟨e, ?_⟩
  convert he using 1
  exact (Category.id_comp _).trans (Category.comp_id _)

variable (c wt)

/-- The weight-`g` part of `C(x, y)`. -/
def wPart (g : G) (x y : V) : Submodule k (obj c x ⟶ obj c y) :=
  (LinearPaths.wpart (k := k) wt g x y).map (quotL c x y)

variable {c wt}

theorem pathMor_mem_wPart {x y : V} (p : Quiver.Path x y) :
    pathMor c p ∈ wPart c wt (wt.deg p) x y :=
  ⟨_, LinearPaths.path_mem_wpart p, rfl⟩

theorem ker_quotL_le_w (hw : MeshHomogeneous (Q := Q) wt) (g : G) (x y : V) :
    LinearMap.ker (quotL c x y) ≤
      LinearMap.ker ((quotL c x y).comp (LinearPaths.wproj (k := k) wt g x y)) := by
  intro F hF
  rw [LinearMap.mem_ker] at hF ⊢
  change (RelationCategory.functor k (meshRelations c)).map F = 0 at hF
  change (RelationCategory.functor k (meshRelations c)).map (LinearPaths.wproj wt g x y F) = 0
  rw [RelationCategory.functor_map_eq_zero_iff] at hF ⊢
  exact LinearPaths.wproj_mem_linearSpan _ (meshRelations_wHomogeneous hw) g hF

variable (c wt) in
/-- The weight-`g` projection on the Hom spaces of `C(Q, c)`. -/
def wProj (hw : MeshHomogeneous (Q := Q) wt) (g : G) (x y : V) :
    (obj c x ⟶ obj c y) →ₗ[k] (obj c x ⟶ obj c y) :=
  ((LinearMap.ker (quotL c x y)).liftQ _ (ker_quotL_le_w hw g x y)).comp
    ((quotL c x y).quotKerEquivOfSurjective (quotL_surjective c x y)).symm.toLinearMap

theorem wProj_apply (hw : MeshHomogeneous (Q := Q) wt) (g : G) {x y : V}
    (F : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    wProj c wt hw g x y ((RelationCategory.functor k (meshRelations c)).map F) =
      (RelationCategory.functor k (meshRelations c)).map (LinearPaths.wproj wt g x y F) := by
  have h1 : ((quotL c x y).quotKerEquivOfSurjective (quotL_surjective c x y)).symm
      ((RelationCategory.functor k (meshRelations c)).map F) = Submodule.Quotient.mk F := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [wProj, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [h1]
  rfl

theorem wProj_of_mem (hw : MeshHomogeneous (Q := Q) wt) {g h : G} {x y : V}
    {f : obj c x ⟶ obj c y} (hf : f ∈ wPart c wt h x y) :
    wProj c wt hw g x y f = if h = g then f else 0 := by
  obtain ⟨F, hF, rfl⟩ := hf
  change wProj c wt hw g x y ((RelationCategory.functor k (meshRelations c)).map F) = _
  rw [wProj_apply, LinearPaths.wproj_of_mem hF]
  split_ifs <;> simp

theorem wProj_mem (hw : MeshHomogeneous (Q := Q) wt) (g : G) {x y : V} (f : obj c x ⟶ obj c y) :
    wProj c wt hw g x y f ∈ wPart c wt g x y := by
  obtain ⟨F, rfl⟩ := quotL_surjective c x y f
  change wProj c wt hw g x y ((RelationCategory.functor k (meshRelations c)).map F) ∈ _
  rw [wProj_apply]
  exact ⟨_, LinearPaths.wproj_mem F, rfl⟩

/-- **The covering formula**, independence: the weight parts are independent. -/
theorem iSupIndep_wPart (hw : MeshHomogeneous (Q := Q) wt) (x y : V) :
    iSupIndep fun g ↦ wPart c wt g x y := by
  rw [iSupIndep_def]
  intro g
  rw [Submodule.disjoint_def]
  intro f hg hsup
  have hle : (⨆ e, ⨆ (_ : e ≠ g), wPart c wt e x y) ≤ LinearMap.ker (wProj c wt hw g x y) := by
    refine iSup₂_le fun e he f' hf' ↦ ?_
    rw [LinearMap.mem_ker, wProj_of_mem hw hf', if_neg he]
  have h1 := wProj_of_mem hw (g := g) hg
  rw [if_pos rfl] at h1
  rw [← h1]
  exact hle hsup

/-- A morphism is the sum of its weight components, over a finite set of
weights. -/
theorem eq_sum_wProj (hw : MeshHomogeneous (Q := Q) wt) {x y : V} (f : obj c x ⟶ obj c y) :
    ∃ s : Finset G, f = ∑ g ∈ s, wProj c wt hw g x y f := by
  obtain ⟨F, rfl⟩ := quotL_surjective c x y f
  obtain ⟨s, hs⟩ := LinearPaths.eq_sum_wproj (k := k) (wt := wt) F
  refine ⟨s, ?_⟩
  change (RelationCategory.functor k (meshRelations c)).map F =
    ∑ g ∈ s, wProj c wt hw g x y ((RelationCategory.functor k (meshRelations c)).map F)
  simp only [wProj_apply]
  change quotL c x y F = ∑ g ∈ s, quotL c x y (LinearPaths.wproj wt g x y F)
  rw [← map_sum (quotL c x y)]
  exact congrArg (quotL c x y) hs

/-- **The covering formula**, spanning. -/
theorem iSup_wPart (hw : MeshHomogeneous (Q := Q) wt) (x y : V) :
    (⨆ g, wPart c wt g x y) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  obtain ⟨s, hs⟩ := eq_sum_wProj hw f
  rw [hs]
  exact Submodule.sum_mem _ fun g _ ↦ Submodule.mem_iSup_of_mem g (wProj_mem hw g f)

theorem comp_mem_wPart {g h : G} {x y z : V} {f : obj c x ⟶ obj c y} {f' : obj c y ⟶ obj c z}
    (hf : f ∈ wPart c wt g x y) (hf' : f' ∈ wPart c wt h y z) :
    f ≫ f' ∈ wPart c wt (g * h) x z := by
  obtain ⟨F, hF, rfl⟩ := hf
  obtain ⟨F', hF', rfl⟩ := hf'
  refine ⟨F ≫ F', LinearPaths.comp_mem_wpart hF hF', ?_⟩
  change (RelationCategory.functor k (meshRelations c)).map (F ≫ F') = _
  rw [Functor.map_comp]
  rfl

end ScalarMeshCategory

end MultiplicativeBasisDeformations
