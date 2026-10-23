module

public import MultiplicativeBasisDeformations.Foundations.PeriodicComponents

/-!
# Object quotients of scalar mesh categories

`graded-category.tex` (`eq:mesh-object-quotient`) and Subsection 5.2
(`mesh-deformations.tex`).

* The retraction `kQ → kQ_S` maps the mesh ideal of `Q` into that of `Q_S`
  (`restrict_mem_meshIdealSub`): a mesh relation based in `S` restricts to the
  mesh relation of `Q_S`, and one based outside `S` consists of paths through
  vertices outside `S`, which the retraction kills.
* In the object quotient `C/[D]`, a morphism of `kQ` vanishes exactly when it
  lies in the mesh ideal plus the paths through `D`
  (`objectQuotient_map_eq_zero_iff`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

open ScalarMeshCategory TranslationQuiver CategoricalIdeal

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

namespace FullSub

variable {S : Set V}

theorem restrict_eq_zero_of_mem_outside {a b : FullSub S}
    {o : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val} (ho : o ∈ outside k S _ _) :
    restrict k a b o = 0 := by
  classical
  induction ho using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, ⟨v, hv, hvS⟩, rfl⟩ := hf
      simp only [restrict, LinearPaths.extend_path, restrictPath]
      rw [dif_neg (fun h ↦ hvS (h v hv))]
  | zero => simp
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul t f _ hf => rw [map_smul, hf, smul_zero]

end FullSub

variable {S : Set V} (hS : Q.IsTauClosed S) (c : MeshCoefficients k Q)

theorem restrict_meshRelation (x : (TranslationQuiver.restrict hS).nonprojective) :
    FullSub.restrict k _ _ (meshRelation c (restrictNonproj hS x)) =
      meshRelation (c.restrict hS) x := by
  have h := inclL_meshRelation_sub_mem hS c x
  have h0 : FullSub.restrict k ((TranslationQuiver.restrict hS).tau x).1 x.1
      (inclMesh hS c x - meshRelation c (restrictNonproj hS x)) = 0 :=
    FullSub.restrict_eq_zero_of_mem_outside h
  have h1 : FullSub.restrict k ((TranslationQuiver.restrict hS).tau x).1 x.1
      (inclMesh hS c x) = meshRelation (c.restrict hS) x :=
    FullSub.restrict_inclL k _
  rw [map_sub, h1, sub_eq_zero] at h0
  exact h0.symm

theorem restrict_comp_meshRelation_comp {a b : FullSub S}
    (x : (TranslationQuiver.restrict hS).nonprojective)
    (u : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj (Q.tau (restrictNonproj hS x)).1)
    (u' : LinearPaths.obj (k := k) (restrictNonproj hS x).1 ⟶ LinearPaths.obj b.val) :
    FullSub.restrict k a b (u ≫ meshRelation c (restrictNonproj hS x) ≫ u') ∈
      meshIdealSub (c.restrict hS) _ _ := by
  rw [FullSub.restrict_comp k (b := ((TranslationQuiver.restrict hS).tau x).1),
    FullSub.restrict_comp k (b := x.1), restrict_meshRelation]
  exact Submodule.subset_span ⟨_, _, _, ⟨x, rfl, rfl, by simp⟩, _, _, rfl⟩

set_option maxHeartbeats 800000 in
/-- The retraction maps the mesh ideal of `Q` into the mesh ideal of `Q_S`. -/
theorem restrict_mem_meshIdealSub {a b : FullSub S}
    {f : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val}
    (hf : f ∈ meshIdealSub c _ _) :
    FullSub.restrict k a b f ∈ meshIdealSub (c.restrict hS) _ _ := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨A, B, r, hr, u, w', rfl⟩ := hg
      obtain ⟨A', rfl⟩ : ∃ A' : V, LinearPaths.obj (k := k) A' = A := ⟨A, rfl⟩
      obtain ⟨B', rfl⟩ : ∃ B' : V, LinearPaths.obj (k := k) B' = B := ⟨B, rfl⟩
      obtain ⟨z, hX, hY, rfl⟩ := hr
      change A' = (Q.tau z).1 at hX
      change B' = z.1 at hY
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      by_cases hz : z.1 ∈ S
      · exact restrict_comp_meshRelation_comp hS c ⟨FullSub.mk z.1 hz, z.2⟩ u w'
      · have hrel : meshRelation c z ∈ FullSub.outside k S _ _ := by
          refine sum_mem fun a _ ↦ Submodule.smul_mem _ _ (path_mem_outside _ ?_ hz)
          rw [Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath, List.mem_append]
          exact Or.inr (by simp)
        rw [FullSub.restrict_eq_zero_of_mem_outside
          (FullSub.comp_outside_mem k _ (FullSub.outside_comp_mem k hrel _))]
        exact zero_mem _
  | zero => simp
  | add g g' _ _ hg hg' => rw [map_add]; exact add_mem hg hg'
  | smul t g _ hg => rw [map_smul]; exact Submodule.smul_mem _ t hg

/-- The paths through some vertex of `D`, spanned in `kQ`. -/
def through (k : Type u) [Field k] (D : Set V) (x y : V) :
    Submodule k (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :=
  Submodule.span k {f | ∃ p : Quiver.Path x y, (∃ v ∈ p.vertices, v ∈ D) ∧ f = LinearPaths.path p}

theorem outside_eq_through (x y : V) : FullSub.outside k S x y = through k Sᶜ x y := rfl

theorem path_comp_mem_through {D : Set V} {x s y : V} (hs : s ∈ D) (p : Quiver.Path x s)
    (q : Quiver.Path s y) : LinearPaths.path (k := k) (p.comp q) ∈ through k D x y :=
  Submodule.subset_span ⟨p.comp q, ⟨s, by
    rw [Quiver.Path.vertices_comp, List.mem_append]
    exact Or.inr (Quiver.Path.start_mem_vertices q), hs⟩, rfl⟩

theorem comp_mem_through {D : Set V} {x s y : V} (hs : s ∈ D)
    (U : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj s)
    (W : LinearPaths.obj (k := k) s ⟶ LinearPaths.obj y) : U ≫ W ∈ through k D x y := by
  induction U using LinearPaths.induction_on with
  | h0 => simp
  | hadd U₁ U₂ h₁ h₂ => rw [Preadditive.add_comp]; exact add_mem h₁ h₂
  | hsingle p t =>
      induction W using LinearPaths.induction_on with
      | h0 => simp
      | hadd W₁ W₂ h₁ h₂ => rw [Preadditive.comp_add]; exact add_mem h₁ h₂
      | hsingle q t' =>
          rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path]
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (path_comp_mem_through hs p q))

/-- The functor `kQ → C(Q,c)/[D]`. -/
abbrev oqFunctor (D : Set V) : LinearPaths k V ⥤ ObjectQuotient c D :=
  RelationCategory.functor k (meshRelations c) ⋙ RelationCategory.functor k (identityRelations c D)

/-- **The object quotient on `kQ`**: a morphism of `kQ` vanishes in `C/[D]`
exactly when it lies in the mesh ideal plus the paths through `D`. -/
theorem oqFunctor_map_eq_zero_iff (D : Set V) {x y : V}
    (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    (oqFunctor c D).map f = 0 ↔ f ∈ meshIdealSub c _ _ ⊔ through k D x y := by
  set FC := RelationCategory.functor k (meshRelations c)
  set FD := RelationCategory.functor k (identityRelations c D)
  constructor
  · intro h
    change FD.map (FC.map f) = 0 at h
    rw [RelationCategory.functor_map_eq_zero_iff] at h
    change FC.map f ∈ HomIdeal.generatedHomSubmodule k _ _ _ at h
    have hle : HomIdeal.generatedHomSubmodule k (identityRelations c D) (FC.obj (LinearPaths.obj x))
        (FC.obj (LinearPaths.obj y)) ≤
        (meshIdealSub c _ _ ⊔ through k D x y).map (FC.mapLinearMap k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨A, B, r, hr, u, u', rfl⟩
      obtain ⟨s, hs, hX, hY, rfl⟩ := hr
      subst hX hY
      obtain ⟨U, rfl⟩ := FC.map_surjective u
      obtain ⟨U', rfl⟩ := FC.map_surjective u'
      refine ⟨U ≫ U', Submodule.mem_sup_right (comp_mem_through hs U U'), ?_⟩
      simp [FC]
    obtain ⟨f', hf', hff'⟩ := hle h
    have hdiff : f - f' ∈ meshIdealSub c _ _ := by
      have : FC.map (f - f') = 0 := by
        rw [Functor.map_sub, sub_eq_zero]; exact hff'.symm
      exact (RelationCategory.functor_map_eq_zero_iff (k := k) _ _).1 this
    have := add_mem (Submodule.mem_sup_left hdiff) hf'
    rwa [sub_add_cancel] at this
  · intro h
    change FD.map (FC.map f) = 0
    obtain ⟨i, hi, t, ht, rfl⟩ := Submodule.mem_sup.1 h
    have hi' : FC.map i = 0 := (RelationCategory.functor_map_eq_zero_iff (k := k) _ _).2 hi
    rw [Functor.map_add, hi', zero_add]
    clear h
    induction ht using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨p, ⟨v, hv, hvD⟩, rfl⟩ := hg
        obtain ⟨p₁, p₂, rfl⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hv
        rw [← LinearPaths.path_comp_path, Functor.map_comp,
          RelationCategory.functor_map_eq_zero_iff]
        have hid : 𝟙 (FC.obj (LinearPaths.obj v)) ∈ identityRelations c D _ _ :=
          ⟨v, hvD, rfl, rfl, by simp⟩
        have := HomIdeal.composite_mem_linearSpan (K := k) (identityRelations c D)
          (FC.map (LinearPaths.path p₁)) hid (FC.map (LinearPaths.path p₂))
        simpa using this
    | zero => simp
    | add a b _ _ ha hb => rw [Functor.map_add, Functor.map_add, ha, hb, add_zero]
    | smul t a _ ha => rw [Functor.map_smul, Functor.map_smul, ha, smul_zero]

theorem oqFunctor_map_surjective (D : Set V) {x y : V}
    (g : (oqFunctor c D).obj (LinearPaths.obj (k := k) x) ⟶
      (oqFunctor c D).obj (LinearPaths.obj y)) :
    ∃ f, (oqFunctor c D).map f = g := by
  obtain ⟨g', rfl⟩ := (RelationCategory.functor k (identityRelations c D)).map_surjective g
  obtain ⟨f, rfl⟩ := (RelationCategory.functor k (meshRelations c)).map_surjective g'
  exact ⟨f, rfl⟩

/-- The Hom spaces of `C/[D]`, as quotients of the Hom spaces of `kQ`. -/
def oqEquiv (D : Set V) (x y : V) :
    ((LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) ⧸ (meshIdealSub c _ _ ⊔ through k D x y))
      ≃ₗ[k] ((oqFunctor c D).obj (LinearPaths.obj (k := k) x) ⟶
        (oqFunctor c D).obj (LinearPaths.obj y)) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext f
    rw [LinearMap.mem_ker]
    exact (oqFunctor_map_eq_zero_iff c D f).symm)).trans
    (((oqFunctor c D).mapLinearMap k).quotKerEquivOfSurjective
      fun g ↦ oqFunctor_map_surjective c D g)

theorem through_mono {D D' : Set V} (h : D ⊆ D') (x y : V) :
    through k D x y ≤ through k D' x y :=
  Submodule.span_mono fun _ ⟨p, ⟨v, hv, hvD⟩, hg⟩ ↦ ⟨p, ⟨v, hv, h hvD⟩, hg⟩

theorem restrict_mem_through {D : Set (FullSub S)} {a b : FullSub S}
    {f : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val}
    (hf : f ∈ through k (FullSub.val '' D ∪ Sᶜ) a.val b.val) :
    FullSub.restrict k a b f ∈ through k D a b := by
  classical
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, ⟨v, hv, hvD⟩, rfl⟩ := hg
      simp only [FullSub.restrict, LinearPaths.extend_path, FullSub.restrictPath]
      split_ifs with hp
      · rcases hvD with ⟨d, hd, rfl⟩ | hvS
        · refine Submodule.subset_span ⟨_, ⟨d, ?_, hd⟩, rfl⟩
          have hmem : d.val ∈ ((FullSub.incl S).mapPath (FullSub.liftPath a b p hp)).vertices := by
            rw [FullSub.incl_mapPath_liftPath]; exact hv
          rw [LinearPaths.vertices_mapPath, List.mem_map] at hmem
          obtain ⟨d', hd', hdd'⟩ := hmem
          rwa [← FullSub.ext hdd']
        · exact absurd (hp v hv) hvS
      · exact zero_mem _
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul t f _ hf => rw [map_smul]; exact Submodule.smul_mem _ t hf

theorem inclL_mem_through {D : Set (FullSub S)} {a b : FullSub S}
    {f : LinearPaths.obj (k := k) a ⟶ LinearPaths.obj b} (hf : f ∈ through k D a b) :
    FullSub.inclL k a b f ∈ through k (FullSub.val '' D ∪ Sᶜ) a.val b.val := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, ⟨v, hv, hvD⟩, rfl⟩ := hg
      rw [LinearPaths.mapPaths_path]
      refine Submodule.subset_span ⟨_, ⟨v.val, ?_, Or.inl ⟨v, hvD, rfl⟩⟩, rfl⟩
      rw [LinearPaths.vertices_mapPath]
      exact List.mem_map_of_mem hv
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul t f _ hf => rw [map_smul]; exact Submodule.smul_mem _ t hf

/-- **`eq:mesh-object-quotient`**: between vertices of `S`, a morphism of `kQ`
vanishes in `C/[val D ∪ Sᶜ]` exactly when its restriction vanishes in
`C(Q_S)/[D]`. -/
theorem mem_sup_through_iff {D : Set (FullSub S)} {a b : FullSub S}
    (f : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val) :
    f ∈ meshIdealSub c _ _ ⊔ through k (FullSub.val '' D ∪ Sᶜ) a.val b.val ↔
      FullSub.restrict k a b f ∈ meshIdealSub (c.restrict hS) _ _ ⊔ through k D a b := by
  constructor
  · intro hf
    obtain ⟨i, hi, t, ht, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    exact Submodule.add_mem_sup (restrict_mem_meshIdealSub hS c hi) (restrict_mem_through ht)
  · intro hf
    have hsplit : f = FullSub.inclL k a b (FullSub.restrict k a b f) +
        (f - FullSub.inclL k a b (FullSub.restrict k a b f)) := by abel
    rw [hsplit]
    have hout : f - FullSub.inclL k a b (FullSub.restrict k a b f) ∈
        through k (FullSub.val '' D ∪ Sᶜ) a.val b.val := by
      have := FullSub.sub_inclL_restrict_mem k f
      rw [outside_eq_through] at this
      exact through_mono Set.subset_union_right _ _ this
    refine add_mem ?_ (Submodule.mem_sup_right hout)
    obtain ⟨i, hi, t, ht, he⟩ := Submodule.mem_sup.1 hf
    rw [← he, map_add]
    refine add_mem ?_ (Submodule.mem_sup_right (inclL_mem_through ht))
    obtain ⟨i', hi', o, ho, he'⟩ := Submodule.mem_sup.1 (inclL_mem_ideal_sup_outside hS c hi)
    rw [← he']
    refine add_mem (Submodule.mem_sup_left hi') (Submodule.mem_sup_right ?_)
    rw [outside_eq_through] at ho
    exact through_mono Set.subset_union_right _ _ ho

theorem restrict_surjective (a b : FullSub S) : Function.Surjective (FullSub.restrict k a b) :=
  fun g ↦ ⟨FullSub.inclL k a b g, FullSub.restrict_inclL k g⟩

/-- `eq:mesh-object-quotient` on Hom spaces between vertices of `S`. -/
def restrictQuotEquiv (D : Set (FullSub S)) (a b : FullSub S) :
    ((LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val) ⧸
        (meshIdealSub c _ _ ⊔ through k (FullSub.val '' D ∪ Sᶜ) a.val b.val)) ≃ₗ[k]
      ((LinearPaths.obj (k := k) a ⟶ LinearPaths.obj b) ⧸
        (meshIdealSub (c.restrict hS) _ _ ⊔ through k D a b)) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext f
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact mem_sup_through_iff hS c f)).trans
    (LinearMap.quotKerEquivOfSurjective
      ((Submodule.mkQ (meshIdealSub (c.restrict hS) _ _ ⊔ through k D a b)).comp
        (FullSub.restrict k a b))
      ((Submodule.mkQ_surjective _).comp (restrict_surjective (k := k) a b)))

theorem path_nil_eq_id (x : V) :
    LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (LinearPaths.obj x) := rfl

theorem oq_id_ne_zero_iff (D : Set V) (x : V) :
    𝟙 (ObjectQuotient.obj c D x) ≠ 0 ↔ 𝟙 (LinearPaths.obj (k := k) x) ∉
      meshIdealSub c _ _ ⊔ through k D x x := by
  rw [← oqFunctor_map_eq_zero_iff, CategoryTheory.Functor.map_id]
  rfl

theorem oq_id_eq_zero_of_mem (D : Set V) {x : V} (hx : x ∈ D) :
    𝟙 (ObjectQuotient.obj c D x) = 0 := by
  by_contra h
  rw [← ne_eq, oq_id_ne_zero_iff] at h
  exact h (Submodule.mem_sup_right (Submodule.subset_span
    ⟨Quiver.Path.nil, ⟨x, by simp, hx⟩, rfl⟩))

/-- **Object quotients of `C(Q_S)` are object quotients of `C(Q)`**
(Subsection 5.2): the brick hypothesis passes to a `τ`-closed full
subquiver. -/
theorem brickHypothesis_restrict (h : BrickHypothesis c) : BrickHypothesis (c.restrict hS) := by
  intro D ⟨x, hx⟩
  set D' : Set V := FullSub.val '' D ∪ Sᶜ
  have hx' : 𝟙 (ObjectQuotient.obj c D' x.val) ≠ 0 := by
    rw [oq_id_ne_zero_iff]
    rw [oq_id_ne_zero_iff] at hx
    intro hmem
    apply hx
    have := (mem_sup_through_iff hS c (D := D) (a := x) (b := x) (𝟙 _)).1 hmem
    have e : FullSub.restrict k x x (𝟙 (LinearPaths.obj x.val)) = 𝟙 (LinearPaths.obj x) := by
      have := FullSub.restrict_inclL k (𝟙 (LinearPaths.obj (k := k) x))
      rwa [← path_nil_eq_id, LinearPaths.mapPaths_path] at this
    rwa [e] at this
  obtain ⟨y, hy⟩ := h D' ⟨x.val, hx'⟩
  by_cases hyS : y ∈ S
  · refine ⟨FullSub.mk y hyS, ?_⟩
    rw [← hy]
    exact (((oqEquiv c D' y y).symm.trans (restrictQuotEquiv hS c D (FullSub.mk y hyS)
      (FullSub.mk y hyS))).trans (oqEquiv (c.restrict hS) D _ _)).finrank_eq.symm
  · exfalso
    have hid := oq_id_eq_zero_of_mem c D' (x := y) (Or.inr hyS)
    have : Subsingleton (ObjectQuotient.obj c D' y ⟶ ObjectQuotient.obj c D' y) :=
      ⟨fun g g' ↦ by rw [← Category.comp_id g, ← Category.comp_id g', hid,
        Limits.comp_zero, Limits.comp_zero]⟩
    rw [Module.finrank_zero_of_subsingleton] at hy
    exact zero_ne_one hy

/-- The scalar mesh category of a `τ`-closed full subquiver is finite-dimensional
if `C(Q, c)` is (`graded-category.tex`). -/
theorem finiteDimensional_restrict
    (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (a b : FullSub S) :
    FiniteDimensional k (ScalarMeshCategory.obj (c.restrict hS) a ⟶
      ScalarMeshCategory.obj (c.restrict hS) b) := by
  set FQ := RelationCategory.functor k (meshRelations c)
  set FS := RelationCategory.functor k (meshRelations (c.restrict hS))
  let g : (LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val) →ₗ[k]
      (ScalarMeshCategory.obj (c.restrict hS) a ⟶ ScalarMeshCategory.obj (c.restrict hS) b) :=
    (FS.mapLinearMap k).comp (FullSub.restrict k a b)
  have hker : LinearMap.ker (FQ.mapLinearMap k (X := LinearPaths.obj a.val)
      (Y := LinearPaths.obj b.val)) ≤ LinearMap.ker g := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    change FQ.map f = 0 at hf
    change FS.map (FullSub.restrict k a b f) = 0
    rw [RelationCategory.functor_map_eq_zero_iff] at hf ⊢
    exact restrict_mem_meshIdealSub hS c hf
  let e := (FQ.mapLinearMap k (X := LinearPaths.obj (k := k) a.val)
    (Y := LinearPaths.obj b.val)).quotKerEquivOfSurjective (fun g ↦ FQ.map_surjective g)
  let g' := ((LinearMap.ker _).liftQ g hker).comp e.symm.toLinearMap
  haveI := hfin a.val b.val
  refine Module.Finite.of_surjective g' ?_
  intro z
  obtain ⟨f, rfl⟩ := FS.map_surjective z
  obtain ⟨f', rfl⟩ := restrict_surjective (k := k) a b f
  refine ⟨FQ.map f', ?_⟩
  simp only [g', LinearMap.comp_apply, LinearEquiv.coe_coe]
  have : e.symm (FQ.map f') = Submodule.Quotient.mk f' := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this, Submodule.liftQ_apply]
  rfl

end MultiplicativeBasisDeformations
