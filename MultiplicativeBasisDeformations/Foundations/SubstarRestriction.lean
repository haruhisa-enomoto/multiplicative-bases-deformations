import MultiplicativeBasisDeformations.Foundations.GradedPreproj
import MultiplicativeBasisDeformations.Foundations.StarCorner

/-!
# Restricting `Π` of a star to a substar

`periodic-mesh-calculations.tex:871–876`: "Removing the outer vertex of the long
`E₈` arm at every repetition coordinate gives exactly this mesh category by
(5.2)." On `Π` this is the identification of `Π(Δ)` modulo the deleted vertices
with `Π(Δ')` of the retained substar `Δ'`: paths through deleted vertices vanish,
a relation at a deleted vertex consists of such paths, and a relation at a
retained vertex loses exactly its terms through deleted neighbours.

For arm lengths `L' ≤ L` the star of `L'` embeds in that of `L` (`ιv`). The
restriction `res` sends a path inside the image to its preimage and other paths
to zero; it maps the ideal of `Π(Δ)` with the outside deleted into the ideal of
`Π(Δ')` (`res_mem`). Hence nonzero paths of `Π(Δ')` stay nonzero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace Substar

open OrientedTree StarCorner

variable {t : ℕ} {L L' : Fin t → ℕ} (hle : ∀ i, L' i ≤ L i)

/-- The embedding of the smaller star. -/
def ιv (x : StarV L') : StarV L :=
  x.map fun y ↦ ⟨y.1, Fin.castLE (by have := hle y.1; omega) y.2⟩

theorem ιv_injective : Function.Injective (ιv hle) := by
  rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) h <;> simp [ιv] at h ⊢
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h ⊢
  exact ⟨trivial, Fin.castLE_injective _ h⟩

theorem depth_ιv (x : StarV L') : starDepth (ιv hle x) = starDepth x := by
  rcases x with _ | ⟨i, j⟩ <;> rfl

theorem adj_ιv (x y : StarV L') : starAdj (ιv hle x) (ιv hle y) ↔ starAdj x y := by
  rcases x with _ | ⟨i, j⟩ <;> rcases y with _ | ⟨i', j'⟩ <;> simp [ιv, starAdj]

variable {k : Type u} [Field k]

theorem sgn_ιv (x y : StarV L') :
    (starTree L).sgn k (ιv hle x) (ιv hle y) = (starTree L').sgn k x y := by
  unfold OrientedTree.sgn
  have : (starTree L).orient (ιv hle x) (ιv hle y) ↔ (starTree L').orient x y := by
    change starOrient _ _ ↔ starOrient _ _
    unfold starOrient
    rw [adj_ιv, depth_ιv, depth_ιv]
  by_cases h : (starTree L').orient x y
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (this.1 h'))]

/-- The embedding of doubled quivers. -/
def ιq : (starTree L').Dbl ⥤q (starTree L).Dbl where
  obj := ιv hle
  map {x y} a := ⟨(adj_ιv hle x y).2 a.down⟩

theorem vertices_mapPath {v : (starTree L').Dbl} : ∀ {w : (starTree L').Dbl}
    (q : Quiver.Path v w), ((ιq hle).mapPath q).vertices = q.vertices.map (ιv hle)
  | _, Quiver.Path.nil => rfl
  | _, Quiver.Path.cons q e => by
      rw [Prefunctor.mapPath_cons, Quiver.Path.vertices_cons, Quiver.Path.vertices_cons,
        vertices_mapPath q, List.map_concat]
      rfl

theorem mapPath_injective {v : (starTree L').Dbl} : ∀ {w : (starTree L').Dbl}
    (q₁ q₂ : Quiver.Path v w), (ιq hle).mapPath q₁ = (ιq hle).mapPath q₂ → q₁ = q₂
  | _, Quiver.Path.nil, Quiver.Path.nil, _ => rfl
  | _, Quiver.Path.nil, Quiver.Path.cons p e, h => by
      rw [Prefunctor.mapPath_cons] at h; exact absurd h (Quiver.Path.nil_ne_cons _ _)
  | _, Quiver.Path.cons p e, Quiver.Path.nil, h => by
      rw [Prefunctor.mapPath_cons] at h; exact absurd h (Quiver.Path.cons_ne_nil _ _)
  | _, Quiver.Path.cons p₁ e₁, Quiver.Path.cons p₂ e₂, h => by
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons] at h
      have h' := Quiver.Path.obj_eq_of_cons_eq_cons h
      have hy := ιv_injective hle h'
      subst hy
      have hp := mapPath_injective p₁ p₂ (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h))
      subst hp
      rw [Subsingleton.elim e₁ e₂]

/-- **Paths inside the image lift.** -/
theorem exists_lift {v : (starTree L').Dbl} : ∀ {z : (starTree L).Dbl}
    (q : Quiver.Path ((ιq hle).obj v) z),
    (∀ x ∈ q.vertices, x ∈ Set.range (ιv hle)) →
      ∃ (w : (starTree L').Dbl) (q' : Quiver.Path v w) (_ : ((ιq hle).obj w) = z),
        HEq ((ιq hle).mapPath q') q
  | _, Quiver.Path.nil, _ => ⟨v, Quiver.Path.nil, rfl, HEq.rfl⟩
  | _, Quiver.Path.cons q e, h => by
      obtain ⟨w₁, q₁, h₁, hq₁⟩ := exists_lift q fun x hx ↦
        h x ((Quiver.Path.mem_vertices_cons _ _).2 (Or.inl hx))
      obtain ⟨w₂, hw₂⟩ := h _ ((Quiver.Path.mem_vertices_cons _ _).2 (Or.inr rfl))
      subst h₁ hw₂
      have hq₁' := eq_of_heq hq₁
      subst hq₁'
      refine ⟨w₂, q₁.cons ⟨(adj_ιv hle w₁ w₂).1 e.down⟩, rfl, ?_⟩
      rw [Prefunctor.mapPath_cons]
      exact heq_of_eq (congrArg _ (Subsingleton.elim _ _))

open Classical in
/-- The restriction to the substar. -/
def res (v w : (starTree L').Dbl) :
    (LinearPaths.obj (k := k) ((ιq hle).obj v) ⟶ LinearPaths.obj ((ιq hle).obj w)) →ₗ[k]
      (LinearPaths.obj (k := k) v ⟶ LinearPaths.obj w) :=
  LinearPaths.extend fun q ↦
    if h : ∃ q' : Quiver.Path v w, (ιq hle).mapPath q' = q then LinearPaths.path h.choose else 0

theorem res_mapPath {v w : (starTree L').Dbl} (q' : Quiver.Path v w) :
    res (k := k) hle v w (LinearPaths.path ((ιq hle).mapPath q')) = LinearPaths.path q' := by
  classical
  unfold res
  rw [LinearPaths.extend_path, dif_pos ⟨q', rfl⟩]
  congr 1
  exact mapPath_injective hle _ _ (Exists.choose_spec (⟨q', rfl⟩ :
    ∃ q'' : Quiver.Path v w, (ιq hle).mapPath q'' = (ιq hle).mapPath q'))

theorem res_out {v w : (starTree L').Dbl} (q : Quiver.Path ((ιq hle).obj v) ((ιq hle).obj w))
    (h : ∃ x ∈ q.vertices, x ∉ Set.range (ιv hle)) :
    res (k := k) hle v w (LinearPaths.path q) = 0 := by
  classical
  unfold res
  rw [LinearPaths.extend_path, dif_neg]
  rintro ⟨q', rfl⟩
  obtain ⟨x, hx, hxr⟩ := h
  rw [vertices_mapPath, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact hxr ⟨y, rfl⟩

theorem mem_comp_left {V : Type*} [Quiver V] {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) {x : V} (hx : x ∈ p.vertices) : x ∈ (p.comp q).vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  rw [← Quiver.Path.dropLast_append_end_eq p, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact Or.inl hx
  · exact Or.inr (Quiver.Path.start_mem_vertices q)

theorem mem_comp_right {V : Type*} [Quiver V] {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) {x : V} (hx : x ∈ q.vertices) : x ∈ (p.comp q).vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  exact Or.inr hx

/-- The vertices outside the substar. -/
def Out : Set (starTree L).Dbl := {x | ∀ y, (ιq hle).obj y ≠ x}

theorem mem_range_iff (x : (starTree L).Dbl) : x ∈ Set.range (ιv hle) ↔ x ∉ Out hle := by
  simp only [Out, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_range]
  rfl

/-- The relation of `Π(Δ)` in path context, expanded. -/
theorem rel_expand {x y u : (starTree L).Dbl} (p : Quiver.Path x u) (p' : Quiver.Path u y) :
    LinearPaths.path (k := k) p ≫ (starTree L).preprojRel k u ≫ LinearPaths.path p' =
      ∑ e : Σ z : (starTree L).Dbl, u ⟶ z, (((starTree L).sgn k (u : StarV L) (e.1 : StarV L) : kˣ) : k) •
        LinearPaths.path ((p.comp (e.2.toPath.comp
          (Quiver.Hom.toPath (show e.1 ⟶ u from ⟨e.2.down.symm⟩)))).comp p') := by
  unfold preprojRel
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path, LinearPaths.path_comp_path]
  simp only [Quiver.Path.comp_assoc]

theorem res_rel {v w : (starTree L').Dbl} {i : (starTree L).Dbl}
    (p : Quiver.Path ((ιq hle).obj v) i) (p' : Quiver.Path i ((ιq hle).obj w)) :
    res (k := k) hle v w (LinearPaths.path p ≫ (starTree L).preprojRel k i ≫ LinearPaths.path p') ∈
      (starTree L').Id k v w := by
  classical
  rw [rel_expand, map_sum]
  by_cases hin : (∀ x ∈ p.vertices, x ∈ Set.range (ιv hle)) ∧
      (∀ x ∈ p'.vertices, x ∈ Set.range (ιv hle))
  · obtain ⟨u, p₀, hu, hp₀⟩ := exists_lift hle p hin.1
    subst hu
    obtain rfl := eq_of_heq hp₀
    obtain ⟨w', p₀', hw', hp₀'⟩ := exists_lift hle p' hin.2
    have hw : w = w' := (ιv_injective hle hw').symm
    subst hw
    obtain rfl := eq_of_heq hp₀'
    have key : ∑ e : Σ z : (starTree L).Dbl, (ιq hle).obj u ⟶ z,
        res (k := k) hle v w ((((starTree L).sgn k (((ιq hle).obj u : (starTree L).Dbl) : StarV L)
          (e.1 : StarV L) : kˣ) : k) • LinearPaths.path ((((ιq hle).mapPath p₀).comp
            (e.2.toPath.comp (Quiver.Hom.toPath (show e.1 ⟶ (ιq hle).obj u from
              ⟨e.2.down.symm⟩)))).comp ((ιq hle).mapPath p₀'))) =
        LinearPaths.path p₀ ≫ (starTree L').preprojRel k u ≫ LinearPaths.path p₀' := by
      rw [rel_expand]
      symm
      refine Fintype.sum_of_injective (fun e : Σ z : (starTree L').Dbl, u ⟶ z ↦
        (⟨(ιq hle).obj e.1, (ιq hle).map e.2⟩ : Σ z : (starTree L).Dbl, (ιq hle).obj u ⟶ z))
        ?_ _ _ ?_ ?_
      · rintro ⟨z, a⟩ ⟨z', a'⟩ h
        have h1 := congrArg Sigma.fst h
        obtain rfl := ιv_injective hle h1
        rw [Subsingleton.elim a a']
      · intro e he
        rw [map_smul, res_out, smul_zero]
        refine ⟨e.1, mem_comp_left _ _ (mem_comp_right _ _ (by simp)), ?_⟩
        rintro ⟨z, hz⟩
        exact he ⟨⟨z, ⟨(adj_ιv hle u z).1 (by rw [hz]; exact e.2.down)⟩⟩, by
          obtain ⟨z', a⟩ := e
          change ιv hle z = z' at hz
          subst hz
          rfl⟩
      · intro e
        rw [map_smul]
        simp only
        rw [show ((starTree L).sgn k ((ιq hle).obj u) ((ιq hle).obj e.1) : kˣ) =
          (starTree L').sgn k u e.1 from sgn_ιv hle u e.1]
        congr 1
        rw [← res_mapPath hle (k := k) ((p₀.comp (e.2.toPath.comp
          (Quiver.Hom.toPath (show e.1 ⟶ u from ⟨e.2.down.symm⟩)))).comp p₀')]
        congr 2
        simp only [Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath]
        rfl
    rw [show (∑ e, res (k := k) hle v w _) = _ from key]
    exact ((starTree L').preproj k).comp_rel_comp_mem u _ _
  · refine Submodule.sum_mem _ fun e _ ↦ ?_
    rw [map_smul, res_out, smul_zero]
    · exact zero_mem _
    simp only [not_and_or, not_forall] at hin
    rcases hin with ⟨x, hx, hxr⟩ | ⟨x, hx, hxr⟩
    · exact ⟨x, mem_comp_left _ _ (mem_comp_left _ _ hx), hxr⟩
    · exact ⟨x, mem_comp_right _ _ hx, hxr⟩

/-- **Restriction maps the ideal with the outside deleted into the ideal of the
substar.** -/
theorem res_mem {v w : (starTree L').Dbl}
    {f : LinearPaths.obj (k := k) ((ιq hle).obj v) ⟶ LinearPaths.obj ((ιq hle).obj w)}
    (hf : f ∈ (((starTree L).preproj k).del (Out hle)).ideal _ _) :
    res (k := k) hle v w f ∈ (starTree L').Id k v w := by
  classical
  refine ((starTree L).preproj k).del_induction (Out hle)
    (P := fun f ↦ res (k := k) hle v w f ∈ (starTree L').Id k v w) (by simp)
    (fun f g hf hg ↦ by rw [map_add]; exact add_mem hf hg)
    (fun c f hf ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hf) (fun i p p' ↦ ?_)
    (fun d hd p p' ↦ ?_) hf
  · exact res_rel hle (i := (i : (starTree L).Dbl)) p p'
  · rw [LinearPaths.path_comp_path, res_out]
    · exact zero_mem _
    refine ⟨d, mem_comp_right _ _ (Quiver.Path.start_mem_vertices _), ?_⟩
    rw [mem_range_iff]
    exact not_not.2 hd

/-- **Nonvanishing passes from the substar.** -/
theorem not_mem_del {v w : (starTree L').Dbl} (p : Quiver.Path v w)
    (hp : LinearPaths.path (k := k) p ∉ (starTree L').Id k v w) :
    LinearPaths.path (k := k) ((ιq hle).mapPath p) ∉
      (((starTree L).preproj k).del (Out hle)).ideal _ _ := by
  intro h
  have := res_mem hle h
  rw [res_mapPath] at this
  exact hp this

end Substar

end MultiplicativeBasisDeformations
