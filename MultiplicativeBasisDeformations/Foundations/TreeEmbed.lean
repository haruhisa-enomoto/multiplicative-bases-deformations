module

public import MultiplicativeBasisDeformations.Foundations.SubstarRestriction

/-!
# Restricting `Π` of a tree to a full subtree

The argument of `SubstarRestriction` for any embedding `f : Δ' → Δ` of oriented trees
that preserves and reflects adjacency and orientation: the restriction `res` maps the
ideal of `Π(Δ)` with the outside of the image deleted into the ideal of `Π(Δ')`
(`res_mem`), so nonzero paths of `Π(Δ')` stay nonzero (`not_mem_del`). We use it for
intervals in the middle of a path (Appendix B, odd quotients of even `A`:
"retain the first `(r+1)/2` levels").
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace TreeEmbed

open OrientedTree

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
  (T : OrientedTree D) (T' : OrientedTree D') [DecidableRel T.orient] [DecidableRel T'.orient]
  (f : D' → D) (hf : Function.Injective f) (hadj : ∀ x y, T.G.Adj (f x) (f y) ↔ T'.G.Adj x y)
  (hor : ∀ x y, T.orient (f x) (f y) ↔ T'.orient x y)

variable {k : Type u} [Field k]

include hor in
theorem sgn_f (x y : D') : T.sgn k (f x) (f y) = T'.sgn k x y := by
  unfold OrientedTree.sgn
  by_cases h : T'.orient x y
  · rw [if_pos ((hor x y).2 h), if_pos h]
  · rw [if_neg (fun h' ↦ h ((hor x y).1 h')), if_neg h]

/-- The embedding of doubled quivers. -/
def ιq : T'.Dbl ⥤q T.Dbl where
  obj := f
  map {x y} a := ⟨(hadj x y).2 a.down⟩

theorem vertices_mapPath {v : T'.Dbl} : ∀ {w : T'.Dbl}
    (q : Quiver.Path v w), ((ιq T T' f hadj).mapPath q).vertices = q.vertices.map (f)
  | _, Quiver.Path.nil => rfl
  | _, Quiver.Path.cons q e => by
      rw [Prefunctor.mapPath_cons, Quiver.Path.vertices_cons, Quiver.Path.vertices_cons,
        vertices_mapPath q, List.map_concat]
      rfl

include hf in
theorem mapPath_injective {v : T'.Dbl} : ∀ {w : T'.Dbl}
    (q₁ q₂ : Quiver.Path v w), (ιq T T' f hadj).mapPath q₁ = (ιq T T' f hadj).mapPath q₂ → q₁ = q₂
  | _, Quiver.Path.nil, Quiver.Path.nil, _ => rfl
  | _, Quiver.Path.nil, Quiver.Path.cons p e, h => by
      rw [Prefunctor.mapPath_cons] at h; exact absurd h (Quiver.Path.nil_ne_cons _ _)
  | _, Quiver.Path.cons p e, Quiver.Path.nil, h => by
      rw [Prefunctor.mapPath_cons] at h; exact absurd h (Quiver.Path.cons_ne_nil _ _)
  | _, Quiver.Path.cons p₁ e₁, Quiver.Path.cons p₂ e₂, h => by
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons] at h
      have h' := Quiver.Path.obj_eq_of_cons_eq_cons h
      have hy := hf h'
      subst hy
      have hp := mapPath_injective p₁ p₂ (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h))
      subst hp
      rw [Subsingleton.elim e₁ e₂]

/-- **Paths inside the image lift.** -/
theorem exists_lift {v : T'.Dbl} : ∀ {z : T.Dbl}
    (q : Quiver.Path ((ιq T T' f hadj).obj v) z),
    (∀ x ∈ q.vertices, x ∈ Set.range (f)) →
      ∃ (w : T'.Dbl) (q' : Quiver.Path v w) (_ : ((ιq T T' f hadj).obj w) = z),
        HEq ((ιq T T' f hadj).mapPath q') q
  | _, Quiver.Path.nil, _ => ⟨v, Quiver.Path.nil, rfl, HEq.rfl⟩
  | _, Quiver.Path.cons q e, h => by
      obtain ⟨w₁, q₁, h₁, hq₁⟩ := exists_lift q fun x hx ↦
        h x ((Quiver.Path.mem_vertices_cons _ _).2 (Or.inl hx))
      obtain ⟨w₂, hw₂⟩ := h _ ((Quiver.Path.mem_vertices_cons _ _).2 (Or.inr rfl))
      subst h₁ hw₂
      have hq₁' := eq_of_heq hq₁
      subst hq₁'
      refine ⟨w₂, q₁.cons ⟨(hadj w₁ w₂).1 e.down⟩, rfl, ?_⟩
      rw [Prefunctor.mapPath_cons]
      exact heq_of_eq (congrArg _ (Subsingleton.elim _ _))

open Classical in
/-- The restriction to the substar. -/
def res (v w : T'.Dbl) :
    (LinearPaths.obj (k := k) ((ιq T T' f hadj).obj v) ⟶ LinearPaths.obj ((ιq T T' f hadj).obj w)) →ₗ[k]
      (LinearPaths.obj (k := k) v ⟶ LinearPaths.obj w) :=
  LinearPaths.extend fun q ↦
    if h : ∃ q' : Quiver.Path v w, (ιq T T' f hadj).mapPath q' = q then LinearPaths.path h.choose else 0

include hf in
theorem res_mapPath {v w : T'.Dbl} (q' : Quiver.Path v w) :
    res (k := k) T T' f hadj v w (LinearPaths.path ((ιq T T' f hadj).mapPath q')) = LinearPaths.path q' := by
  classical
  unfold res
  rw [LinearPaths.extend_path, dif_pos ⟨q', rfl⟩]
  congr 1
  exact mapPath_injective T T' f hf hadj _ _ (Exists.choose_spec (⟨q', rfl⟩ :
    ∃ q'' : Quiver.Path v w, (ιq T T' f hadj).mapPath q'' = (ιq T T' f hadj).mapPath q'))

theorem res_out {v w : T'.Dbl} (q : Quiver.Path ((ιq T T' f hadj).obj v) ((ιq T T' f hadj).obj w))
    (h : ∃ x ∈ q.vertices, x ∉ Set.range (f)) :
    res (k := k) T T' f hadj v w (LinearPaths.path q) = 0 := by
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
def Out : Set T.Dbl := {x | ∀ y, (ιq T T' f hadj).obj y ≠ x}

theorem mem_range_iff (x : T.Dbl) : x ∈ Set.range (f) ↔ x ∉ Out T T' f hadj := by
  simp only [Out, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_range]
  rfl

/-- The relation of `Π(Δ)` in path context, expanded. -/
theorem rel_expand {x y u : T.Dbl} (p : Quiver.Path x u) (p' : Quiver.Path u y) :
    LinearPaths.path (k := k) p ≫ T.preprojRel k u ≫ LinearPaths.path p' =
      ∑ e : Σ z : T.Dbl, u ⟶ z, ((T.sgn k (u : D) (e.1 : D) : kˣ) : k) •
        LinearPaths.path ((p.comp (e.2.toPath.comp
          (Quiver.Hom.toPath (show e.1 ⟶ u from ⟨e.2.down.symm⟩)))).comp p') := by
  unfold preprojRel
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path, LinearPaths.path_comp_path]
  simp only [Quiver.Path.comp_assoc]

include hf hor in
theorem res_rel {v w : T'.Dbl} {i : T.Dbl}
    (p : Quiver.Path ((ιq T T' f hadj).obj v) i) (p' : Quiver.Path i ((ιq T T' f hadj).obj w)) :
    res (k := k) T T' f hadj v w (LinearPaths.path p ≫ T.preprojRel k i ≫ LinearPaths.path p') ∈
      T'.Id k v w := by
  classical
  rw [rel_expand, map_sum]
  by_cases hin : (∀ x ∈ p.vertices, x ∈ Set.range (f)) ∧
      (∀ x ∈ p'.vertices, x ∈ Set.range (f))
  · obtain ⟨u, p₀, hu, hp₀⟩ := exists_lift T T' f hadj p hin.1
    subst hu
    obtain rfl := eq_of_heq hp₀
    obtain ⟨w', p₀', hw', hp₀'⟩ := exists_lift T T' f hadj p' hin.2
    have hw : w = w' := (hf hw').symm
    subst hw
    obtain rfl := eq_of_heq hp₀'
    have key : ∑ e : Σ z : T.Dbl, (ιq T T' f hadj).obj u ⟶ z,
        res (k := k) T T' f hadj v w (((T.sgn k (((ιq T T' f hadj).obj u : T.Dbl) : D)
          (e.1 : D) : kˣ) : k) • LinearPaths.path ((((ιq T T' f hadj).mapPath p₀).comp
            (e.2.toPath.comp (Quiver.Hom.toPath (show e.1 ⟶ (ιq T T' f hadj).obj u from
              ⟨e.2.down.symm⟩)))).comp ((ιq T T' f hadj).mapPath p₀'))) =
        LinearPaths.path p₀ ≫ T'.preprojRel k u ≫ LinearPaths.path p₀' := by
      rw [rel_expand]
      symm
      refine Fintype.sum_of_injective (fun e : Σ z : T'.Dbl, u ⟶ z ↦
        (⟨(ιq T T' f hadj).obj e.1, (ιq T T' f hadj).map e.2⟩ : Σ z : T.Dbl, (ιq T T' f hadj).obj u ⟶ z))
        ?_ _ _ ?_ ?_
      · rintro ⟨z, a⟩ ⟨z', a'⟩ h
        have h1 := congrArg Sigma.fst h
        obtain rfl := hf h1
        rw [Subsingleton.elim a a']
      · intro e he
        rw [map_smul, res_out, smul_zero]
        refine ⟨e.1, mem_comp_left _ _ (mem_comp_right _ _ (by simp)), ?_⟩
        rintro ⟨z, hz⟩
        exact he ⟨⟨z, ⟨(hadj u z).1 (by rw [hz]; exact e.2.down)⟩⟩, by
          obtain ⟨z', a⟩ := e
          change f z = z' at hz
          subst hz
          rfl⟩
      · intro e
        rw [map_smul]
        simp only
        rw [show (T.sgn k ((ιq T T' f hadj).obj u) ((ιq T T' f hadj).obj e.1) : kˣ) =
          T'.sgn k u e.1 from sgn_f T T' f hor u e.1]
        congr 1
        rw [← res_mapPath T T' f hf hadj (k := k) ((p₀.comp (e.2.toPath.comp
          (Quiver.Hom.toPath (show e.1 ⟶ u from ⟨e.2.down.symm⟩)))).comp p₀')]
        congr 2
        simp only [Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath]
        rfl
    rw [show (∑ e, res (k := k) T T' f hadj v w _) = _ from key]
    exact (T'.preproj k).comp_rel_comp_mem u _ _
  · refine Submodule.sum_mem _ fun e _ ↦ ?_
    rw [map_smul, res_out, smul_zero]
    · exact zero_mem _
    simp only [not_and_or, not_forall] at hin
    rcases hin with ⟨x, hx, hxr⟩ | ⟨x, hx, hxr⟩
    · exact ⟨x, mem_comp_left _ _ (mem_comp_left _ _ hx), hxr⟩
    · exact ⟨x, mem_comp_right _ _ hx, hxr⟩

include hf hor in
/-- **Restriction maps the ideal with the outside deleted into the ideal of the
substar.** -/
theorem res_mem {v w : T'.Dbl}
    {φ : LinearPaths.obj (k := k) ((ιq T T' f hadj).obj v) ⟶ LinearPaths.obj ((ιq T T' f hadj).obj w)}
    (hφ : φ ∈ ((T.preproj k).del (Out T T' f hadj)).ideal _ _) :
    res (k := k) T T' f hadj v w φ ∈ T'.Id k v w := by
  classical
  refine (T.preproj k).del_induction (Out T T' f hadj)
    (P := fun φ ↦ res (k := k) T T' f hadj v w φ ∈ T'.Id k v w) (by simp)
    (fun φ ψ hφ hψ ↦ by rw [map_add]; exact add_mem hφ hψ)
    (fun c φ hφ ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hφ) (fun i p p' ↦ ?_)
    (fun d hd p p' ↦ ?_) hφ
  · exact res_rel T T' f hf hadj hor (i := (i : T.Dbl)) p p'
  · rw [LinearPaths.path_comp_path, res_out]
    · exact zero_mem _
    refine ⟨d, mem_comp_right _ _ (Quiver.Path.start_mem_vertices _), ?_⟩
    rw [mem_range_iff T T' f hadj]
    exact not_not.2 hd

include hf hor in
/-- **Nonvanishing passes from the substar.** -/
theorem not_mem_del {v w : T'.Dbl} (p : Quiver.Path v w)
    (hp : LinearPaths.path (k := k) p ∉ T'.Id k v w) :
    LinearPaths.path (k := k) ((ιq T T' f hadj).mapPath p) ∉
      ((T.preproj k).del (Out T T' f hadj)).ideal _ _ := by
  intro h
  have := res_mem T T' f hf hadj hor h
  rw [res_mapPath T T' f hf hadj] at this
  exact hp this

end TreeEmbed

end MultiplicativeBasisDeformations
