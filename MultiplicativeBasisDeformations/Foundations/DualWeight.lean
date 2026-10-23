module

public import MultiplicativeBasisDeformations.Foundations.ZCocycle
public import MultiplicativeBasisDeformations.Foundations.PeriodicDepth
public import MultiplicativeBasisDeformations.Foundations.MeshWeights

/-!
# Extending a mesh weight from one periodic component (Proposition 7.5)

A mesh weight on a periodic component `T` of `Q` extends to a mesh weight on `Q` which
agrees with it on the edges inside `T` and vanishes on the edges inside every other periodic
component (`exists_ext_wt`). The values on the unmatched edges of the collapse of Lemma 4.2
are prescribed (the given weight inside `T`, zero elsewhere), and the matched edges are
solved from their triangles (`Morse.zval`); the triangles which solve edges inside a
periodic component lie in that component.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open TranslationQuiver PeriodicDepth Classical

variable {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V}

/-- An edge of `K` inside a set of vertices. -/
def EdIn (T : Set V) : Ed Q → Prop
  | Sum.inl A => A.1 ∈ T ∧ A.2.1 ∈ T
  | Sum.inr x => x.1 ∈ T

theorem MeshWt.w_congr {M : Type} [AddCommGroup M] {V' : Type} [Quiver.{0} V']
    [∀ x y : V', Subsingleton (x ⟶ y)] {Q' : TranslationQuiver V'} (W : MeshWt Q' M)
    {a b a' b' : V'} (e : a ⟶ b) (e' : a' ⟶ b') (ha : a = a') (hb : b = b') : W.w e = W.w e' := by
  subst ha hb; rw [Subsingleton.elim e e']

variable [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {k : Type*} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k
    (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

theorem mem_comp_of_arrow {r y x : V} (hx : x ∈ Q.component r) (hy : y ∈ Q.periodic) (a : y ⟶ x) :
    y ∈ Q.component r := by
  have h1 := comp_arrow hy hx.1 a
  have h2 : Q.component x = Q.component r := component_eq (Relation.EqvGen.symm _ _ hx.2)
  rw [← h2, ← h1]; exact mem_component_self hy

include hfin in
/-- The triangles solving edges inside a periodic component lie in it. -/
theorem edIn_tri {r : V} (t : Tri Q)
    (h : EdIn (Q.component r) ((meshTris Q).edge t ((meshMatching (meshDepth c hfin)).m t))) :
    ∀ j, EdIn (Q.component r) ((meshTris Q).edge t j) := by
  have hτ : ∀ x : Q.nonprojective, x.1 ∈ Q.component r → (Q.tau x).1 ∈ Q.component r :=
    fun x hx ↦ (isTauClosed_component r x.1 x.2).1 hx
  change EdIn _ ((meshTris Q).edge t (if Up (meshDepth c hfin) t then 2 else 1)) at h
  by_cases hu : Up (meshDepth c hfin) t
  · rw [if_pos hu] at h
    change t.1.1 ∈ Q.component r at h
    have hy := mem_comp_of_arrow h (periodic_of_cyclic hu.1).2 t.2.2
    intro j
    fin_cases j
    · exact ⟨hτ t.1 h, hy⟩
    · exact ⟨hy, h⟩
    · exact h
  · rw [if_neg hu] at h
    obtain ⟨hy, hx⟩ := h
    intro j
    fin_cases j
    · exact ⟨hτ t.1 hx, hy⟩
    · exact ⟨hy, hx⟩
    · exact hx

/-- The mesh weight of an integer cocycle on `K`. -/
def ofZ (z : Ed Q → ℤ) (hz : ∀ t : Tri Q, z (Sum.inl t.mateArr) + z (Sum.inl t.arr) = z (Sum.inr t.1)) :
    MeshWt Q ℤ where
  w {y x} a := z (Sum.inl ⟨y, x, a⟩)
  ν x := z (Sum.inr x)
  mesh x a := hz ⟨x, a.1, a.2⟩

variable (r : V)

/-- The values of a weight of the component of `r` on the edges of `K`. -/
def gT (WT : MeshWt (restrict (isTauClosed_component (Q := Q) r)) ℤ) : Ed Q → ℤ
  | Sum.inl A => if h : A.1 ∈ Q.component r ∧ A.2.1 ∈ Q.component r then
      WT.w (show FullSub.mk A.1 h.1 ⟶ FullSub.mk A.2.1 h.2 from A.2.2) else 0
  | Sum.inr x => if h : x.1 ∈ Q.component r then WT.ν ⟨FullSub.mk x.1 h, x.2⟩ else 0

theorem gT_tri (WT : MeshWt (restrict (isTauClosed_component (Q := Q) r)) ℤ) (t : Tri Q)
    (ht : ∀ j, EdIn (Q.component r) ((meshTris Q).edge t j)) :
    gT r WT (Sum.inl t.mateArr) + gT r WT (Sum.inl t.arr) = gT r WT (Sum.inr t.1) := by
  have h0 : EdIn (Q.component r) (Sum.inl t.mateArr) := ht 0
  have h1 : EdIn (Q.component r) (Sum.inl t.arr) := ht 1
  have h2 : EdIn (Q.component r) (Sum.inr t.1) := ht 2
  have h0' : t.mateArr.1 ∈ Q.component r ∧ t.mateArr.2.1 ∈ Q.component r := h0
  have h1' : t.arr.1 ∈ Q.component r ∧ t.arr.2.1 ∈ Q.component r := h1
  have h2' : t.1.1 ∈ Q.component r := h2
  simp only [gT]
  rw [dif_pos h0', dif_pos h1', dif_pos h2']
  have hm := WT.mesh ⟨FullSub.mk t.1.1 h2', t.1.2⟩ ⟨FullSub.mk t.2.1 h1'.1, t.2.2⟩
  rw [← hm]
  congr 1

theorem edIn_disjoint {r r' : V} (hne : Q.component r' ≠ Q.component r) {e : Ed Q}
    (h : EdIn (Q.component r') e) : ¬ EdIn (Q.component r) e := by
  have key : ∀ v, v ∈ Q.component r' → v ∉ Q.component r := fun v h1 h2 ↦ by
    apply hne
    rw [← component_eq (Relation.EqvGen.symm _ _ h1.2), ← component_eq (Relation.EqvGen.symm _ _ h2.2)]
  rcases e with A | x
  · exact fun h' ↦ key _ h.1 h'.1
  · exact fun h' ↦ key _ h h'

include hfin in
/-- **Extension of a mesh weight of a periodic component.** -/
theorem exists_ext_wt (WT : MeshWt (restrict (isTauClosed_component (Q := Q) r)) ℤ) :
    ∃ W : MeshWt Q ℤ,
      (∀ {y x : V} (a : y ⟶ x) (hy : y ∈ Q.component r) (hx : x ∈ Q.component r),
        W.w a = WT.w (show FullSub.mk y hy ⟶ FullSub.mk x hx from a)) ∧
      (∀ (x : Q.nonprojective) (hx : x.1 ∈ Q.component r), W.ν x = WT.ν ⟨FullSub.mk x.1 hx, x.2⟩) ∧
      ∀ r', Q.component r' ≠ Q.component r →
        (∀ {y x : V} (a : y ⟶ x), y ∈ Q.component r' → x ∈ Q.component r' → W.w a = 0) ∧
        ∀ x : Q.nonprojective, x.1 ∈ Q.component r' → W.ν x = 0 := by
  set M := meshMatching (meshDepth c hfin)
  set f : Ed Q → ℤ := fun e ↦ if EdIn (Q.component r) e then gT r WT e else 0
  have hz : ∀ t : Tri Q, Morse.zval M f (Sum.inl t.mateArr) + Morse.zval M f (Sum.inl t.arr) =
      Morse.zval M f (Sum.inr t.1) := fun t ↦ Morse.zval_tri M f t
  have hT := Morse.zval_agree M f {e | EdIn (Q.component r) e} (gT r WT)
    (fun t ht ↦ edIn_tri c hfin t ht) (fun t ht ↦ gT_tri r WT t ht)
    (fun e he _ ↦ by simp only [f, if_pos (show EdIn (Q.component r) e from he)])
  have hT' : ∀ r', Q.component r' ≠ Q.component r → ∀ e, EdIn (Q.component r') e →
      Morse.zval M f e = 0 := fun r' hne ↦
    Morse.zval_agree M f {e | EdIn (Q.component r') e} (fun _ ↦ 0)
      (fun t ht ↦ edIn_tri c hfin t ht) (fun _ _ ↦ by simp)
      (fun e he _ ↦ by simp only [f, if_neg (edIn_disjoint hne he)])
  refine ⟨ofZ (fun e ↦ Morse.zval M f e) hz, fun {y x} a hy hx ↦ ?_, fun x hx ↦ ?_,
    fun r' hne ↦ ⟨fun {y x} a hy hx ↦ hT' r' hne (Sum.inl ⟨y, x, a⟩) ⟨hy, hx⟩,
      fun x hx ↦ hT' r' hne (Sum.inr x) hx⟩⟩
  · change Morse.zval M f (Sum.inl ⟨y, x, a⟩) = _
    rw [hT _ (show EdIn (Q := Q) (Q.component r) (Sum.inl ⟨y, x, a⟩) from ⟨hy, hx⟩)]
    simp only [gT]
    rw [dif_pos ⟨hy, hx⟩]
  · change Morse.zval M f (Sum.inr x) = _
    rw [hT _ (show EdIn (Q := Q) (Q.component r) (Sum.inr x) from hx)]
    simp only [gT]
    rw [dif_pos hx]

theorem edIn_mono {T T' : Set V} (h : T ⊆ T') {e : Ed Q} (he : EdIn T e) : EdIn T' e := by
  rcases e with A | x
  · exact ⟨h he.1, h he.2⟩
  · exact h he

include hfin in
/-- The triangles solving edges inside the periodic vertices lie inside them. -/
theorem edIn_tri_periodic (t : Tri Q)
    (h : EdIn Q.periodic ((meshTris Q).edge t ((meshMatching (meshDepth c hfin)).m t))) :
    ∀ j, EdIn Q.periodic ((meshTris Q).edge t j) := by
  generalize he : (meshTris Q).edge t ((meshMatching (meshDepth c hfin)).m t) = e at h
  obtain ⟨r, hr⟩ : ∃ r, EdIn (Q.component r) e := by
    rcases e with A | x
    · exact ⟨A.2.1, mem_comp_of_arrow (mem_component_self h.2) h.1 A.2.2,
        mem_component_self h.2⟩
    · exact ⟨x.1, mem_component_self h⟩
  subst he
  exact fun j ↦ edIn_mono (component_subset_periodic r) (edIn_tri c hfin t hr j)

include hfin in
/-- **Lemma 4.3** (`lem:periodic-weight-extension`): every closed edge weight, with values in
an abelian group, on the union of the periodic subcomplexes extends to a closed edge weight on
`K`. Closed means that the triangle relations hold; the extension solves the edges matched by
the collapse of Lemma 4.2 from their triangles (`Morse.zval`), with the prescribed values on
the unmatched periodic edges and zero on the other unmatched edges. -/
theorem periodicWeightExtension {G : Type*} [AddCommGroup G] (w : Ed Q → G)
    (hw : ∀ t : Tri Q, (∀ j, EdIn Q.periodic ((meshTris Q).edge t j)) →
      w (Sum.inl t.mateArr) + w (Sum.inl t.arr) = w (Sum.inr t.1)) :
    ∃ w' : Ed Q → G, (∀ t : Tri Q,
      w' (Sum.inl t.mateArr) + w' (Sum.inl t.arr) = w' (Sum.inr t.1)) ∧
      ∀ e, EdIn Q.periodic e → w' e = w e := by
  set M := meshMatching (meshDepth c hfin)
  set f : Ed Q → G := fun e ↦ if EdIn Q.periodic e then w e else 0
  refine ⟨Morse.zval M f, fun t ↦ Morse.zval_tri M f t, fun e he ↦ ?_⟩
  exact Morse.zval_agree M f {e | EdIn Q.periodic e} w (fun t ht ↦ edIn_tri_periodic c hfin t ht)
    (fun t ht ↦ hw t ht) (fun e he _ ↦ by simp only [f, if_pos (show EdIn Q.periodic e from he)])
    e he

/-! ### Weights of included paths -/

theorem pw_incl_of {S : Set V} (hS : Q.IsTauClosed S) (W : MeshWt Q ℤ) (WT : MeshWt (restrict hS) ℤ)
    (hw : ∀ {a b : FullSub S} (e : a ⟶ b), W.w (show a.val ⟶ b.val from e) = WT.w e) :
    ∀ {a b : FullSub S} (p : Quiver.Path a b), W.pw ((FullSub.incl S).mapPath p) = WT.pw p
  | _, _, Quiver.Path.nil => by simp [MeshWt.pw]
  | _, _, Quiver.Path.cons p e => by
      rw [Prefunctor.mapPath_cons, MeshWt.pw, MeshWt.pw, pw_incl_of hS W WT hw p]
      congr 1
      exact hw e

theorem pw_incl_zero {S : Set V} (W : MeshWt Q ℤ)
    (hw : ∀ {a b : FullSub S} (e : a ⟶ b), W.w (show a.val ⟶ b.val from e) = 0) :
    ∀ {a b : FullSub S} (p : Quiver.Path a b), W.pw ((FullSub.incl S).mapPath p) = 0
  | _, _, Quiver.Path.nil => by simp [MeshWt.pw]
  | _, _, Quiver.Path.cons p e => by
      rw [Prefunctor.mapPath_cons, MeshWt.pw, pw_incl_zero W hw p, hw e, add_zero]

end MeshWalk

end MultiplicativeBasisDeformations
