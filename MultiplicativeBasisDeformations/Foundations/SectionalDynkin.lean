module

public import MultiplicativeBasisDeformations.Foundations.PreprojectiveNilpotent
public import MultiplicativeBasisDeformations.Foundations.PreprojectiveDimension
public import MultiplicativeBasisDeformations.Foundations.TreeArms

/-!
# The sectional tree is a Dynkin tree

Proof of Proposition 4.1, Step 2: combining the preceding steps for the tree `Δ`
of sectional paths of a finite stable translation quiver with a
finite-dimensional scalar mesh category.

* `Δ` is a tree (`isTree`): it is connected through parents, and its edges are
  the parent edges.
* Long paths vanish in `Π(Δ)` (`PreprojectiveNilpotent.lean`), so `n_i = dim P_i`
  is finite and `∑_{j∼i} n_j < 2 n_i` (`PreprojectiveDimension.lean`).
* Hence `Δ` is a star model with at most one arm, or with three arms satisfying
  `∑ p_i/(p_i + 1) < 2` (`classify_tree`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace TranslationQuiver.SecPath

variable {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V} {x₀ : V}

theorem eq_root_of_len {p : Q.SecPath x₀} (h : p.len = 0) : p = root Q x₀ := by
  obtain ⟨⟨y, q⟩, hq⟩ := p
  cases q with
  | nil => rfl
  | cons q a => simp [len] at h

theorem len_parent (p : Q.SecPath x₀) (hp : p.len ≠ 0) : (p.parent hp).len + 1 = p.len :=
  (len_of_isParent (parent_isParent p hp)).symm

/-- `Δ` is connected. -/
theorem reachable_root (p : Q.SecPath x₀) :
    (SecPath.tree (Q := Q) (x₀ := x₀)).G.Reachable (root Q x₀) p := by
  induction h : p.len generalizing p with
  | zero => rw [eq_root_of_len h]
  | succ n ih =>
      have hp : p.len ≠ 0 := by omega
      have h1 := ih (p.parent hp) (by have := len_parent p hp; omega)
      exact h1.trans (SimpleGraph.Adj.reachable (Or.inl (parent_isParent p hp)))

/-- The parent edge of a nonroot vertex. -/
def parentEdge (p : {p : Q.SecPath x₀ // p ≠ root Q x₀}) :
    (SecPath.tree (Q := Q) (x₀ := x₀)).G.edgeSet :=
  have hp : p.1.len ≠ 0 := fun h ↦ p.2 (eq_root_of_len h)
  ⟨s(p.1.parent hp, p.1), Or.inl (parent_isParent p.1 hp)⟩

theorem parentEdge_bijective : Function.Bijective (parentEdge (Q := Q) (x₀ := x₀)) := by
  constructor
  · rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    have hp' : p.len ≠ 0 := fun h ↦ hp (eq_root_of_len h)
    have hq' : q.len ≠ 0 := fun h ↦ hq (eq_root_of_len h)
    simp only [parentEdge, Subtype.mk.injEq, Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact Subtype.ext h
    · exfalso
      have e1 := len_parent p hp'
      have e2 := len_parent q hq'
      rw [h1] at e1
      rw [← h2] at e2
      omega
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h a b =>
        rcases he with h | h
        · change IsParent a b at h
          have hb : b.len ≠ 0 := by have := len_of_isParent h; omega
          have hb' : b ≠ root Q x₀ := by
            intro hb'; rw [hb'] at hb; exact hb rfl
          refine ⟨⟨b, hb'⟩, Subtype.ext ?_⟩
          simp only [parentEdge]
          rw [← eq_parent_of_isParent h hb]
        · change IsParent b a at h
          have ha : a.len ≠ 0 := by have := len_of_isParent h; omega
          have ha' : a ≠ root Q x₀ := by
            intro ha'; rw [ha'] at ha; exact ha rfl
          refine ⟨⟨a, ha'⟩, Subtype.ext ?_⟩
          simp only [parentEdge]
          rw [← eq_parent_of_isParent h ha, Sym2.eq_swap]

/-- **`Δ` is a tree.** -/
theorem isTree [Finite (Q.SecPath x₀)] : (SecPath.tree (Q := Q) (x₀ := x₀)).G.IsTree := by
  classical
  haveI := Fintype.ofFinite (Q.SecPath x₀)
  haveI : Nonempty (Q.SecPath x₀) := ⟨root Q x₀⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨⟨fun p q ↦ (reachable_root p).symm.trans (reachable_root q)⟩, ?_⟩
  rw [← Nat.card_eq_of_bijective _ parentEdge_bijective, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have : 0 < Fintype.card (Q.SecPath x₀) := Fintype.card_pos_iff.2 ⟨root Q x₀⟩
  omega

theorem sum_outArrow {D : Type*} [Fintype D] [DecidableEq D] (T : OrientedTree D)
    [DecidableRel T.G.Adj] (i : D) (f : D → ℚ) :
    ∑ e : T.OutArrow (T.toDbl i), f e.1 = ∑ j ∈ T.G.neighborFinset i, f j := by
  let E : T.OutArrow (T.toDbl i) ≃ {j // T.G.Adj i j} :=
    { toFun := fun e ↦ ⟨e.1, e.2.down⟩
      invFun := fun j ↦ ⟨T.toDbl j.1, ⟨j.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine (Fintype.sum_equiv E _ (fun j ↦ f j.1) fun _ ↦ rfl).trans ?_
  exact (Finset.sum_subtype (T.G.neighborFinset i) (p := fun j ↦ T.G.Adj i j)
    (fun j ↦ SimpleGraph.mem_neighborFinset _ _ _) f).symm

variable {k : Type u} [Field k]

/-- **Proposition 4.1, Step 2**: the tree of sectional paths of a finite stable
translation quiver with a finite-dimensional scalar mesh category is a Dynkin
tree, in the form of a star model. -/
theorem sectional_star_model [Finite V] [∀ x y : V, Subsingleton (x ⟶ y)]
    [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (hQ : Q.IsStable) (c : MeshCoefficients k Q)
    (hfin : ∀ x y : V, FiniteDimensional k
      (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    [Fintype (Q.SecPath x₀)] [DecidableEq (Q.SecPath x₀)] :
    ∃ (t : ℕ) (L : Fin t → ℕ) (e : Q.SecPath x₀ ≃ StarV L),
      (∀ p q, (SecPath.tree (Q := Q) (x₀ := x₀)).G.Adj p q ↔ starAdj (e p) (e q)) ∧
      (t ≤ 1 ∨ (t = 3 ∧ ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2)) := by
  classical
  set T := SecPath.tree (Q := Q) (x₀ := x₀)
  obtain ⟨N, hN⟩ := ScalarMeshCategory.exists_pathMor_eq_zero c hfin
  have hNmesh : ∀ (x y : V) (p : Quiver.Path x y), N ≤ p.length →
      LinearPaths.path (k := k) p ∈ (RelSystem.mesh c).ideal _ _ := by
    intro x y p hp
    have := hN x y p hp
    rw [ScalarMeshCategory.pathMor, RelationCategory.functor_map_eq_zero_iff] at this
    exact this
  have hineq := fun i : T.Dbl ↦ OrientedTree.sum_finrank_add_one_le (T := T) (k := k) N
    (fun v Y P hP ↦ path_mem_preproj (x₀ := x₀) hQ c N hNmesh P hP) i
  let n : Q.SecPath x₀ → ℚ := fun i ↦ (Module.finrank k (T.Pq k (T.toDbl i)) : ℚ)
  have hMn : ∀ i, 0 < 2 * n i - ∑ j ∈ T.G.neighborFinset i, n j := by
    intro i
    have h := hineq (T.toDbl i)
    rw [← sum_outArrow T i n]
    have h' : (∑ e : T.OutArrow (T.toDbl i), n e.1) + 1 ≤ 2 * n i := by
      have h2 : ((∑ e : T.OutArrow (T.toDbl i), Module.finrank k (T.Pq k e.1) : ℕ) : ℚ) + 1 ≤
          2 * (Module.finrank k (T.Pq k (T.toDbl i)) : ℚ) := by exact_mod_cast h
      push_cast at h2
      exact h2
    linarith
  have hn : ∀ i, 0 < n i := by
    intro i
    have h := hineq (T.toDbl i)
    have : 1 ≤ Module.finrank k (T.Pq k (T.toDbl i)) := by omega
    simp only [n]
    exact_mod_cast this
  haveI : Nonempty (Q.SecPath x₀) := ⟨root Q x₀⟩
  have htree := isTree (Q := Q) (x₀ := x₀)
  exact RootedTree.classify_tree T.G T.par T.par_adj htree.1 htree.IsAcyclic hn hMn

end TranslationQuiver.SecPath

end MultiplicativeBasisDeformations
