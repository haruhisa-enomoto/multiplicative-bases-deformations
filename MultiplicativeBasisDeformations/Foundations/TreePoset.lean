module

public import MultiplicativeBasisDeformations.Foundations.PosetRepInfinite

/-!
# Lemma 8.8 for tree posets

`local-ray-geometry.tex`: "These counts depend only on the underlying graphs; for a
tree any orientation is allowed." For a finite poset whose cover graph is acyclic, paths
along covering relations are unique (`subsingleton_ePath`) and exist between comparable
points (`nonempty_ePath`), so the incidence algebra is the path algebra of the oriented
tree and Lemma 8.8 applies (`tree_not_isRepresentationFinite`); the dual poset has the same
cover graph (`tree_not_isRepresentationFinite_dual`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace PosetRep

universe u

variable {P : Type} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
  [DecidableLE P]

/-- The cover graph. -/
def coverGraph (P : Type) [PartialOrder P] : SimpleGraph P :=
  SimpleGraph.fromRel fun x y : P ↦ x ⋖ y

theorem adj_of_covBy {y z : P} (h : y ⋖ z) : (coverGraph P).Adj y z := by
  simp only [coverGraph, SimpleGraph.fromRel_adj]
  exact ⟨h.lt.ne, Or.inl h⟩

/-- A path along covers as a walk of the cover graph. -/
def toWalk : ∀ {x y : P}, EPath (· ⋖ ·) x y → (coverGraph P).Walk x y
  | _, _, EPath.nil _ => SimpleGraph.Walk.nil
  | _, _, EPath.cons p h => (toWalk p).concat (adj_of_covBy h)

theorem toWalk_nil (x : P) : toWalk (EPath.nil x : EPath (· ⋖ ·) x x) = SimpleGraph.Walk.nil := by
  rw [toWalk]

theorem toWalk_cons {x y z : P} (p : EPath (· ⋖ ·) x y) (h : y ⋖ z) :
    toWalk (EPath.cons p h) = (toWalk p).concat (adj_of_covBy h) := by
  rw [toWalk]

theorem toWalk_support_lt : ∀ {x y : P} (p : EPath (· ⋖ ·) x y), ∀ v ∈ (toWalk p).support, v ≤ y
  | _, _, EPath.nil _ => by intro v hv; rw [toWalk_nil] at hv; simp at hv; rw [hv]
  | _, _, EPath.cons p h => by
      intro v hv
      rw [toWalk_cons, SimpleGraph.Walk.support_concat, List.mem_append,
        List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact (toWalk_support_lt p v hv).trans h.lt.le
      · exact le_rfl

theorem toWalk_isPath : ∀ {x y : P} (p : EPath (· ⋖ ·) x y), (toWalk p).IsPath
  | _, _, EPath.nil _ => by rw [toWalk_nil]; exact SimpleGraph.Walk.IsPath.nil
  | _, _, EPath.cons p h => by
      rw [toWalk_cons]
      refine (toWalk_isPath p).concat ?_ _
      intro hz
      exact h.lt.not_ge (toWalk_support_lt p _ hz)

theorem toWalk_injective : ∀ {x y : P} (p q : EPath (· ⋖ ·) x y), toWalk p = toWalk q → p = q
  | _, _, EPath.nil _, EPath.nil _, _ => rfl
  | _, _, EPath.nil _, EPath.cons q h, hpq => by
      exfalso
      have := congrArg SimpleGraph.Walk.length hpq
      rw [toWalk_nil, toWalk_cons, SimpleGraph.Walk.length_concat] at this
      simp at this
  | _, _, EPath.cons p h, EPath.nil _, hpq => by
      exfalso
      have := congrArg SimpleGraph.Walk.length hpq
      rw [toWalk_nil, toWalk_cons, SimpleGraph.Walk.length_concat] at this
      simp at this
  | _, _, @EPath.cons _ _ _ _ _ p h, @EPath.cons _ _ _ _ _ q h', hpq => by
      rw [toWalk_cons, toWalk_cons] at hpq
      obtain ⟨rfl, hpq'⟩ := SimpleGraph.Walk.concat_inj hpq
      rw [toWalk_injective p q hpq']

/-- **Paths along covers are unique when the cover graph is acyclic.** -/
theorem subsingleton_ePath (hT : (coverGraph P).IsAcyclic) (x y : P) :
    Subsingleton (EPath (· ⋖ ·) x y) := by
  refine ⟨fun p q ↦ toWalk_injective p q ?_⟩
  have := (hT.subsingleton_path x y).elim ⟨toWalk p, toWalk_isPath p⟩ ⟨toWalk q, toWalk_isPath q⟩
  exact congrArg Subtype.val this

/-- **Paths along covers are unique when lower covers above a point are unique**: if every
`y` has at most one lower cover `m` with `x ≤ m` (true for trees and crowns). -/
theorem subsingleton_ePath_of_lowerCover
    (h : ∀ x y m m' : P, x ≤ m → m ⋖ y → x ≤ m' → m' ⋖ y → m = m') :
    ∀ {x y : P} (p q : EPath (· ⋖ ·) x y), p = q
  | _, _, EPath.nil _, EPath.nil _ => rfl
  | _, _, EPath.nil _, EPath.cons q h' => by
      exact absurd (q.le (fun _ _ h ↦ h.lt)) h'.lt.not_ge
  | _, _, EPath.cons p h', EPath.nil _ => by
      exact absurd (p.le (fun _ _ h ↦ h.lt)) h'.lt.not_ge
  | _, _, @EPath.cons _ _ _ _ _ p h₁, @EPath.cons _ _ _ _ _ q h₂ => by
      obtain rfl := h _ _ _ _ (p.le (fun _ _ h ↦ h.lt)) h₁ (q.le (fun _ _ h ↦ h.lt)) h₂
      rw [subsingleton_ePath_of_lowerCover h p q]

/-- **Comparable points are joined by covers.** -/
theorem nonempty_ePath (x y : P) (h : x ≤ y) : Nonempty (EPath (· ⋖ ·) x y) := by
  induction hn : (Finset.Icc x y).card using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    rcases h.lt_or_eq with hlt | rfl
    · obtain ⟨z, hxz, hzy⟩ := exists_le_covBy_of_lt hlt
      obtain ⟨p⟩ := ih (Finset.Icc x z).card (by
        rw [← hn]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
          ⟨Finset.Icc_subset_Icc_right hzy.lt.le, fun he ↦ ?_⟩)
        have : y ∈ Finset.Icc x z := he ▸ Finset.mem_Icc.2 ⟨h, le_rfl⟩
        exact hzy.lt.not_ge (Finset.mem_Icc.1 this).2) z hxz rfl
      exact ⟨EPath.cons p hzy⟩
    · exact ⟨EPath.nil x⟩

/-- **A rank criterion for acyclicity**: if every vertex has at most one neighbour of smaller
rank, the graph is acyclic (the vertex of largest rank on a cycle would have two). -/
theorem isAcyclic_of_rank {V : Type*} [DecidableEq V] (G : SimpleGraph V) (r : V → ℕ)
    (hr : Function.Injective r)
    (h : ∀ v a b, G.Adj v a → G.Adj v b → r a < r v → r b < r v → a = b) : G.IsAcyclic := by
  intro u c hc
  obtain ⟨v, hv, hmax⟩ := c.support.toFinset.exists_max_image r ⟨u, by simp⟩
  rw [List.mem_toFinset] at hv
  set c' := c.rotate v hv
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate hv).2 hc
  have hn := hc'.not_nil
  have ha : G.Adj v c'.snd := SimpleGraph.Walk.adj_snd hn
  have hb : G.Adj c'.penultimate v := SimpleGraph.Walk.adj_penultimate hn
  have hsa : c'.snd ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c v hv]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have hsb : c'.penultimate ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c v hv]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have hla : r c'.snd < r v := lt_of_le_of_ne (hmax _ (List.mem_toFinset.2 hsa))
    fun he ↦ ha.ne (hr he).symm
  have hlb : r c'.penultimate < r v := lt_of_le_of_ne (hmax _ (List.mem_toFinset.2 hsb))
    fun he ↦ hb.ne (hr he)
  exact hc'.snd_ne_penultimate (h v _ _ ha hb.symm hla hlb)

/-- Transport of incidence functions along an order isomorphism. -/
def incMap {k : Type u} [Field k] {Q : Type} [PartialOrder Q] (e : P ≃o Q)
    (f : IncidenceAlgebra k P) : IncidenceAlgebra k Q :=
  ⟨fun a b ↦ f (e.symm a) (e.symm b), fun a b hab ↦
    IncidenceAlgebra.apply_eq_zero_of_not_le (fun h ↦ hab (by simpa using e.monotone h)) _⟩

/-- **Incidence algebras of isomorphic posets are isomorphic.** -/
def incidenceEquiv {k : Type u} [Field k] {Q : Type} [PartialOrder Q] [Fintype Q] [DecidableEq Q]
    [LocallyFiniteOrder Q] (e : P ≃o Q) : IncidenceAlgebra k P ≃ₐ[k] IncidenceAlgebra k Q where
  toFun := incMap e
  invFun := incMap e.symm
  left_inv f := by ext a b _; simp [incMap]
  right_inv f := by ext a b _; simp [incMap]
  map_mul' f g := by
    ext a b _
    simp only [incMap, IncidenceAlgebra.coe_mk, IncidenceAlgebra.mul_apply]
    refine Finset.sum_nbij' (fun x ↦ e x) (fun x ↦ e.symm x) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (fun x _ ↦ by simp) (fun x _ ↦ by simp) (fun x _ ↦ by simp)
    · rw [Finset.mem_Icc] at hx ⊢
      exact ⟨by simpa using e.monotone hx.1, by simpa using e.monotone hx.2⟩
    · rw [Finset.mem_Icc] at hx ⊢
      exact ⟨by simpa using e.symm.monotone hx.1, by simpa using e.symm.monotone hx.2⟩
  map_add' f g := by ext a b _; simp [incMap]
  commutes' c := by
    ext a b _
    change (algebraMap k k c • (1 : IncidenceAlgebra k P)) (e.symm a) (e.symm b) =
      (algebraMap k k c • (1 : IncidenceAlgebra k Q)) a b
    rw [IncidenceAlgebra.constSMul_apply, IncidenceAlgebra.constSMul_apply,
      IncidenceAlgebra.one_apply, IncidenceAlgebra.one_apply]
    simp

theorem covBy_lt (x y : P) (h : x ⋖ y) : x < y := h.lt

variable (k : Type u) [Field k] [IsAlgClosed k] [DecidableRel (α := P) (· ⋖ ·)]

/-- **Lemma 8.8 for a poset whose cover graph is acyclic.** -/
theorem tree_not_isRepresentationFinite (hT : (coverGraph P).IsAcyclic) (d : P → ℕ)
    (hd : ∃ v, 0 < d v) (hN : ∑ v, d v ^ 2 ≤ ∑ a : Arr (P := P) (· ⋖ ·), d (tgt a) * d (src a)) :
    ¬ IsRepresentationFinite k (IncidenceAlgebra k P) :=
  not_isRepresentationFinite (k := k) d covBy_lt (subsingleton_ePath hT) nonempty_ePath hd hN

/-! ### Duals -/

theorem coverGraph_dual_adj (x y : Pᵒᵈ) :
    (coverGraph Pᵒᵈ).Adj x y ↔ (coverGraph P).Adj (OrderDual.ofDual x) (OrderDual.ofDual y) := by
  simp only [coverGraph, SimpleGraph.fromRel_adj]
  have e1 : x ⋖ y ↔ OrderDual.ofDual y ⋖ OrderDual.ofDual x := ofDual_covBy_ofDual_iff.symm
  have e2 : y ⋖ x ↔ OrderDual.ofDual x ⋖ OrderDual.ofDual y := ofDual_covBy_ofDual_iff.symm
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩

theorem isAcyclic_dual (hT : (coverGraph P).IsAcyclic) : (coverGraph Pᵒᵈ).IsAcyclic := by
  have e : coverGraph Pᵒᵈ ≃g coverGraph P :=
    { toEquiv := OrderDual.ofDual
      map_rel_iff' := fun {x y} ↦ (coverGraph_dual_adj x y).symm }
  exact hT.comap e.toEmbedding.toHom e.injective

/-- The arrows of the dual poset. -/
def arrDual : Arr (P := Pᵒᵈ) (· ⋖ ·) ≃ Arr (P := P) (· ⋖ ·) where
  toFun a := (⟨(OrderDual.ofDual a.1.2, OrderDual.ofDual a.1.1), ofDual_covBy_ofDual_iff.2 a.2⟩ :
    Arr (P := P) (· ⋖ ·))
  invFun a := (⟨(OrderDual.toDual a.1.2, OrderDual.toDual a.1.1), toDual_covBy_toDual_iff.2 a.2⟩ :
    Arr (P := Pᵒᵈ) (· ⋖ ·))
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

theorem sum_arr_dual [DecidableRel (α := Pᵒᵈ) (· ⋖ ·)] (d : P → ℕ) :
    ∑ a : Arr (P := Pᵒᵈ) (· ⋖ ·), d (OrderDual.ofDual (tgt a)) * d (OrderDual.ofDual (src a)) =
      ∑ a : Arr (P := P) (· ⋖ ·), d (tgt a) * d (src a) :=
  Fintype.sum_equiv arrDual _ _ fun _ ↦ mul_comm _ _

theorem tree_not_isRepresentationFinite_dual [DecidableRel (α := Pᵒᵈ) (· ⋖ ·)]
    (hT : (coverGraph P).IsAcyclic) (d : P → ℕ)
    (hd : ∃ v, 0 < d v) (hN : ∑ v, d v ^ 2 ≤ ∑ a : Arr (P := P) (· ⋖ ·), d (tgt a) * d (src a)) :
    ¬ IsRepresentationFinite k (IncidenceAlgebra k Pᵒᵈ) := by
  refine tree_not_isRepresentationFinite (P := Pᵒᵈ) k (isAcyclic_dual hT)
    (fun v ↦ d (OrderDual.ofDual v)) (by obtain ⟨v, hv⟩ := hd; exact ⟨OrderDual.toDual v, hv⟩) ?_
  rw [sum_arr_dual d]
  exact (Fintype.sum_equiv OrderDual.ofDual _ _ fun _ ↦ rfl).trans_le hN

end PosetRep

end MultiplicativeBasisDeformations
