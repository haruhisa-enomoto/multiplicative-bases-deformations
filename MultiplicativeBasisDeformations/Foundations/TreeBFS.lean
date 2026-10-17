import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Trees seen from a root

Elementary facts about a finite tree with a proper two-colouring, used in the
proof of Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex:118–131`):
seen from a root `o`, adjacent vertices have distances differing by one, and
every other vertex has a unique neighbour closer to `o` (its parent).
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

universe v

namespace TreeBFS

variable {D : Type v} {G : SimpleGraph D} (par : D → ZMod 2)
  (hpar : ∀ {u w : D}, G.Adj u w → par w = par u + 1)

include hpar in
theorem walk_length_parity {u w : D} (p : G.Walk u w) :
    (p.length : ZMod 2) = par w - par u := by
  induction p with
  | nil => simp
  | cons h p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, ih, hpar h]
      push_cast
      ring

variable (hG : G.Connected)

include hpar hG in
/-- Adjacent vertices have distances to the root differing by exactly one. -/
theorem dist_adj (o : D) {u w : D} (h : G.Adj u w) :
    G.dist o w = G.dist o u + 1 ∨ G.dist o u = G.dist o w + 1 := by
  have h1 := h.diff_dist_adj (u := o)
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist o u
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist o w
  have e1 := walk_length_parity par hpar p
  have e2 := walk_length_parity par hpar q
  rw [hp] at e1
  rw [hq] at e2
  have hne : G.dist o u ≠ G.dist o w := by
    intro he
    rw [he, e2, hpar h] at e1
    have : (1 : ZMod 2) = 0 := by linear_combination e1
    exact absurd this (by decide)
  omega

include hG in
/-- Every vertex other than the root has a neighbour closer to the root. -/
theorem exists_parent (o : D) {v : D} (hv : v ≠ o) :
    ∃ u, G.Adj u v ∧ G.dist o u + 1 = G.dist o v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v o
  cases p with
  | nil => exact absurd rfl hv
  | cons h q =>
      rename_i u
      refine ⟨u, h.symm, le_antisymm ?_ ?_⟩
      · rw [SimpleGraph.Walk.length_cons] at hp
        have h1 := SimpleGraph.dist_le q.reverse
        rw [SimpleGraph.Walk.length_reverse] at h1
        rw [SimpleGraph.dist_comm] at hp
        omega
      · have h2 := h.diff_dist_adj (u := o)
        omega

include hG in
/-- In a tree, the parent is unique. -/
theorem parent_unique (hA : G.IsAcyclic) (o : D) {v u u' : D} (h : G.Adj u v)
    (hu : G.dist o u + 1 = G.dist o v) (h' : G.Adj u' v) (hu' : G.dist o u' + 1 = G.dist o v) :
    u = u' := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist o u
  obtain ⟨p', hp'⟩ := hG.exists_walk_length_eq_dist o u'
  have l1 : (p.concat h).length = G.dist o v := by
    rw [SimpleGraph.Walk.length_concat, hp, hu]
  have l2 : (p'.concat h').length = G.dist o v := by
    rw [SimpleGraph.Walk.length_concat, hp', hu']
  have e := hA.path_unique ⟨_, (p.concat h).isPath_of_length_eq_dist l1⟩
    ⟨_, (p'.concat h').isPath_of_length_eq_dist l2⟩
  have e' := congrArg Subtype.val e
  obtain ⟨huu, -⟩ := SimpleGraph.Walk.concat_inj e'
  exact huu

end TreeBFS

end MultiplicativeBasisDeformations
