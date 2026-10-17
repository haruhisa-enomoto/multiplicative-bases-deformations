import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-!
# Star models of Dynkin trees

The finite trees of Proposition 4.1 are stars: a centre with arms. The star
model `StarV L` has the centre `none` and, on arm `i`, the vertices
`some ⟨i, k⟩` for `k ≤ L i`, the vertex `k` being at distance `k + 1` from the
centre. Paths are stars with at most two arms; `D_n`, `E_6`, `E_7`, `E_8` have
three arms of lengths `(1, 1, n - 3)`, `(1, 2, 2)`, `(1, 2, 3)`, `(1, 2, 4)`.
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

/-- The vertices of the star with arms of lengths `L i + 1`. -/
abbrev StarV {t : ℕ} (L : Fin t → ℕ) := Option (Σ i : Fin t, Fin (L i + 1))

/-- Adjacency in the star model. -/
def starAdj {t : ℕ} {L : Fin t → ℕ} : StarV L → StarV L → Prop
  | none, none => False
  | none, some x => (x.2 : ℕ) = 0
  | some x, none => (x.2 : ℕ) = 0
  | some x, some y => x.1 = y.1 ∧ ((y.2 : ℕ) = x.2 + 1 ∨ (x.2 : ℕ) = y.2 + 1)

/-- The star as a simple graph. -/
def starGraph {t : ℕ} (L : Fin t → ℕ) : SimpleGraph (StarV L) where
  Adj := starAdj
  symm := ⟨fun a b h ↦ by
    rcases a with _ | ⟨i, k⟩ <;> rcases b with _ | ⟨j, l⟩ <;> simp only [starAdj] at h ⊢ <;>
      first | exact h | exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h ↦ by
    rcases a with _ | ⟨i, k⟩ <;> simp only [starAdj] at h
    omega⟩

instance {t : ℕ} (L : Fin t → ℕ) : DecidableRel (starGraph L).Adj := fun a b ↦ by
  rcases a with _ | ⟨i, k⟩ <;> rcases b with _ | ⟨j, l⟩ <;>
    simp only [starGraph, starAdj] <;> infer_instance

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

/-- The distance of a star vertex from the centre. -/
def starDepth {t : ℕ} {L : Fin t → ℕ} : StarV L → ℕ
  | none => 0
  | some x => x.2 + 1

/-- Orientation away from the centre. -/
def starOrient {t : ℕ} {L : Fin t → ℕ} (x y : StarV L) : Prop :=
  starAdj x y ∧ starDepth y = starDepth x + 1

theorem starAdj_depth {t : ℕ} {L : Fin t → ℕ} {x y : StarV L} (h : starAdj x y) :
    starDepth y = starDepth x + 1 ∨ starDepth x = starDepth y + 1 := by
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩ <;> simp only [starAdj] at h <;>
    simp only [starDepth] <;> omega

instance {t : ℕ} {L : Fin t → ℕ} : DecidableRel (starOrient (L := L)) := fun x y ↦ by
  unfold starOrient
  exact instDecidableAnd (dp := (inferInstance : DecidableRel (starGraph L).Adj) x y)

end MultiplicativeBasisDeformations
