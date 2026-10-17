import MultiplicativeBasisDeformations.Foundations.TreeRepetition
import MultiplicativeBasisDeformations.Foundations.SectionalPaths
import Mathlib.Data.Set.Finite.List

/-!
# The tree of sectional paths

Proof of Proposition 4.1, Step 1 (`periodic-mesh-calculations.tex:24–56`).
"Fix a vertex `x₀` in the component. Let `Δ` have as vertices all sectional
paths starting at `x₀`, including the empty path. Join a path to each of its
sectional one-arrow extensions, orienting the edge towards the extension. This
is a finite rooted tree."

Throughout, `Q` is a stable translation quiver on a finite set with at most one
arrow between two vertices. This file builds the type `SecPath` of sectional
paths from `x₀`, shows it is finite when sectional paths are bounded, and
equips it with the oriented tree structure (edges from a path to its sectional
one-arrow extensions).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe v w

namespace Quiver.Path

variable {V : Type v} [Quiver.{w} V]

theorem eq_nil_of_arrowList_eq_nil {x y : V} (p : Quiver.Path x y) (h : p.arrowList = []) :
    (⟨y, p⟩ : Quiver.PathStar x) = ⟨x, Quiver.Path.nil⟩ := by
  cases p with
  | nil => rfl
  | cons p a => simp at h

/-- A path from a fixed start is determined by its arrows. -/
theorem arrowList_injective {x : V} :
    ∀ {y y' : V} (p : Quiver.Path x y) (q : Quiver.Path x y'),
      p.arrowList = q.arrowList → (⟨y, p⟩ : Quiver.PathStar x) = ⟨y', q⟩
  | _, _, Quiver.Path.nil, q, h => (eq_nil_of_arrowList_eq_nil q h.symm).symm
  | _, _, Quiver.Path.cons p a, Quiver.Path.nil, h => by simp at h
  | _, _, Quiver.Path.cons p a, Quiver.Path.cons q b, h => by
      simp only [Quiver.Path.arrowList_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      have ih := arrowList_injective p q h1
      simp only [List.cons.injEq, and_true] at h2
      cases ih
      cases h2
      rfl

theorem length_arrowList {x : V} : ∀ {y : V} (p : Quiver.Path x y), p.arrowList.length = p.length
  | _, Quiver.Path.nil => rfl
  | _, Quiver.Path.cons p a => by simp [length_arrowList p]

end Quiver.Path

namespace MultiplicativeBasisDeformations

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] (Q : TranslationQuiver V) (x₀ : V)

/-- The sectional paths starting at `x₀`: the vertices of the tree `Δ`. -/
def SecPath : Type (max v w) := {p : Quiver.PathStar x₀ // Q.IsSectional p.2}

namespace SecPath

variable {Q x₀}

/-- The end vertex of a sectional path. -/
def endv (p : Q.SecPath x₀) : V := p.1.1

/-- The length of a sectional path (its depth in the tree). -/
def len (p : Q.SecPath x₀) : ℕ := p.1.2.length

variable (Q x₀) in
/-- The empty path, the root of the tree. -/
def root : Q.SecPath x₀ := ⟨⟨x₀, Quiver.Path.nil⟩, List.isChain_nil⟩

/-- `q` is a sectional one-arrow extension of `p`. -/
def IsParent (p q : Q.SecPath x₀) : Prop :=
  ∃ (w : V) (a : p.endv ⟶ w), q.1 = ⟨w, p.1.2.cons a⟩

theorem len_of_isParent {p q : Q.SecPath x₀} (h : IsParent p q) : q.len = p.len + 1 := by
  obtain ⟨w, a, h⟩ := h
  unfold len
  rw [h]
  rfl

theorem isSectional_of_cons {y z : V} (p : Quiver.Path x₀ y) (a : y ⟶ z)
    (h : Q.IsSectional (p.cons a)) : Q.IsSectional p := by
  unfold IsSectional at h ⊢
  rw [Quiver.Path.arrowList_cons] at h
  exact h.infix ⟨[], [⟨_, _, a⟩], by simp⟩

/-- The parent of a nonempty sectional path. -/
def parent (p : Q.SecPath x₀) (hp : p.len ≠ 0) : Q.SecPath x₀ :=
  match p, hp with
  | ⟨⟨_, Quiver.Path.nil⟩, _⟩, hp => absurd rfl hp
  | ⟨⟨_, Quiver.Path.cons p' _⟩, h⟩, _ => ⟨⟨_, p'⟩, isSectional_of_cons p' _ h⟩

theorem parent_isParent (p : Q.SecPath x₀) (hp : p.len ≠ 0) : IsParent (p.parent hp) p := by
  obtain ⟨⟨y, q⟩, h⟩ := p
  cases q with
  | nil => exact absurd rfl hp
  | cons q a => exact ⟨y, a, rfl⟩

theorem eq_parent_of_isParent {p q : Q.SecPath x₀} (h : IsParent p q) (hq : q.len ≠ 0) :
    p = q.parent hq := by
  obtain ⟨w, a, hq'⟩ := h
  obtain ⟨⟨y, q'⟩, hs⟩ := q
  simp only at hq'
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 hq'
  cases eq_of_heq h2
  rfl

/-- The tree `Δ` of sectional paths, oriented from each path to its
extensions. Its two-colouring is the parity of the length. -/
def tree : OrientedTree (Q.SecPath x₀) where
  G :=
    { Adj := fun p q ↦ IsParent p q ∨ IsParent q p
      symm := ⟨fun _ _ h ↦ Or.symm h⟩
      loopless := ⟨fun p h ↦ by
        rcases h with h | h <;> · have := len_of_isParent h; omega⟩ }
  par p := (p.len : ZMod 2)
  par_adj := by
    rintro p q (h | h)
    · rw [len_of_isParent h]; push_cast; rfl
    · rw [len_of_isParent h]; push_cast
      rw [add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]
  orient := IsParent
  orient_adj := fun h ↦ Or.inl h
  orient_or := by
    rintro p q (h | h)
    · refine ⟨fun _ h' ↦ ?_, fun _ ↦ h⟩
      have := len_of_isParent h; have := len_of_isParent h'; omega
    · refine ⟨fun h' ↦ ?_, fun h' ↦ absurd h h'⟩
      have := len_of_isParent h; have := len_of_isParent h'; omega

/-- With a bound on the lengths of sectional paths, `Δ` is finite. -/
theorem finite_of_bound [Finite V] [∀ x y : V, Finite (x ⟶ y)] (N : ℕ)
    (hN : ∀ (y : V) (p : Quiver.Path x₀ y), Q.IsSectional p → p.length < N) :
    Finite (Q.SecPath x₀) := by
  haveI : Finite {l : List (Σ u v : V, u ⟶ v) // l.length < N} :=
    (List.finite_length_lt (Σ u v : V, u ⟶ v) N).to_subtype
  refine Finite.of_injective (β := {l : List (Σ u v : V, u ⟶ v) // l.length < N})
    (fun p ↦ ⟨p.1.2.arrowList, by rw [Quiver.Path.length_arrowList]; exact hN _ _ p.2⟩) ?_
  intro p q h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Quiver.Path.arrowList_injective _ _ h)

end SecPath

end TranslationQuiver

end MultiplicativeBasisDeformations
