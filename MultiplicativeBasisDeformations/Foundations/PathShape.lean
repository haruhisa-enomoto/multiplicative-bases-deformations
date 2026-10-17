import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Cast

/-!
# Paths with at most one arrow between vertices

In a quiver with at most one arrow between any two vertices, a path is
determined by its list of vertices. This is used to compare images of paths under
automorphisms of trees.
-/

set_option autoImplicit false

namespace Quiver.Path

variable {V : Type*} [Quiver V] [∀ x y : V, Subsingleton (x ⟶ y)]

theorem heq_of_vertices_eq {a b : V} (p : Path a b) :
    ∀ {a' b' : V} (q : Path a' b'), p.vertices = q.vertices → HEq p q := by
  induction p with
  | nil =>
      intro a' b' q h
      cases q with
      | nil =>
          simp only [vertices_nil, List.cons.injEq, and_true] at h
          subst h; rfl
      | cons q e =>
          have := congrArg List.length h
          simp [vertices_length] at this
  | @cons b c p e ih =>
      intro a' b' q h
      cases q with
      | nil =>
          have := congrArg List.length h
          simp [vertices_length] at this
      | @cons b'' _ q e' =>
          simp only [vertices_cons, List.concat_eq_append] at h
          obtain ⟨h1, h2⟩ := List.append_inj' h rfl
          simp only [List.cons.injEq, and_true] at h2
          subst h2
          have hq := ih q h1
          have ha : a = a' := by
            have := congrArg List.head? h1
            rw [vertices_head?, vertices_head?] at this
            exact Option.some.inj this
          have hb : b = b'' := by
            have e1 := p.vertices_getLast
            have e2 := q.vertices_getLast
            simp only [h1] at e1
            exact e1.symm.trans e2
          subst ha hb
          rw [eq_of_heq hq, Subsingleton.elim e e']

theorem eq_cast_of_vertices_eq {a b a' b' : V} (p : Path a b) (q : Path a' b') (ha : a' = a)
    (hb : b' = b) (h : p.vertices = q.vertices) : p = q.cast ha hb :=
  (eq_cast_iff_heq ha hb q p).2 (heq_of_vertices_eq p q h)

end Quiver.Path
