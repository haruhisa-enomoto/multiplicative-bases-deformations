module

public import MultiplicativeBasisDeformations.Foundations.PreprojFunctionals
public import MultiplicativeBasisDeformations.Foundations.StarCorner

/-!
# Lemma A.5: closed paths of degree four in `Π(D₄)`

`lem:d4-four-return` (`periodic-mesh-calculations.tex`): "At the centre,
degree-four paths are the six `x_i x_j` with `i ≠ j`, and their remaining
relations are the row and column sums. In the order `12, 13, 21, 23, 31, 32`,
their classes are `z, -z, -z, z, z, -z`. Assigning these values in `k` gives a
nonzero functional annihilating all the relations, so `z ≠ 0`. At leaf `i`, the
two possible paths `b_i a_j b_j a_i`, `j ≠ i`, have only the relation that their
sum is zero."

We work in a star with three arms, deleting every vertex at depth at least two:
the retained vertices form the `D₄` with centre `o` and leaves `a_i`. The
functional takes the value `M i j` on `o a_i o a_j o` and on `a_i o a_j o a_i`,
where `M` is the cyclic matrix with rows and columns summing to zero.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace D4Return

open StarCorner OrientedTree

variable {L : Fin 3 → ℕ} {k : Type u} [Field k]

/-- The values `M i j = 1` for `j = i + 1`, `-1` for `i = j + 1`. -/
def M (i j : Fin 3) : k := if j = i + 1 then 1 else if i = j + 1 then -1 else 0

theorem M_self (i : Fin 3) : M (k := k) i i = 0 := by
  fin_cases i <;> simp [M] <;> decide

theorem M_succ (i : Fin 3) : M (k := k) i (i + 1) = 1 := by simp [M]

theorem sum_M_left (j : Fin 3) : ∑ i, M (k := k) i j = 0 := by
  fin_cases j <;> simp [M, Fin.sum_univ_three] <;> decide

theorem sum_M_right (i : Fin 3) : ∑ j, M (k := k) i j = 0 := by
  fin_cases i <;> simp [M, Fin.sum_univ_three] <;> decide

/-- The arm of a vertex at depth one. -/
def armIdx : StarV L → Option (Fin 3)
  | none => none
  | some ⟨i, j⟩ => if (j : ℕ) = 0 then some i else none

/-- The value on a pair of depth-one vertices. -/
def MA (a b : StarV L) : k :=
  match armIdx a, armIdx b with
  | some i, some j => M i j
  | _, _ => 0

theorem MA_self (a : StarV L) : MA (k := k) a a = 0 := by
  unfold MA
  cases armIdx a with
  | none => rfl
  | some i => exact M_self i

theorem depth_of_MA_ne {a b : StarV L} (h : MA (k := k) a b ≠ 0) :
    starDepth a = 1 ∧ starDepth b = 1 := by
  unfold MA at h
  rcases a with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases b with _ | ⟨i', ⟨j', hj'⟩⟩ <;>
    simp only [armIdx] at h <;> try exact absurd rfl h
  all_goals (split_ifs at h with h1 h2 <;> simp_all [starDepth])

/-- The functional on vertex lists of length five. -/
def G : List (StarV L) → k
  | [v₀, v₁, v₂, v₃, v₄] =>
      if v₀ = none ∧ v₂ = none ∧ v₄ = none then MA v₁ v₃
      else if v₁ = none ∧ v₃ = none ∧ v₀ = v₄ then MA v₀ v₂ else 0
  | _ => 0

/-- Sums over the arrows out of the centre. -/
theorem sum_centre (h : StarV L → k) :
    ∑ e : Σ w : (starTree L).Dbl, o L ⟶ w,
      (((starTree L).sgn k ((o L : (starTree L).Dbl) : StarV L) (e.1 : StarV L) : kˣ) : k) * h e.1 =
      ∑ i, h (av L i 0 (Nat.zero_le _)) := by
  symm
  refine Fintype.sum_bijective (fun i ↦ (⟨_, out0 i⟩ : Σ y : (starTree L).Dbl, o L ⟶ y))
    ⟨fun i i' hii ↦ ?_, fun e ↦ ?_⟩ _ _ fun i ↦ ?_
  · have := congrArg Sigma.fst hii
    exact (Sigma.mk.inj_iff.1 (Option.some.inj this)).1
  · obtain ⟨i, rfl⟩ := nbr_centre e
    exact ⟨i, rfl⟩
  · have hs : (starTree L).sgn k (o L : StarV L) (av L i 0 (Nat.zero_le _)) = 1 := by
      unfold OrientedTree.sgn
      rw [if_pos]
      exact ⟨(out0 i).down, by simp [starDepth, av, o, OrientedTree.toDbl]⟩
    simp only
    rw [hs, Units.val_one, one_mul]

theorem sum_MA_left (y : StarV L) : ∑ i, MA (k := k) (av L i 0 (Nat.zero_le _)) y = 0 := by
  unfold MA
  cases hy : armIdx y with
  | none => simp [av, armIdx, OrientedTree.toDbl]
  | some j => simpa [av, armIdx, OrientedTree.toDbl] using sum_M_left j

theorem sum_MA_right (x : StarV L) : ∑ j, MA (k := k) x (av L j 0 (Nat.zero_le _)) = 0 := by
  unfold MA
  cases hx : armIdx x with
  | none => simp [av, armIdx, OrientedTree.toDbl]
  | some i => simpa [av, armIdx, OrientedTree.toDbl] using sum_M_right i

theorem G_len (l : List (StarV L)) (h : l.length ≠ 5) : G (k := k) l = 0 := by
  rcases l with _ | ⟨v₀, _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, _ | ⟨v₄, _ | ⟨v₅, l⟩⟩⟩⟩⟩⟩ <;> simp_all [G]

theorem case02 (u y z : (starTree L).Dbl) :
    ∑ e : Σ w : (starTree L).Dbl, u ⟶ w,
      (((starTree L).sgn k (u : StarV L) (e.1 : StarV L) : kˣ) : k) *
        G (k := k) [u, e.1, u, y, z] = 0 := by
  by_cases hu : (u : StarV L) = none
  · change u = o L at hu
    subst hu
    rw [sum_centre (h := fun w ↦ G (k := k) [o L, w, o L, y, z])]
    by_cases hz : (z : StarV L) = none
    · simp only [G, o, OrientedTree.toDbl, hz, and_self, if_true]
      exact sum_MA_left y
    · simp only [G, o, OrientedTree.toDbl, hz, and_false, if_false]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs <;> simp_all [av, OrientedTree.toDbl]
  · refine Finset.sum_eq_zero fun e _ ↦ ?_
    simp only [G, hu, false_and, if_false]
    split_ifs with h
    · obtain ⟨-, -, rfl⟩ := h
      rw [MA_self, mul_zero]
    · rw [mul_zero]

theorem case11 (u x y : (starTree L).Dbl) :
    ∑ e : Σ w : (starTree L).Dbl, u ⟶ w,
      (((starTree L).sgn k (u : StarV L) (e.1 : StarV L) : kˣ) : k) *
        G (k := k) [x, u, e.1, u, y] = 0 := by
  by_cases hu : (u : StarV L) = none
  · change u = o L at hu
    subst hu
    rw [sum_centre (h := fun w ↦ G (k := k) [x, o L, w, o L, y])]
    by_cases hxy : (x : StarV L) = y
    · subst hxy
      rw [← sum_MA_right (k := k) x]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [G, o, OrientedTree.toDbl]
      split_ifs with h1 h2
      · simp [av, OrientedTree.toDbl] at h1
      · rfl
      · exact absurd (by simp) h2
    · refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp only [G, o, OrientedTree.toDbl]
      split_ifs with h1 h2
      · simp [av, OrientedTree.toDbl] at h1
      · exact absurd h2.2.2 hxy
      · rfl
  · refine Finset.sum_eq_zero fun e _ ↦ ?_
    simp only [G, hu, false_and, and_false, if_false]
    split_ifs with h
    · rw [MA_self, mul_zero]
    · rw [mul_zero]

theorem case20 (u x x' : (starTree L).Dbl) :
    ∑ e : Σ w : (starTree L).Dbl, u ⟶ w,
      (((starTree L).sgn k (u : StarV L) (e.1 : StarV L) : kˣ) : k) *
        G (k := k) [x, x', u, e.1, u] = 0 := by
  by_cases hu : (u : StarV L) = none
  · change u = o L at hu
    subst hu
    rw [sum_centre (h := fun w ↦ G (k := k) [x, x', o L, w, o L])]
    by_cases hx : (x : StarV L) = none
    · simp only [G, o, OrientedTree.toDbl, hx, and_self, if_true]
      exact sum_MA_right x'
    · simp only [G, o, OrientedTree.toDbl, hx, false_and, if_false]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      split_ifs <;> simp_all [av, OrientedTree.toDbl]
  · refine Finset.sum_eq_zero fun e _ ↦ ?_
    simp only [G, hu, false_and, and_false, if_false]
    split_ifs with h
    · obtain ⟨-, -, rfl⟩ := h
      rw [MA_self, mul_zero]
    · rw [mul_zero]

/-- **The functional annihilates the relations.** -/
theorem G_rel (u : (starTree L).Dbl) (l₀ l₂ : List (starTree L).Dbl) :
    ∑ e : Σ w : (starTree L).Dbl, u ⟶ w,
      (((starTree L).sgn k (u : StarV L) (e.1 : StarV L) : kˣ) : k) *
        G (k := k) (l₀ ++ u :: e.1 :: u :: l₂) = 0 := by
  by_cases hl : l₀.length + l₂.length = 2
  · rcases l₀ with _ | ⟨x, _ | ⟨x', _ | ⟨x'', l₀⟩⟩⟩ <;>
      rcases l₂ with _ | ⟨y, _ | ⟨z, _ | ⟨z', l₂⟩⟩⟩ <;> simp at hl <;> try omega
    · exact case02 u y z
    · exact case11 u x y
    · exact case20 u x x'
  · refine Finset.sum_eq_zero fun e _ ↦ ?_
    rw [G_len _ (by simp; omega), mul_zero]

/-- The deleted vertices: depth at least two. -/
def Del : Set (starTree L).Dbl := {v | 2 ≤ starDepth (L := L) v}

theorem G_del (l : List (starTree L).Dbl) (h : ∃ d ∈ l, d ∈ Del) : G (k := k) l = 0 := by
  obtain ⟨d, hd, hdD⟩ := h
  change 2 ≤ starDepth (L := L) d at hdD
  by_cases hl : l.length = 5
  · rcases l with _ | ⟨v₀, _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, _ | ⟨v₄, _ | ⟨v₅, l⟩⟩⟩⟩⟩⟩ <;> simp at hl
    simp only [G]
    split_ifs with h1 h2
    · by_contra hne
      obtain ⟨d1, d3⟩ := depth_of_MA_ne hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp_all [starDepth]
    · by_contra hne
      obtain ⟨d0, d2⟩ := depth_of_MA_ne hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp_all [starDepth]
    · rfl
  · exact G_len l hl

theorem not_mem_of_G {v : (starTree L).Dbl} (p : Quiver.Path v v) (hp : G (k := k) p.vertices ≠ 0) :
    LinearPaths.path (k := k) p ∉ (((starTree L).preproj k).del Del).ideal _ _ := by
  intro h
  have := (starTree L).vfun_eq_zero_of_mem Del G (fun u l₀ l₂ ↦ G_rel u l₀ l₂) G_del h
  rw [vfun_path] at this
  exact hp this

/-- **Lemma A.5**: every vertex of the `D₄` part carries a nonzero closed path of
degree four in `Π(Δ)` modulo the deeper vertices. -/
theorem d4_return (v : (starTree L).Dbl) (hv : starDepth (L := L) v ≤ 1) :
    ∃ p : Quiver.Path v v, p.length = 4 ∧
      LinearPaths.path (k := k) p ∉ (((starTree L).preproj k).del Del).ideal _ _ := by
  rcases v with _ | ⟨i, ⟨j, hj⟩⟩
  · -- the centre: `x₀ x₁`
    refine ⟨(xp (L := L) 0).comp (xp 1), by simp [xp], not_mem_of_G _ ?_⟩
    simp only [xp, Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath]
    simp [G, MA, av, armIdx, OrientedTree.toDbl, o, M]
  · obtain rfl : j = 0 := by simp [starDepth] at hv; omega
    -- the leaf `a_i`: `a_i o a_{i+1} o a_i`
    refine ⟨(in0 (L := L) i).toPath.comp ((out0 (i + 1)).toPath.comp ((in0 (i + 1)).toPath.comp
      (out0 i).toPath)), by simp, not_mem_of_G _ ?_⟩
    simp only [Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath]
    simp [G, MA, av, armIdx, OrientedTree.toDbl, o, M]

end D4Return

end MultiplicativeBasisDeformations
