module

public import Mathlib

/-!
# Connected algebras and their idempotents

An algebra is *connected* if its only central idempotents are `0` and `1`. For a complete set of
nonzero orthogonal idempotents `f_i` of a connected ring, any two indices are joined by a chain
of nonzero corners `f_i A f_j` (`eqvGen_corner`): otherwise the sum of the `f_l` over the
component of an index is a central idempotent other than `0` and `1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

/-- **A connected ring**: the only central idempotents are `0` and `1`. -/
def IsConnectedRing (A : Type*) [Ring A] : Prop :=
  ∀ e : A, IsIdempotentElem e → (∀ a, e * a = a * e) → e = 0 ∨ e = 1

variable {A : Type*} [Ring A]

theorem eqvGen_corner (hconn : IsConnectedRing A) {n : ℕ} {f : Fin n → A}
    (hf : CompleteOrthogonalIdempotents f) (hne : ∀ i, f i ≠ 0) (i j : Fin n) :
    Relation.EqvGen (fun i j ↦ ∃ a, f i * a * f j ≠ 0) i j := by
  classical
  by_contra hij
  set R : Fin n → Fin n → Prop := fun i j ↦ ∃ a, f i * a * f j ≠ 0
  set U : Finset (Fin n) := univ.filter fun l ↦ Relation.EqvGen R i l
  have hiU : i ∈ U := mem_filter.2 ⟨mem_univ _, Relation.EqvGen.refl _⟩
  have hjU : j ∉ U := fun h ↦ hij (mem_filter.1 h).2
  have hcut : ∀ l m, l ∈ U → m ∉ U → ∀ a, f l * a * f m = 0 ∧ f m * a * f l = 0 := by
    intro l m hl hm a
    have hl' := (mem_filter.1 hl).2
    refine ⟨?_, ?_⟩ <;> by_contra h <;> apply hm <;> refine mem_filter.2 ⟨mem_univ _, ?_⟩
    · exact Relation.EqvGen.trans _ _ _ hl' (Relation.EqvGen.rel _ _ ⟨a, h⟩)
    · exact Relation.EqvGen.trans _ _ _ hl' (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨a, h⟩))
  set e := ∑ l ∈ U, f l
  have hmul : ∀ l m, f l * f m = if l = m then f l else 0 := fun l m ↦ by
    split_ifs with h
    · subst h; exact (hf.idem l).eq
    · exact hf.ortho h
  have hfe : ∀ m, f m * e = if m ∈ U then f m else 0 := fun m ↦ by
    rw [mul_sum]; simp_rw [hmul]; rw [sum_ite_eq]
  have hleft : ∀ l a, f l * a = ∑ m, f l * a * f m := fun l a ↦ by
    rw [← mul_sum, hf.complete, mul_one]
  have hright : ∀ m a, a * f m = ∑ l, f l * a * f m := fun m a ↦ by
    rw [← sum_mul, ← sum_mul, hf.complete, one_mul]
  have hsplit : ∀ (g : Fin n → A), (∀ m, m ∉ U → g m = 0) → ∑ m, g m = ∑ m ∈ U, g m := by
    intro g hg
    rw [← sum_filter_add_sum_filter_not univ (· ∈ U)]
    rw [sum_eq_zero (s := univ.filter fun m ↦ m ∉ U) fun m hm ↦ hg m (mem_filter.1 hm).2,
      add_zero]
    congr 1; ext m; simp [U]
  have hcentral : ∀ a, e * a = a * e := by
    intro a
    have h1 : e * a = ∑ l ∈ U, ∑ m ∈ U, f l * a * f m := by
      rw [sum_mul]
      refine sum_congr rfl fun l hl ↦ ?_
      conv_lhs => rw [hleft l a]
      rw [hsplit _ fun m hm ↦ (hcut l m hl hm a).1]
    have h2 : a * e = ∑ m ∈ U, ∑ l ∈ U, f l * a * f m := by
      rw [mul_sum]
      refine sum_congr rfl fun m hm ↦ ?_
      conv_lhs => rw [hright m a]
      rw [hsplit _ fun l hl ↦ (hcut m l hm hl a).2]
    rw [h1, h2, sum_comm]
  have hidem : IsIdempotentElem e := by
    change e * e = e
    conv_lhs => rw [show e * e = ∑ l ∈ U, f l * e from sum_mul _ _ _]
    exact sum_congr rfl fun l hl ↦ by rw [hfe, if_pos hl]
  rcases hconn e hidem hcentral with h0 | h1
  · have := hfe i
    rw [if_pos hiU, h0, mul_zero] at this
    exact hne i this.symm
  · have := hfe j
    rw [if_neg hjU, h1, mul_one] at this
    exact hne j this

end MultiplicativeBasisDeformations
