import Mathlib.Data.Set.Card
import MBDVendor.QSE.ConvexGeometry.Basic

/-!
# Finite convex geometries

This file proves the finite extreme-point and unique-basis consequences of
anti-exchange used in the manuscript.
-/

open Set

namespace MBDVendor.QSE.SetClosure

variable {E : Type*} {c : SetClosure E}

/-- A generating set is inclusion-minimal when no one-point deletion still
generates the same closed set.  For closure operators this is equivalent
to ordinary inclusion-minimality. -/
def IsMinimalGenerator (c : SetClosure E) (B C : Set E) : Prop :=
  c B = C ∧ ∀ ⦃b : E⦄, b ∈ B → c (B \ {b}) ≠ C

/-- One-point deletion minimality is equivalent to ordinary
inclusion-minimality among generating sets. -/
theorem isMinimalGenerator_iff_no_proper_subset
    {B C : Set E} :
    c.IsMinimalGenerator B C ↔
      c B = C ∧ ∀ ⦃D : Set E⦄, D ⊂ B → c D ≠ C := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro D hDB hDC
    obtain ⟨b, hbB, hbD⟩ := Set.exists_of_ssubset hDB
    apply h.2 hbB
    apply Set.Subset.antisymm
    · calc
        c (B \ {b}) ⊆ c B := c.monotone sdiff_subset
        _ = C := h.1
    · calc
        C = c D := hDC.symm
        _ ⊆ c (B \ {b}) := c.monotone fun x hxD ↦
          ⟨hDB.subset hxD, fun hxb ↦ hbD (hxb ▸ hxD)⟩
  · rintro ⟨hBC, hminimal⟩
    refine ⟨hBC, ?_⟩
    intro b hbB
    apply hminimal
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have : b ∈ B \ {b} := heq.symm ▸ hbB
    exact this.2 rfl

/-- Anti-exchange can be iterated over a finite set: if all points of `Y`
are available after adding `b` to a closed set `K`, then adjoining all of
`Y` without `b` still cannot regenerate `b`. -/
theorem not_mem_closure_union_of_finite
    (hae : c.IsAntiExchange) {K Y : Set E} {b : E}
    (hK : c.IsClosed K) (hbK : b ∉ K) (hYfin : Y.Finite)
    (hY : Y ⊆ c (insert b K)) (hbY : b ∉ Y) :
    b ∉ c (K ∪ Y) := by
  induction Y, hYfin using Set.Finite.induction_on generalizing K with
  | empty =>
      simpa [hK.closure_eq] using hbK
  | @insert y Y hyY hYfin ih =>
      have hyb : y ≠ b := by
        intro hyb
        exact hbY (hyb ▸ mem_insert y Y)
      have hbY' : b ∉ Y := fun hb ↦ hbY (mem_insert_of_mem y hb)
      by_cases hyK : y ∈ K
      · have hnot := ih hK hbK
          (fun z hz ↦ hY (mem_insert_of_mem y hz)) hbY'
        rw [show K ∪ insert y Y = K ∪ Y by
          ext z
          simp only [mem_union, mem_insert_iff]
          constructor
          · rintro (hzK | rfl | hzY)
            · exact Or.inl hzK
            · exact Or.inl hyK
            · exact Or.inr hzY
          · rintro (hzK | hzY)
            · exact Or.inl hzK
            · exact Or.inr (Or.inr hzY)]
        exact hnot
      · let K' : Set E := c (insert y K)
        have hK' : c.IsClosed K' := c.isClosed_closure _
        have hyAvailable : y ∈ c (insert b K) := hY (mem_insert y Y)
        have hbK' : b ∉ K' :=
          hae hK hyK hbK hyb hyAvailable
        have hKK' : K ⊆ K' := by
          intro z hz
          exact c.le_closure (insert y K) (mem_insert_of_mem y hz)
        have hY' : Y ⊆ c (insert b K') := by
          intro z hz
          apply c.monotone _ (hY (mem_insert_of_mem y hz))
          exact Set.insert_subset_insert hKK'
        have hnot := ih hK' hbK' hY' hbY'
        intro hb
        apply hnot
        have heq : c (K' ∪ Y) = c (K ∪ insert y Y) := by
          dsimp [K']
          calc
            c (c (insert y K) ∪ Y) = c (insert y K ∪ Y) := by
              change c (c (insert y K) ⊔ Y) = c (insert y K ⊔ Y)
              exact c.closure_sup_closure_left _ _
            _ = c (K ∪ insert y Y) := by
              congr 1
              ext z
              simp [or_left_comm, or_comm]
        exact heq.symm ▸ hb

/-- Every closed set on a finite ground type has an inclusion-minimal
generating set. -/
theorem exists_isMinimalGenerator [Finite E]
    {C : Set E} (hC : c.IsClosed C) :
    ∃ B : Set E, c.IsMinimalGenerator B C := by
  let P : Set (Set E) := {B | c B = C}
  have hPfin : P.Finite := Set.toFinite P
  have hPnonempty : P.Nonempty := ⟨C, hC.closure_eq⟩
  obtain ⟨B, hBmin⟩ := hPfin.exists_minimal hPnonempty
  refine ⟨B, hBmin.prop, ?_⟩
  intro b hb hdel
  have hproper : B \ {b} ⊂ B := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have : b ∈ B \ {b} := heq.symm ▸ hb
    exact this.2 rfl
  exact hBmin.not_prop_of_ssubset hproper hdel

/-- A one-point-minimal generator is the set of extreme points.  This is
the finite anti-exchange core of uniqueness of minimal generators. -/
theorem minimalGenerator_eq_extremePoints [Finite E]
    (hae : c.IsAntiExchange) {B C : Set E}
    (hC : c.IsClosed C) (hB : c.IsMinimalGenerator B C) :
    B = c.extremePoints C := by
  apply Set.Subset.antisymm
  · intro b hbB
    rw [mem_extremePoints]
    have hbC : b ∈ C := hB.1 ▸ c.le_closure B hbB
    refine ⟨hbC, ?_⟩
    have hbK : b ∉ c (B \ {b}) := by
      intro hb
      apply hB.2 hbB
      apply Set.Subset.antisymm
      · exact c.closure_min
          (fun z hz ↦ hB.1 ▸ c.le_closure B (sdiff_subset hz)) hC
      · intro z hzC
        have hzClosureB : z ∈ c B := hB.1.symm ▸ hzC
        have hBsub : B ⊆ c (B \ {b}) := by
          intro w hwB
          by_cases hwb : w = b
          · subst w
            exact hb
          · exact c.le_closure (B \ {b}) ⟨hwB, by simpa using hwb⟩
        have hz := c.monotone hBsub hzClosureB
        simpa using hz
    let K : Set E := c (B \ {b})
    have hK : c.IsClosed K := c.isClosed_closure _
    have hBinsert : B ⊆ insert b K := by
      intro z hzB
      by_cases hzb : z = b
      · simp [hzb]
      · exact mem_insert_of_mem b
          (c.le_closure (B \ {b}) ⟨hzB, by simpa using hzb⟩)
    have hCavailable : C ⊆ c (insert b K) := by
      intro z hzC
      exact c.monotone hBinsert (hB.1.symm ▸ hzC)
    have hYfin : (C \ {b}).Finite := Set.toFinite _
    have hnot : b ∉ c (K ∪ (C \ {b})) :=
      not_mem_closure_union_of_finite hae hK hbK hYfin
        (fun z hz ↦ hCavailable hz.1) (by simp)
    intro hb
    exact hnot (c.monotone (subset_union_right) hb)
  · exact extremePoints_subset_of_closure_eq hB.1

/-- The extreme points form the unique minimal generating set of a closed
set in a finite anti-exchange closure system. -/
theorem closure_extremePoints [Finite E]
    (hae : c.IsAntiExchange) {C : Set E} (hC : c.IsClosed C) :
    c (c.extremePoints C) = C := by
  obtain ⟨B, hB⟩ := exists_isMinimalGenerator hC
  rw [← minimalGenerator_eq_extremePoints hae hC hB]
  exact hB.1

/-- Every nonempty closed set in a finite convex geometry has an extreme
point. -/
theorem extremePoints_nonempty [Finite E]
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅)
    {C : Set E} (hC : c.IsClosed C) (hCne : C.Nonempty) :
    (c.extremePoints C).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have : C = ∅ := by
    rw [← closure_extremePoints hae hC, h, hempty.closure_eq]
  exact hCne.ne_empty this

/-- A proper inclusion of finite closed sets admits a legal one-point
deletion of the upper set which stays above the lower set. -/
theorem exists_extreme_not_mem_of_ssubset [Finite E]
    (hae : c.IsAntiExchange) {C D : Set E}
    (hC : c.IsClosed C) (hD : c.IsClosed D) (hCD : C ⊂ D) :
    ∃ x ∈ c.extremePoints D, x ∉ C := by
  by_contra h
  push Not at h
  have hextreme : c.extremePoints D ⊆ C := fun x hx ↦ h x hx
  have hDC : D ⊆ C := by
    intro x hxD
    have hxClosure : x ∈ c (c.extremePoints D) := by
      rw [closure_extremePoints hae hD]
      exact hxD
    have hx := c.monotone hextreme hxClosure
    simpa [hC.closure_eq] using hx
  exact hCD.not_subset hDC

/-- Accessibility in interval form: a proper inclusion of finite closed
sets can be shortened by deleting one extreme point from the upper set. -/
theorem exists_closed_sdiff_singleton_between [Finite E]
    (hae : c.IsAntiExchange) {C D : Set E}
    (hC : c.IsClosed C) (hD : c.IsClosed D) (hCD : C ⊂ D) :
    ∃ x : E, x ∈ D \ C ∧ c.IsClosed (D \ {x}) ∧ C ⊆ D \ {x} := by
  obtain ⟨x, hxextreme, hxC⟩ :=
    exists_extreme_not_mem_of_ssubset hae hC hD hCD
  refine ⟨x, ⟨hxextreme.1, hxC⟩,
    (mem_extremePoints_iff_isClosed_sdiff_singleton hD hxextreme.1).1 hxextreme, ?_⟩
  intro y hyC
  exact ⟨hCD.subset hyC, by
    simpa [Set.mem_singleton_iff] using fun hyx : y = x ↦ hxC (hyx ▸ hyC)⟩

end MBDVendor.QSE.SetClosure
