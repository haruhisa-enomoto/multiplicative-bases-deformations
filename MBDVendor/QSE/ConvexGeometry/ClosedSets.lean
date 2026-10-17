import Mathlib.Order.Grade
import MBDVendor.QSE.ConvexGeometry.Finite

/-!
# The lattice of closed sets

Every closure system is a complete lattice.  For a finite anti-exchange
closure system, cardinality is a grading: every cover adds exactly one
point.
-/

open Set

namespace MBDVendor.QSE.SetClosure

variable {E : Type*}

/-- The complete lattice structure transported along the Galois insertion
from closed sets to all subsets. -/
noncomputable instance instCompleteLatticeCloseds (c : SetClosure E) :
    CompleteLattice c.Closeds :=
  c.gi.liftCompleteLattice

variable {c : SetClosure E}

/-- A point closure, regarded as an element of the closed-set lattice. -/
def pointClosure (c : SetClosure E) (x : E) : c.Closeds :=
  c.toCloseds ({x} : Set E)

@[simp]
theorem coe_pointClosure (c : SetClosure E) (x : E) :
    (c.pointClosure x : Set E) = c ({x} : Set E) :=
  rfl

@[simp]
theorem coe_bot (c : SetClosure E) :
    ((⊥ : c.Closeds) : Set E) = c ∅ :=
  rfl

@[simp]
theorem coe_top (c : SetClosure E) :
    ((⊤ : c.Closeds) : Set E) = Set.univ :=
  rfl

@[simp]
theorem coe_inf (C D : c.Closeds) :
    ((C ⊓ D : c.Closeds) : Set E) = (C : Set E) ∩ (D : Set E) :=
  rfl

@[simp]
theorem coe_sup (C D : c.Closeds) :
    ((C ⊔ D : c.Closeds) : Set E) = c ((C : Set E) ∪ (D : Set E)) :=
  rfl

@[simp]
theorem coe_iSup {ι : Sort*} (f : ι → c.Closeds) :
    ((⨆ i, f i : c.Closeds) : Set E) = c (⋃ i, (f i : Set E)) :=
  congrArg Subtype.val (c.gi.l_iSup_u f).symm

@[simp]
theorem coe_iInf {ι : Sort*} (f : ι → c.Closeds) :
    ((⨅ i, f i : c.Closeds) : Set E) = ⋂ i, (f i : Set E) :=
  c.gi.gc.u_iInf

@[simp]
theorem coe_sSup (S : Set c.Closeds) :
    ((sSup S : c.Closeds) : Set E) =
      c (⋃ C : S, (C.1 : Set E)) := by
  rw [sSup_eq_iSup' S, coe_iSup]

/-- A point closure lies below a closed set exactly when the point lies in
that set. -/
theorem pointClosure_le_iff {x : E} {C : c.Closeds} :
    c.pointClosure x ≤ C ↔ x ∈ (C : Set E) := by
  change c ({x} : Set E) ⊆ (C : Set E) ↔ _
  rw [C.2.closure_le_iff, singleton_subset_iff]

/-- Distinct ground points give distinct point closures, now as elements
of the closed-set lattice. -/
theorem pointClosure_injective_closeds
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    Function.Injective c.pointClosure := by
  intro x y hxy
  apply pointClosure_injective hae hempty
  exact congrArg Subtype.val hxy

/-- Every closed set is the supremum of the point closures of its
elements. -/
theorem iSup_pointClosure (C : c.Closeds) :
    (⨆ x : (C : Set E), c.pointClosure x.1) = C := by
  apply Subtype.ext
  rw [coe_iSup]
  have hunion :
      (⋃ x : (C : Set E), ({x.1} : Set E)) = (C : Set E) := by
    ext x
    simp
  change c (⨆ x : (C : Set E), c ({x.1} : Set E)) = (C : Set E)
  rw [c.closure_iSup_closure]
  change c (⋃ x : (C : Set E), ({x.1} : Set E)) = (C : Set E)
  rw [hunion, C.2.closure_eq]

/-- In a finite anti-exchange closure system, a cover of closed sets adds
one point. -/
theorem covBy_eq_insert [Finite E]
    (hae : c.IsAntiExchange) {C D : c.Closeds} (hCD : C ⋖ D) :
    ∃ x : E, x ∉ (C : Set E) ∧ (D : Set E) = insert x (C : Set E) := by
  have hlt := hCD.lt
  change (C : Set E) ⊂ (D : Set E) at hlt
  obtain ⟨x, hxDC, hdel, hCdel⟩ :=
    exists_closed_sdiff_singleton_between hae C.2 D.2 hlt
  let D' : c.Closeds := ⟨(D : Set E) \ {x}, hdel⟩
  have hCD' : C ≤ D' := hCdel
  have hD'D : D' ≤ D := sdiff_subset
  have hD'ne : D' ≠ D := by
    intro heq
    have hxD' : x ∈ (D' : Set E) := by
      rw [heq]
      exact hxDC.1
    exact hxD'.2 rfl
  have hD'eq : D' = C :=
    (hCD.eq_or_eq hCD' hD'D).resolve_right hD'ne
  have hdiff : (D : Set E) \ {x} = (C : Set E) :=
    congrArg Subtype.val hD'eq
  refine ⟨x, hxDC.2, ?_⟩
  calc
    (D : Set E) = insert x ((D : Set E) \ {x}) :=
      (insert_sdiff_self_of_mem hxDC.1).symm
    _ = insert x (C : Set E) := congrArg (insert x) hdiff

/-- Cardinality increases by one across every cover. -/
theorem ncard_add_one_eq_of_covBy [Finite E]
    (hae : c.IsAntiExchange) {C D : c.Closeds} (hCD : C ⋖ D) :
    (C : Set E).ncard + 1 = (D : Set E).ncard := by
  obtain ⟨x, hxC, hD⟩ := covBy_eq_insert hae hCD
  rw [hD]
  exact (ncard_insert_of_notMem hxC).symm

/-- Cardinality supplies the grading of the finite closed-set lattice. -/
@[reducible] noncomputable def gradeOrder [Finite E]
    (hae : c.IsAntiExchange) : GradeOrder ℕ c.Closeds where
  grade C := (C : Set E).ncard
  grade_strictMono := by
    intro C D hCD
    exact Set.ncard_strictMono hCD
  covBy_grade := by
    intro C D hCD
    rw [Nat.covBy_iff_add_one_eq]
    exact ncard_add_one_eq_of_covBy hae hCD

end MBDVendor.QSE.SetClosure
