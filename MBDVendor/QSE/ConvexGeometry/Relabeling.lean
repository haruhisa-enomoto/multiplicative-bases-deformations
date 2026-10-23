module

public import Mathlib.Logic.Equiv.Fintype
public import MBDVendor.QSE.ConvexGeometry.LevelPolynomial

/-!
# Relabeling a closure system

This is the closure-theoretic target of either a Morita equivalence or
finite-dimensional vector-space duality.  The categorical work only has to
produce `map_closure`; all lattice and level-polynomial consequences are then
formal.
-/

@[expose] public section

noncomputable section

open Polynomial Set

namespace MBDVendor.QSE.SetClosure

universe u v

variable {E : Type u} {F : Type v}
  {c : SetClosure E} {d : SetClosure F}

/-- Transport a closure operator across an equivalence of its ground type. -/
def transport (c : SetClosure E) (e : E ≃ F) : SetClosure F where
  toFun S := e '' c (e.symm '' S)
  monotone' := by
    intro S T hST
    exact Set.image_mono <| c.monotone <| Set.image_mono hST
  le_closure' := by
    intro S x hx
    refine ⟨e.symm x, c.le_closure (e.symm '' S) ?_, e.apply_symm_apply x⟩
    exact ⟨x, hx, rfl⟩
  idempotent' := by
    intro S
    rw [e.symm_image_image]
    exact congrArg (fun T : Set E ↦ e '' T) (c.idempotent _)

@[simp]
theorem transport_refl (c : SetClosure E) :
    transport c (Equiv.refl E) = c := by
  apply ClosureOperator.ext
  intro S
  ext x
  change x ∈ (Equiv.refl E) '' c ((Equiv.refl E).symm '' S) ↔ x ∈ c S
  simp

/-- An equivalence of ground labels which conjugates two closure operators. -/
structure RelabelingEquiv (c : SetClosure E) (d : SetClosure F) where
  equiv : E ≃ F
  map_closure : ∀ S : Set E, equiv '' c S = d (equiv '' S)

/-- The canonical relabeling from a closure operator to its transport. -/
def transportRelabeling (c : SetClosure E) (e : E ≃ F) :
    RelabelingEquiv c (transport c e) where
  equiv := e
  map_closure S := by
    change e '' c S = e '' c (e.symm '' (e '' S))
    rw [e.symm_image_image]

namespace RelabelingEquiv

variable (h : RelabelingEquiv c d)

/-- A closed set remains closed after relabeling. -/
def mapClosed (C : c.Closeds) : d.Closeds :=
  ⟨h.equiv '' (C : Set E), by
    apply d.isClosed_iff.2
    calc
      d (h.equiv '' (C : Set E)) =
          h.equiv '' c (C : Set E) := (h.map_closure _).symm
      _ = h.equiv '' (C : Set E) :=
        congrArg (fun S : Set E ↦ h.equiv '' S) C.2.closure_eq⟩

/-- A closed set can be pulled back along the relabeling. -/
def invClosed (D : d.Closeds) : c.Closeds :=
  ⟨h.equiv.symm '' (D : Set F), by
    apply c.isClosed_iff.2
    apply h.equiv.injective.image_injective
    calc
      h.equiv '' c (h.equiv.symm '' (D : Set F)) =
          d (h.equiv '' (h.equiv.symm '' (D : Set F))) :=
        h.map_closure _
      _ = d (D : Set F) := by rw [h.equiv.image_symm_image]
      _ = (D : Set F) := D.2.closure_eq
      _ = h.equiv '' (h.equiv.symm '' (D : Set F)) :=
        (h.equiv.image_symm_image _).symm⟩

/-- Conjugate closure systems have order-isomorphic lattices of closed sets. -/
def closedsOrderIso : c.Closeds ≃o d.Closeds where
  toFun := h.mapClosed
  invFun := h.invClosed
  left_inv C := by
    apply Subtype.ext
    exact h.equiv.symm_image_image (C : Set E)
  right_inv D := by
    apply Subtype.ext
    exact h.equiv.image_symm_image (D : Set F)
  map_rel_iff' := Set.image_subset_image_iff h.equiv.injective

@[simp]
theorem coe_closedsOrderIso_apply (C : c.Closeds) :
    ((h.closedsOrderIso C : d.Closeds) : Set F) =
      h.equiv '' (C : Set E) :=
  rfl

/-- Relabeling preserves the cardinality of every closed set. -/
@[simp]
theorem ncard_closedsOrderIso_apply (C : c.Closeds) :
    ((h.closedsOrderIso C : d.Closeds) : Set F).ncard =
      (C : Set E).ncard :=
  Set.ncard_image_of_injective _ h.equiv.injective

/-- Relabeling preserves the level-generating polynomial. -/
theorem levelPolynomial_eq (h : RelabelingEquiv c d)
    [Finite E] [Finite F] :
    c.levelPolynomial = d.levelPolynomial := by
  classical
  letI := Fintype.ofFinite c.Closeds
  letI := Fintype.ofFinite d.Closeds
  unfold levelPolynomial
  apply Fintype.sum_equiv (closedsOrderIso h).toEquiv
  intro C
  change X ^ (C : Set E).ncard =
    X ^ ((((closedsOrderIso h) C : d.Closeds) : Set F).ncard)
  rw [ncard_closedsOrderIso_apply h]

end RelabelingEquiv

end MBDVendor.QSE.SetClosure
