module

public import MBDVendor.QSE.ConvexGeometry.Relabeling
public import MBDVendor.QSE.RepresentationTheory.AdditiveSubcategory
public import MBDVendor.QSE.RepresentationTheory.ContravariantTransport

/-!
# Closure and polynomial consequences of an aligned biduality
-/

@[expose] public section

noncomputable section

namespace MBDVendor.QSE.IndecomposableSkeleton.AlignedBiduality

universe uR uS vR vS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {ι : Type vR} {κ : Type vS}
  (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
  (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)
  (D : AlignedBiduality σ τ)

/-- Quotient closure on the source is relabeled submodule closure on the
target. -/
def qToSClosureRelabeling :
    SetClosure.RelabelingEquiv σ.qClosure τ.sClosure where
  equiv := D.forward.labelEquiv
  map_closure := image_qClosure_eq_sClosure σ τ D

/-- Submodule closure on the source is relabeled quotient closure on the
target. -/
def sToQClosureRelabeling :
    SetClosure.RelabelingEquiv σ.sClosure τ.qClosure where
  equiv := D.forward.labelEquiv
  map_closure := image_sClosure_eq_qClosure σ τ D

/-- A support is submodule-closed exactly when its dual image is
quotient-closed. -/
theorem sClosure_isClosed_iff_qClosure_image (T : Set ι) :
    σ.sClosure.IsClosed T ↔
      τ.qClosure.IsClosed (D.forward.labelEquiv '' T) := by
  constructor
  · intro hT
    apply τ.qClosure.isClosed_iff.2
    change τ.qClosure (D.forward.labelEquiv '' T) =
      D.forward.labelEquiv '' T
    rw [← image_sClosure_eq_qClosure σ τ D T,
      hT.closure_eq]
  · intro hT
    apply σ.sClosure.isClosed_iff.2
    apply D.forward.labelEquiv.injective.image_injective
    change D.forward.labelEquiv '' σ.sClosure T =
      D.forward.labelEquiv '' T
    rw [image_sClosure_eq_qClosure σ τ D T,
      hT.closure_eq]

/-- Duality gives the paper's order isomorphism from quotient-closed
supports to submodule-closed supports. -/
def quotientToSubmoduleClosedOrderIso :
    σ.qClosure.Closeds ≃o τ.sClosure.Closeds :=
  (qToSClosureRelabeling σ τ D).closedsOrderIso

/-- The paper-facing duality isomorphism from literal quotient-closed
additive subcategories to literal subobject-closed additive subcategories. -/
def quotientToSubobjectClosedAdditiveSubcategoryOrderIso :
    QuotientClosedAdditiveSubcategory.{uR, wR} (R := R) ≃o
      SubobjectClosedAdditiveSubcategory.{uS, wS} (R := S) :=
  σ.quotientClosedSupportOrderIso.trans <|
    (quotientToSubmoduleClosedOrderIso σ τ D).trans
      τ.subobjectClosedSupportOrderIso.symm

/-- Duality preserves the number of indecomposable isomorphism classes in
every literal quotient-closed subcategory. -/
@[simp]
theorem ncard_support_quotientToSubobjectClosedAdditiveSubcategoryOrderIso
    (C : QuotientClosedAdditiveSubcategory.{uR, wR} (R := R)) :
    (τ.support
        ((quotientToSubobjectClosedAdditiveSubcategoryOrderIso
          σ τ D C).1)).ncard =
      (σ.support C.1).ncard := by
  simp only [quotientToSubobjectClosedAdditiveSubcategoryOrderIso,
    OrderIso.trans_apply]
  change
    (((τ.subobjectClosedSupportOrderIso
        (τ.subobjectClosedSupportOrderIso.symm
          ((quotientToSubmoduleClosedOrderIso σ τ D)
            (σ.quotientClosedSupportOrderIso C)))) :
      τ.sClosure.Closeds) : Set κ).ncard =
      (σ.support C.1).ncard
  rw [τ.subobjectClosedSupportOrderIso.apply_symm_apply]
  exact
    SetClosure.RelabelingEquiv.ncard_closedsOrderIso_apply
      (qToSClosureRelabeling σ τ D)
      (σ.quotientClosedSupportOrderIso C)

/-- In finite type, duality identifies the quotient and submodule
level-generating polynomials. -/
theorem quotientToSubmoduleLevelPolynomial_eq
    (D : AlignedBiduality σ τ) [Finite ι] [Finite κ] :
    σ.qClosure.levelPolynomial = τ.sClosure.levelPolynomial :=
  SetClosure.RelabelingEquiv.levelPolynomial_eq
    (qToSClosureRelabeling σ τ D)

/-- The reverse exchange of level-generating polynomials. -/
theorem submoduleToQuotientLevelPolynomial_eq
    (D : AlignedBiduality σ τ) [Finite ι] [Finite κ] :
    σ.sClosure.levelPolynomial = τ.qClosure.levelPolynomial :=
  SetClosure.RelabelingEquiv.levelPolynomial_eq
    (sToQClosureRelabeling σ τ D)

end MBDVendor.QSE.IndecomposableSkeleton.AlignedBiduality
