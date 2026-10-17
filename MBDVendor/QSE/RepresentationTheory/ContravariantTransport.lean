import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import MBDVendor.QSE.RepresentationTheory.FacSub

/-!
# Quotient/submodule exchange under an anti-equivalence

This is the abstract categorical interface expected from finite-dimensional
`k`-linear duality.  It deliberately does not construct that concrete duality.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

universe uR uS vR vS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {ι : Type vR} {κ : Type vS}
  (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
  (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- An anti-equivalence of module categories aligned with two chosen
indecomposable skeletons. -/
structure AlignedAntiEquivalence where
  categoryEquiv :
    (FGModuleCat.{wR} R)ᵒᵖ ≌ FGModuleCat.{wS} S
  labelEquiv : ι ≃ κ
  objIso :
    ∀ i, categoryEquiv.functor.obj (Opposite.op (σ.obj i)) ≅
      τ.obj (labelEquiv i)

namespace AlignedAntiEquivalence

variable (D : AlignedAntiEquivalence σ τ)

/-- An aligned anti-equivalence identifies injective source labels with
projective target labels. -/
theorem injective_iff_projective_image (i : ι) :
    Injective (σ.obj i) ↔ Projective (τ.obj (D.labelEquiv i)) := by
  constructor
  · intro hi
    have hop : Projective (Opposite.op (σ.obj i)) :=
      Injective.injective_iff_projective_op.mp hi
    have hmap : Projective
        (D.categoryEquiv.functor.obj (Opposite.op (σ.obj i))) :=
      (D.categoryEquiv.map_projective_iff
        (Opposite.op (σ.obj i))).2 hop
    exact Projective.of_iso (D.objIso i) hmap
  · intro hi
    have hmap : Projective
        (D.categoryEquiv.functor.obj (Opposite.op (σ.obj i))) :=
      Projective.of_iso (D.objIso i).symm hi
    have hop : Projective (Opposite.op (σ.obj i)) :=
      (D.categoryEquiv.map_projective_iff
        (Opposite.op (σ.obj i))).1 hmap
    exact Injective.injective_iff_projective_op.mpr hop

/-- An anti-equivalence sends a displayed finite direct sum to the
displayed sum of the dual representatives.

The route is: biproduct as coproduct, opposite coproduct as product,
preservation of products by the equivalence, then product as biproduct. -/
def sumIso (J : FintypeCat.{0}) (a : J → ι) :
    D.categoryEquiv.functor.obj
        (Opposite.op (σ.sumOver J a)) ≅
      τ.sumOver J (fun j ↦ D.labelEquiv (a j)) :=
  D.categoryEquiv.functor.mapIso
      ((biproduct.isoCoproduct
        (fun j : J ↦ σ.obj (a j))).op.symm ≪≫
        opCoproductIsoProduct (fun j : J ↦ σ.obj (a j))) ≪≫
    PreservesProduct.iso D.categoryEquiv.functor
      (fun j : J ↦ Opposite.op (σ.obj (a j))) ≪≫
    (biproduct.isoProduct
      (fun j : J ↦
        D.categoryEquiv.functor.obj
          (Opposite.op (σ.obj (a j))))).symm ≪≫
    biproduct.mapIso (fun j ↦ D.objIso (a j))

/-- A quotient presentation dualizes to a submodule presentation. -/
def facToSubObj {T : Set ι} {i : ι}
    (P : σ.FacPresentation T (σ.obj i)) :
    τ.SubPresentation (D.labelEquiv '' T)
      (τ.obj (D.labelEquiv i)) where
  index := P.index
  label := fun t ↦ D.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (D.objIso i).inv ≫
      D.categoryEquiv.functor.map P.map.op ≫
      (sumIso σ τ D P.index P.label).hom
  mono := by
    letI : Epi P.map := P.epi
    infer_instance

/-- A submodule presentation dualizes to a quotient presentation. -/
def subToFacObj {T : Set ι} {i : ι}
    (P : σ.SubPresentation T (σ.obj i)) :
    τ.FacPresentation (D.labelEquiv '' T)
      (τ.obj (D.labelEquiv i)) where
  index := P.index
  label := fun t ↦ D.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (sumIso σ τ D P.index P.label).inv ≫
      D.categoryEquiv.functor.map P.map.op ≫
      (D.objIso i).hom
  epi := by
    letI : Mono P.map := P.mono
    infer_instance

/-- The forward half of `qClosure ↔ sClosure` under duality. -/
theorem mem_sSet_image_of_mem_qSet {T : Set ι} {i : ι}
    (hi : i ∈ σ.qSet T) :
    D.labelEquiv i ∈ τ.sSet (D.labelEquiv '' T) :=
  hi.map (facToSubObj σ τ D ·)

/-- The forward half of `sClosure ↔ qClosure` under duality. -/
theorem mem_qSet_image_of_mem_sSet {T : Set ι} {i : ι}
    (hi : i ∈ σ.sSet T) :
    D.labelEquiv i ∈ τ.qSet (D.labelEquiv '' T) :=
  hi.map (subToFacObj σ τ D ·)

end AlignedAntiEquivalence

/-- Forward and backward aligned anti-equivalences with inverse actions on
the chosen skeleton labels.  Finite-dimensional vector-space duality is
expected to instantiate this using biduality. -/
structure AlignedBiduality where
  forward : AlignedAntiEquivalence σ τ
  backward : AlignedAntiEquivalence τ σ
  backward_label :
    backward.labelEquiv = forward.labelEquiv.symm

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

/-- Under a biduality, quotient generation on the source is equivalent to
submodule generation on the target. -/
theorem mem_sSet_image_iff_mem_qSet {T : Set ι} {i : ι} :
    D.forward.labelEquiv i ∈
        τ.sSet (D.forward.labelEquiv '' T) ↔
      i ∈ σ.qSet T := by
  constructor
  · intro hi
    have hback :=
      AlignedAntiEquivalence.mem_qSet_image_of_mem_sSet
        τ σ D.backward hi
    rw [D.backward_label] at hback
    simpa only [Equiv.symm_apply_apply,
      Equiv.symm_image_image] using hback
  · exact
      AlignedAntiEquivalence.mem_sSet_image_of_mem_qSet
        σ τ D.forward

/-- Under a biduality, submodule generation on the source is equivalent to
quotient generation on the target. -/
theorem mem_qSet_image_iff_mem_sSet {T : Set ι} {i : ι} :
    D.forward.labelEquiv i ∈
        τ.qSet (D.forward.labelEquiv '' T) ↔
      i ∈ σ.sSet T := by
  constructor
  · intro hi
    have hback :=
      AlignedAntiEquivalence.mem_sSet_image_of_mem_qSet
        τ σ D.backward hi
    rw [D.backward_label] at hback
    simpa only [Equiv.symm_apply_apply,
      Equiv.symm_image_image] using hback
  · exact
      AlignedAntiEquivalence.mem_qSet_image_of_mem_sSet
        σ τ D.forward

/-- Duality conjugates quotient closure to submodule closure. -/
theorem image_qClosure_eq_sClosure (T : Set ι) :
    D.forward.labelEquiv '' σ.qClosure T =
      τ.sClosure (D.forward.labelEquiv '' T) := by
  change D.forward.labelEquiv '' σ.qSet T =
    τ.sSet (D.forward.labelEquiv '' T)
  ext j
  rw [Set.mem_image_equiv]
  simpa using
    (mem_sSet_image_iff_mem_qSet σ τ D
      (T := T) (i := D.forward.labelEquiv.symm j)).symm

/-- Duality conjugates submodule closure to quotient closure. -/
theorem image_sClosure_eq_qClosure (T : Set ι) :
    D.forward.labelEquiv '' σ.sClosure T =
      τ.qClosure (D.forward.labelEquiv '' T) := by
  change D.forward.labelEquiv '' σ.sSet T =
    τ.qSet (D.forward.labelEquiv '' T)
  ext j
  rw [Set.mem_image_equiv]
  simpa using
    (mem_qSet_image_iff_mem_sSet σ τ D
      (T := T) (i := D.forward.labelEquiv.symm j)).symm

end AlignedBiduality

end MBDVendor.QSE.IndecomposableSkeleton
