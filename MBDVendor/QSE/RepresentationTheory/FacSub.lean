import Mathlib.CategoryTheory.FintypeCat
import MBDVendor.QSE.ConvexGeometry.Basic
import MBDVendor.QSE.RepresentationTheory.FiniteType

/-!
# Quotient and submodule generation on an indecomposable skeleton

This file defines membership in `add S`, `Fac(add S)`, and `Sub(add S)` by
explicit finite biproduct presentations.  The finite indexing type is
bundled so that iterated finite sums can be flattened without any
cardinality bookkeeping.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A finite direct sum indexed by a bundled finite type. -/
abbrev sumOver (J : FintypeCat.{0}) (a : J → ι) : FGModuleCat.{w} R :=
  biproduct fun t ↦ σ.obj (a t)

/-- A concrete presentation of `X` as an object of `add S`. -/
structure AddPresentation (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  iso : X ≅ σ.sumOver index label

/-- A concrete presentation of `X` as a quotient of an object of
`add S`. -/
structure FacPresentation (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : σ.sumOver index label ⟶ X
  epi : Epi map

/-- A concrete presentation of `X` as a submodule of an object of
`add S`. -/
structure SubPresentation (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : X ⟶ σ.sumOver index label
  mono : Mono map

/-- Membership in the additive closure of the selected representatives. -/
def InAdd (S : Set ι) (X : FGModuleCat.{w} R) : Prop :=
  Nonempty (σ.AddPresentation S X)

/-- Membership in the quotient closure `Fac(add S)`. -/
def InFac (S : Set ι) (X : FGModuleCat.{w} R) : Prop :=
  Nonempty (σ.FacPresentation S X)

/-- Membership in the submodule closure `Sub(add S)`. -/
def InSub (S : Set ι) (X : FGModuleCat.{w} R) : Prop :=
  Nonempty (σ.SubPresentation S X)

/-- Indecomposable representatives lying in `Fac(add S)`. -/
def qSet (S : Set ι) : Set ι :=
  {j | σ.InFac S (σ.obj j)}

/-- Indecomposable representatives lying in `Sub(add S)`. -/
def sSet (S : Set ι) : Set ι :=
  {j | σ.InSub S (σ.obj j)}

namespace FacPresentation

/-- Enlarging the selected set preserves a quotient presentation. -/
def of_subset {S T : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation S X) (hST : S ⊆ T) :
    σ.FacPresentation T X where
  index := P.index
  label := P.label
  mem t := hST (P.mem t)
  map := P.map
  epi := P.epi

end FacPresentation

namespace SubPresentation

/-- Enlarging the selected set preserves a submodule presentation. -/
def of_subset {S T : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.SubPresentation S X) (hST : S ⊆ T) :
    σ.SubPresentation T X where
  index := P.index
  label := P.label
  mem t := hST (P.mem t)
  map := P.map
  mono := P.mono

end SubPresentation

/-- Quotient generation is monotone in the selected representatives. -/
theorem qSet_monotone : Monotone σ.qSet := by
  intro S T hST j hj
  exact hj.map fun P ↦ FacPresentation.of_subset σ P hST

/-- Submodule generation is monotone in the selected representatives. -/
theorem sSet_monotone : Monotone σ.sSet := by
  intro S T hST j hj
  exact hj.map fun P ↦ SubPresentation.of_subset σ P hST

/-- Every selected representative lies in its quotient closure. -/
theorem subset_qSet (S : Set ι) : S ⊆ σ.qSet S := by
  intro j hj
  let a : Fin 1 → ι := fun _ ↦ j
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hj
    map := (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom
    epi := inferInstance }⟩

/-- Every selected representative lies in its submodule closure. -/
theorem subset_sSet (S : Set ι) : S ⊆ σ.sSet S := by
  intro j hj
  let a : Fin 1 → ι := fun _ ↦ j
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hj
    map := (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).inv
    mono := inferInstance }⟩

/-- An iterated quotient presentation can be flattened to one finite
direct sum. -/
theorem inFac_trans {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation (σ.qSet S) X) :
    σ.InFac S X := by
  classical
  let inner : ∀ t : P.index,
      σ.FacPresentation S (σ.obj (P.label t)) :=
    fun t ↦ Classical.choice (P.mem t)
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : P.index, (inner t).index)
  let a : J → ι :=
    fun p ↦ (inner p.1).label p.2
  let flattenIso :
      (⨁ fun t : P.index ↦
        σ.sumOver (inner t).index (inner t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : P.index ↦ (inner t).index)
      (fun t s ↦ σ.obj ((inner t).label s))
  let g :
      σ.sumOver J a ⟶ X :=
    flattenIso.inv ≫
      biproduct.map (fun t ↦ (inner t).map) ≫ P.map
  refine ⟨{
    index := J
    label := a
    mem := ?_
    map := g
    epi := ?_ }⟩
  · intro p
    exact (inner p.1).mem p.2
  · letI (t : P.index) : Epi (inner t).map :=
      (inner t).epi
    letI : Epi P.map := P.epi
    dsimp only [g]
    infer_instance

/-- An iterated submodule presentation can be flattened to one finite
direct sum. -/
theorem inSub_trans {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.SubPresentation (σ.sSet S) X) :
    σ.InSub S X := by
  classical
  let inner : ∀ t : P.index,
      σ.SubPresentation S (σ.obj (P.label t)) :=
    fun t ↦ Classical.choice (P.mem t)
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : P.index, (inner t).index)
  let a : J → ι :=
    fun p ↦ (inner p.1).label p.2
  let flattenIso :
      (⨁ fun t : P.index ↦
        σ.sumOver (inner t).index (inner t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : P.index ↦ (inner t).index)
      (fun t s ↦ σ.obj ((inner t).label s))
  let g :
      X ⟶ σ.sumOver J a :=
    P.map ≫
      biproduct.map (fun t ↦ (inner t).map) ≫ flattenIso.hom
  refine ⟨{
    index := J
    label := a
    mem := ?_
    map := g
    mono := ?_ }⟩
  · intro p
    exact (inner p.1).mem p.2
  · letI (t : P.index) : Mono (inner t).map :=
      (inner t).mono
    letI : Mono P.map := P.mono
    dsimp only [g]
    infer_instance

/-- Quotient generation is idempotent. -/
theorem qSet_idempotent (S : Set ι) :
    σ.qSet (σ.qSet S) = σ.qSet S := by
  apply Set.Subset.antisymm
  · intro j hj
    exact inFac_trans σ (Classical.choice hj)
  · exact qSet_monotone σ (subset_qSet σ S)

/-- Submodule generation is idempotent. -/
theorem sSet_idempotent (S : Set ι) :
    σ.sSet (σ.sSet S) = σ.sSet S := by
  apply Set.Subset.antisymm
  · intro j hj
    exact inSub_trans σ (Classical.choice hj)
  · exact sSet_monotone σ (subset_sSet σ S)

/-- Quotient closure as a genuine closure operator on the representative
type. -/
def qClosure : SetClosure ι where
  toFun := σ.qSet
  monotone' := qSet_monotone σ
  le_closure' := subset_qSet σ
  idempotent' := qSet_idempotent σ

/-- Submodule closure as a genuine closure operator on the representative
type. -/
def sClosure : SetClosure ι where
  toFun := σ.sSet
  monotone' := sSet_monotone σ
  le_closure' := subset_sSet σ
  idempotent' := sSet_idempotent σ

/-- Membership in quotient closure is witnessed by finitely many selected
representatives. -/
theorem qSet_finite_witness {S : Set ι} {j : ι}
    (hj : j ∈ σ.qSet S) :
    ∃ T : Set ι, T.Finite ∧ T ⊆ S ∧ j ∈ σ.qSet T := by
  obtain ⟨P⟩ := hj
  let T : Set ι := Set.range P.label
  refine ⟨T, Set.finite_range P.label, ?_, ?_⟩
  · rintro i ⟨t, rfl⟩
    exact P.mem t
  · exact ⟨{
      index := P.index
      label := P.label
      mem := fun t ↦ ⟨t, rfl⟩
      map := P.map
      epi := P.epi }⟩

/-- Membership in submodule closure is witnessed by finitely many selected
representatives. -/
theorem sSet_finite_witness {S : Set ι} {j : ι}
    (hj : j ∈ σ.sSet S) :
    ∃ T : Set ι, T.Finite ∧ T ⊆ S ∧ j ∈ σ.sSet T := by
  obtain ⟨P⟩ := hj
  let T : Set ι := Set.range P.label
  refine ⟨T, Set.finite_range P.label, ?_, ?_⟩
  · rintro i ⟨t, rfl⟩
    exact P.mem t
  · exact ⟨{
      index := P.index
      label := P.label
      mem := fun t ↦ ⟨t, rfl⟩
      map := P.map
      mono := P.mono }⟩

/-- Quotient closure is finitary. -/
theorem qClosure_isFinitary : σ.qClosure.IsFinitary := by
  intro S j hj
  exact qSet_finite_witness σ hj

/-- Submodule closure is finitary. -/
theorem sClosure_isFinitary : σ.sClosure.IsFinitary := by
  intro S j hj
  exact sSet_finite_witness σ hj

end MBDVendor.QSE.IndecomposableSkeleton
