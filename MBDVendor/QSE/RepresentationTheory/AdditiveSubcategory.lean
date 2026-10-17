import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Retract
import MBDVendor.QSE.RepresentationTheory.SplitInjective

/-!
# Additive subcategories and indecomposable support

The adapter needed by the paper: a full, replete
subcategory of finitely generated modules which is closed under finite direct
sums and direct summands is completely determined by its indecomposable
support.

No Krull--Schmidt multiplicity-uniqueness theorem is used.  The only uniqueness
input is the existing radical argument
`IndecomposableSkeleton.not_splitMono_of_labels_ne`.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A literal full additive, replete, summand-closed subcategory, represented
by its object predicate.  Fullness is supplied by `carrier.FullSubcategory`;
finite-biproduct closure includes the empty biproduct, and retract closure
implies repleteness. -/
structure AdditiveRepleteSummandSubcategory where
  carrier : ObjectProperty (FGModuleCat.{w} R)
  biproduct_mem :
    ∀ (J : FintypeCat.{0}) (F : J → FGModuleCat.{w} R),
      (∀ j, carrier (F j)) → carrier (biproduct F)
  retract_mem :
    ∀ {X Y : FGModuleCat.{w} R}, Retract X Y → carrier Y → carrier X

namespace AdditiveRepleteSummandSubcategory

variable {σ}

/-- The corresponding literal full subcategory. -/
abbrev FullSubcategory
    (C : AdditiveRepleteSummandSubcategory (R := R)) :=
  C.carrier.FullSubcategory

omit [IsNoetherianRing R] in
/-- Retract closure entails closure under isomorphisms. -/
theorem iso_mem (C : AdditiveRepleteSummandSubcategory (R := R))
    {X Y : FGModuleCat.{w} R} (e : X ≅ Y) (hX : C.carrier X) :
    C.carrier Y :=
  C.retract_mem (Retract.ofIso e.symm) hX

omit [IsNoetherianRing R] in
@[ext]
theorem ext {C D : AdditiveRepleteSummandSubcategory (R := R)}
    (h : ∀ X, C.carrier X ↔ D.carrier X) :
    C = D := by
  cases C with
  | mk C hCb hCr =>
    cases D with
    | mk D hDb hDr =>
      have hCD : C = D := by
        funext X
        exact propext (h X)
      subst hCD
      rfl

instance : LE (AdditiveRepleteSummandSubcategory (R := R)) where
  le C D := C.carrier ≤ D.carrier

instance : PartialOrder (AdditiveRepleteSummandSubcategory (R := R)) where
  le_refl C := fun _ h ↦ h
  le_trans C D E hCD hDE := fun X hX ↦ hDE X (hCD X hX)
  le_antisymm C D hCD hDC :=
    ext fun X ↦ ⟨hCD X, hDC X⟩

end AdditiveRepleteSummandSubcategory

namespace AddPresentation

/-- Enlarging the support preserves an additive presentation. -/
def of_subset {S T : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.AddPresentation S X) (hST : S ⊆ T) :
    σ.AddPresentation T X where
  index := P.index
  label := P.label
  mem t := hST (P.mem t)
  iso := P.iso

end AddPresentation

/-- Additive closure is monotone in the support. -/
theorem inAdd_mono {S T : Set ι} (hST : S ⊆ T)
    {X : FGModuleCat.{w} R} :
    σ.InAdd S X → σ.InAdd T X :=
  Nonempty.map fun P ↦ AddPresentation.of_subset σ P hST

/-- `InAdd` is replete. -/
theorem inAdd_iff_of_iso {S : Set ι} {X Y : FGModuleCat.{w} R}
    (e : X ≅ Y) :
    σ.InAdd S X ↔ σ.InAdd S Y := by
  constructor
  · exact Nonempty.map fun P ↦
      { index := P.index
        label := P.label
        mem := P.mem
        iso := e.symm ≪≫ P.iso }
  · exact Nonempty.map fun P ↦
      { index := P.index
        label := P.label
        mem := P.mem
        iso := e ≪≫ P.iso }

/-- A finite biproduct of objects in `InAdd S` again lies in `InAdd S`. -/
theorem inAdd_biproduct {S : Set ι}
    (J : FintypeCat.{0}) (F : J → FGModuleCat.{w} R)
    (hF : ∀ j, σ.InAdd S (F j)) :
    σ.InAdd S (biproduct F) := by
  classical
  let inner : ∀ j : J, σ.AddPresentation S (F j) :=
    fun j ↦ Classical.choice (hF j)
  let K : FintypeCat.{0} :=
    FintypeCat.of (Σ j : J, (inner j).index)
  let a : K → ι :=
    fun p ↦ (inner p.1).label p.2
  let componentIso :
      (⨁ F) ≅
        (⨁ fun j : J ↦
          σ.sumOver (inner j).index (inner j).label) :=
    biproduct.mapIso fun j ↦ (inner j).iso
  let flattenIso :
      (⨁ fun j : J ↦
        σ.sumOver (inner j).index (inner j).label) ≅
        σ.sumOver K a :=
    biproductBiproductIso
      (fun j : J ↦ (inner j).index)
      (fun j t ↦ σ.obj ((inner j).label t))
  exact ⟨{
    index := K
    label := a
    mem := fun p ↦ (inner p.1).mem p.2
    iso := componentIso ≪≫ flattenIso }⟩

/-- Every selected representative belongs to its additive closure. -/
theorem inAdd_obj {S : Set ι} {i : ι} (hi : i ∈ S) :
    σ.InAdd S (σ.obj i) := by
  let a : Fin 1 → ι := fun _ ↦ i
  exact ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hi
    iso := (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).symm }⟩

/-- If an indecomposable representative is a retract of an object in
`add S`, its index already lies in `S`.

This is the precise substitute for a global Krull--Schmidt uniqueness API:
otherwise the split embedding into the displayed sum would have all its
components in the endomorphism radical. -/
theorem index_mem_of_retract_inAdd {S : Set ι} {i : ι}
    {Y : FGModuleCat.{w} R} (r : Retract (σ.obj i) Y)
    (hY : σ.InAdd S Y) :
    i ∈ S := by
  classical
  obtain ⟨P⟩ := hY
  let g : σ.obj i ⟶ σ.sumOver P.index P.label :=
    r.i ≫ P.iso.hom
  let s : SplitMono g :=
    { retraction := P.iso.inv ≫ r.r
      id := by
        dsimp only [g]
        simp }
  letI : IsSplitMono g := ⟨⟨s⟩⟩
  let Q : σ.SubPresentation S (σ.obj i) :=
    { index := P.index
      label := P.label
      mem := P.mem
      map := g
      mono := inferInstance }
  by_contra hi
  have hne : ∀ t, i ≠ Q.label t := by
    intro t hit
    apply hi
    simpa only [Q] using hit ▸ P.mem t
  exact (not_splitMono_of_labels_ne σ Q hne) ⟨s⟩

/-- `InAdd S` is closed under retracts (direct summands). -/
theorem inAdd_of_retract {S : Set ι} {X Y : FGModuleCat.{w} R}
    (r : Retract X Y) (hY : σ.InAdd S Y) :
    σ.InAdd S X := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  have ha : ∀ t : Fin n, a t ∈ S := by
    intro t
    let rt : Retract (σ.obj (a t)) X :=
      { i :=
          biproduct.ι
              (fun j : Fin n ↦ σ.obj (a j)) t ≫
            e.inv
        r :=
          e.hom ≫
            biproduct.π
              (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    exact index_mem_of_retract_inAdd σ (rt.trans r) hY
  exact ⟨{
    index := FintypeCat.of (Fin n)
    label := a
    mem := ha
    iso := e }⟩

/-- The literal additive/replete/summand-closed subcategory generated by a
set of indecomposable representatives. -/
def generated (S : Set ι) :
    AdditiveRepleteSummandSubcategory (R := R) where
  carrier := σ.InAdd S
  biproduct_mem := inAdd_biproduct σ
  retract_mem := inAdd_of_retract σ

/-- The indecomposable support of a literal additive subcategory. -/
def support (C : AdditiveRepleteSummandSubcategory (R := R)) : Set ι :=
  {i | C.carrier (σ.obj i)}

/-- Generating and then taking support returns the original set. -/
theorem support_generated (S : Set ι) :
    σ.support (σ.generated S) = S := by
  ext i
  constructor
  · intro hi
    exact index_mem_of_retract_inAdd σ (Retract.refl (σ.obj i)) hi
  · exact inAdd_obj σ

/-- Taking support and then additive closure returns the original literal
subcategory. -/
theorem generated_support
    (C : AdditiveRepleteSummandSubcategory (R := R)) :
    σ.generated (σ.support C) = C := by
  apply AdditiveRepleteSummandSubcategory.ext
  intro X
  constructor
  · rintro ⟨P⟩
    apply C.iso_mem P.iso.symm
    exact C.biproduct_mem P.index
      (fun t ↦ σ.obj (P.label t)) P.mem
  · intro hX
    obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
    refine ⟨{
      index := FintypeCat.of (Fin n)
      label := a
      mem := ?_
      iso := e }⟩
    intro t
    let rt : Retract (σ.obj (a t)) X :=
      { i :=
          biproduct.ι
              (fun j : Fin n ↦ σ.obj (a j)) t ≫
            e.inv
        r :=
          e.hom ≫
            biproduct.π
              (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    exact C.retract_mem rt hX

theorem generated_monotone : Monotone σ.generated := by
  intro S T hST X hX
  exact inAdd_mono σ hST hX

theorem support_monotone : Monotone σ.support := by
  intro C D hCD i hi
  exact hCD (σ.obj i) hi

/-- Order equivalence between indecomposable supports and literal full
additive, replete, summand-closed subcategories. -/
def supportOrderIso :
    AdditiveRepleteSummandSubcategory (R := R) ≃o Set ι where
  toFun := σ.support
  invFun := σ.generated
  left_inv := generated_support σ
  right_inv := support_generated σ
  map_rel_iff' := by
    intro C D
    constructor
    · intro h
      rw [← generated_support σ C, ← generated_support σ D]
      exact generated_monotone σ h
    · exact fun hCD ↦ support_monotone σ hCD

/-- Every object presented as a quotient of `add S` belongs to
`add (qSet S)`. -/
theorem inAdd_qSet_of_inFac {S : Set ι} {X : FGModuleCat.{w} R}
    (hX : σ.InFac S X) :
    σ.InAdd (σ.qSet S) X := by
  classical
  obtain ⟨P⟩ := hX
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  refine ⟨{
    index := FintypeCat.of (Fin n)
    label := a
    mem := ?_
    iso := e }⟩
  intro t
  let f : σ.sumOver P.index P.label ⟶ σ.obj (a t) :=
    P.map ≫ e.hom ≫
      biproduct.π (fun j : Fin n ↦ σ.obj (a j)) t
  letI : Epi P.map := P.epi
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := f
    epi := by
      dsimp only [f]
      infer_instance }⟩

/-- Every object presented as a subobject of `add S` belongs to
`add (sSet S)`. -/
theorem inAdd_sSet_of_inSub {S : Set ι} {X : FGModuleCat.{w} R}
    (hX : σ.InSub S X) :
    σ.InAdd (σ.sSet S) X := by
  classical
  obtain ⟨P⟩ := hX
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  refine ⟨{
    index := FintypeCat.of (Fin n)
    label := a
    mem := ?_
    iso := e }⟩
  intro t
  let f : σ.obj (a t) ⟶ σ.sumOver P.index P.label :=
    biproduct.ι (fun j : Fin n ↦ σ.obj (a j)) t ≫
      e.inv ≫ P.map
  letI : Mono P.map := P.mono
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := f
    mono := by
      dsimp only [f]
      infer_instance }⟩

/-- `q`-closed supports are exactly the supports whose literal additive
subcategory is closed under categorical quotients. -/
theorem qClosed_iff_generated_isClosedUnderQuotients (S : Set ι) :
    σ.qClosure.IsClosed S ↔
      (σ.generated S).carrier.IsClosedUnderQuotients := by
  constructor
  · intro hS
    have hq : σ.qSet S = S := hS.closure_eq
    refine ⟨?_⟩
    intro X Y f _ hX
    obtain ⟨P⟩ := hX
    letI : Epi f := inferInstance
    let Q : σ.FacPresentation S Y :=
      { index := P.index
        label := P.label
        mem := P.mem
        map := P.iso.inv ≫ f
        epi := inferInstance }
    have hY : σ.InAdd (σ.qSet S) Y :=
      inAdd_qSet_of_inFac σ ⟨Q⟩
    rwa [hq] at hY
  · intro hquot
    apply σ.qClosure.isClosed_iff.2
    change σ.qSet S = S
    apply Set.Subset.antisymm
    · intro i hi
      obtain ⟨P⟩ := hi
      letI : (σ.generated S).carrier.IsClosedUnderQuotients :=
        hquot
      letI : Epi P.map := P.epi
      have hsource :
          σ.InAdd S (σ.sumOver P.index P.label) :=
        ⟨{
          index := P.index
          label := P.label
          mem := P.mem
          iso := Iso.refl _ }⟩
      have hiadd : σ.InAdd S (σ.obj i) :=
        (σ.generated S).carrier.prop_of_epi P.map hsource
      exact index_mem_of_retract_inAdd σ
        (Retract.refl (σ.obj i)) hiadd
    · exact subset_qSet σ S

/-- `s`-closed supports are exactly the supports whose literal additive
subcategory is closed under categorical subobjects. -/
theorem sClosed_iff_generated_isClosedUnderSubobjects (S : Set ι) :
    σ.sClosure.IsClosed S ↔
      (σ.generated S).carrier.IsClosedUnderSubobjects := by
  constructor
  · intro hS
    have hs : σ.sSet S = S := hS.closure_eq
    refine ⟨?_⟩
    intro X Y f _ hY
    obtain ⟨P⟩ := hY
    letI : Mono f := inferInstance
    let Q : σ.SubPresentation S X :=
      { index := P.index
        label := P.label
        mem := P.mem
        map := f ≫ P.iso.hom
        mono := inferInstance }
    have hX : σ.InAdd (σ.sSet S) X :=
      inAdd_sSet_of_inSub σ ⟨Q⟩
    rwa [hs] at hX
  · intro hsub
    apply σ.sClosure.isClosed_iff.2
    change σ.sSet S = S
    apply Set.Subset.antisymm
    · intro i hi
      obtain ⟨P⟩ := hi
      letI : (σ.generated S).carrier.IsClosedUnderSubobjects :=
        hsub
      letI : Mono P.map := P.mono
      have htarget :
          σ.InAdd S (σ.sumOver P.index P.label) :=
        ⟨{
          index := P.index
          label := P.label
          mem := P.mem
          iso := Iso.refl _ }⟩
      have hiadd : σ.InAdd S (σ.obj i) :=
        (σ.generated S).carrier.prop_of_mono P.map htarget
      exact index_mem_of_retract_inAdd σ
        (Retract.refl (σ.obj i)) hiadd
    · exact subset_sSet σ S

/-- Literal additive subcategories which are also quotient-closed. -/
abbrev QuotientClosedAdditiveSubcategory :=
  {C : AdditiveRepleteSummandSubcategory (R := R) //
    C.carrier.IsClosedUnderQuotients}

/-- Literal additive subcategories which are also subobject-closed. -/
abbrev SubobjectClosedAdditiveSubcategory :=
  {C : AdditiveRepleteSummandSubcategory (R := R) //
    C.carrier.IsClosedUnderSubobjects}

/-- The exact order-level adapter for the paper's quotient-closed
subcategories. -/
def quotientClosedSupportOrderIso :
    QuotientClosedAdditiveSubcategory (R := R) ≃o
      σ.qClosure.Closeds where
  toFun C :=
    ⟨σ.support C.1, by
      apply (qClosed_iff_generated_isClosedUnderQuotients σ _).2
      rw [generated_support σ C.1]
      exact C.2⟩
  invFun S :=
    ⟨σ.generated S.1,
      (qClosed_iff_generated_isClosedUnderQuotients σ S.1).1 S.2⟩
  left_inv C := by
    apply Subtype.ext
    exact generated_support σ C.1
  right_inv S := by
    apply Subtype.ext
    exact support_generated σ S.1
  map_rel_iff' := by
    intro C D
    change σ.support C.1 ⊆ σ.support D.1 ↔ C.1 ≤ D.1
    constructor
    · intro h
      rw [← generated_support σ C.1, ← generated_support σ D.1]
      exact generated_monotone σ h
    · exact fun h ↦ support_monotone σ h

/-- The exact order-level adapter for the paper's subobject-closed
subcategories. -/
def subobjectClosedSupportOrderIso :
    SubobjectClosedAdditiveSubcategory (R := R) ≃o
      σ.sClosure.Closeds where
  toFun C :=
    ⟨σ.support C.1, by
      apply (sClosed_iff_generated_isClosedUnderSubobjects σ _).2
      rw [generated_support σ C.1]
      exact C.2⟩
  invFun S :=
    ⟨σ.generated S.1,
      (sClosed_iff_generated_isClosedUnderSubobjects σ S.1).1 S.2⟩
  left_inv C := by
    apply Subtype.ext
    exact generated_support σ C.1
  right_inv S := by
    apply Subtype.ext
    exact support_generated σ S.1
  map_rel_iff' := by
    intro C D
    change σ.support C.1 ⊆ σ.support D.1 ↔ C.1 ≤ D.1
    constructor
    · intro h
      rw [← generated_support σ C.1, ← generated_support σ D.1]
      exact generated_monotone σ h
    · exact fun h ↦ support_monotone σ h

end MBDVendor.QSE.IndecomposableSkeleton
