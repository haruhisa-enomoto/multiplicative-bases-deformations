module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import MBDVendor.QSE.RepresentationTheory.FacSub

/-!
# Trace and reject submodules

The quotient-side anti-exchange proof is organized around the trace of
`add S` in a target module.  We represent a map from `add S` by an explicit
finite direct-sum presentation.  This convention makes the equivalence
between trace generation and `Fac(add S)` literal rather than implicit.

The dual object is the intersection of the kernels of all maps into
explicit finite sums from `add S`.
-/

@[expose] public section

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A map to `X` from one explicitly presented object of `add S`. -/
structure SelectedMapTo (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : σ.sumOver index label ⟶ X

/-- A map from `X` to one explicitly presented object of `add S`. -/
structure SelectedMapFrom (S : Set ι) (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → ι
  mem : ∀ t, label t ∈ S
  map : X ⟶ σ.sumOver index label

/-- The trace of `add S` in `X`: the sum of the ranges of all maps from
explicit finite sums of selected representatives. -/
def trace (S : Set ι) (X : FGModuleCat.{w} R) : Submodule R X :=
  ⨆ f : σ.SelectedMapTo S X, LinearMap.range f.map.hom.hom

/-- The reject of `add S` in `X`: the intersection of the kernels of all
maps to explicit finite sums of selected representatives. -/
def reject (S : Set ι) (X : FGModuleCat.{w} R) : Submodule R X :=
  ⨅ f : σ.SelectedMapFrom S X, LinearMap.ker f.map.hom.hom

/-- If all maps from selected representatives to `X` vanish, their trace in
`X` is zero. -/
theorem trace_eq_bot_of_forall_hom_eq_zero
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hzero : ∀ i : ι, i ∈ S → ∀ f : σ.obj i ⟶ X, f = 0) :
    σ.trace S X = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro f
  have hmap : f.map = 0 := by
    apply biproduct.hom_ext'
    intro t
    simpa using hzero (f.label t) (f.mem t)
      (biproduct.ι (fun t : f.index ↦ σ.obj (f.label t)) t ≫ f.map)
  rw [hmap]
  simp

/-- Dually, if all maps from `X` to selected representatives vanish, their
reject in `X` is all of `X`. -/
theorem reject_eq_top_of_forall_hom_eq_zero
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hzero : ∀ i : ι, i ∈ S → ∀ f : X ⟶ σ.obj i, f = 0) :
    σ.reject S X = ⊤ := by
  apply top_unique
  apply le_iInf
  intro f
  have hmap : f.map = 0 := by
    apply biproduct.hom_ext
    intro t
    simpa using hzero (f.label t) (f.mem t)
      (f.map ≫ biproduct.π (fun t : f.index ↦ σ.obj (f.label t)) t)
  rw [hmap]
  simp

/-- The range of every selected map lies in the trace. -/
theorem range_le_trace {S : Set ι} {X : FGModuleCat.{w} R}
    (f : σ.SelectedMapTo S X) :
    LinearMap.range f.map.hom.hom ≤ σ.trace S X :=
  le_iSup (fun g : σ.SelectedMapTo S X ↦
    LinearMap.range g.map.hom.hom) f

/-- The reject lies in the kernel of every selected map. -/
theorem reject_le_ker {S : Set ι} {X : FGModuleCat.{w} R}
    (f : σ.SelectedMapFrom S X) :
    σ.reject S X ≤ LinearMap.ker f.map.hom.hom :=
  iInf_le (fun g : σ.SelectedMapFrom S X ↦
    LinearMap.ker g.map.hom.hom) f

/-- Trace is monotone in the selected representatives. -/
theorem trace_mono {S T : Set ι} (hST : S ⊆ T)
    (X : FGModuleCat.{w} R) :
    σ.trace S X ≤ σ.trace T X := by
  apply iSup_le
  intro f
  let g : σ.SelectedMapTo T X :=
    { index := f.index
      label := f.label
      mem := fun t ↦ hST (f.mem t)
      map := f.map }
  exact le_iSup_of_le g le_rfl

/-- Reject is antitone in the selected representatives. -/
theorem reject_anti {S T : Set ι} (hST : S ⊆ T)
    (X : FGModuleCat.{w} R) :
    σ.reject T X ≤ σ.reject S X := by
  apply le_iInf
  intro f
  let g : σ.SelectedMapFrom T X :=
    { index := f.index
      label := f.label
      mem := fun t ↦ hST (f.mem t)
      map := f.map }
  exact iInf_le_of_le g le_rfl

/-- The trace of the empty selection is zero.  A selected map with no
labels has an empty biproduct as its source and is therefore the zero map. -/
@[simp]
theorem trace_empty (X : FGModuleCat.{w} R) :
    σ.trace ∅ X = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro f
  have hzero : f.map = 0 := by
    apply biproduct.hom_ext'
    intro t
    exact False.elim (f.mem t)
  rw [hzero]
  simp

/-- The reject of the empty selection is the whole module.  Every map to
an empty biproduct is zero. -/
@[simp]
theorem reject_empty (X : FGModuleCat.{w} R) :
    σ.reject ∅ X = ⊤ := by
  apply top_unique
  apply le_iInf
  intro f
  have hzero : f.map = 0 := by
    apply biproduct.hom_ext
    intro t
    exact False.elim (f.mem t)
  rw [hzero]
  simp

/-- A finite family of selected maps can be flattened into one map from
an object explicitly presented in `add S`. -/
private def SelectedMapTo.flattenFinset
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapTo S X)) :
    σ.SelectedMapTo S X := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapTo S X :=
    fun t ↦ (F.equivFin.symm t).1
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : outer, (pick t).index)
  let a : J → ι :=
    fun p ↦ (pick p.1).label p.2
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  exact
    { index := J
      label := a
      mem := fun p ↦ (pick p.1).mem p.2
      map := flattenIso.inv ≫
        biproduct.desc (fun t ↦ (pick t).map) }

/-- Every member of a finite family factors through its flattened selected
map. -/
private theorem range_le_flattenFinset
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapTo S X))
    (f : σ.SelectedMapTo S X) (hf : f ∈ F) :
    LinearMap.range f.map.hom.hom ≤
      LinearMap.range
        (SelectedMapTo.flattenFinset σ F).map.hom.hom := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapTo S X :=
    fun t ↦ (F.equivFin.symm t).1
  let t : outer := F.equivFin ⟨f, hf⟩
  have hpick : pick t = f := by
    simp [pick, t]
  rw [← hpick]
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver
          (FintypeCat.of (Σ t : outer, (pick t).index))
          (fun p ↦ (pick p.1).label p.2) :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  let e :
      σ.sumOver (pick t).index (pick t).label ⟶
        σ.sumOver
          (SelectedMapTo.flattenFinset σ F).index
          (SelectedMapTo.flattenFinset σ F).label :=
    biproduct.ι (fun t : outer ↦
      σ.sumOver (pick t).index (pick t).label) t ≫
        flattenIso.hom
  have hfac :
      e ≫ (SelectedMapTo.flattenFinset σ F).map =
        (pick t).map := by
    dsimp only [e, SelectedMapTo.flattenFinset]
    change
      (biproduct.ι (fun t : outer ↦
          σ.sumOver (pick t).index (pick t).label) t ≫
        flattenIso.hom) ≫
          (flattenIso.inv ≫
            biproduct.desc (fun t ↦ (pick t).map)) =
        (pick t).map
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact biproduct.ι_desc _ _
  have hlinear := congrArg (fun q ↦ q.hom.hom) hfac
  simp only [FGModuleCat.hom_hom_comp] at hlinear
  rw [← hlinear]
  exact LinearMap.range_comp_le_range e.hom.hom
    (SelectedMapTo.flattenFinset σ F).map.hom.hom

/-- Quotient generation is equivalent to the trace filling the target
module. -/
theorem inFac_iff_trace_eq_top (S : Set ι)
    (X : FGModuleCat.{w} R) :
    σ.InFac S X ↔ σ.trace S X = ⊤ := by
  constructor
  · rintro ⟨P⟩
    let f : σ.SelectedMapTo S X :=
      { index := P.index
        label := P.label
        mem := P.mem
        map := P.map }
    letI : Epi P.map := P.epi
    letI : Epi P.map.hom := by
      change Epi
        ((forget₂ (FGModuleCat R) (ModuleCat R)).map P.map)
      infer_instance
    apply top_unique
    rw [← ModuleCat.range_eq_top_of_epi P.map.hom]
    exact le_iSup (fun g : σ.SelectedMapTo S X ↦
      LinearMap.range g.map.hom.hom) f
  · intro htrace
    have hcompact :
        IsCompactElement (⊤ : Submodule R X) := by
      obtain ⟨G, hG⟩ :=
        Module.Finite.fg_top (R := R) (M := X)
      rw [← hG]
      exact Submodule.finset_span_isCompactElement G
    have hle :
        (⊤ : Submodule R X) ≤
          ⨆ f : σ.SelectedMapTo S X,
            LinearMap.range f.map.hom.hom := by
      change (⊤ : Submodule R X) ≤ σ.trace S X
      exact htrace.ge
    obtain ⟨F, hF⟩ :=
      IsCompactElement.exists_finset_of_le_iSup
        hcompact
        (fun f : σ.SelectedMapTo S X ↦
          LinearMap.range f.map.hom.hom) hle
    let f := SelectedMapTo.flattenFinset σ F
    have hrange :
        LinearMap.range f.map.hom.hom = ⊤ := by
      apply top_unique
      refine hF.trans ?_
      refine iSup_le fun g ↦ iSup_le fun hg ↦ ?_
      exact range_le_flattenFinset σ F g hg
    refine ⟨{
      index := f.index
      label := f.label
      mem := f.mem
      map := f.map
      epi := ?_ }⟩
    haveI : Epi f.map.hom :=
      (ModuleCat.epi_iff_range_eq_top f.map.hom).mpr hrange
    apply
      (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map
    change Epi f.map.hom
    infer_instance

/-- Membership in quotient closure is the trace criterion used throughout
the manuscript. -/
theorem mem_qSet_iff_trace_eq_top (S : Set ι) (j : ι) :
    j ∈ σ.qSet S ↔ σ.trace S (σ.obj j) = ⊤ :=
  inFac_iff_trace_eq_top σ S (σ.obj j)

/-- No nonzero indecomposable is generated by the empty selection. -/
@[simp]
theorem qSet_empty : σ.qSet ∅ = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have htrace :=
    (mem_qSet_iff_trace_eq_top σ ∅ j).1 hj
  rw [trace_empty] at htrace
  letI : Nontrivial (σ.obj j) :=
    (σ.indecomposable j).nontrivial
  exact bot_ne_top htrace

/-- The empty set is closed for quotient generation. -/
theorem qClosure_isClosed_empty :
    σ.qClosure.IsClosed ∅ := by
  rw [σ.qClosure.isClosed_iff]
  exact qSet_empty σ

section Epi

variable {R₀ : Type u₀} [Ring R₀]

/-- In `FGModuleCat`, categorical epimorphisms are exactly surjective
underlying linear maps. -/
theorem fg_epi_iff_surjective
    {X Y : FGModuleCat.{w} R₀} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f.hom.hom := by
  rw [← ModuleCat.epi_iff_surjective f.hom]
  exact
    ((forget₂ (FGModuleCat R₀) (ModuleCat R₀)).epi_map_iff_epi f).symm

/-- An epi in `FGModuleCat` has full linear range. -/
theorem range_eq_top_of_epi
    {X Y : FGModuleCat.{w} R₀} (f : X ⟶ Y) [Epi f] :
    LinearMap.range f.hom.hom = ⊤ :=
  LinearMap.range_eq_top.2
    ((fg_epi_iff_surjective f).1 inferInstance)

end Epi

/-- In `FGModuleCat` over a noetherian ring, categorical monomorphisms are
exactly injective underlying linear maps. -/
theorem fg_mono_iff_injective
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.hom.hom := by
  rw [← ModuleCat.mono_iff_injective f.hom]
  exact
    ((forget₂ (FGModuleCat R) (ModuleCat R)).mono_map_iff_mono f).symm

/-- A mono in `FGModuleCat` over a noetherian ring has zero linear
kernel. -/
theorem ker_eq_bot_of_mono
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) [Mono f] :
    LinearMap.ker f.hom.hom = ⊥ :=
  LinearMap.ker_eq_bot.2
    ((fg_mono_iff_injective f).1 inferInstance)

namespace SelectedMapFrom

/-- Flatten a finite family of maps from `X` into objects of `add S` to
one map from `X` into a single explicitly presented object of `add S`. -/
def flattenFinset
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapFrom S X)) :
    σ.SelectedMapFrom S X := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapFrom S X :=
    fun t ↦ (F.equivFin.symm t).1
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : outer, (pick t).index)
  let a : J → ι :=
    fun p ↦ (pick p.1).label p.2
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  exact
    { index := J
      label := a
      mem := fun p ↦ (pick p.1).mem p.2
      map := biproduct.lift (fun t ↦ (pick t).map) ≫
        flattenIso.hom }

/-- The kernel of the flattened map is contained in the kernel of each
map in the finite family. -/
theorem ker_flattenFinset_le
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapFrom S X))
    (f : σ.SelectedMapFrom S X) (hf : f ∈ F) :
    LinearMap.ker (flattenFinset σ F).map.hom.hom ≤
      LinearMap.ker f.map.hom.hom := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapFrom S X :=
    fun t ↦ (F.equivFin.symm t).1
  let t : outer := F.equivFin ⟨f, hf⟩
  have hpick : pick t = f := by
    simp [pick, t]
  rw [← hpick]
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver
          (FintypeCat.of (Σ t : outer, (pick t).index))
          (fun p ↦ (pick p.1).label p.2) :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  let e :
      σ.sumOver
          (flattenFinset σ F).index
          (flattenFinset σ F).label ⟶
        σ.sumOver (pick t).index (pick t).label :=
    flattenIso.inv ≫
      biproduct.π (fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) t
  have hfac :
      (flattenFinset σ F).map ≫ e = (pick t).map := by
    dsimp only [e, flattenFinset]
    change
      (biproduct.lift (fun t : outer ↦ (pick t).map) ≫
        flattenIso.hom) ≫
          (flattenIso.inv ≫
            biproduct.π (fun t : outer ↦
              σ.sumOver (pick t).index (pick t).label) t) =
        (pick t).map
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      biproduct.lift_π]
  have hlinear := congrArg (fun q ↦ q.hom.hom) hfac
  simp only [FGModuleCat.hom_hom_comp] at hlinear
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← hlinear]
  simp only [LinearMap.comp_apply, hx, map_zero]

end SelectedMapFrom

/-- In an Artinian module, the intersection defining `reject` is already
the intersection of finitely many selected-map kernels. -/
theorem exists_finset_reject_eq
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X) :
    ∃ F : Finset (σ.SelectedMapFrom S X),
      (⨅ f ∈ F, LinearMap.ker f.map.hom.hom) =
        σ.reject S X := by
  classical
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hX
  letI : IsArtinian R X := hNA.2
  let L := (Submodule R X)ᵒᵈ
  have hcompact :
      IsCompactElement (OrderDual.toDual (σ.reject S X) : L) :=
    (isSupFiniteCompact_iff_all_elements_compact (α := L)).mp
      (WellFoundedGT.isSupFiniteCompact (α := L)) _
  have hall :
      (OrderDual.toDual (σ.reject S X) : L) ≤
        ⨆ f : σ.SelectedMapFrom S X,
          OrderDual.toDual (LinearMap.ker f.map.hom.hom) := by
    change (⨅ f : σ.SelectedMapFrom S X,
      LinearMap.ker f.map.hom.hom) ≤ σ.reject S X
    exact le_of_eq rfl
  obtain ⟨F, hF⟩ :=
    IsCompactElement.exists_finset_of_le_iSup hcompact
      (fun f : σ.SelectedMapFrom S X =>
        (OrderDual.toDual (LinearMap.ker f.map.hom.hom) : L)) hall
  refine ⟨F, le_antisymm hF ?_⟩
  rw [le_iInf_iff]
  intro f
  rw [le_iInf_iff]
  intro hf
  exact iInf_le_of_le f le_rfl

/-- Vanishing reject gives an embedding into one selected finite sum. -/
theorem inSub_of_reject_eq_bot
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X)
    (hreject : σ.reject S X = ⊥) :
    σ.InSub S X := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_reject_eq σ S X hX
  let f := SelectedMapFrom.flattenFinset σ F
  have hker_le :
      LinearMap.ker f.map.hom.hom ≤
        ⨅ g ∈ F, LinearMap.ker g.map.hom.hom := by
    rw [le_iInf_iff]
    intro g
    rw [le_iInf_iff]
    intro hg
    exact SelectedMapFrom.ker_flattenFinset_le σ F g hg
  have hker : LinearMap.ker f.map.hom.hom = ⊥ := by
    apply bot_unique
    rw [hF, hreject] at hker_le
    exact hker_le
  refine ⟨{
    index := f.index
    label := f.label
    mem := f.mem
    map := f.map
    mono := ?_ }⟩
  apply (fg_mono_iff_injective f.map).mpr
  exact LinearMap.ker_eq_bot.mp hker

/-- A submodule presentation is itself one of the maps occurring in the
reject intersection, so its monicity forces reject to vanish. -/
theorem reject_eq_bot_of_inSub
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hsub : σ.InSub S X) :
    σ.reject S X = ⊥ := by
  obtain ⟨P⟩ := hsub
  let f : σ.SelectedMapFrom S X :=
    { index := P.index
      label := P.label
      mem := P.mem
      map := P.map }
  letI : Mono P.map := P.mono
  apply bot_unique
  exact (reject_le_ker σ f).trans
    (le_of_eq (ker_eq_bot_of_mono P.map))

/-- For finite-length modules, submodule generation is exactly reject
vanishing. -/
theorem inSub_iff_reject_eq_bot
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X) :
    σ.InSub S X ↔ σ.reject S X = ⊥ :=
  ⟨reject_eq_bot_of_inSub σ S X,
    inSub_of_reject_eq_bot σ S X hX⟩

/-- Membership in submodule closure is the reject criterion. -/
theorem mem_sSet_iff_reject_eq_bot (S : Set ι) (j : ι) :
    j ∈ σ.sSet S ↔ σ.reject S (σ.obj j) = ⊥ :=
  inSub_iff_reject_eq_bot σ S (σ.obj j) (σ.finiteLength j)

/-- No nonzero indecomposable embeds into the empty selected sum. -/
@[simp]
theorem sSet_empty : σ.sSet ∅ = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have hreject :=
    (mem_sSet_iff_reject_eq_bot σ ∅ j).1 hj
  rw [reject_empty] at hreject
  letI : Nontrivial (σ.obj j) :=
    (σ.indecomposable j).nontrivial
  exact top_ne_bot hreject

/-- The empty set is closed for submodule generation. -/
theorem sClosure_isClosed_empty :
    σ.sClosure.IsClosed ∅ := by
  rw [σ.sClosure.isClosed_iff]
  exact sSet_empty σ

/-- Membership in the quotient closure, unfolded to its presentation. -/
@[simp]
theorem mem_qClosure_iff_inFac (S : Set ι) (j : ι) :
    j ∈ σ.qClosure S ↔ σ.InFac S (σ.obj j) :=
  Iff.rfl

/-- Membership in the submodule closure, unfolded to its presentation. -/
@[simp]
theorem mem_sClosure_iff_inSub (S : Set ι) (j : ι) :
    j ∈ σ.sClosure S ↔ σ.InSub S (σ.obj j) :=
  Iff.rfl

/-- Membership in the quotient closure, expressed by the trace criterion. -/
theorem mem_qClosure_iff_trace_eq_top (S : Set ι) (j : ι) :
    j ∈ σ.qClosure S ↔ σ.trace S (σ.obj j) = ⊤ :=
  mem_qSet_iff_trace_eq_top σ S j

/-- Membership in the submodule closure, expressed by the reject
criterion. -/
theorem mem_sClosure_iff_reject_eq_bot (S : Set ι) (j : ι) :
    j ∈ σ.sClosure S ↔ σ.reject S (σ.obj j) = ⊥ :=
  mem_sSet_iff_reject_eq_bot σ S j

/-- Postcomposition carries the selected trace into the selected trace.
This is the fully invariant property used in the anti-exchange proof. -/
theorem map_trace_le_trace {S : Set ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    Submodule.map f.hom.hom (σ.trace S X) ≤ σ.trace S Y := by
  rw [trace, Submodule.map_iSup]
  apply iSup_le
  intro g
  let h : σ.SelectedMapTo S Y :=
    { index := g.index
      label := g.label
      mem := g.mem
      map := g.map ≫ f }
  have hrange := range_le_trace σ h
  rw [← LinearMap.range_comp]
  simpa only [h, FGModuleCat.hom_hom_comp] using hrange

/-- Precomposition carries the reject into the inverse image of the
reject. -/
theorem reject_le_comap_reject {S : Set ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    σ.reject S X ≤ Submodule.comap f.hom.hom (σ.reject S Y) := by
  change
    (⨅ h : σ.SelectedMapFrom S X,
      LinearMap.ker h.map.hom.hom) ≤
        Submodule.comap f.hom.hom
          (⨅ g : σ.SelectedMapFrom S Y,
            LinearMap.ker g.map.hom.hom)
  rw [Submodule.comap_iInf]
  apply le_iInf
  intro g
  let h : σ.SelectedMapFrom S X :=
    { index := g.index
      label := g.label
      mem := g.mem
      map := f ≫ g.map }
  have hker :
      (⨅ k : σ.SelectedMapFrom S X,
        LinearMap.ker k.map.hom.hom) ≤
          LinearMap.ker h.map.hom.hom :=
    iInf_le (fun k : σ.SelectedMapFrom S X ↦
      LinearMap.ker k.map.hom.hom) h
  simpa only [h, FGModuleCat.hom_hom_comp, LinearMap.ker_comp] using hker

/-- The trace is stable under every endomorphism of its target. -/
theorem trace_fullyInvariant {S : Set ι}
    (X : FGModuleCat.{w} R) (f : X ⟶ X) :
    Submodule.map f.hom.hom (σ.trace S X) ≤ σ.trace S X :=
  map_trace_le_trace σ f

/-- The reject is stable under inverse image by every endomorphism of its
source. -/
theorem reject_fullyInvariant {S : Set ι}
    (X : FGModuleCat.{w} R) (f : X ⟶ X) :
    σ.reject S X ≤ Submodule.comap f.hom.hom (σ.reject S X) :=
  reject_le_comap_reject σ f

/-- A map from one selected indecomposable has range in the trace. -/
theorem range_le_trace_of_mem {S : Set ι} {i : ι}
    (hi : i ∈ S) {X : FGModuleCat.{w} R}
    (f : σ.obj i ⟶ X) :
    LinearMap.range f.hom.hom ≤ σ.trace S X := by
  let a : Fin 1 → ι := fun _ ↦ i
  let e :
      σ.sumOver (FintypeCat.of (Fin 1)) a ⟶ σ.obj i :=
    (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom
  let g : σ.SelectedMapTo S X :=
    { index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ hi
      map := e ≫ f }
  have hepi : Epi e := inferInstance
  have herange : LinearMap.range e.hom.hom = ⊤ :=
    range_eq_top_of_epi e
  have hcomp :
      LinearMap.range (f.hom.hom.comp e.hom.hom) =
        LinearMap.range f.hom.hom :=
    LinearMap.range_comp_of_range_eq_top f.hom.hom herange
  rw [← hcomp]
  simpa only [g, FGModuleCat.hom_hom_comp] using range_le_trace σ g

omit [IsNoetherianRing R] in
private theorem fg_hom_sum_apply {J : Type*} [Fintype J]
    {X Y : FGModuleCat.{w} R} (f : J → (X ⟶ Y)) (x : X) :
    ((∑ j, f j).hom.hom) x =
      ∑ j, (f j).hom.hom x := by
  have h₁ :
      (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h₁, ModuleCat.hom_sum]
  exact LinearMap.sum_apply _ _ x

/-- Trace converts unions of selected indecomposables to joins of
submodules. -/
theorem trace_union (S T : Set ι) (X : FGModuleCat.{w} R) :
    σ.trace (S ∪ T) X = σ.trace S X ⊔ σ.trace T X := by
  apply le_antisymm
  · apply iSup_le
    intro f
    letI : Fintype f.index := FintypeCat.fintype
    rintro x ⟨y, rfl⟩
    have hmap :
        f.map =
          ∑ t : f.index,
            biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t ≫
              (biproduct.ι
                  (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                f.map) := by
      calc
        f.map = 𝟙 _ ≫ f.map := (Category.id_comp _).symm
        _ =
            (∑ t : f.index,
              biproduct.π
                  (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                biproduct.ι
                  (fun t : f.index ↦ σ.obj (f.label t)) t) ≫
              f.map := by rw [biproduct.total]
        _ = _ := by
          rw [Preadditive.sum_comp]
          simp only [Category.assoc]
    rw [hmap, fg_hom_sum_apply]
    apply Submodule.sum_mem
    intro t _
    let ft : σ.obj (f.label t) ⟶ X :=
      biproduct.ι (fun t : f.index ↦ σ.obj (f.label t)) t ≫ f.map
    have hmemRange :
        ft
          ((biproduct.π
            (fun t : f.index ↦ σ.obj (f.label t)) t) y) ∈
          LinearMap.range ft.hom.hom :=
      LinearMap.mem_range_self ft.hom.hom _
    rcases f.mem t with ht | ht
    · exact
        (show σ.trace S X ≤ σ.trace S X ⊔ σ.trace T X from le_sup_left)
          ((range_le_trace_of_mem σ ht ft) hmemRange)
    · exact
        (show σ.trace T X ≤ σ.trace S X ⊔ σ.trace T X from le_sup_right)
          ((range_le_trace_of_mem σ ht ft) hmemRange)
  · exact sup_le
      (trace_mono σ Set.subset_union_left X)
      (trace_mono σ Set.subset_union_right X)

/-- Adjoining one indecomposable adds precisely its singleton trace. -/
theorem trace_insert (S : Set ι) (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.trace (insert i S) X =
      σ.trace S X ⊔ σ.trace {i} X := by
  rw [show insert i S = S ∪ {i} by ext; simp]
  exact trace_union σ S {i} X

end MBDVendor.QSE.IndecomposableSkeleton
