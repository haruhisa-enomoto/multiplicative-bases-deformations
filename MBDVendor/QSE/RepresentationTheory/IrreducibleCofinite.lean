module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import MBDVendor.QSE.RepresentationTheory.AdditiveSubcategory
public import MBDVendor.QSE.RepresentationTheory.SplitProjective

/-!
# Irreducible maps and the converse cofinite-two criterion

This file formalizes the elementary (non-Auslander--Reiten) half of
the manuscript's mixed cofinite-two criterion.  If `P` is projective and
there is an irreducible map `P ⟶ Z`, then deleting the labels of `P` and `Z`
leaves a quotient-closed support.  The dual injective statement is included
as well.

The definition of irreducibility is categorical: the map itself is neither
a split monomorphism nor a split epimorphism, and in every factorization the
first factor is a split monomorphism or the second is a split epimorphism.
-/

@[expose] public section

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe u v

variable {C : Type u} [Category.{v} C]

/-- A morphism is irreducible if it is not split in either direction and
every factorization has a split-monomorphic first factor or a split-epimorphic
second factor. -/
structure IsIrreducibleMorphism {X Y : C} (f : X ⟶ Y) : Prop where
  not_isSplitMono : ¬ IsSplitMono f
  not_isSplitEpi : ¬ IsSplitEpi f
  factorization :
    ∀ {M : C} (g : X ⟶ M) (h : M ⟶ Y),
      g ≫ h = f → IsSplitMono g ∨ IsSplitEpi h

namespace IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The displayed sum in a quotient or submodule presentation belongs to
the additive closure of the presentation's support. -/
private theorem sumOver_inAdd {S : Set ι}
    (J : FintypeCat.{0}) (a : J → ι) (ha : ∀ j, a j ∈ S) :
    σ.InAdd S (σ.sumOver J a) :=
  ⟨{
    index := J
    label := a
    mem := ha
    iso := Iso.refl _ }⟩

/-- A categorical projective is split-projective relative to the top
support in the existing explicit-presentation sense. -/
theorem isRelativeSplitProjective_univ_of_projective {p : ι}
    [Projective (σ.obj p)] :
    σ.IsRelativeSplitProjective Set.univ p := by
  intro P
  letI : Epi P.map := P.epi
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 (σ.obj p)) P.map
  exact IsSplitEpi.mk' {
    section_ := s
    id := hs }

/-- Conversely, top relative split-projectivity is categorical
projectivity.  The pullback of an epimorphism along a map out of `P` gives
an epimorphism onto `P`; the skeleton decomposition turns its source into
one of the explicit presentations tested by the relative predicate. -/
theorem projective_of_isRelativeSplitProjective_univ {p : ι}
    (hp : σ.IsRelativeSplitProjective Set.univ p) :
    Projective (σ.obj p) := by
  constructor
  intro E X f e _
  obtain ⟨n, a, ⟨t⟩⟩ := σ.decomposes (pullback e f)
  let q : σ.sum n a ⟶ σ.obj p :=
    t.inv ≫ pullback.snd e f
  let P : σ.FacPresentation Set.univ (σ.obj p) :=
    { index := FintypeCat.of (Fin n)
      label := a
      mem := fun _ ↦ Set.mem_univ _
      map := q
      epi := by
        dsimp only [q]
        infer_instance }
  obtain ⟨se⟩ := (hp P).exists_splitEpi
  have hsection :
      se.section_ ≫ t.inv ≫ pullback.snd e f = 𝟙 (σ.obj p) := by
    simpa only [P, q, Category.assoc] using se.id
  refine
    ⟨se.section_ ≫ t.inv ≫ pullback.fst e f, ?_⟩
  calc
    (se.section_ ≫ t.inv ≫ pullback.fst e f) ≫ e =
        se.section_ ≫ t.inv ≫ (pullback.fst e f ≫ e) := by
          simp only [Category.assoc]
    _ = se.section_ ≫ t.inv ≫ (pullback.snd e f ≫ f) := by
          rw [pullback.condition]
    _ = (se.section_ ≫ t.inv ≫ pullback.snd e f) ≫ f := by
          simp only [Category.assoc]
    _ = f := by rw [hsection, Category.id_comp]

/-- Categorical projectivity and the package's top relative
split-projectivity agree on the chosen indecomposable objects. -/
theorem projective_iff_isRelativeSplitProjective_univ {p : ι} :
    Projective (σ.obj p) ↔
      σ.IsRelativeSplitProjective Set.univ p :=
  ⟨fun hp ↦ by
      letI : Projective (σ.obj p) := hp
      exact isRelativeSplitProjective_univ_of_projective σ,
    projective_of_isRelativeSplitProjective_univ σ⟩

/-- A categorical injective is split-injective relative to the top support
in the existing explicit-presentation sense. -/
theorem isRelativeSplitInjective_univ_of_injective {i : ι}
    [Injective (σ.obj i)] :
    σ.IsRelativeSplitInjective Set.univ i := by
  intro P
  letI : Mono P.map := P.mono
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 (σ.obj i)) P.map
  exact ⟨{
    retraction := r
    id := hr }⟩

/-- Conversely, top relative split-injectivity is categorical injectivity,
by the dual pushout argument. -/
theorem injective_of_isRelativeSplitInjective_univ {i : ι}
    (hi : σ.IsRelativeSplitInjective Set.univ i) :
    Injective (σ.obj i) := by
  constructor
  intro X Y g f _
  obtain ⟨n, a, ⟨t⟩⟩ := σ.decomposes (pushout f g)
  let m : σ.obj i ⟶ σ.sum n a :=
    pushout.inr _ _ ≫ t.hom
  let P : σ.SubPresentation Set.univ (σ.obj i) :=
    { index := FintypeCat.of (Fin n)
      label := a
      mem := fun _ ↦ Set.mem_univ _
      map := m
      mono := by
        dsimp only [m]
        infer_instance }
  obtain ⟨sm⟩ := hi P
  have hretraction :
      pushout.inr f g ≫ t.hom ≫ sm.retraction = 𝟙 (σ.obj i) := by
    simpa only [P, m, Category.assoc] using sm.id
  refine
    ⟨pushout.inl f g ≫ t.hom ≫ sm.retraction, ?_⟩
  calc
    f ≫ (pushout.inl f g ≫ t.hom ≫ sm.retraction) =
        (f ≫ pushout.inl f g) ≫ t.hom ≫ sm.retraction := by
          simp only [Category.assoc]
    _ = (g ≫ pushout.inr f g) ≫ t.hom ≫ sm.retraction := by
          rw [pushout.condition]
    _ = g ≫ (pushout.inr f g ≫ t.hom ≫ sm.retraction) := by
          simp only [Category.assoc]
    _ = g := by rw [hretraction, Category.comp_id]

/-- Categorical injectivity and top relative split-injectivity agree on
the chosen indecomposable objects. -/
theorem injective_iff_isRelativeSplitInjective_univ {i : ι} :
    Injective (σ.obj i) ↔
      σ.IsRelativeSplitInjective Set.univ i :=
  ⟨fun hi ↦ by
      letI : Injective (σ.obj i) := hi
      exact isRelativeSplitInjective_univ_of_injective σ,
    injective_of_isRelativeSplitInjective_univ σ⟩

/-- A projective indecomposable cannot be quotient-generated by a support
which omits its label. -/
private theorem projective_not_mem_qSet {S : Set ι} {p : ι}
    [Projective (σ.obj p)] (hp : p ∉ S) :
    p ∉ σ.qSet S := by
  rintro ⟨P⟩
  letI : Epi P.map := P.epi
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 (σ.obj p)) P.map
  let r : Retract (σ.obj p) (σ.sumOver P.index P.label) :=
    { i := s
      r := P.map
      retract := hs }
  exact hp (index_mem_of_retract_inAdd σ r
    (sumOver_inAdd σ P.index P.label P.mem))

/-- If `P` and `Z` are both omitted, projectivity of `P` and an irreducible
map `P ⟶ Z` prevent `Z` from being quotient-generated by the retained
support. -/
private theorem irreducible_target_not_mem_qSet
    {S : Set ι} {p z : ι} [Projective (σ.obj p)]
    (hp : p ∉ S) (hz : z ∉ S)
    (f : σ.obj p ⟶ σ.obj z) (hf : IsIrreducibleMorphism f) :
    z ∉ σ.qSet S := by
  rintro ⟨P⟩
  letI : Epi P.map := P.epi
  obtain ⟨g, hg⟩ := Projective.factors f P.map
  have hsource :
      σ.InAdd S (σ.sumOver P.index P.label) :=
    sumOver_inAdd σ P.index P.label P.mem
  rcases hf.factorization g P.map hg with hg_split | hP_split
  · obtain ⟨sm⟩ := hg_split.exists_splitMono
    let r : Retract (σ.obj p) (σ.sumOver P.index P.label) :=
      { i := g
        r := sm.retraction
        retract := sm.id }
    exact hp (index_mem_of_retract_inAdd σ r hsource)
  · obtain ⟨se⟩ := hP_split.exists_splitEpi
    let r : Retract (σ.obj z) (σ.sumOver P.index P.label) :=
      { i := se.section_
        r := P.map
        retract := se.id }
    exact hz (index_mem_of_retract_inAdd σ r hsource)

/-- Converse half of the mixed quotient cofinite-two criterion: an
irreducible map from a projective indecomposable forces the two-point
complement to be quotient-closed. -/
theorem qClosed_compl_pair_of_projective_irreducible
    {p z : ι} [Projective (σ.obj p)] (_hpz : p ≠ z)
    (f : σ.obj p ⟶ σ.obj z) (hf : IsIrreducibleMorphism f) :
    σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ := by
  apply σ.qClosure.isClosed_iff.2
  change σ.qSet ({p, z} : Set ι)ᶜ = ({p, z} : Set ι)ᶜ
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxC
    have hxpair : x = p ∨ x = z := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_not] using hxC
    rcases hxpair with hx_eq | hx_eq
    · subst x
      exact (projective_not_mem_qSet σ (S := ({p, z} : Set ι)ᶜ)
        (by simp)) hx
    · subst x
      exact (irreducible_target_not_mem_qSet σ
        (S := ({p, z} : Set ι)ᶜ) (by simp) (by simp) f hf) hx
  · exact subset_qSet σ _

/-- The same converse criterion with the manuscript's top
split-projectivity hypothesis. -/
theorem qClosed_compl_pair_of_topSplitProjective_irreducible
    {p z : ι} (hp : σ.IsRelativeSplitProjective Set.univ p)
    (hpz : p ≠ z) (f : σ.obj p ⟶ σ.obj z)
    (hf : IsIrreducibleMorphism f) :
    σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ := by
  letI : Projective (σ.obj p) :=
    projective_of_isRelativeSplitProjective_univ σ hp
  exact qClosed_compl_pair_of_projective_irreducible σ hpz f hf

/-- Combined formulation matching the manuscript terminology: the
projective label is top split-projective, and deleting it together with the
target of an irreducible map gives a quotient-closed support. -/
theorem projective_irreducible_implies_topSplit_and_qClosed
    {p z : ι} [Projective (σ.obj p)] (hpz : p ≠ z)
    (f : σ.obj p ⟶ σ.obj z) (hf : IsIrreducibleMorphism f) :
    σ.IsRelativeSplitProjective Set.univ p ∧
      σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ :=
  ⟨isRelativeSplitProjective_univ_of_projective σ,
    qClosed_compl_pair_of_projective_irreducible σ hpz f hf⟩

/-- An injective indecomposable cannot be submodule-generated by a support
which omits its label. -/
private theorem injective_not_mem_sSet {S : Set ι} {i : ι}
    [Injective (σ.obj i)] (hi : i ∉ S) :
    i ∉ σ.sSet S := by
  rintro ⟨P⟩
  letI : Mono P.map := P.mono
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 (σ.obj i)) P.map
  let rt : Retract (σ.obj i) (σ.sumOver P.index P.label) :=
    { i := P.map
      r := r
      retract := hr }
  exact hi (index_mem_of_retract_inAdd σ rt
    (sumOver_inAdd σ P.index P.label P.mem))

/-- Dual mixed obstruction: if `Z` and `I` are omitted, injectivity of `I`
and an irreducible map `Z ⟶ I` prevent `Z` from being submodule-generated
by the retained support. -/
private theorem irreducible_source_not_mem_sSet
    {S : Set ι} {z i : ι} [Injective (σ.obj i)]
    (hz : z ∉ S) (hi : i ∉ S)
    (f : σ.obj z ⟶ σ.obj i) (hf : IsIrreducibleMorphism f) :
    z ∉ σ.sSet S := by
  rintro ⟨P⟩
  letI : Mono P.map := P.mono
  obtain ⟨g, hg⟩ := Injective.factors f P.map
  have htarget :
      σ.InAdd S (σ.sumOver P.index P.label) :=
    sumOver_inAdd σ P.index P.label P.mem
  rcases hf.factorization P.map g hg with hP_split | hg_split
  · obtain ⟨sm⟩ := hP_split.exists_splitMono
    let r : Retract (σ.obj z) (σ.sumOver P.index P.label) :=
      { i := P.map
        r := sm.retraction
        retract := sm.id }
    exact hz (index_mem_of_retract_inAdd σ r htarget)
  · obtain ⟨se⟩ := hg_split.exists_splitEpi
    let r : Retract (σ.obj i) (σ.sumOver P.index P.label) :=
      { i := se.section_
        r := g
        retract := se.id }
    exact hi (index_mem_of_retract_inAdd σ r htarget)

/-- Dual converse half: an irreducible map into an injective
indecomposable forces the two-point complement to be submodule-closed. -/
theorem sClosed_compl_pair_of_irreducible_injective
    {z i : ι} [Injective (σ.obj i)] (_hzi : z ≠ i)
    (f : σ.obj z ⟶ σ.obj i) (hf : IsIrreducibleMorphism f) :
    σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ := by
  apply σ.sClosure.isClosed_iff.2
  change σ.sSet ({z, i} : Set ι)ᶜ = ({z, i} : Set ι)ᶜ
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxC
    have hxpair : x = z ∨ x = i := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_not] using hxC
    rcases hxpair with hx_eq | hx_eq
    · subst x
      exact (irreducible_source_not_mem_sSet σ
        (S := ({z, i} : Set ι)ᶜ) (by simp) (by simp) f hf) hx
    · subst x
      exact (injective_not_mem_sSet σ (S := ({z, i} : Set ι)ᶜ)
        (by simp)) hx
  · exact subset_sSet σ _

/-- The dual criterion with the manuscript's top split-injectivity
hypothesis. -/
theorem sClosed_compl_pair_of_irreducible_topSplitInjective
    {z i : ι} (hi : σ.IsRelativeSplitInjective Set.univ i)
    (hzi : z ≠ i) (f : σ.obj z ⟶ σ.obj i)
    (hf : IsIrreducibleMorphism f) :
    σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ := by
  letI : Injective (σ.obj i) :=
    injective_of_isRelativeSplitInjective_univ σ hi
  exact sClosed_compl_pair_of_irreducible_injective σ hzi f hf

/-- Dual combined formulation. -/
theorem irreducible_injective_implies_topSplit_and_sClosed
    {z i : ι} [Injective (σ.obj i)] (hzi : z ≠ i)
    (f : σ.obj z ⟶ σ.obj i) (hf : IsIrreducibleMorphism f) :
    σ.IsRelativeSplitInjective Set.univ i ∧
      σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ :=
  ⟨isRelativeSplitInjective_univ_of_injective σ,
    sClosed_compl_pair_of_irreducible_injective σ hzi f hf⟩

end IndecomposableSkeleton

end MBDVendor.QSE
