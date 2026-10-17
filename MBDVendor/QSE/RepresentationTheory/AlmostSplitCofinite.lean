import MBDVendor.QSE.RepresentationTheory.IrreducibleCofinite
import MBDVendor.QSE.CategoryTheory.MinimalMorphism
import Mathlib.RingTheory.Length

/-!
# An abstract almost-split interface for the forward cofinite-two criterion

This file isolates the Auslander--Reiten input needed for the forward half
of the manuscript's mixed cofinite-two criterion.  It proves the usual
correspondence between the indecomposable summands of a minimal almost-split
middle term and irreducible morphisms.  It also proves that a supplied
finite-length almost-split map can be replaced by a minimal one.  Existence
of ordinary almost-split maps is still left as a separate input.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe u v

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : E ⟶ Z` is right almost split when it is not a split
epimorphism and every morphism into `Z` which is not a split epimorphism
factors through it.

Here "non-split epimorphism" is used in the standard AR sense of a morphism
which is not a retraction; the morphism being factored need not itself be
categorically epic. -/
structure IsRightAlmostSplit {E Z : C} (f : E ⟶ Z) : Prop where
  not_isSplitEpi : ¬ IsSplitEpi f
  factors :
    ∀ {X : C} (g : X ⟶ Z),
      ¬ IsSplitEpi g → ∃ h : X ⟶ E, h ≫ f = g

/-- The dual notion of a left almost-split morphism. -/
structure IsLeftAlmostSplit {Z E : C} (f : Z ⟶ E) : Prop where
  not_isSplitMono : ¬ IsSplitMono f
  factors :
    ∀ {X : C} (g : Z ⟶ X),
      ¬ IsSplitMono g → ∃ h : E ⟶ X, f ≫ h = g

/-- Existence of an irreducible morphism between two objects. -/
def HasIrreducibleMorphism (X Y : C) : Prop :=
  ∃ f : X ⟶ Y, IsIrreducibleMorphism f

/-- The no-loop input used for an almost-split middle term: there is no
irreducible endomorphism of `X`. -/
def HasNoIrreducibleEndomorphism (X : C) : Prop :=
  ¬ HasIrreducibleMorphism X X

/-- A monic endomorphism of a finite-length finitely generated module is an
isomorphism. -/
private theorem isIso_of_mono_finiteLength_endo
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {X : FGModuleCat.{v} R} (hX : IsFiniteLength R X)
    (f : X ⟶ X) [Mono f] :
    IsIso f := by
  obtain ⟨hN, hA⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hX
  letI : IsNoetherian R X := hN
  letI : IsArtinian R X := hA
  have hinj : Function.Injective f.hom.hom :=
    (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
  have hsurj : Function.Surjective f.hom.hom :=
    IsArtinian.surjective_of_injective_endomorphism f.hom.hom hinj
  letI : Epi f :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurj
  exact isIso_of_mono_of_epi f

/-- An epic endomorphism of a finite-length finitely generated module is an
isomorphism. -/
private theorem isIso_of_epi_finiteLength_endo
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {X : FGModuleCat.{v} R} (hX : IsFiniteLength R X)
    (f : X ⟶ X) [Epi f] :
    IsIso f := by
  obtain ⟨hN, hA⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hX
  letI : IsNoetherian R X := hN
  letI : IsArtinian R X := hA
  have hsurj : Function.Surjective f.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
  have hinj : Function.Injective f.hom.hom :=
    IsNoetherian.injective_of_surjective_endomorphism f.hom.hom hsurj
  letI : Mono f :=
    (IndecomposableSkeleton.fg_mono_iff_injective f).2 hinj
  exact isIso_of_mono_of_epi f

/-- The categorical image of a noninvertible endomorphism of a finite-length
finitely generated module has strictly smaller finite length. -/
private theorem image_finiteLength_and_length_toNat_lt
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {E : FGModuleCat.{v} R} (hE : IsFiniteLength R E)
    (e : E ⟶ E) (hnotiso : ¬ IsIso e) :
    IsFiniteLength R (Abelian.image e : FGModuleCat.{v} R) ∧
      (Module.length R (Abelian.image e : FGModuleCat.{v} R)).toNat <
        (Module.length R E).toNat := by
  let I : FGModuleCat.{v} R := Abelian.image e
  change IsFiniteLength R I ∧
    (Module.length R I).toNat < (Module.length R E).toNat
  let i : I ⟶ E := Abelian.image.ι e
  have hIfinite : IsFiniteLength R I := by
    apply hE.of_injective
      (f := i.hom.hom)
    exact
      (IndecomposableSkeleton.fg_mono_iff_injective i).1
        inferInstance
  refine ⟨hIfinite, ?_⟩
  obtain ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hE
  letI : IsNoetherian R E := hNoetherian
  letI : IsArtinian R E := hArtinian
  have hiInjective : Function.Injective i.hom.hom :=
    (IndecomposableSkeleton.fg_mono_iff_injective i).1 inferInstance
  have hrangeProper : LinearMap.range i.hom.hom ≠ ⊤ := by
    intro hrange
    have hiSurjective : Function.Surjective i.hom.hom :=
      LinearMap.range_eq_top.mp hrange
    letI : Epi i :=
      (IndecomposableSkeleton.fg_epi_iff_surjective i).2 hiSurjective
    letI : Epi e := by
      rw [← Abelian.image.fac e]
      infer_instance
    exact hnotiso (isIso_of_epi_finiteLength_endo hE e)
  have hlengthRange :
      Module.length R I = Module.length R (LinearMap.range i.hom.hom) :=
    (LinearEquiv.ofInjective i.hom.hom hiInjective).length_eq
  have hltENat :
      Module.length R I < Module.length R E :=
    hlengthRange.trans_lt (Submodule.length_lt hrangeProper)
  have hIne : Module.length R I ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hIfinite
  have hEne : Module.length R E ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hE
  rw [← ENat.coe_toNat hIne, ← ENat.coe_toNat hEne] at hltENat
  exact_mod_cast hltENat

/-- A finite-length finitely generated module has no irreducible
endomorphism.

The canonical epi--mono image factorization of a hypothetical irreducible
endomorphism would make one factor split.  The split factor is then an
isomorphism, making the original endomorphism monic or epic; finite length
makes it an isomorphism, contradicting irreducibility. -/
theorem noIrreducibleEndomorphism_of_finiteLength
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {X : FGModuleCat.{v} R} (hX : IsFiniteLength R X) :
    HasNoIrreducibleEndomorphism X := by
  rintro ⟨f, hf⟩
  rcases hf.factorization
      (Abelian.factorThruImage f) (Abelian.image.ι f)
      (Abelian.image.fac f) with hq | hi
  · letI : IsSplitMono (Abelian.factorThruImage f) := hq
    letI : IsIso (Abelian.factorThruImage f) :=
      isIso_of_epi_of_isSplitMono _
    letI : Mono f := by
      rw [← Abelian.image.fac f]
      infer_instance
    letI : IsIso f := isIso_of_mono_finiteLength_endo hX f
    exact hf.not_isSplitMono (by infer_instance)
  · letI : IsSplitEpi (Abelian.image.ι f) := hi
    letI : IsIso (Abelian.image.ι f) :=
      isIso_of_mono_of_isSplitEpi _
    letI : Epi f := by
      rw [← Abelian.image.fac f]
      infer_instance
    letI : IsIso f := isIso_of_epi_finiteLength_endo hX f
    exact hf.not_isSplitEpi (by infer_instance)

namespace IsRightAlmostSplit

/-- A right almost-split map is epic as soon as its target admits one
categorically epic map which is not split. -/
theorem epi_of_nonsplit_epi {E Z X : C} {f : E ⟶ Z}
    (hf : IsRightAlmostSplit f) (g : X ⟶ Z) [Epi g]
    (hg : ¬ IsSplitEpi g) :
    Epi f := by
  obtain ⟨h, hh⟩ := hf.factors g hg
  exact epi_of_epi_fac hh

end IsRightAlmostSplit

namespace IsLeftAlmostSplit

/-- Dually, a left almost-split map is monic as soon as its source admits
one categorical monomorphism which is not split. -/
theorem mono_of_nonsplit_mono {Z E X : C} {f : Z ⟶ E}
    (hf : IsLeftAlmostSplit f) (g : Z ⟶ X) [Mono g]
    (hg : ¬ IsSplitMono g) :
    Mono f := by
  obtain ⟨h, hh⟩ := hf.factors g hg
  exact mono_of_mono_fac hh

end IsLeftAlmostSplit

namespace IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Each chosen skeleton representative has no irreducible endomorphism.
Only its recorded finite length is needed. -/
theorem hasNoIrreducibleEndomorphism_obj (z : ι) :
    HasNoIrreducibleEndomorphism (σ.obj z) :=
  noIrreducibleEndomorphism_of_finiteLength (σ.finiteLength z)

/-- To prove that a map into a chosen indecomposable is right almost split,
it suffices to establish the factorization property on the chosen
indecomposable representatives.  The skeleton decomposition then handles an
arbitrary source one component at a time. -/
theorem isRightAlmostSplit_of_factors_obj
    {z : ι} {E : FGModuleCat.{w} R} (f : E ⟶ σ.obj z)
    (hnosplit : ¬ IsSplitEpi f)
    (hfac : ∀ (x : ι) (g : σ.obj x ⟶ σ.obj z),
      ¬ IsSplitEpi g → ∃ h : σ.obj x ⟶ E, h ≫ f = g) :
    IsRightAlmostSplit f := by
  refine ⟨hnosplit, ?_⟩
  intro X g hg
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  let F : Fin n → FGModuleCat.{w} R := fun t ↦ σ.obj (a t)
  let inc (t : Fin n) : F t ⟶ X := biproduct.ι F t ≫ e.inv
  let component (t : Fin n) : F t ⟶ σ.obj z := inc t ≫ g
  have hcomponent (t : Fin n) : ¬ IsSplitEpi (component t) := by
    intro hs
    obtain ⟨se⟩ := hs.exists_splitEpi
    apply hg
    exact IsSplitEpi.mk'
      { section_ := se.section_ ≫ inc t
        id := by simpa only [component, Category.assoc] using se.id }
  let factor (t : Fin n) : F t ⟶ E :=
    Classical.choose (hfac (a t) (component t) (hcomponent t))
  have factor_spec (t : Fin n) : factor t ≫ f = component t :=
    Classical.choose_spec (hfac (a t) (component t) (hcomponent t))
  let h : X ⟶ E := e.hom ≫ biproduct.desc factor
  refine ⟨h, ?_⟩
  rw [← cancel_epi e.inv]
  apply biproduct.hom_ext'
  intro t
  simp only [h, Category.assoc, Iso.inv_hom_id_assoc]
  change (biproduct.ι F t ≫ biproduct.desc factor) ≫ f = component t
  rw [biproduct.ι_desc, factor_spec]

/-- The left-dual reduction: factorization on the chosen indecomposable
representatives implies the full left almost-split property. -/
theorem isLeftAlmostSplit_of_factors_obj
    {z : ι} {E : FGModuleCat.{w} R} (f : σ.obj z ⟶ E)
    (hnosplit : ¬ IsSplitMono f)
    (hfac : ∀ (x : ι) (g : σ.obj z ⟶ σ.obj x),
      ¬ IsSplitMono g → ∃ h : E ⟶ σ.obj x, f ≫ h = g) :
    IsLeftAlmostSplit f := by
  refine ⟨hnosplit, ?_⟩
  intro X g hg
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  let F : Fin n → FGModuleCat.{w} R := fun t ↦ σ.obj (a t)
  let proj (t : Fin n) : X ⟶ F t := e.hom ≫ biproduct.π F t
  let component (t : Fin n) : σ.obj z ⟶ F t := g ≫ proj t
  have hcomponent (t : Fin n) : ¬ IsSplitMono (component t) := by
    intro hs
    obtain ⟨sm⟩ := hs.exists_splitMono
    apply hg
    exact IsSplitMono.mk'
      { retraction := proj t ≫ sm.retraction
        id := by simpa only [component, Category.assoc] using sm.id }
  let factor (t : Fin n) : E ⟶ F t :=
    Classical.choose (hfac (a t) (component t) (hcomponent t))
  have factor_spec (t : Fin n) : f ≫ factor t = component t :=
    Classical.choose_spec (hfac (a t) (component t) (hcomponent t))
  let h : E ⟶ X := biproduct.lift factor ≫ e.inv
  refine ⟨h, ?_⟩
  rw [← cancel_mono e.hom]
  apply biproduct.hom_ext
  intro t
  simp only [h, Category.assoc, Iso.inv_hom_id_assoc]
  change f ≫ (biproduct.lift factor ≫ biproduct.π F t) = component t
  rw [biproduct.lift_π, factor_spec]

/-- A split monomorphism between chosen indecomposables is also split epic.
The splitting exhibits the source as a retract of the target, so the
duplicate-free skeleton identifies their labels; finite length then upgrades
the resulting monic endomorphism to an isomorphism. -/
theorem isSplitEpi_of_isSplitMono_between_obj
    {x y : ι} (g : σ.obj x ⟶ σ.obj y) [IsSplitMono g] :
    IsSplitEpi g := by
  let rt : Retract (σ.obj x) (σ.obj y) :=
    { i := g
      r := retraction g
      retract := IsSplitMono.id g }
  have hxy : x = y := by
    simpa only [Set.mem_singleton_iff] using
      index_mem_of_retract_inAdd σ rt
        (inAdd_obj σ (Set.mem_singleton y))
  subst x
  letI : Mono g := inferInstance
  letI : IsIso g :=
    isIso_of_mono_finiteLength_endo (σ.finiteLength y) g
  infer_instance

/-- Dually, a split epimorphism between chosen indecomposables is also split
monic. -/
theorem isSplitMono_of_isSplitEpi_between_obj
    {x y : ι} (g : σ.obj x ⟶ σ.obj y) [IsSplitEpi g] :
    IsSplitMono g := by
  let rt : Retract (σ.obj y) (σ.obj x) :=
    { i := section_ g
      r := g
      retract := IsSplitEpi.id g }
  have hyx : y = x := by
    simpa only [Set.mem_singleton_iff] using
      index_mem_of_retract_inAdd σ rt
        (inAdd_obj σ (Set.mem_singleton x))
  subst y
  letI : Epi g := inferInstance
  letI : IsIso g :=
    isIso_of_epi_finiteLength_endo (σ.finiteLength x) g
  infer_instance

/-- A chosen finite indecomposable decomposition of the middle object of a
minimal right almost-split map ending at `σ.obj z`. -/
structure MinimalRightAlmostSplitDecomposition (z : ι) where
  middle : FGModuleCat.{w} R
  finiteLength : IsFiniteLength R middle
  map : middle ⟶ σ.obj z
  rightAlmostSplit : IsRightAlmostSplit map
  rightMinimal : IsRightMinimal map
  index : FintypeCat.{0}
  label : index → ι
  decomposition : middle ≅ σ.sumOver index label

/-- A chosen finite indecomposable decomposition of the middle object of a
minimal left almost-split map starting at `σ.obj z`. -/
structure MinimalLeftAlmostSplitDecomposition (z : ι) where
  middle : FGModuleCat.{w} R
  finiteLength : IsFiniteLength R middle
  map : σ.obj z ⟶ middle
  leftAlmostSplit : IsLeftAlmostSplit map
  leftMinimal : IsLeftMinimal map
  index : FintypeCat.{0}
  label : index → ι
  decomposition : middle ≅ σ.sumOver index label

namespace MinimalRightAlmostSplitDecomposition

/-- Bundle any supplied minimal right almost-split map with a decomposition
provided by the existing skeleton. -/
def ofMap {z : ι} {E : FGModuleCat.{w} R} (f : E ⟶ σ.obj z)
    (hE : IsFiniteLength R E)
    (har : IsRightAlmostSplit f) (hmin : IsRightMinimal f) :
    σ.MinimalRightAlmostSplitDecomposition z :=
  let n := (σ.decomposes E).choose
  let a := (σ.decomposes E).choose_spec.choose
  let e := (σ.decomposes E).choose_spec.choose_spec.some
  { middle := E
    finiteLength := hE
    map := f
    rightAlmostSplit := har
    rightMinimal := hmin
    index := FintypeCat.of (Fin n)
    label := a
    decomposition := e }

/-- Any right almost-split morphism with finite-length middle term can be
replaced by a minimal one.  Choose an almost-split middle term of least
finite length; if an endomorphism fixing its map were noninvertible, its
categorical image would give a strictly shorter right almost-split middle
term. -/
theorem exists_of_rightAlmostSplit_of_finiteLength
    {z : ι} {E : FGModuleCat.{w} R}
    (f : E ⟶ σ.obj z) (hf : IsRightAlmostSplit f)
    (hE : IsFiniteLength R E) :
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ (E' : FGModuleCat.{w} R) (f' : E' ⟶ σ.obj z),
      IsFiniteLength R E' ∧ IsRightAlmostSplit f' ∧
        (Module.length R E').toNat = n
  have hP : ∃ n, P n :=
    ⟨(Module.length R E).toNat, E, f, hE, hf, rfl⟩
  let n : ℕ := Nat.find hP
  obtain ⟨Emin, fmin, hEmin, hfmin, hlength⟩ := Nat.find_spec hP
  have hminimal : IsRightMinimal fmin := by
    intro e he
    by_contra hnotiso
    let I : FGModuleCat.{w} R := Abelian.image e
    let i : I ⟶ Emin := Abelian.image.ι e
    let q : Emin ⟶ I := Abelian.factorThruImage e
    let fI : I ⟶ σ.obj z := i ≫ fmin
    obtain ⟨hIfinite, hlt⟩ :=
      image_finiteLength_and_length_toNat_lt hEmin e hnotiso
    have hfI : IsRightAlmostSplit fI := by
      constructor
      · intro hsplit
        obtain ⟨se⟩ := hsplit.exists_splitEpi
        apply hfmin.not_isSplitEpi
        exact IsSplitEpi.mk'
          { section_ := se.section_ ≫ i
            id := by simpa only [fI, Category.assoc] using se.id }
      · intro X g hg
        obtain ⟨h, hh⟩ := hfmin.factors g hg
        refine ⟨h ≫ q, ?_⟩
        calc
          (h ≫ q) ≫ fI = h ≫ (q ≫ i) ≫ fmin := by
            simp only [fI, Category.assoc]
          _ = h ≫ e ≫ fmin := by rw [Abelian.image.fac]
          _ = h ≫ fmin := by rw [he]
          _ = g := hh
    have hPI : P (Module.length R I).toNat :=
      ⟨I, fI, hIfinite, hfI, rfl⟩
    have hle : n ≤ (Module.length R I).toNat := by
      dsimp only [n]
      exact Nat.find_min' hP hPI
    rw [hlength] at hlt
    exact Nat.not_lt_of_ge hle hlt
  exact ⟨ofMap σ fmin hEmin hfmin hminimal⟩

end MinimalRightAlmostSplitDecomposition

namespace MinimalLeftAlmostSplitDecomposition

/-- Bundle any supplied minimal left almost-split map with a decomposition
provided by the existing skeleton. -/
def ofMap {z : ι} {E : FGModuleCat.{w} R} (f : σ.obj z ⟶ E)
    (hE : IsFiniteLength R E)
    (hal : IsLeftAlmostSplit f) (hmin : IsLeftMinimal f) :
    σ.MinimalLeftAlmostSplitDecomposition z :=
  let n := (σ.decomposes E).choose
  let a := (σ.decomposes E).choose_spec.choose
  let e := (σ.decomposes E).choose_spec.choose_spec.some
  { middle := E
    finiteLength := hE
    map := f
    leftAlmostSplit := hal
    leftMinimal := hmin
    index := FintypeCat.of (Fin n)
    label := a
    decomposition := e }

/-- Any left almost-split morphism with finite-length middle term can be
replaced by a minimal one.  This is the dual least-length image argument to
`exists_of_rightAlmostSplit_of_finiteLength`. -/
theorem exists_of_leftAlmostSplit_of_finiteLength
    {z : ι} {E : FGModuleCat.{w} R}
    (f : σ.obj z ⟶ E) (hf : IsLeftAlmostSplit f)
    (hE : IsFiniteLength R E) :
    Nonempty (σ.MinimalLeftAlmostSplitDecomposition z) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ (E' : FGModuleCat.{w} R) (f' : σ.obj z ⟶ E'),
      IsFiniteLength R E' ∧ IsLeftAlmostSplit f' ∧
        (Module.length R E').toNat = n
  have hP : ∃ n, P n :=
    ⟨(Module.length R E).toNat, E, f, hE, hf, rfl⟩
  let n : ℕ := Nat.find hP
  obtain ⟨Emin, fmin, hEmin, hfmin, hlength⟩ := Nat.find_spec hP
  have hminimal : IsLeftMinimal fmin := by
    intro e he
    by_contra hnotiso
    let I : FGModuleCat.{w} R := Abelian.image e
    let i : I ⟶ Emin := Abelian.image.ι e
    let q : Emin ⟶ I := Abelian.factorThruImage e
    let fI : σ.obj z ⟶ I := fmin ≫ q
    obtain ⟨hIfinite, hlt⟩ :=
      image_finiteLength_and_length_toNat_lt hEmin e hnotiso
    have hfI : IsLeftAlmostSplit fI := by
      constructor
      · intro hsplit
        obtain ⟨sm⟩ := hsplit.exists_splitMono
        apply hfmin.not_isSplitMono
        exact IsSplitMono.mk'
          { retraction := q ≫ sm.retraction
            id := by simpa only [fI, Category.assoc] using sm.id }
      · intro X g hg
        obtain ⟨h, hh⟩ := hfmin.factors g hg
        refine ⟨i ≫ h, ?_⟩
        calc
          fI ≫ (i ≫ h) = fmin ≫ (q ≫ i) ≫ h := by
            simp only [fI, Category.assoc]
          _ = fmin ≫ e ≫ h := by rw [Abelian.image.fac]
          _ = fmin ≫ h := by rw [← Category.assoc, he]
          _ = g := hh
    have hPI : P (Module.length R I).toNat :=
      ⟨I, fI, hIfinite, hfI, rfl⟩
    have hle : n ≤ (Module.length R I).toNat := by
      dsimp only [n]
      exact Nat.find_min' hP hPI
    rw [hlength] at hlt
    exact Nat.not_lt_of_ge hle hlt
  exact ⟨ofMap σ fmin hEmin hfmin hminimal⟩

end MinimalLeftAlmostSplitDecomposition

/-- A legal mixed quotient-side two-point deletion: `p` is top
split-projective, `z` is not, the labels are distinct, and their complement
is quotient-closed. -/
structure IsLegalQMixedDeletion (p z : ι) : Prop where
  ne : p ≠ z
  projective : σ.IsRelativeSplitProjective Set.univ p
  not_projective : ¬ σ.IsRelativeSplitProjective Set.univ z
  closed : σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ

/-- The dual notion of a legal mixed submodule-side deletion. -/
structure IsLegalSMixedDeletion (z i : ι) : Prop where
  ne : z ≠ i
  not_injective : ¬ σ.IsRelativeSplitInjective Set.univ z
  injective : σ.IsRelativeSplitInjective Set.univ i
  closed : σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ

/-- The existence-level AR correspondence for a chosen right almost-split
middle decomposition: a label occurs in the middle exactly when there is an
irreducible map from that indecomposable to the end term. -/
def HasRightSummandIrreducibleCorrespondence {z : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition z) : Prop :=
  ∀ x : ι,
    (∃ t : A.index, A.label t = x) ↔
      HasIrreducibleMorphism (σ.obj x) (σ.obj z)

/-- The dual existence-level AR correspondence for a chosen left
almost-split middle decomposition. -/
def HasLeftSummandIrreducibleCorrespondence {z : ι}
    (A : σ.MinimalLeftAlmostSplitDecomposition z) : Prop :=
  ∀ x : ι,
    (∃ t : A.index, A.label t = x) ↔
      HasIrreducibleMorphism (σ.obj z) (σ.obj x)

namespace MinimalRightAlmostSplitDecomposition

variable {σ}

/-- The indecomposable summands of a minimal right almost-split middle term
are exactly the sources of irreducible morphisms to its endpoint.

For an occurring summand, right minimality is applied to the rank-one
perturbation which replaces that coordinate by a supplied factorization.
Conversely, right almost-splitness factors an irreducible morphism through
the middle; irreducibility makes the first factor split monic, and retract
support detects the corresponding label. -/
theorem summandIrreducibleCorrespondence {z : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition z) :
    σ.HasRightSummandIrreducibleCorrespondence A := by
  intro x
  constructor
  · rintro ⟨t, rfl⟩
    let F : A.index → FGModuleCat.{w} R :=
      fun j ↦ σ.obj (A.label j)
    let inc : F t ⟶ A.middle :=
      biproduct.ι F t ≫ A.decomposition.inv
    let proj : A.middle ⟶ F t :=
      A.decomposition.hom ≫ biproduct.π F t
    let g : F t ⟶ σ.obj z := inc ≫ A.map
    have hincproj : inc ≫ proj = 𝟙 (F t) := by
      simp [inc, proj, Category.assoc]
    have hnotepi : ¬ IsSplitEpi g := by
      intro hg
      apply A.rightAlmostSplit.not_isSplitEpi
      obtain ⟨se⟩ := hg.exists_splitEpi
      exact IsSplitEpi.mk'
        { section_ := se.section_ ≫ inc
          id := by
            simpa only [g, Category.assoc] using se.id }
    have hnotmono : ¬ IsSplitMono g := by
      intro hg
      letI : IsSplitMono g := hg
      exact hnotepi
        (isSplitEpi_of_isSplitMono_between_obj σ g)
    refine ⟨g, ⟨hnotmono, hnotepi, ?_⟩⟩
    intro M a b hab
    by_cases hb : IsSplitEpi b
    · exact Or.inr hb
    · obtain ⟨c, hc⟩ := A.rightAlmostSplit.factors b hb
      let e : A.middle ⟶ A.middle :=
        𝟙 A.middle + proj ≫ (a ≫ c - inc)
      have hefix : e ≫ A.map = A.map := by
        dsimp only [e]
        rw [Preadditive.add_comp, Category.id_comp,
          Category.assoc, Preadditive.sub_comp]
        have hac : (a ≫ c) ≫ A.map = g := by
          rw [Category.assoc, hc, hab]
        rw [hac]
        change A.map + proj ≫ (g - g) = A.map
        simp
      have hince : inc ≫ e = a ≫ c := by
        dsimp only [e]
        rw [Preadditive.comp_add, Category.comp_id,
          ← Category.assoc, hincproj, Category.id_comp]
        abel
      letI : IsIso e := A.rightMinimal e hefix
      exact Or.inl (IsSplitMono.mk'
        { retraction := c ≫ inv e ≫ proj
          id := by
            calc
              a ≫ (c ≫ inv e ≫ proj) =
                  (a ≫ c) ≫ inv e ≫ proj := by
                    simp only [Category.assoc]
              _ = (inc ≫ e) ≫ inv e ≫ proj := by
                    rw [hince]
              _ = 𝟙 (F t) := by
                    simp only [Category.assoc,
                      IsIso.hom_inv_id_assoc, hincproj] })
  · rintro ⟨g, hg⟩
    obtain ⟨h, hh⟩ :=
      A.rightAlmostSplit.factors g hg.not_isSplitEpi
    have hsplit : IsSplitMono h :=
      (hg.factorization h A.map hh).resolve_right
        A.rightAlmostSplit.not_isSplitEpi
    obtain ⟨sm⟩ := hsplit.exists_splitMono
    let rt : Retract (σ.obj x) A.middle :=
      { i := h
        r := sm.retraction
        retract := sm.id }
    let S : Set ι := Set.range A.label
    have hmiddle : σ.InAdd S A.middle :=
      ⟨{
        index := A.index
        label := A.label
        mem := fun t ↦ ⟨t, rfl⟩
        iso := A.decomposition }⟩
    exact index_mem_of_retract_inAdd σ rt hmiddle

/-- Coordinate-free form of the right almost-split summand correspondence:
an indecomposable is a retract of the middle term exactly when it is the
source of an irreducible morphism to the endpoint. -/
theorem indecomposableRetract_middle_iff_irreducible {z : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition z) (x : ι) :
    Nonempty (Retract (σ.obj x) A.middle) ↔
      HasIrreducibleMorphism (σ.obj x) (σ.obj z) := by
  constructor
  · rintro ⟨r⟩
    let S : Set ι := Set.range A.label
    have hmiddle : σ.InAdd S A.middle :=
      ⟨{
        index := A.index
        label := A.label
        mem := fun t ↦ ⟨t, rfl⟩
        iso := A.decomposition }⟩
    exact (A.summandIrreducibleCorrespondence x).1
      (index_mem_of_retract_inAdd σ r hmiddle)
  · intro hirr
    obtain ⟨t, ht⟩ :=
      (A.summandIrreducibleCorrespondence x).2 hirr
    subst x
    let F : A.index → FGModuleCat.{w} R :=
      fun j ↦ σ.obj (A.label j)
    exact ⟨{
      i := biproduct.ι F t ≫ A.decomposition.inv
      r := A.decomposition.hom ≫ biproduct.π F t
      retract := by
        simp
        rfl }⟩

/-- Non-top-projectivity of the end term supplies the nonsplit epimorphism
needed to show that a right almost-split map is categorically epic. -/
theorem epi_of_not_topSplitProjective {z : ι}
    (A : σ.MinimalRightAlmostSplitDecomposition z)
    (hz : ¬ σ.IsRelativeSplitProjective Set.univ z) :
    Epi A.map := by
  change ¬ ∀ P : σ.FacPresentation Set.univ (σ.obj z),
    IsSplitEpi P.map at hz
  obtain ⟨P, hP⟩ := Classical.not_forall.mp hz
  letI : Epi P.map := P.epi
  exact A.rightAlmostSplit.epi_of_nonsplit_epi P.map hP

end MinimalRightAlmostSplitDecomposition

namespace MinimalLeftAlmostSplitDecomposition

variable {σ}

/-- The indecomposable summands of a minimal left almost-split middle term
are exactly the targets of irreducible morphisms from its endpoint. -/
theorem summandIrreducibleCorrespondence {z : ι}
    (A : σ.MinimalLeftAlmostSplitDecomposition z) :
    σ.HasLeftSummandIrreducibleCorrespondence A := by
  intro x
  constructor
  · rintro ⟨t, rfl⟩
    let F : A.index → FGModuleCat.{w} R :=
      fun j ↦ σ.obj (A.label j)
    let inc : F t ⟶ A.middle :=
      biproduct.ι F t ≫ A.decomposition.inv
    let proj : A.middle ⟶ F t :=
      A.decomposition.hom ≫ biproduct.π F t
    let g : σ.obj z ⟶ F t := A.map ≫ proj
    have hincproj : inc ≫ proj = 𝟙 (F t) := by
      simp [inc, proj, Category.assoc]
    have hnotmono : ¬ IsSplitMono g := by
      intro hg
      apply A.leftAlmostSplit.not_isSplitMono
      obtain ⟨sm⟩ := hg.exists_splitMono
      exact IsSplitMono.mk'
        { retraction := proj ≫ sm.retraction
          id := by
            simpa only [g, Category.assoc] using sm.id }
    have hnotepi : ¬ IsSplitEpi g := by
      intro hg
      letI : IsSplitEpi g := hg
      exact hnotmono
        (isSplitMono_of_isSplitEpi_between_obj σ g)
    refine ⟨g, ⟨hnotmono, hnotepi, ?_⟩⟩
    intro M a b hab
    by_cases ha : IsSplitMono a
    · exact Or.inl ha
    · obtain ⟨c, hc⟩ := A.leftAlmostSplit.factors a ha
      let e : A.middle ⟶ A.middle :=
        𝟙 A.middle + (c ≫ b - proj) ≫ inc
      have hefix : A.map ≫ e = A.map := by
        dsimp only [e]
        rw [Preadditive.comp_add, Category.comp_id,
          ← Category.assoc, Preadditive.comp_sub]
        have hcb : A.map ≫ (c ≫ b) = g := by
          rw [← Category.assoc, hc, hab]
        rw [hcb]
        change A.map + (g - g) ≫ inc = A.map
        simp
      have heproj : e ≫ proj = c ≫ b := by
        dsimp only [e]
        rw [Preadditive.add_comp, Category.id_comp,
          Category.assoc, hincproj, Category.comp_id]
        abel
      letI : IsIso e := A.leftMinimal e hefix
      exact Or.inr (IsSplitEpi.mk'
        { section_ := inc ≫ inv e ≫ c
          id := by
            calc
              (inc ≫ inv e ≫ c) ≫ b =
                  inc ≫ inv e ≫ (c ≫ b) := by
                    simp only [Category.assoc]
              _ = inc ≫ inv e ≫ (e ≫ proj) := by
                    rw [← heproj]
              _ = 𝟙 (F t) := by
                    simp only [IsIso.inv_hom_id_assoc, hincproj] })
  · rintro ⟨g, hg⟩
    obtain ⟨h, hh⟩ :=
      A.leftAlmostSplit.factors g hg.not_isSplitMono
    have hsplit : IsSplitEpi h :=
      (hg.factorization A.map h hh).resolve_left
        A.leftAlmostSplit.not_isSplitMono
    obtain ⟨se⟩ := hsplit.exists_splitEpi
    let rt : Retract (σ.obj x) A.middle :=
      { i := se.section_
        r := h
        retract := se.id }
    let S : Set ι := Set.range A.label
    have hmiddle : σ.InAdd S A.middle :=
      ⟨{
        index := A.index
        label := A.label
        mem := fun t ↦ ⟨t, rfl⟩
        iso := A.decomposition }⟩
    exact index_mem_of_retract_inAdd σ rt hmiddle

/-- Non-top-injectivity of the start term supplies the nonsplit monomorphism
needed to show that a left almost-split map is categorically monic. -/
theorem mono_of_not_topSplitInjective {z : ι}
    (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (hz : ¬ σ.IsRelativeSplitInjective Set.univ z) :
    Mono A.map := by
  change ¬ ∀ P : σ.SubPresentation Set.univ (σ.obj z),
    Nonempty (SplitMono P.map) at hz
  obtain ⟨P, hP⟩ := Classical.not_forall.mp hz
  letI : Mono P.map := P.mono
  apply A.leftAlmostSplit.mono_of_nonsplit_mono P.map
  intro hsplit
  exact hP hsplit.exists_splitMono

end MinimalLeftAlmostSplitDecomposition

/-- Core quotient-side forcing lemma.  For a legal mixed deletion, if the
end label `z` does not occur in the chosen right almost-split middle, then
the deleted projective label `p` must occur there.

Minimality is recorded in `A`; this elementary forcing step uses only its
right almost-split field. -/
theorem deletedProjective_mem_rightAlmostSplitMiddle
    {p z : ι} (hlegal : σ.IsLegalQMixedDeletion p z)
    (A : σ.MinimalRightAlmostSplitDecomposition z)
    (hz_middle : ¬ ∃ t : A.index, A.label t = z) :
    ∃ t : A.index, A.label t = p := by
  by_contra hp_middle
  let C : Set ι := ({p, z} : Set ι)ᶜ
  have hlabel : ∀ t : A.index, A.label t ∈ C := by
    intro t
    simp only [C, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    intro ht
    rcases ht with ht | ht
    · exact hp_middle ⟨t, ht⟩
    · exact hz_middle ⟨t, ht⟩
  letI : Epi A.map :=
    A.epi_of_not_topSplitProjective hlegal.not_projective
  let P : σ.FacPresentation C (σ.obj z) :=
    { index := A.index
      label := A.label
      mem := hlabel
      map := A.decomposition.inv ≫ A.map
      epi := inferInstance }
  have hzq : z ∈ σ.qSet C := ⟨P⟩
  have hclosed : σ.qSet C = C := by
    change σ.qClosure C = C
    exact hlegal.closed.closure_eq
  have hzC : z ∈ C := by
    rw [← hclosed]
    exact hzq
  simp only [C, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_true, not_true_eq_false] at hzC

/-- Core dual forcing lemma. -/
theorem deletedInjective_mem_leftAlmostSplitMiddle
    {z i : ι} (hlegal : σ.IsLegalSMixedDeletion z i)
    (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (hz_middle : ¬ ∃ t : A.index, A.label t = z) :
    ∃ t : A.index, A.label t = i := by
  by_contra hi_middle
  let C : Set ι := ({z, i} : Set ι)ᶜ
  have hlabel : ∀ t : A.index, A.label t ∈ C := by
    intro t
    simp only [C, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    intro ht
    rcases ht with ht | ht
    · exact hz_middle ⟨t, ht⟩
    · exact hi_middle ⟨t, ht⟩
  letI : Mono A.map :=
    A.mono_of_not_topSplitInjective hlegal.not_injective
  let P : σ.SubPresentation C (σ.obj z) :=
    { index := A.index
      label := A.label
      mem := hlabel
      map := A.map ≫ A.decomposition.hom
      mono := inferInstance }
  have hzs : z ∈ σ.sSet C := ⟨P⟩
  have hclosed : σ.sSet C = C := by
    change σ.sClosure C = C
    exact hlegal.closed.closure_eq
  have hzC : z ∈ C := by
    rw [← hclosed]
    exact hzs
  simp only [C, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, true_or, not_true_eq_false] at hzC

/-- With the standard existence-level AR correspondence and the finite-length
no-loop theorem above, a legal mixed quotient deletion forces the projective
label to occur in the minimal right almost-split middle. -/
theorem deletedProjective_mem_rightAlmostSplitMiddle_of_correspondence
    {p z : ι} (hlegal : σ.IsLegalQMixedDeletion p z)
    (A : σ.MinimalRightAlmostSplitDecomposition z)
    (hcorr : σ.HasRightSummandIrreducibleCorrespondence A) :
    ∃ t : A.index, A.label t = p := by
  apply deletedProjective_mem_rightAlmostSplitMiddle σ hlegal A
  intro hz
  exact (hasNoIrreducibleEndomorphism_obj σ z) ((hcorr z).1 hz)

/-- Dual middle-term forcing theorem under the left AR correspondence and
the finite-length no-loop theorem. -/
theorem deletedInjective_mem_leftAlmostSplitMiddle_of_correspondence
    {z i : ι} (hlegal : σ.IsLegalSMixedDeletion z i)
    (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (hcorr : σ.HasLeftSummandIrreducibleCorrespondence A) :
    ∃ t : A.index, A.label t = i := by
  apply deletedInjective_mem_leftAlmostSplitMiddle σ hlegal A
  intro hz
  exact (hasNoIrreducibleEndomorphism_obj σ z) ((hcorr z).1 hz)

/-- Forward quotient criterion with target-absence stated directly.  This
separates the elementary closure argument from the later no-loop input. -/
theorem hasIrreducible_of_legalQMixedDeletion_of_target_not_middle
    {p z : ι} (hlegal : σ.IsLegalQMixedDeletion p z)
    (A : σ.MinimalRightAlmostSplitDecomposition z)
    (hz_middle : ¬ ∃ t : A.index, A.label t = z) :
    HasIrreducibleMorphism (σ.obj p) (σ.obj z) :=
  (A.summandIrreducibleCorrespondence p).1
    (deletedProjective_mem_rightAlmostSplitMiddle
      σ hlegal A hz_middle)

/-- Dual forward criterion with start-label absence stated directly. -/
theorem hasIrreducible_of_legalSMixedDeletion_of_source_not_middle
    {z i : ι} (hlegal : σ.IsLegalSMixedDeletion z i)
    (A : σ.MinimalLeftAlmostSplitDecomposition z)
    (hz_middle : ¬ ∃ t : A.index, A.label t = z) :
    HasIrreducibleMorphism (σ.obj z) (σ.obj i) :=
  (A.summandIrreducibleCorrespondence i).1
    (deletedInjective_mem_leftAlmostSplitMiddle
      σ hlegal A hz_middle)

/-- Forward mixed quotient criterion for a minimal right almost-split map.
Finite length excludes `z` from the middle; closedness then forces `p` into
the middle, and the proved correspondence produces an irreducible map
`p ⟶ z`. -/
theorem hasIrreducible_of_legalQMixedDeletion
    {p z : ι} (hlegal : σ.IsLegalQMixedDeletion p z)
    (A : σ.MinimalRightAlmostSplitDecomposition z) :
    HasIrreducibleMorphism (σ.obj p) (σ.obj z) := by
  apply hasIrreducible_of_legalQMixedDeletion_of_target_not_middle
    σ hlegal A
  · intro hz
    exact (hasNoIrreducibleEndomorphism_obj σ z)
      ((A.summandIrreducibleCorrespondence z).1 hz)

/-- Dual forward mixed criterion for a minimal left almost-split map. -/
theorem hasIrreducible_of_legalSMixedDeletion
    {z i : ι} (hlegal : σ.IsLegalSMixedDeletion z i)
    (A : σ.MinimalLeftAlmostSplitDecomposition z) :
    HasIrreducibleMorphism (σ.obj z) (σ.obj i) := by
  apply hasIrreducible_of_legalSMixedDeletion_of_source_not_middle
    σ hlegal A
  · intro hz
    exact (hasNoIrreducibleEndomorphism_obj σ z)
      ((A.summandIrreducibleCorrespondence z).1 hz)

/-- A minimal right almost-split decomposition and the elementary converse
give the full mixed criterion. -/
theorem qClosed_compl_pair_iff_hasIrreducible_of_rightAR
    {p z : ι} (hpz : p ≠ z)
    (hp : σ.IsRelativeSplitProjective Set.univ p)
    (hz : ¬ σ.IsRelativeSplitProjective Set.univ z)
    (A : σ.MinimalRightAlmostSplitDecomposition z) :
    σ.qClosure.IsClosed ({p, z} : Set ι)ᶜ ↔
      HasIrreducibleMorphism (σ.obj p) (σ.obj z) := by
  constructor
  · intro hclosed
    exact hasIrreducible_of_legalQMixedDeletion σ
      { ne := hpz
        projective := hp
        not_projective := hz
        closed := hclosed }
      A
  · rintro ⟨f, hf⟩
    exact qClosed_compl_pair_of_topSplitProjective_irreducible
      σ hp hpz f hf

/-- Dual full mixed criterion under a minimal left almost-split
decomposition. -/
theorem sClosed_compl_pair_iff_hasIrreducible_of_leftAR
    {z i : ι} (hzi : z ≠ i)
    (hz : ¬ σ.IsRelativeSplitInjective Set.univ z)
    (hi : σ.IsRelativeSplitInjective Set.univ i)
    (A : σ.MinimalLeftAlmostSplitDecomposition z) :
    σ.sClosure.IsClosed ({z, i} : Set ι)ᶜ ↔
      HasIrreducibleMorphism (σ.obj z) (σ.obj i) := by
  constructor
  · intro hclosed
    exact hasIrreducible_of_legalSMixedDeletion σ
      { ne := hzi
        not_injective := hz
        injective := hi
        closed := hclosed }
      A
  · rintro ⟨f, hf⟩
    exact sClosed_compl_pair_of_irreducible_topSplitInjective
      σ hi hzi f hf

end IndecomposableSkeleton

end MBDVendor.QSE
