module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Split morphisms in an idempotent-complete preadditive category

This file constructs the complementary summand of a split monomorphism, and
dually of a split epimorphism, directly by splitting the complementary
idempotent.  No kernel or cokernel is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section SplitMono

variable {X Y : C} (f : X ⟶ Y) [IsSplitMono f]

/-- A splitting of the idempotent complementary to a split monomorphism. -/
structure SplitMonoComplement where
  /-- The complementary object. -/
  complement : C
  /-- Inclusion of the complementary object. -/
  inclusion : complement ⟶ Y
  /-- Projection onto the complementary object. -/
  projection : Y ⟶ complement
  inclusion_projection : inclusion ≫ projection = 𝟙 complement
  projection_inclusion :
    projection ≫ inclusion = 𝟙 Y - retraction f ≫ f

/-- An idempotent-complete preadditive category supplies a complement to every
split monomorphism, by splitting `𝟙 Y - retraction f ≫ f`. -/
def splitMonoComplement [IsIdempotentComplete C] :
    SplitMonoComplement f :=
  Classical.choice <| by
    have hIdem :
        (𝟙 Y - retraction f ≫ f) ≫ (𝟙 Y - retraction f ≫ f) =
          𝟙 Y - retraction f ≫ f := by
      simp
    obtain ⟨Z, i, p, hi, hp⟩ :=
      IsIdempotentComplete.idempotents_split Y
        (𝟙 Y - retraction f ≫ f) hIdem
    exact
      ⟨{ complement := Z
         inclusion := i
         projection := p
         inclusion_projection := hi
         projection_inclusion := hp }⟩

namespace SplitMonoComplement

variable {X Y : C} {f : X ⟶ Y} [hf : IsSplitMono f]

@[reassoc (attr := simp)]
lemma f_projection (d : SplitMonoComplement f) : f ≫ d.projection = 0 := by
  letI : IsSplitMono d.inclusion :=
    IsSplitMono.mk'
      { retraction := d.projection, id := d.inclusion_projection }
  rw [← cancel_mono d.inclusion]
  simp [Category.assoc, d.projection_inclusion]

@[reassoc (attr := simp)]
lemma inclusion_retraction (d : SplitMonoComplement f) :
    d.inclusion ≫ retraction f = 0 := by
  letI : IsSplitEpi d.projection :=
    IsSplitEpi.mk'
      { section_ := d.inclusion, id := d.inclusion_projection }
  rw [← cancel_epi d.projection]
  simp only [comp_zero]
  rw [← Category.assoc, d.projection_inclusion]
  simp

lemma total (d : SplitMonoComplement f) :
    retraction f ≫ f + d.projection ≫ d.inclusion = 𝟙 Y := by
  rw [d.projection_inclusion]
  abel

/-- The chosen ambient object `Y` as the biproduct of the source and the
complement. -/
@[simps]
def binaryBicone (d : SplitMonoComplement f) :
    BinaryBicone X d.complement where
  pt := Y
  fst := retraction f
  snd := d.projection
  inl := f
  inr := d.inclusion
  inl_fst := IsSplitMono.id f
  inl_snd := d.f_projection
  inr_fst := d.inclusion_retraction
  inr_snd := d.inclusion_projection

/-- The preceding bicone is a genuine binary biproduct, without assuming that
the category has binary biproducts globally. -/
def isBilimitBinaryBicone (d : SplitMonoComplement f) :
    d.binaryBicone.IsBilimit :=
  isBinaryBilimitOfTotal d.binaryBicone d.total

/-- The split short complex `X → Y → complement` attached to a split
monomorphism. -/
def shortComplex (d : SplitMonoComplement f) : ShortComplex C :=
  ShortComplex.mk f d.projection d.f_projection

/-- The complement data give Mathlib's native short-complex splitting. -/
def splitting (d : SplitMonoComplement f) : d.shortComplex.Splitting where
  r := hf.exists_splitMono.some.retraction
  s := d.inclusion
  f_r := hf.exists_splitMono.some.id
  s_g := d.inclusion_projection
  id := d.total

end SplitMonoComplement

end SplitMono

section SplitEpi

variable {X Y : C} (g : X ⟶ Y) [IsSplitEpi g]

/-- A splitting of the idempotent complementary to a split epimorphism. -/
structure SplitEpiComplement where
  /-- The complementary object. -/
  complement : C
  /-- Inclusion of the complementary object. -/
  inclusion : complement ⟶ X
  /-- Projection onto the complementary object. -/
  projection : X ⟶ complement
  inclusion_projection : inclusion ≫ projection = 𝟙 complement
  projection_inclusion :
    projection ≫ inclusion = 𝟙 X - g ≫ section_ g

/-- An idempotent-complete preadditive category supplies a complement to every
split epimorphism, by splitting `𝟙 X - g ≫ section_ g`. -/
def splitEpiComplement [IsIdempotentComplete C] :
    SplitEpiComplement g :=
  Classical.choice <| by
    have hIdem :
        (𝟙 X - g ≫ section_ g) ≫ (𝟙 X - g ≫ section_ g) =
          𝟙 X - g ≫ section_ g := by
      simp
    obtain ⟨Z, i, p, hi, hp⟩ :=
      IsIdempotentComplete.idempotents_split X
        (𝟙 X - g ≫ section_ g) hIdem
    exact
      ⟨{ complement := Z
         inclusion := i
         projection := p
         inclusion_projection := hi
         projection_inclusion := hp }⟩

namespace SplitEpiComplement

variable {X Y : C} {g : X ⟶ Y} [hg : IsSplitEpi g]

@[reassoc (attr := simp)]
lemma section_projection (d : SplitEpiComplement g) :
    section_ g ≫ d.projection = 0 := by
  letI : IsSplitMono d.inclusion :=
    IsSplitMono.mk'
      { retraction := d.projection, id := d.inclusion_projection }
  rw [← cancel_mono d.inclusion]
  simp [Category.assoc, d.projection_inclusion]

@[reassoc (attr := simp)]
lemma inclusion_g (d : SplitEpiComplement g) : d.inclusion ≫ g = 0 := by
  letI : IsSplitEpi d.projection :=
    IsSplitEpi.mk'
      { section_ := d.inclusion, id := d.inclusion_projection }
  rw [← cancel_epi d.projection]
  simp only [comp_zero]
  rw [← Category.assoc, d.projection_inclusion]
  simp

lemma total (d : SplitEpiComplement g) :
    d.projection ≫ d.inclusion + g ≫ section_ g = 𝟙 X := by
  rw [d.projection_inclusion]
  abel

/-- The chosen ambient object `X` as the biproduct of the complement and the
target. -/
@[simps]
def binaryBicone (d : SplitEpiComplement g) :
    BinaryBicone d.complement Y where
  pt := X
  fst := d.projection
  snd := g
  inl := d.inclusion
  inr := section_ g
  inl_fst := d.inclusion_projection
  inl_snd := d.inclusion_g
  inr_fst := d.section_projection
  inr_snd := IsSplitEpi.id g

/-- The preceding bicone is a genuine binary biproduct, without assuming that
the category has binary biproducts globally. -/
def isBilimitBinaryBicone (d : SplitEpiComplement g) :
    d.binaryBicone.IsBilimit :=
  isBinaryBilimitOfTotal d.binaryBicone d.total

/-- The split short complex `complement → X → Y` attached to a split
epimorphism. -/
def shortComplex (d : SplitEpiComplement g) : ShortComplex C :=
  ShortComplex.mk d.inclusion g d.inclusion_g

/-- The complement data give Mathlib's native short-complex splitting. -/
def splitting (d : SplitEpiComplement g) : d.shortComplex.Splitting where
  r := d.projection
  s := hg.exists_splitEpi.some.section_
  f_r := d.inclusion_projection
  s_g := hg.exists_splitEpi.some.id
  id := d.total

end SplitEpiComplement

end SplitEpi

end MBDVendor.QSE
