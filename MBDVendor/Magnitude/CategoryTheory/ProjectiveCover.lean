import MBDVendor.QSE.CategoryTheory.MinimalMorphism
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Categorical projective covers

A minimal projective presentation is a projective epimorphism which is right
minimal.  This file records its transport and uniqueness calculus and relates
right minimality to the essential-epimorphism characterization of projective
covers.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE

namespace MBDVendor.Magnitude

universe u v

variable {C : Type u} [Category.{v} C]

/-- A retract of a projective object is projective. -/
theorem projective_of_retract
    {P Q : C} (hP : Projective P) (i : Q ⟶ P) (r : P ⟶ Q)
    (hir : i ≫ r = 𝟙 Q) : Projective Q := by
  letI : Projective P := hP
  constructor
  intro X E f e hepi
  letI : Epi e := hepi
  obtain ⟨l, hl⟩ := Projective.factors (r ≫ f) e
  refine ⟨i ≫ l, ?_⟩
  rw [Category.assoc, hl, ← Category.assoc, hir, Category.id_comp]

/-- A projective presentation whose epimorphism is right minimal. -/
structure MinimalProjectivePresentation (X : C)
    extends ProjectivePresentation X where
  rightMinimal : IsRightMinimal f

namespace MinimalProjectivePresentation

variable {X Y : C}

instance (P : MinimalProjectivePresentation X) : Projective P.p :=
  P.toProjectivePresentation.projective

instance (P : MinimalProjectivePresentation X) : Epi P.f :=
  P.toProjectivePresentation.epi

/-- Postcomposing the cover map with an isomorphism gives a minimal
projective presentation of the new target. -/
def postIso (P : MinimalProjectivePresentation X) (e : X ≅ Y) :
    MinimalProjectivePresentation Y where
  p := P.p
  f := P.f ≫ e.hom
  rightMinimal := P.rightMinimal.postcomp_iso e

/-- Precomposing a projective cover by an isomorphism gives the same minimal
projective presentation in new source coordinates. -/
noncomputable def preIso [Preadditive C] {Z : C}
    (P : MinimalProjectivePresentation X) (e : Z ≅ P.p) :
    MinimalProjectivePresentation X := by
  letI : Projective Z := Projective.of_iso e.symm inferInstance
  exact
    { p := Z
      f := e.hom ≫ P.f
      rightMinimal := P.rightMinimal.precomp_splitMono e.hom }

/-- The projective sources of two minimal projective presentations of the
same object are isomorphic compatibly with their cover maps. -/
noncomputable def objectIso
    (P Q : MinimalProjectivePresentation X) : P.p ≅ Q.p := by
  let a : P.p ⟶ Q.p := Projective.factorThru P.f Q.f
  let b : Q.p ⟶ P.p := Projective.factorThru Q.f P.f
  have ha : a ≫ Q.f = P.f := Projective.factorThru_comp P.f Q.f
  have hb : b ≫ P.f = Q.f := Projective.factorThru_comp Q.f P.f
  haveI hab : IsIso (a ≫ b) := P.rightMinimal (a ≫ b) (by
    rw [Category.assoc, hb, ha])
  haveI hba : IsIso (b ≫ a) := Q.rightMinimal (b ≫ a) (by
    rw [Category.assoc, ha, hb])
  letI : IsIso a := isIso_of_isIso_comp_both a b
  exact asIso a

@[reassoc]
theorem objectIso_hom_comp
    (P Q : MinimalProjectivePresentation X) :
    (P.objectIso Q).hom ≫ Q.f = P.f :=
  Projective.factorThru_comp P.f Q.f

/-- Minimal projective presentations of isomorphic targets have isomorphic
projective sources. -/
noncomputable def objectIsoOfTargetIso
    (P : MinimalProjectivePresentation X)
    (Q : MinimalProjectivePresentation Y) (e : X ≅ Y) : P.p ≅ Q.p :=
  (P.postIso e).objectIso Q

@[reassoc]
theorem objectIsoOfTargetIso_hom_comp
    (P : MinimalProjectivePresentation X)
    (Q : MinimalProjectivePresentation Y) (e : X ≅ Y) :
    (P.objectIsoOfTargetIso Q e).hom ≫ Q.f = P.f ≫ e.hom :=
  (P.postIso e).objectIso_hom_comp Q

end MinimalProjectivePresentation

section Abelian

variable [Abelian C]

/-- A two-step minimal projective presentation consists of projective covers
of an object and of the kernel of its cover. -/
structure TwoStepMinimalProjectivePresentation (X : C) where
  augmentation : MinimalProjectivePresentation X
  syzygyPresentation :
    MinimalProjectivePresentation (kernel augmentation.f)

namespace TwoStepMinimalProjectivePresentation

variable {X : C}

/-- The first differential `P₁ ⟶ P₀`. -/
def differential (P : TwoStepMinimalProjectivePresentation X) :
    P.syzygyPresentation.p ⟶ P.augmentation.p :=
  P.syzygyPresentation.f ≫ kernel.ι P.augmentation.f

@[simp]
theorem differential_comp_augmentation
    (P : TwoStepMinimalProjectivePresentation X) :
    P.differential ≫ P.augmentation.f = 0 := by
  simp [differential]

/-- The associated exact projective complex `P₁ ⟶ P₀ ⟶ X`. -/
def presentationComplex (P : TwoStepMinimalProjectivePresentation X) :
    ShortComplex C :=
  ShortComplex.mk P.differential P.augmentation.f
    P.differential_comp_augmentation

/-- The stored cover of the first syzygy certifies exactness of the
two-step projective presentation. -/
theorem presentationComplex_exact
    (P : TwoStepMinimalProjectivePresentation X) :
    P.presentationComplex.Exact := by
  change (ShortComplex.mk P.differential P.augmentation.f
    P.differential_comp_augmentation).Exact
  apply (ShortComplex.exact_iff_epi_kernel_lift _).2
  have hLift :
      kernel.lift P.augmentation.f P.differential
          P.differential_comp_augmentation =
        P.syzygyPresentation.f := by
    apply (cancel_mono (kernel.ι P.augmentation.f)).1
    simp [differential]
  rw [hLift]
  infer_instance

/-- The compatible isomorphism between the augmentation sources of two
two-step minimal projective presentations. -/
noncomputable def augmentationObjectIso
    (P Q : TwoStepMinimalProjectivePresentation X) :
    P.augmentation.p ≅ Q.augmentation.p :=
  P.augmentation.objectIso Q.augmentation

/-- The augmentation-source comparison induces the corresponding
isomorphism between the first syzygies. -/
noncomputable def kernelObjectIso
    (P Q : TwoStepMinimalProjectivePresentation X) :
    kernel P.augmentation.f ≅ kernel Q.augmentation.f :=
  kernel.mapIso (f := P.augmentation.f) Q.augmentation.f
    (P.augmentationObjectIso Q) (Iso.refl X)
    (by
      simpa [augmentationObjectIso] using
        (P.augmentation.objectIso_hom_comp Q.augmentation).symm)

/-- The compatible isomorphism between the first projective sources of two
two-step minimal projective presentations. -/
noncomputable def syzygyObjectIso
    (P Q : TwoStepMinimalProjectivePresentation X) :
    P.syzygyPresentation.p ≅ Q.syzygyPresentation.p :=
  P.syzygyPresentation.objectIsoOfTargetIso Q.syzygyPresentation
    (P.kernelObjectIso Q)

@[reassoc]
theorem syzygyObjectIso_hom_comp
    (P Q : TwoStepMinimalProjectivePresentation X) :
    (P.syzygyObjectIso Q).hom ≫ Q.syzygyPresentation.f =
      P.syzygyPresentation.f ≫ (P.kernelObjectIso Q).hom :=
  P.syzygyPresentation.objectIsoOfTargetIso_hom_comp
    Q.syzygyPresentation (P.kernelObjectIso Q)

/-- The two compatible source isomorphisms intertwine the first
differentials. -/
@[reassoc]
theorem syzygyObjectIso_hom_comp_differential
    (P Q : TwoStepMinimalProjectivePresentation X) :
    (P.syzygyObjectIso Q).hom ≫ Q.differential =
      P.differential ≫ (P.augmentationObjectIso Q).hom := by
  rw [differential, differential, ← Category.assoc,
    P.syzygyObjectIso_hom_comp]
  simp [kernelObjectIso, augmentationObjectIso]

/-- The compatible isomorphism between augmentation sources when the
presented targets are isomorphic. -/
noncomputable def augmentationObjectIsoOfTargetIso {Y : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (Q : TwoStepMinimalProjectivePresentation Y) (e : X ≅ Y) :
    P.augmentation.p ≅ Q.augmentation.p :=
  P.augmentation.objectIsoOfTargetIso Q.augmentation e

/-- An isomorphism of presented targets and the induced augmentation-source
isomorphism identify the first syzygies. -/
noncomputable def kernelObjectIsoOfTargetIso {Y : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (Q : TwoStepMinimalProjectivePresentation Y) (e : X ≅ Y) :
    kernel P.augmentation.f ≅ kernel Q.augmentation.f :=
  kernel.mapIso (f := P.augmentation.f) Q.augmentation.f
    (P.augmentationObjectIsoOfTargetIso Q e) e
    (by
      simpa [augmentationObjectIsoOfTargetIso] using
        (P.augmentation.objectIsoOfTargetIso_hom_comp
          Q.augmentation e).symm)

/-- The compatible isomorphism between the first projective sources when
the presented targets are isomorphic. -/
noncomputable def syzygyObjectIsoOfTargetIso {Y : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (Q : TwoStepMinimalProjectivePresentation Y) (e : X ≅ Y) :
    P.syzygyPresentation.p ≅ Q.syzygyPresentation.p :=
  P.syzygyPresentation.objectIsoOfTargetIso Q.syzygyPresentation
    (P.kernelObjectIsoOfTargetIso Q e)

@[reassoc]
theorem syzygyObjectIsoOfTargetIso_hom_comp {Y : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (Q : TwoStepMinimalProjectivePresentation Y) (e : X ≅ Y) :
    (P.syzygyObjectIsoOfTargetIso Q e).hom ≫
        Q.syzygyPresentation.f =
      P.syzygyPresentation.f ≫
        (P.kernelObjectIsoOfTargetIso Q e).hom :=
  P.syzygyPresentation.objectIsoOfTargetIso_hom_comp
    Q.syzygyPresentation (P.kernelObjectIsoOfTargetIso Q e)

/-- Isomorphic targets of two-step minimal projective presentations induce
compatible isomorphisms of both projective sources. -/
@[reassoc]
theorem syzygyObjectIsoOfTargetIso_hom_comp_differential {Y : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (Q : TwoStepMinimalProjectivePresentation Y) (e : X ≅ Y) :
    (P.syzygyObjectIsoOfTargetIso Q e).hom ≫ Q.differential =
      P.differential ≫
        (P.augmentationObjectIsoOfTargetIso Q e).hom := by
  rw [differential, differential, ← Category.assoc,
    P.syzygyObjectIsoOfTargetIso_hom_comp Q e]
  simp [kernelObjectIsoOfTargetIso, augmentationObjectIsoOfTargetIso]

/-- Replace both projective sources of a two-step minimal presentation by
isomorphic coordinate objects. -/
noncomputable def recoordinate {P₀ P₁ : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (e₀ : P₀ ≅ P.augmentation.p)
    (e₁ : P₁ ≅ P.syzygyPresentation.p) :
    TwoStepMinimalProjectivePresentation X := by
  let A := P.augmentation.preIso e₀
  let eK : kernel A.f ≅ kernel P.augmentation.f :=
    kernel.mapIso (f := A.f) P.augmentation.f e₀ (Iso.refl X) (by
      dsimp [A, MinimalProjectivePresentation.preIso]
      simp)
  exact
    { augmentation := A
      syzygyPresentation :=
        (P.syzygyPresentation.postIso eK.symm).preIso e₁ }

set_option backward.isDefEq.respectTransparency false in
/-- Recoordinating both projective sources conjugates the first differential
by the two source isomorphisms. -/
theorem recoordinate_differential {P₀ P₁ : C}
    (P : TwoStepMinimalProjectivePresentation X)
    (e₀ : P₀ ≅ P.augmentation.p)
    (e₁ : P₁ ≅ P.syzygyPresentation.p) :
    (P.recoordinate e₀ e₁).differential =
      e₁.hom ≫ P.differential ≫ e₀.inv := by
  change
    (e₁.hom ≫ P.syzygyPresentation.f ≫
        (kernel.mapIso (f := e₀.hom ≫ P.augmentation.f)
          P.augmentation.f e₀ (Iso.refl X) (by simp)).inv) ≫
      kernel.ι (e₀.hom ≫ P.augmentation.f) =
        e₁.hom ≫
          (P.syzygyPresentation.f ≫ kernel.ι P.augmentation.f) ≫
            e₀.inv
  simp

end TwoStepMinimalProjectivePresentation

end Abelian

/-- An epimorphism is essential if epimorphicity of a composite ending in it
forces epimorphicity of the first factor. -/
def IsEssentialEpi {X Y : C} (f : X ⟶ Y) : Prop :=
  Epi f ∧ ∀ ⦃Z : C⦄ (g : Z ⟶ X), Epi (g ≫ f) → Epi g

/-- A right-minimal epimorphism from a projective object is essential. -/
theorem isEssentialEpi_of_isRightMinimal
    {P X : C} [Projective P] (f : P ⟶ X) [Epi f]
    (hmin : IsRightMinimal f) : IsEssentialEpi f := by
  constructor
  · infer_instance
  · intro Z g hg
    letI : Epi (g ≫ f) := hg
    let l : P ⟶ Z := Projective.factorThru f (g ≫ f)
    have hl : (l ≫ g) ≫ f = f := by
      simpa only [Category.assoc] using
        Projective.factorThru_comp f (g ≫ f)
    haveI : IsIso (l ≫ g) := hmin (l ≫ g) hl
    exact epi_of_epi_fac (f := l) (g := g) rfl

/-- An essential epimorphism from a projective object is right minimal when
epic endomorphisms of the projective source are invertible. -/
theorem isRightMinimal_of_isEssentialEpi
    {P X : C} [Projective P] (f : P ⟶ X)
    (hessential : IsEssentialEpi f)
    (hendo : ∀ e : P ⟶ P, Epi e → IsIso e) : IsRightMinimal f := by
  letI : Epi f := hessential.1
  intro e he
  have hepiComp : Epi (e ≫ f) := by
    rw [he]
    infer_instance
  exact hendo e (hessential.2 e hepiComp)

/-- For an epimorphism from a projective object whose epic endomorphisms are
invertible, categorical right minimality is equivalent to essentiality. -/
theorem isEssentialEpi_iff_isRightMinimal
    {P X : C} [Projective P] (f : P ⟶ X) [Epi f] :
    (∀ e : P ⟶ P, Epi e → IsIso e) →
      (IsEssentialEpi f ↔ IsRightMinimal f) := by
  intro hendo
  constructor
  · exact fun h ↦ isRightMinimal_of_isEssentialEpi f h hendo
  · exact isEssentialEpi_of_isRightMinimal f

namespace MinimalProjectivePresentation

/-- A projective cover is a split summand of every projective epimorphism
onto the same target, compatibly with the two epimorphisms. -/
theorem exists_splitEpi_factor
    {X Q : C} (P : MinimalProjectivePresentation X)
    [Projective Q] (q : Q ⟶ X) [Epi q] :
    ∃ a : Q ⟶ P.p, IsSplitEpi a ∧ a ≫ P.f = q := by
  let a : Q ⟶ P.p := Projective.factorThru q P.f
  have ha : a ≫ P.f = q := Projective.factorThru_comp q P.f
  have hessential : IsEssentialEpi P.f :=
    isEssentialEpi_of_isRightMinimal P.f P.rightMinimal
  haveI : Epi a := hessential.2 a (by rw [ha]; infer_instance)
  let s : P.p ⟶ Q := Projective.factorThru (𝟙 P.p) a
  have hs : s ≫ a = 𝟙 P.p := Projective.factorThru_comp (𝟙 P.p) a
  exact ⟨a, IsSplitEpi.mk' { section_ := s, id := hs }, ha⟩

end MinimalProjectivePresentation

end MBDVendor.Magnitude
