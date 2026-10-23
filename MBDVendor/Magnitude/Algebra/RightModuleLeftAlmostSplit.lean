module

public import MBDVendor.Magnitude.Algebra.RightModuleRightTau
public import MBDVendor.Magnitude.CategoryTheory.AlmostSplitCokernel
public import MBDVendor.QSE.RepresentationTheory.ContragredientDuality

/-!
# Left almost-split monomorphisms for finite-dimensional modules

Finite-dimensional contragredient duality transfers finite projective
presentations to finite injective copresentations.  Consequently the chosen
left almost-split map at a noninjective indecomposable is monic.  Its
cokernel projection is then the dual Auslander--Reiten map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MBDVendor.QSE
open scoped ModuleCat.Algebra

namespace MBDVendor.Magnitude

universe u

/-- Module projectivity gives categorical projectivity in the finitely
generated subcategory. -/
theorem fgProjective_of_moduleProjective
    {R : Type u} [Ring R]
    (X : FGModuleCat.{u} R) (h : Module.Projective R X) :
    Projective X := by
  letI : Module.Projective R X := h
  constructor
  intro E Y f e _hepi
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property e.hom.hom f.hom.hom
      ((IndecomposableSkeleton.fg_epi_iff_surjective e).1 inferInstance)
  refine ⟨FGModuleCat.ofHom g, ?_⟩
  apply FGModuleCat.hom_ext
  exact hg

/-- Every finitely generated module has a finite free projective
presentation. -/
theorem fgModuleCat_projectivePresentation_nonempty
    {R : Type u} [Ring R] (X : FGModuleCat.{u} R) :
    Nonempty (ProjectivePresentation X) := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let P : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
  let q : P ⟶ X := FGModuleCat.ofHom p
  have hP : Projective P := by
    apply fgProjective_of_moduleProjective P
    exact Module.Projective.of_basis (Pi.basisFun R (Fin n))
  have hq : Epi q :=
    (IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
  exact ⟨{ p := P, projective := hP, f := q, epi := hq }⟩

/-- The category of finitely generated modules has enough finitely
generated projectives. -/
theorem fgModuleCat_enoughProjectives
    (R : Type u) [Ring R] :
    EnoughProjectives (FGModuleCat.{u} R) where
  presentation := fgModuleCat_projectivePresentation_nonempty

/-- Finite-dimensional contragredient duality supplies enough injectives in
the category of finitely generated modules. -/
theorem fgModuleCat_enoughInjectives
    (k R : Type u) [Field k] [Ring R] [Algebra k R]
    [FiniteDimensional k R] :
    EnoughInjectives (FGModuleCat.{u} R) := by
  letI : EnoughProjectives (FGModuleCat.{u} Rᵐᵒᵖ) :=
    fgModuleCat_enoughProjectives Rᵐᵒᵖ
  letI : EnoughInjectives (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ := inferInstance
  exact
    (Contragredient.reverseDualityEquivalence k R
      |>.enoughInjectives_iff).mp inferInstance

/-- The target of a right almost-split morphism of finitely generated
modules is indecomposable. -/
theorem rightAlmostSplit_target_isIndecomposableModule
    {R : Type u} [Ring R] {E Z : FGModuleCat.{u} R}
    (f : E ⟶ Z) (hf : IsRightAlmostSplit f) :
    Foundation.IsIndecomposableModule R Z := by
  rw [Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    letI : Subsingleton Z := hsub
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := 0
        id := by
          ext z
          exact Subsingleton.elim _ _ }
  · intro p hp
    let e : Z ⟶ Z := FGModuleCat.ofHom p
    have he : e ≫ e = e := by
      ext z
      exact DFunLike.congr_fun hp z
    by_cases hse : IsSplitEpi e
    · letI : IsSplitEpi e := hse
      have hei : e = 𝟙 Z := by
        apply (cancel_epi e).1
        rw [he, Category.comp_id]
      exact Or.inr (by
        ext z
        exact ConcreteCategory.congr_hom hei z)
    · let c : Z ⟶ Z := 𝟙 Z - e
      have hc : c ≫ c = c := by
        dsimp only [c]
        rw [Preadditive.sub_comp, Preadditive.comp_sub,
          Preadditive.comp_sub, he, Category.id_comp,
          Category.comp_id]
        abel
      by_cases hsc : IsSplitEpi c
      · letI : IsSplitEpi c := hsc
        have hci : c = 𝟙 Z := by
          apply (cancel_epi c).1
          rw [hc, Category.comp_id]
        have hezero : e = 0 := by
          change 𝟙 Z - e = 𝟙 Z at hci
          exact sub_eq_self.mp hci
        exact Or.inl (by
          ext z
          exact ConcreteCategory.congr_hom hezero z)
      · obtain ⟨a, ha⟩ := hf.factors e hse
        obtain ⟨b, hb⟩ := hf.factors c hsc
        exfalso
        apply hf.not_isSplitEpi
        exact IsSplitEpi.mk'
          { section_ := a + b
            id := by
              rw [Preadditive.add_comp, ha, hb]
              dsimp only [c]
              abel }

/-- An epic right almost-split morphism cannot end at a projective object. -/
theorem IsRightAlmostSplit.not_projective_target
    {C : Type u} [Category C] {E Z : C}
    (f : E ⟶ Z) [Epi f] (hf : IsRightAlmostSplit f) :
    ¬ Projective Z := by
  intro hZ
  letI : Projective Z := hZ
  apply hf.not_isSplitEpi
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Z) f
  exact IsSplitEpi.mk' { section_ := s, id := hs }

namespace RightModule.FiniteIndecomposableSkeleton

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- At a noninjective selected module, the chosen minimal left
almost-split map is monic. -/
theorem noninjectiveLeftAlmostSplit_mono
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)}) :
    Mono (S.minimalLeftAlmostSplitAt x.1).map := by
  letI : EnoughInjectives
      (RightModule.FinitelyGeneratedCategory A) :=
    fgModuleCat_enoughInjectives k Aᵐᵒᵖ
  let B := S.minimalLeftAlmostSplitAt x.1
  let P := (EnoughInjectives.presentation (S.fgObj x.1)).some
  apply B.leftAlmostSplit.mono_of_nonsplit_mono P.f
  intro hsplit
  let s := hsplit.exists_splitMono.some
  apply x.2
  exact Retract.injective
    { i := P.f
      r := s.retraction
      retract := s.id }

/-- The cokernel projection of the chosen noninjective left almost-split
map is right almost split. -/
theorem noninjectiveLeftCokernel_rightAlmostSplit
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)}) :
    IsRightAlmostSplit
      (cokernel.π (S.minimalLeftAlmostSplitAt x.1).map) := by
  let B := S.minimalLeftAlmostSplitAt x.1
  letI : Mono B.map := S.noninjectiveLeftAlmostSplit_mono x
  exact
    MBDVendor.Magnitude.CategoryTheory.leftAlmostSplit_cokernel_π_isRightAlmostSplit
      B.map B.leftAlmostSplit B.leftMinimal

/-- At a selected indecomposable source, the cokernel projection of a
left-almost-split monomorphism is right minimal. -/
theorem leftAlmostSplit_cokernel_π_isRightMinimal_obj
    {x : Fin S.n} {E : RightModule.FinitelyGeneratedCategory A}
    (f : S.fgObj x ⟶ E) [Mono f]
    (hf : IsLeftAlmostSplit f)
    (hq : IsRightAlmostSplit (cokernel.π f)) :
    IsRightMinimal (cokernel.π f) := by
  let sigma := S.almostSplitSkeleton
  let q := cokernel.π f
  intro e he
  have hzero : (f ≫ e) ≫ q = 0 := by
    rw [Category.assoc, he, cokernel.condition]
  let d : S.fgObj x ⟶ S.fgObj x :=
    Abelian.monoLift f (f ≫ e) hzero
  have hd : d ≫ f = f ≫ e :=
    Abelian.monoLift_comp f (f ≫ e) hzero
  have hdsplit : IsSplitMono d := by
    by_contra hdnot
    obtain ⟨h, hh⟩ := hf.factors d hdnot
    let a : E ⟶ E := e - h ≫ f
    have hfa : f ≫ a = 0 := by
      dsimp only [a]
      rw [Preadditive.comp_sub, ← Category.assoc, hh, hd]
      simp
    let t : cokernel f ⟶ E := cokernel.desc f a hfa
    have hqt : q ≫ t = a := cokernel.π_desc f a hfa
    apply hq.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := t
        id := by
          apply (cancel_epi q).1
          rw [← Category.assoc, hqt, Category.comp_id]
          dsimp only [a]
          rw [Preadditive.sub_comp, he, Category.assoc,
            cokernel.condition, comp_zero, sub_zero]
          }
  haveI hsplitMonoD : IsSplitMono d := hdsplit
  haveI hsplitEpiD : IsSplitEpi d :=
    @IndecomposableSkeleton.isSplitEpi_of_isSplitMono_between_obj
      _ _ _ _ sigma _ _ d hsplitMonoD
  haveI : IsIso d := isIso_of_mono_of_isSplitEpi d
  let T : ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
    ShortComplex.mk f q (cokernel.condition f)
  have hT : T.ShortExact :=
    { exact := T.exact_of_f_is_kernel
        (Abelian.monoIsKernelOfCokernel
          (CokernelCofork.ofπ q (cokernel.condition f))
          (cokernelIsCokernel f)) }
  let φ : T ⟶ T :=
    { τ₁ := d
      τ₂ := e
      τ₃ := 𝟙 _
      comm₁₂ := hd
      comm₂₃ := by simpa only [Category.comp_id] using he
      }
  change IsIso φ.τ₂
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hT hT

/-- The chosen noninjective left cokernel projection is right minimal. -/
theorem noninjectiveLeftCokernel_rightMinimal
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)}) :
    IsRightMinimal
      (cokernel.π (S.minimalLeftAlmostSplitAt x.1).map) := by
  let hmono : Mono (S.minimalLeftAlmostSplitAt x.1).map :=
    S.noninjectiveLeftAlmostSplit_mono x
  exact @leftAlmostSplit_cokernel_π_isRightMinimal_obj
    _ _ _ _ _ _ _ S _ _
    (S.minimalLeftAlmostSplitAt x.1).map hmono
    (S.minimalLeftAlmostSplitAt x.1).leftAlmostSplit
    (S.noninjectiveLeftCokernel_rightAlmostSplit x)

end RightModule.FiniteIndecomposableSkeleton

end MBDVendor.Magnitude
