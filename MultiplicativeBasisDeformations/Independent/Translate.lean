module

public import MultiplicativeBasisDeformations.Independent.MeshComparison

/-!
# The independent translate is the translation of `Γ_A`

The independent statement defines `τ X_i = X_t` by an almost split sequence
`0 → X_t → E → X_i → 0` of right modules, with the almost split properties
tested on finite-dimensional modules. The proof library takes the translation
from the vendored Auslander–Reiten theory: the kernel of the chosen minimal
right almost split map in the category `mod A = FGModuleCat Aᵐᵒᵖ` of finitely
generated right modules. This file proves that the two agree
(`translateCompatible`).

* The inclusion `mod A → Mod A` is fully faithful and exact, so split
  monomorphisms and epimorphisms, almost split maps and short exact sequences
  correspond.
* The vendored sequence is an almost split sequence.
* Conversely, in an almost split sequence the first map is radical, so the
  second map is right minimal; uniqueness of minimal right almost split maps
  identifies the left term with the vendored translate.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
open MBDVendor.QSE MBDVendor.QSE.CategoricalRadical

namespace MultiplicativeBasisDeformations.Statement

universe u

section RightMinimal

variable {C : Type*} [Category C] [Abelian C]

/-- In a short exact sequence with a radical first map, the second map is right
minimal. -/
theorem isRightMinimal_g_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (hf : IsRadicalMorphism S.f) : IsRightMinimal S.g := by
  intro e he
  have heZero : (e - 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
  haveI := hS.mono_f
  let q : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  haveI : Epi q := hS.exact.epi_kernelLift
  haveI : Mono q := mono_of_mono_fac (kernel.lift_ι S.g S.f S.zero)
  haveI : IsIso q := isIso_of_mono_of_epi q
  let t : S.X₂ ⟶ kernel S.g := kernel.lift S.g (e - 𝟙 S.X₂) heZero
  let l : S.X₂ ⟶ S.X₁ := t ≫ inv q
  have hl : l ≫ S.f = e - 𝟙 S.X₂ := by
    have hq : inv q ≫ S.f = kernel.ι S.g := by
      rw [IsIso.inv_comp_eq, kernel.lift_ι]
    simp only [l, Category.assoc, hq, t, kernel.lift_ι]
  have hi : IsIso (𝟙 S.X₂ - (l ≫ S.f) ≫ (-𝟙 S.X₂)) := isRadicalMorphism_precomp l hf (-𝟙 S.X₂)
  have hid : 𝟙 S.X₂ - (l ≫ S.f) ≫ (-𝟙 S.X₂) = e := by
    rw [hl]
    simp
  exact hid ▸ hi

end RightMinimal

section FG

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

/-- The inclusion of finitely generated right modules into all right modules. -/
abbrev ιFG : FGModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Aᵐᵒᵖ :=
  forget₂ (FGModuleCat.{u} Aᵐᵒᵖ) (ModuleCat.{u} Aᵐᵒᵖ)

variable (k) in
/-- A finite-dimensional right module as a finitely generated one. -/
def fgOf (M : ModuleCat.{u} Aᵐᵒᵖ) (hM : Module.Finite k M) : FGModuleCat.{u} Aᵐᵒᵖ :=
  ⟨M, Module.Finite.of_restrictScalars_finite k Aᵐᵒᵖ M⟩

variable (k) in
/-- A finitely generated right module is finite-dimensional. -/
theorem finite_of_fg (X : FGModuleCat.{u} Aᵐᵒᵖ) : Module.Finite k (ιFG.obj X) := by
  haveI : Module.Finite Aᵐᵒᵖ (ιFG.obj X) := X.2
  haveI : Module.Finite k Aᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv k)
  exact Module.Finite.trans Aᵐᵒᵖ (ιFG.obj X)

/-- The preimage of a morphism of modules under the inclusion. -/
def homFG {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f : ιFG.obj X ⟶ ιFG.obj Y) : X ⟶ Y :=
  ιFG.preimage f

@[simp] theorem map_homFG {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f : ιFG.obj X ⟶ ιFG.obj Y) :
    ιFG.map (homFG f) = f :=
  ιFG.map_preimage f

theorem isSplitMono_map_iff {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f : X ⟶ Y) :
    IsSplitMono (ιFG.map f) ↔ IsSplitMono f := by
  constructor
  · intro h
    refine IsSplitMono.mk' ⟨homFG (retraction (ιFG.map f)), ιFG.map_injective ?_⟩
    rw [ιFG.map_comp, map_homFG, IsSplitMono.id, ιFG.map_id]
  · intro h
    infer_instance

theorem isSplitEpi_map_iff {X Y : FGModuleCat.{u} Aᵐᵒᵖ} (f : X ⟶ Y) :
    IsSplitEpi (ιFG.map f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    refine IsSplitEpi.mk' ⟨homFG (section_ (ιFG.map f)), ιFG.map_injective ?_⟩
    rw [ιFG.map_comp, map_homFG, IsSplitEpi.id, ιFG.map_id]
  · intro h
    infer_instance

theorem shortExact_map_iff (T : ShortComplex (FGModuleCat.{u} Aᵐᵒᵖ)) :
    (T.map ιFG).ShortExact ↔ T.ShortExact := by
  constructor
  · intro h
    have hm : Mono (ιFG.map T.f) := h.mono_f
    have he : Epi (ιFG.map T.g) := h.epi_g
    haveI := ιFG.mono_of_mono_map hm
    haveI := ιFG.epi_of_epi_map he
    exact ShortComplex.ShortExact.mk' ((T.exact_map_iff_of_faithful ιFG).1 h.exact) inferInstance
      inferInstance
  · intro h
    exact h.map_of_exact ιFG

end FG

section Translate

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

/-- An almost split sequence of finitely generated modules is an almost split
sequence of right modules in the independent sense. -/
theorem isAlmostSplitSequence_of_fg {X Y Z : FGModuleCat.{u} Aᵐᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : f ≫ g = 0) (hSE : (ShortComplex.mk f g w).ShortExact)
    (hL : MBDVendor.QSE.IsLeftAlmostSplit f) (hR : MBDVendor.QSE.IsRightAlmostSplit g) :
    IsAlmostSplitSequence k (ιFG.map f) (ιFG.map g) where
  comp_eq_zero := by rw [← ιFG.map_comp, w, ιFG.map_zero]
  shortExact := (shortExact_map_iff (ShortComplex.mk f g w)).2 hSE
  not_isSplitMono h := hL.not_isSplitMono ((isSplitMono_map_iff f).1 h)
  not_isSplitEpi h := hR.not_isSplitEpi ((isSplitEpi_map_iff g).1 h)
  left W hW h hh := by
    let h₀ : X ⟶ fgOf k W hW := homFG (X := X) (Y := fgOf k W hW) h
    have hh₀ : ¬ IsSplitMono h₀ := fun hs ↦ hh (by
      rw [← map_homFG (X := X) (Y := fgOf k W hW) h]
      exact (isSplitMono_map_iff h₀).2 hs)
    obtain ⟨h', hh'⟩ := hL.factors h₀ hh₀
    have e := congrArg ιFG.map hh'
    have h0 : ιFG.map h₀ = h := map_homFG (X := X) (Y := fgOf k W hW) h
    rw [ιFG.map_comp, h0] at e
    exact ⟨ιFG.map h', e⟩
  right W hW h hh := by
    let h₀ : fgOf k W hW ⟶ Z := homFG (X := fgOf k W hW) (Y := Z) h
    have hh₀ : ¬ IsSplitEpi h₀ := fun hs ↦ hh (by
      rw [← map_homFG (X := fgOf k W hW) (Y := Z) h]
      exact (isSplitEpi_map_iff h₀).2 hs)
    obtain ⟨h', hh'⟩ := hR.factors h₀ hh₀
    have e := congrArg ιFG.map hh'
    have h0 : ιFG.map h₀ = h := map_homFG (X := fgOf k W hW) (Y := Z) h
    rw [ιFG.map_comp, h0] at e
    exact ⟨ιFG.map h', e⟩

/-- Conversely, an almost split sequence of right modules between finitely
generated modules is short exact with a right almost split second map there. -/
theorem fg_of_isAlmostSplitSequence {X Y Z : FGModuleCat.{u} Aᵐᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : IsAlmostSplitSequence k (ιFG.map f) (ιFG.map g)) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact ∧ ¬ IsSplitMono f ∧
      MBDVendor.QSE.IsRightAlmostSplit g := by
  have w : f ≫ g = 0 := ιFG.map_injective (by rw [ιFG.map_comp, h.comp_eq_zero, ιFG.map_zero])
  refine ⟨w, (shortExact_map_iff (ShortComplex.mk f g w)).1 h.shortExact,
    fun hs ↦ h.not_isSplitMono ((isSplitMono_map_iff f).2 hs), ?_⟩
  refine ⟨fun hs ↦ h.not_isSplitEpi ((isSplitEpi_map_iff g).2 hs), fun {W} g' hg' ↦ ?_⟩
  have hg'' : ¬ IsSplitEpi (ιFG.map g') := fun hs ↦ hg' ((isSplitEpi_map_iff g').1 hs)
  obtain ⟨h', hh'⟩ := h.right (ιFG.obj W) (finite_of_fg k W) (ιFG.map g') hg''
  refine ⟨homFG h', ιFG.map_injective ?_⟩
  rw [ιFG.map_comp, map_homFG, hh']

end Translate

section Compatible

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : IndecomposableFamily k A)

/-- The vendored sequence ending at a nonprojective vertex is an almost split
sequence in the independent sense. -/
theorem isTranslate_tau (x : (toSkeleton S).arTranslationQuiver.nonprojective) :
    IsTranslate S ((toSkeleton S).arTranslationQuiver.tau x).1 x.1 := by
  let V := (toSkeleton S).toVendor
  let z : {z : Fin V.n // ¬ Projective (V.fgObj z)} := ⟨x.1, x.2⟩
  let B := V.minimalRightAlmostSplitAt z.1
  obtain ⟨hL, -, -, -⟩ := V.chosenRight_kernel_ar_sequence z
  haveI : Epi B.map :=
    MBDVendor.QSE.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      V.almostSplitSkeleton B.map B.rightAlmostSplit z.2
  let e := V.rightTranslationKernelIso z
  have w : (e.inv ≫ kernel.ι B.map) ≫ B.map = 0 := by simp
  have hSE : (ShortComplex.mk (e.inv ≫ kernel.ι B.map) B.map w).ShortExact := by
    have h0 : (ShortComplex.mk (kernel.ι B.map) B.map (kernel.condition _)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel B.map) inferInstance inferInstance
    refine ShortComplex.shortExact_of_iso ?_ h0
    exact ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  exact ⟨_, _, _, isAlmostSplitSequence_of_fg _ B.map w hSE
    (MBDVendor.QSE.IsLeftAlmostSplit.precomp_iso e.symm hL) B.rightAlmostSplit⟩

/-- An almost split sequence `0 → X_t → E → X_i → 0` forces `X_i` to be
nonprojective and `X_t` to be its vendored translate. -/
theorem exists_of_isTranslate {t i : Vertex S} (h : IsTranslate S t i) :
    ∃ x : (toSkeleton S).arTranslationQuiver.nonprojective,
      x.1 = i ∧ ((toSkeleton S).arTranslationQuiver.tau x).1 = t := by
  obtain ⟨E, f, g, hA⟩ := h
  let V := (toSkeleton S).toVendor
  have hE : Module.Finite k E := by
    have hSE := hA.shortExact
    haveI : Module.Finite k (S.obj t) := S.finite t
    haveI : Module.Finite k (S.obj i) := S.finite i
    have hex : Function.Exact f g :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hSE.exact
    exact Module.Finite.of_exact (f := f.hom.restrictScalars k) (g := g.hom.restrictScalars k)
      hex hSE.moduleCat_surjective_g
  let E' := fgOf k E hE
  let f₀ : V.fgObj t ⟶ E' := homFG (X := V.fgObj t) (Y := E') f
  let g₀ : E' ⟶ V.fgObj i := homFG (X := E') (Y := V.fgObj i) g
  have hf₀ : ιFG.map f₀ = f := map_homFG (X := V.fgObj t) (Y := E') f
  have hg₀ : ιFG.map g₀ = g := map_homFG (X := E') (Y := V.fgObj i) g
  have hA₀ : IsAlmostSplitSequence k (ιFG.map f₀) (ιFG.map g₀) := by rw [hf₀, hg₀]; exact hA
  obtain ⟨w, hSE₀, hnsm, hR⟩ := fg_of_isAlmostSplitSequence f₀ g₀ hA₀
  have hnp : ¬ Projective (V.fgObj i) := by
    intro hP
    haveI := hSE₀.epi_g
    exact hR.not_isSplitEpi
      (IsSplitEpi.mk' ⟨Projective.factorThru (𝟙 _) g₀, Projective.factorThru_comp _ _⟩)
  refine ⟨⟨i, hnp⟩, rfl, ?_⟩
  have hrad : IsRadicalMorphism f₀ :=
    (MBDVendor.QSE.IndecomposableSkeleton.isRadicalMorphism_iff_not_isSplitMono_from_obj
      V.almostSplitSkeleton f₀).2 hnsm
  have hmin : IsRightMinimal g₀ := isRightMinimal_g_of_shortExact hSE₀ hrad
  let B := V.minimalRightAlmostSplitAt i
  obtain ⟨e, he⟩ := exists_rightAlmostSplit_middleIso hR hmin B.rightAlmostSplit B.rightMinimal
  haveI := hSE₀.mono_f
  haveI : IsIso (kernel.lift g₀ f₀ w) := by
    haveI : Epi (kernel.lift g₀ f₀ w) := hSE₀.exact.epi_kernelLift
    haveI : Mono (kernel.lift g₀ f₀ w) := mono_of_mono_fac (kernel.lift_ι g₀ f₀ w)
    exact isIso_of_mono_of_epi _
  have k2 : kernel g₀ ≅ kernel B.map :=
    kernel.mapIso g₀ B.map e (Iso.refl _) (by simp only [Iso.refl_hom]; exact (Category.comp_id g₀).trans he.symm)
  have k3 := V.rightTranslationKernelIso ⟨i, hnp⟩
  let k1 : V.fgObj t ≅ kernel g₀ := asIso (kernel.lift g₀ f₀ w)
  exact (V.almostSplitSkeleton.eq_of_iso ⟨k1 ≪≫ k2 ≪≫ k3⟩).symm

/-- **The independent translate is the translation of `Γ_A`.** -/
theorem translateCompatible : TranslateCompatible S := fun _ _ ↦
  ⟨exists_of_isTranslate S, fun ⟨x, hx, ht⟩ ↦ hx ▸ ht ▸ isTranslate_tau S x⟩

end Compatible

end MultiplicativeBasisDeformations.Statement
