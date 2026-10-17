import MultiplicativeBasisDeformations.Foundations.ARBridge
import MBDVendor.Magnitude.Algebra.RightModuleProjectiveBoundary
import MBDVendor.Magnitude.CategoryTheory.AlgebraicallyClosedOccurrenceBasis
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# Simple tops of indecomposable projective modules

The original simple module `S_x = P_x / rad P_x` of a projective label
(`graded-category.tex`) and the identity
`dim Hom_A(P_y, S_x) = δ_{xy}` used in the proof of Proposition 2.10. The
code adapts general module theory from the magnitude-conjecture formalization
(`Algebra/RightModuleSimpleTop.lean` and
`Algebra/RightModuleBasicSimpleDimension.lean`), stated here for an
`IndSkeleton`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u

/-- A simple module carried by `FGModuleCat` is a simple object. -/
theorem fgModule_simple_of_isSimpleModule {R : Type u} [Ring R] [IsNoetherianRing R]
    (X : FGModuleCat.{u} R) [IsSimpleModule R X] : Simple X := by
  letI : Nontrivial X := IsSimpleModule.nontrivial R X
  constructor
  intro Y f _
  constructor
  · intro hf hzero
    letI : IsIso f := hf
    have hid : (𝟙 X : X ⟶ X) = 0 := by
      have hinv : inv f ≫ f = 𝟙 X := IsIso.inv_hom_id_assoc f (𝟙 X)
      have hzeroInv : inv f ≫ f = 0 := by
        calc inv f ≫ f = inv f ≫ 0 := congrArg (fun q ↦ inv f ≫ q) hzero
          _ = 0 := comp_zero
      exact hinv.symm.trans hzeroInv
    obtain ⟨x, hx⟩ : ∃ x : X, x ≠ 0 := exists_ne 0
    apply hx
    have hvalue := congrArg (fun q : X ⟶ X ↦ q.hom.hom x) hid
    simpa using hvalue
  · intro hne
    have hlinear : f.hom.hom ≠ 0 := by
      intro hzero
      apply hne
      apply FGModuleCat.hom_ext
      exact hzero
    have hsurjective : Function.Surjective f.hom.hom :=
      LinearMap.surjective_of_ne_zero hlinear
    letI : Epi f := (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurjective
    exact isIso_of_mono_of_epi f

namespace IndSkeleton

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A)

omit [Algebra k A] [FiniteDimensional k A] in
/-- The quotient of a finite module by its module Jacobson radical. -/
def radQuot (P : ModCat A) : ModCat A :=
  FGModuleCat.of Aᵐᵒᵖ (P ⧸ Module.jacobson Aᵐᵒᵖ P)

omit [Algebra k A] [FiniteDimensional k A] in
/-- The quotient map to the module-Jacobson-radical quotient. -/
def radQuotProj (P : ModCat A) : P ⟶ radQuot P :=
  FGModuleCat.ofHom (Module.jacobson Aᵐᵒᵖ P).mkQ

/-- The radical quotient `S_x = P_x / rad P_x`. -/
abbrev top (x : Fin S.n) : ModCat A := radQuot (S.fg x)

/-- The projection `P_x → S_x`. -/
abbrev topProj (x : Fin S.n) : S.fg x ⟶ S.top x := radQuotProj (S.fg x)

instance topProj_epi (x : Fin S.n) : Epi (S.topProj x) := by
  apply (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective _).2
  change Function.Surjective (Module.jacobson Aᵐᵒᵖ (S.fg x)).mkQ
  exact Submodule.mkQ_surjective _

theorem topProj_ne_zero (x : Fin S.n) (hx : Projective (S.fg x)) : S.topProj x ≠ 0 := by
  intro hzero
  have hmkQ : (Module.jacobson Aᵐᵒᵖ (S.fg x)).mkQ = 0 := by
    apply LinearMap.ext
    intro y
    have hy := DFunLike.congr_fun (congrArg (fun f ↦ f.hom.hom) hzero) y
    change (Module.jacobson Aᵐᵒᵖ (S.fg x)).mkQ y = 0 at hy
    exact hy
  have hjtop : Module.jacobson Aᵐᵒᵖ (S.fg x) = ⊤ := by
    rw [← (Module.jacobson Aᵐᵒᵖ (S.fg x)).ker_mkQ, hmkQ, LinearMap.ker_zero]
  have hsurjective : Function.Surjective
      (S.toVendor.projectiveBoundaryRadicalInclusion x).hom.hom := by
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [hjtop]
    trivial
  letI : Epi (S.toVendor.projectiveBoundaryRadicalInclusion x) :=
    (MBDVendor.QSE.IndecomposableSkeleton.fg_epi_iff_surjective _).2 hsurjective
  letI : Projective (S.fg x) := hx
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 (S.fg x)) (S.toVendor.projectiveBoundaryRadicalInclusion x)
  exact (S.toVendor.projectiveBoundaryRadicalInclusion_isRightAlmostSplit x hx).not_isSplitEpi
    (IsSplitEpi.mk' { section_ := s, id := hs })

theorem top_isSimpleModule (x : Fin S.n) (hx : Projective (S.fg x)) :
    IsSimpleModule Aᵐᵒᵖ (S.top x) := by
  apply isSimpleModule_iff_isCoatom.mpr
  exact S.toVendor.projectiveBoundary_jacobson_isCoatom x hx

theorem top_indecomposable (x : Fin S.n) (hx : Projective (S.fg x)) : Indecomposable (S.top x) := by
  haveI := S.top_isSimpleModule x hx
  haveI := fgModule_simple_of_isSimpleModule (S.top x)
  exact indecomposable_of_simple _

/-- A distinct indecomposable projective has no map to the simple top of `p`. -/
theorem hom_top_eq_zero (p q : Fin S.n) (hp : Projective (S.fg p)) (hq : Projective (S.fg q))
    (hqp : q ≠ p) (f : S.fg q ⟶ S.top p) : f = 0 := by
  letI : Projective (S.fg q) := hq
  obtain ⟨g, hg⟩ := Projective.factors f (S.topProj p)
  have hnot : ¬ IsSplitEpi g := by
    intro hsplit
    let hmono : IsSplitMono g :=
      @MBDVendor.QSE.IndecomposableSkeleton.isSplitMono_of_isSplitEpi_between_obj
        Aᵐᵒᵖ _ _ (Fin S.n) S.toVendor.almostSplitSkeleton q p g hsplit
    letI : IsSplitMono g := hmono
    letI : IsSplitEpi g := hsplit
    letI : IsIso g := isIso_of_mono_of_epi g
    exact hqp (S.toVendor.fgObj_skeletal ⟨asIso g⟩)
  obtain ⟨l, hl⟩ := (S.toVendor.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp).factors g hnot
  rw [← hg, ← hl, Category.assoc]
  apply FGModuleCat.hom_ext
  ext y
  change (Module.jacobson Aᵐᵒᵖ (S.fg p)).mkQ (l.hom.hom y).1 = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (l.hom.hom y).2

/-- The projective `P_p` maps one-dimensionally to its simple top. -/
theorem finrank_hom_top_self [IsAlgClosed k] (p : Fin S.n) (hp : Projective (S.fg p)) :
    Module.finrank k (S.fg p ⟶ S.top p) = 1 := by
  letI : Projective (S.fg p) := hp
  apply (finrank_eq_one_iff_of_nonzero' (S.topProj p) (S.topProj_ne_zero p hp)).2
  intro f
  obtain ⟨g, hg⟩ := Projective.factors f (S.topProj p)
  obtain ⟨c, hc⟩ := S.toVendor.almostSplitSkeleton.exists_scalar_sub_isRadicalMorphism
    (K := k) p g
  have hnot : ¬ IsSplitEpi (g - c • 𝟙 (S.fg p)) :=
    (S.toVendor.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (g - c • 𝟙 (S.fg p))).1 hc
  obtain ⟨l, hl⟩ := (S.toVendor.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp).factors
    (g - c • 𝟙 (S.fg p)) hnot
  have hzero : (g - c • 𝟙 (S.fg p)) ≫ S.topProj p = 0 := by
    rw [← hl, Category.assoc]
    apply FGModuleCat.hom_ext
    ext y
    change (Module.jacobson Aᵐᵒᵖ (S.fg p)).mkQ (l.hom.hom y).1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (l.hom.hom y).2
  refine ⟨c, ?_⟩
  rw [← hg]
  have hdecomp : g = (g - c • 𝟙 (S.fg p)) + c • 𝟙 (S.fg p) := by abel
  rw [hdecomp, Preadditive.add_comp, hzero, zero_add, CategoryTheory.Linear.smul_comp,
    Category.id_comp]

/-- **`dim Hom_A(P_q, S_p) = δ_{qp}`.** -/
theorem finrank_hom_top [IsAlgClosed k] (p q : Fin S.n) (hp : Projective (S.fg p))
    (hq : Projective (S.fg q)) :
    Module.finrank k (S.fg q ⟶ S.top p) = if q = p then 1 else 0 := by
  split_ifs with h
  · subst h; exact S.finrank_hom_top_self q hq
  · rw [Module.finrank_zero_iff]
    exact ⟨fun f g ↦ (S.hom_top_eq_zero p q hp hq h f).trans (S.hom_top_eq_zero p q hp hq h g).symm⟩

end IndSkeleton

end MultiplicativeBasisDeformations
