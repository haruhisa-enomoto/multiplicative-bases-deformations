import MBDVendor.QSE.RepresentationTheory.AlmostSplitCofinite
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Kernels of minimal right almost-split epimorphisms

This file proves the kernel half of the abstract Auslander--Reiten sequence
theorem needed for mesh rotation.  In an abelian category, the kernel
inclusion of a right-minimal right almost-split epimorphism is left almost
split.  For finite-length finitely generated modules its source is
indecomposable and noninjective.  At a chosen indecomposable endpoint the
kernel inclusion is also left minimal.

No presentation or classification of an algebra or of its modules is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The kernel inclusion of a right-minimal right almost-split epimorphism
is left almost split. -/
theorem IsRightAlmostSplit.kernel_ι_isLeftAlmostSplit
    {E Z : C} (f : E ⟶ Z) [Epi f]
    (hf : IsRightAlmostSplit f) (hmin : IsRightMinimal f) :
    IsLeftAlmostSplit (kernel.ι f) := by
  constructor
  · intro hsplit
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.Exact :=
      S.exact_of_f_is_kernel (kernelIsKernel f)
    obtain ⟨sm⟩ := hsplit.exists_splitMono
    let spl : S.Splitting :=
      ShortComplex.Splitting.ofExactOfRetraction
        S hS sm.retraction sm.id inferInstance
    exact hf.not_isSplitEpi spl.isSplitEpi_g
  · intro X g hg
    let P := pushout (kernel.ι f) g
    let inl : E ⟶ P := pushout.inl (kernel.ι f) g
    let inr : X ⟶ P := pushout.inr (kernel.ι f) g
    let p : P ⟶ Z := pushout.desc f 0 (by simp)
    have hpush : kernel.ι f ≫ inl = g ≫ inr := by
      exact pushout.condition
    have hinlp : inl ≫ p = f := by
      dsimp only [inl, p, P]
      exact pushout.inl_desc _ _ _
    have hinrp : inr ≫ p = 0 := by
      dsimp only [inr, p, P]
      exact pushout.inr_desc _ _ _
    letI : Epi p := epi_of_epi_fac hinlp
    by_cases hp : IsSplitEpi p
    · have hpCokernel :
          IsColimit (CokernelCofork.ofπ p hinrp) :=
        CokernelCofork.IsColimit.ofπ' p hinrp fun {T} q hq => by
          have hzero : kernel.ι f ≫ inl ≫ q = 0 := by
            rw [← Category.assoc, hpush, Category.assoc, hq, comp_zero]
          let d : Z ⟶ T :=
            Abelian.epiDesc f (inl ≫ q) (by
              simpa only [Category.assoc] using hzero)
          refine ⟨d, ?_⟩
          apply pushout.hom_ext
          · change inl ≫ (p ≫ d) = inl ≫ q
            rw [← Category.assoc, hinlp]
            exact Abelian.comp_epiDesc f (inl ≫ q) _
          · change inr ≫ (p ≫ d) = inr ≫ q
            rw [← Category.assoc, hinrp, zero_comp, hq]
      let S := ShortComplex.mk inr p hinrp
      have hS : S.Exact :=
        S.exact_of_g_is_cokernel hpCokernel
      obtain ⟨se⟩ := hp.exists_splitEpi
      let spl : S.Splitting :=
        ShortComplex.Splitting.ofExactOfSection
          S hS se.section_ se.id inferInstance
      refine ⟨inl ≫ spl.r, ?_⟩
      rw [← Category.assoc, hpush, Category.assoc, spl.f_r,
        Category.comp_id]
    · obtain ⟨s, hs⟩ := hf.factors p hp
      let e : E ⟶ E := inl ≫ s
      have hefix : e ≫ f = f := by
        dsimp only [e]
        rw [Category.assoc, hs, hinlp]
      letI : IsIso e := hmin e hefix
      let r : P ⟶ E := s ≫ inv e
      have hinlr : inl ≫ r = 𝟙 E := by
        dsimp only [r]
        rw [← Category.assoc]
        change e ≫ inv e = 𝟙 E
        simp
      have hinvf : inv e ≫ f = f := by
        rw [← cancel_epi e]
        simp only [IsIso.hom_inv_id_assoc, hefix]
      have hinrrf : (inr ≫ r) ≫ f = 0 := by
        calc
          (inr ≫ r) ≫ f = inr ≫ s ≫ (inv e ≫ f) := by
            simp only [r, Category.assoc]
          _ = inr ≫ s ≫ f := by rw [hinvf]
          _ = inr ≫ p := by rw [hs]
          _ = 0 := hinrp
      let q : X ⟶ kernel f := kernel.lift f (inr ≫ r) hinrrf
      have hgq : g ≫ q = 𝟙 (kernel f) := by
        rw [← cancel_mono (kernel.ι f)]
        rw [Category.assoc, kernel.lift_ι, Category.id_comp]
        calc
          g ≫ (inr ≫ r) = (g ≫ inr) ≫ r := by rw [Category.assoc]
          _ = (kernel.ι f ≫ inl) ≫ r := by rw [hpush]
          _ = kernel.ι f ≫ (inl ≫ r) := by rw [Category.assoc]
          _ = kernel.ι f := by rw [hinlr, Category.comp_id]
      exact (hg (IsSplitMono.mk' { retraction := q, id := hgq })).elim

omit [Abelian C] in
/-- A left almost-split monomorphism cannot start at an injective object. -/
theorem IsLeftAlmostSplit.not_injective_source
    {A B : C} (i : A ⟶ B) [Mono i] (hi : IsLeftAlmostSplit i) :
    ¬ Injective A := by
  intro hA
  letI : Injective A := hA
  apply hi.not_isSplitMono
  exact IsSplitMono.mk'
    { retraction := Injective.factorThru (𝟙 A) i
      id := Injective.comp_factorThru (𝟙 A) i }

namespace IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- The source of a left almost-split morphism of finitely generated modules
is indecomposable. -/
theorem IsLeftAlmostSplit.isIndecomposableModule_source
    {A B : FGModuleCat.{w} R} (i : A ⟶ B)
    (hi : IsLeftAlmostSplit i) :
    MBDVendor.QSE.Foundation.IsIndecomposableModule R A := by
  rw [MBDVendor.QSE.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    letI : Subsingleton A := hsub
    apply hi.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := 0
        id := by
          ext x
          exact Subsingleton.elim _ _ }
  · intro p hp
    let e : A ⟶ A := FGModuleCat.ofHom p
    have he : e ≫ e = e := by
      ext x
      exact DFunLike.congr_fun hp x
    by_cases hse : IsSplitMono e
    · letI : IsSplitMono e := hse
      have hei : e = 𝟙 A := by
        apply (cancel_mono e).1
        rw [he, Category.id_comp]
      exact Or.inr (by
        ext x
        exact ConcreteCategory.congr_hom hei x)
    · let c : A ⟶ A := 𝟙 A - e
      have hc : c ≫ c = c := by
        dsimp only [c]
        rw [Preadditive.sub_comp, Preadditive.comp_sub,
          Preadditive.comp_sub, he, Category.id_comp,
          Category.comp_id]
        abel
      by_cases hsc : IsSplitMono c
      · letI : IsSplitMono c := hsc
        have hci : c = 𝟙 A := by
          apply (cancel_mono c).1
          rw [hc, Category.id_comp]
        have hezero : e = 0 := by
          change 𝟙 A - e = 𝟙 A at hci
          exact sub_eq_self.mp hci
        exact Or.inl (by
          ext x
          exact ConcreteCategory.congr_hom hezero x)
      · obtain ⟨a, ha⟩ := hi.factors e hse
        obtain ⟨b, hb⟩ := hi.factors c hsc
        exfalso
        apply hi.not_isSplitMono
        exact IsSplitMono.mk'
          { retraction := a + b
            id := by
              rw [Preadditive.comp_add, ha, hb]
              dsimp only [c]
              abel }

variable {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- A right almost-split map to a nonprojective chosen indecomposable is
epic. -/
theorem IsRightAlmostSplit.epi_of_not_projective_obj
    {E : FGModuleCat.{w} R} {z : ι} (f : E ⟶ σ.obj z)
    (hf : IsRightAlmostSplit f) (hz : ¬ Projective (σ.obj z)) :
    Epi f := by
  have hzrel : ¬ σ.IsRelativeSplitProjective Set.univ z := by
    intro hrel
    exact hz ((σ.projective_iff_isRelativeSplitProjective_univ).2 hrel)
  change ¬ ∀ P : σ.FacPresentation Set.univ (σ.obj z),
    IsSplitEpi P.map at hzrel
  obtain ⟨P, hP⟩ := Classical.not_forall.mp hzrel
  letI : Epi P.map := P.epi
  exact hf.epi_of_nonsplit_epi P.map hP

/-- Once its kernel inclusion is left almost split, a right almost-split
epimorphism to a chosen indecomposable has a left-minimal kernel inclusion. -/
theorem IsRightAlmostSplit.kernel_ι_isLeftMinimal_obj
    {E : FGModuleCat.{w} R} {z : ι} (f : E ⟶ σ.obj z) [Epi f]
    (hf : IsRightAlmostSplit f)
    (hk : IsLeftAlmostSplit (kernel.ι f)) :
    IsLeftMinimal (kernel.ι f) := by
  intro e he
  let hcok := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι f) (kernel.condition f))
    (kernelIsKernel f)
  have hezero : kernel.ι f ≫ (e ≫ f) = 0 := by
    rw [← Category.assoc, he, kernel.condition]
  obtain ⟨d, hd⟩ :=
    CokernelCofork.IsColimit.desc' hcok (e ≫ f) hezero
  change σ.obj z ⟶ σ.obj z at d
  change f ≫ d = e ≫ f at hd
  have hdsplit : IsSplitEpi d := by
    by_contra hdnot
    obtain ⟨h, hh⟩ := hf.factors d hdnot
    let a : E ⟶ E := e - f ≫ h
    have haf : a ≫ f = 0 := by
      dsimp only [a]
      rw [Preadditive.sub_comp, Category.assoc, hh, hd]
      simp
    let t : E ⟶ kernel f := kernel.lift f a haf
    have ht : t ≫ kernel.ι f = a := kernel.lift_ι f a haf
    apply hk.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := t
        id := by
          apply (cancel_mono (kernel.ι f)).1
          rw [Category.assoc, ht]
          dsimp only [a]
          rw [Preadditive.comp_sub, he, ← Category.assoc,
            kernel.condition, zero_comp, sub_zero,
            Category.id_comp] }
  letI : IsSplitEpi d := hdsplit
  letI : IsSplitMono d :=
    σ.isSplitMono_of_isSplitEpi_between_obj d
  letI : IsIso d := isIso_of_epi_of_isSplitMono d
  let S : ShortComplex (FGModuleCat.{w} R) :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel f) }
  let φ : S ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := e
      τ₃ := d
      comm₁₂ := by simpa only [Category.id_comp] using he.symm
      comm₂₃ := hd.symm }
  change IsIso φ.τ₂
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hS

/-- The kernel of a chosen minimal right almost-split map at a
nonprojective endpoint is the start of a minimal left almost-split map and
is an indecomposable noninjective module. -/
theorem MinimalRightAlmostSplitDecomposition.kernel_ar_sequence
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (hz : ¬ Projective (σ.obj z)) :
    IsLeftAlmostSplit (kernel.ι A.map) ∧
      IsLeftMinimal (kernel.ι A.map) ∧
      MBDVendor.QSE.Foundation.IsIndecomposableModule R
        (kernel A.map : FGModuleCat.{w} R) ∧
      ¬ Injective (kernel A.map) := by
  letI : Epi A.map :=
    MBDVendor.QSE.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      σ A.map A.rightAlmostSplit hz
  have hleft : IsLeftAlmostSplit (kernel.ι A.map) :=
    A.rightAlmostSplit.kernel_ι_isLeftAlmostSplit A.map A.rightMinimal
  exact
    ⟨hleft,
      MBDVendor.QSE.IndecomposableSkeleton.IsRightAlmostSplit.kernel_ι_isLeftMinimal_obj
        σ A.map A.rightAlmostSplit hleft,
      MBDVendor.QSE.IndecomposableSkeleton.IsLeftAlmostSplit.isIndecomposableModule_source
        (kernel.ι A.map) hleft,
      hleft.not_injective_source (kernel.ι A.map)⟩

end IndecomposableSkeleton

end MBDVendor.QSE
