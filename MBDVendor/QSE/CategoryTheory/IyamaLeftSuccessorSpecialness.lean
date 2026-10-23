module

public import MBDVendor.QSE.CategoryTheory.IyamaRightSuccessorSpecialness

/-!
# Special successors in Iyama left ladders

This file proves the categorical dual of Iyama, *Tau-categories I*,
3.6.1(2)(ii).  A special split-epimorphic cofactor through the first map of
a left tau-sequence has a special complementary successor through the second
map.  No concrete algebra or module classification is used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.LeftLadder

open CategoricalIdeal CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

private theorem isIso_add_of_isIso_of_isRadicalMorphism
    {X Y : C} (e r : X ⟶ Y) [IsIso e]
    (hr : IsRadicalMorphism r) : IsIso (e + r) := by
  have hq : IsRadicalMorphism (inv e ≫ r) :=
    isRadicalMorphism_precomp (inv e) hr
  haveI : IsIso (𝟙 Y + inv e ≫ r) := by
    have hi : IsIso (𝟙 Y - (inv e ≫ r) ≫ (-𝟙 Y)) := hq (-𝟙 Y)
    simpa using hi
  have heq : e + r = e ≫ (𝟙 Y + inv e ≫ r) := by
    simp [Preadditive.comp_add]
  rw [heq]
  infer_instance

/-- Component-exposing form of left-tau-sequence endpoint uniqueness. -/
theorem exists_automorphisms_lifting_left_endpoint_iso
    {S : ShortComplex C} (hS : LeftTauSequence S)
    (e₁ : S.X₁ ≅ S.X₁) :
    ∃ (e₂ : S.X₂ ≅ S.X₂) (e₃ : S.X₃ ≅ S.X₃),
      e₁.hom ≫ S.f = S.f ≫ e₂.hom ∧
        e₂.hom ≫ S.g = S.g ≫ e₃.hom := by
  have hSf : IsRadicalMorphism (e₁.hom ≫ S.f) :=
    isRadicalMorphism_precomp e₁.hom hS.f_radical
  obtain ⟨a, ha⟩ := hS.factors_from_left (e₁.hom ≫ S.f) hSf
  have hSf' : IsRadicalMorphism (e₁.inv ≫ S.f) :=
    isRadicalMorphism_precomp e₁.inv hS.f_radical
  obtain ⟨b, hb⟩ := hS.factors_from_left (e₁.inv ≫ S.f) hSf'
  have hab : S.f ≫ (a ≫ b) = S.f := by
    calc
      S.f ≫ (a ≫ b) = (S.f ≫ a) ≫ b :=
        (Category.assoc _ _ _).symm
      _ = (e₁.hom ≫ S.f) ≫ b := by rw [ha]
      _ = e₁.hom ≫ (S.f ≫ b) := Category.assoc _ _ _
      _ = e₁.hom ≫ (e₁.inv ≫ S.f) := by rw [hb]
      _ = S.f := by simp
  have hba : S.f ≫ (b ≫ a) = S.f := by
    calc
      S.f ≫ (b ≫ a) = (S.f ≫ b) ≫ a :=
        (Category.assoc _ _ _).symm
      _ = (e₁.inv ≫ S.f) ≫ a := by rw [hb]
      _ = e₁.inv ≫ (S.f ≫ a) := Category.assoc _ _ _
      _ = e₁.inv ≫ (e₁.hom ≫ S.f) := by rw [ha]
      _ = S.f := by simp
  letI : IsIso (a ≫ b) := hS.isLeftMinimal_f (a ≫ b) hab
  letI : IsIso (b ≫ a) := hS.isLeftMinimal_f (b ≫ a) hba
  letI : IsIso a := isIso_of_isIso_comp_both a b
  let e₂ : S.X₂ ≅ S.X₂ := asIso a
  have he₂ : e₂.hom = a := by simp [e₂]
  have hfa : S.f ≫ e₂.inv = e₁.inv ≫ S.f := by
    rw [← cancel_epi e₁.hom]
    calc
      e₁.hom ≫ (S.f ≫ e₂.inv) =
          (e₁.hom ≫ S.f) ≫ e₂.inv :=
        (Category.assoc _ _ _).symm
      _ = (S.f ≫ a) ≫ e₂.inv := by rw [ha]
      _ = S.f := by rw [← he₂]; simp
      _ = e₁.hom ≫ (e₁.inv ≫ S.f) := by simp
  have hSag : S.f ≫ (a ≫ S.g) = 0 := by
    rw [← Category.assoc, ha, Category.assoc, S.zero, comp_zero]
  obtain ⟨p, hp⟩ :=
    (ShortComplex.isWeakCokernel_iff S).mp
      hS.minimalWeakCokernel.1 (a ≫ S.g) hSag
  have hSinv : S.f ≫ (e₂.inv ≫ S.g) = 0 := by
    rw [← Category.assoc, hfa, Category.assoc, S.zero, comp_zero]
  obtain ⟨q, hq⟩ :=
    (ShortComplex.isWeakCokernel_iff S).mp
      hS.minimalWeakCokernel.1 (e₂.inv ≫ S.g) hSinv
  have hpq : S.g ≫ (p ≫ q) = S.g := by
    calc
      S.g ≫ (p ≫ q) = (S.g ≫ p) ≫ q :=
        (Category.assoc _ _ _).symm
      _ = (a ≫ S.g) ≫ q := by rw [hp]
      _ = a ≫ (S.g ≫ q) := Category.assoc _ _ _
      _ = a ≫ (e₂.inv ≫ S.g) := by rw [hq]
      _ = S.g := by rw [← he₂]; simp
  have hqp : S.g ≫ (q ≫ p) = S.g := by
    calc
      S.g ≫ (q ≫ p) = (S.g ≫ q) ≫ p :=
        (Category.assoc _ _ _).symm
      _ = (e₂.inv ≫ S.g) ≫ p := by rw [hq]
      _ = e₂.inv ≫ (S.g ≫ p) := Category.assoc _ _ _
      _ = e₂.inv ≫ (a ≫ S.g) := by rw [hp]
      _ = S.g := by rw [← he₂]; simp
  letI : IsIso (p ≫ q) :=
    hS.minimalWeakCokernel.2 (p ≫ q) hpq
  letI : IsIso (q ≫ p) :=
    hS.minimalWeakCokernel.2 (q ≫ p) hqp
  letI : IsIso p := isIso_of_isIso_comp_both p q
  refine ⟨e₂, asIso p, ?_, ?_⟩
  · simpa only [he₂] using ha.symm
  · simpa only [asIso_hom, he₂] using hp.symm

/-- Invariant well-definedness of the complementary left successor. -/
theorem nonempty_successor_iso_of_splitCofactors_arrow_iso
    {S : ShortComplex C} (hS : LeftTauSequence S)
    {Z Z' Q Q' : C}
    (p : S.X₂ ⟶ Z) [IsSplitEpi p]
    (p' : S.X₂ ⟶ Z')
    (i : Q ⟶ S.X₂) (i' : Q' ⟶ S.X₂)
    (hip : i ≫ p = 0) (hip' : i' ≫ p' = 0)
    (hi : IsLimit (KernelFork.ofι i hip))
    (hi' : IsLimit (KernelFork.ofι i' hip'))
    (e : Arrow.mk (S.f ≫ p) ≅ Arrow.mk (S.f ≫ p')) :
    Nonempty (Arrow.mk (i ≫ S.g) ≅ Arrow.mk (i' ≫ S.g)) := by
  let eX := Arrow.leftFunc.mapIso e
  let eZ := Arrow.rightFunc.mapIso e
  change S.X₁ ≅ S.X₁ at eX
  change Z ≅ Z' at eZ
  obtain ⟨e₂, e₃, he₂, he₃⟩ :=
    exists_automorphisms_lifting_left_endpoint_iso hS eX.symm
  simp only [Iso.symm_hom] at he₂
  let k : S.X₂ ⟶ Z := p' ≫ eZ.inv - e₂.hom ≫ p
  have hfk : S.f ≫ k = 0 := by
    dsimp only [k]
    rw [Preadditive.comp_sub]
    have heInv : eX.inv ≫ (S.f ≫ p) =
        (S.f ≫ p') ≫ eZ.inv := by
      have hw := e.inv.w
      change e.inv.left ≫ (S.f ≫ p) =
        (S.f ≫ p') ≫ e.inv.right at hw
      exact hw
    simp only [← Category.assoc]
    rw [← heInv, ← he₂, ← Category.assoc, sub_self]
  obtain ⟨q, hq⟩ :=
    (ShortComplex.isWeakCokernel_iff S).mp
      hS.minimalWeakCokernel.1 k hfk
  let r₂ : S.X₂ ⟶ S.X₂ := S.g ≫ q ≫ section_ p
  let B : S.X₂ ⟶ S.X₂ := e₂.hom + r₂
  have hr₂ : IsRadicalMorphism r₂ := by
    dsimp only [r₂]
    simpa only [Category.assoc] using
      isRadicalMorphism_postcomp (q ≫ section_ p) hS.g_radical
  haveI : IsIso B := by
    dsimp only [B]
    exact isIso_add_of_isIso_of_isRadicalMorphism e₂.hom r₂ hr₂
  have hBp : B ≫ p = p' ≫ eZ.inv := by
    dsimp only [B, r₂]
    rw [Preadditive.add_comp]
    simp only [Category.assoc, IsSplitEpi.id, Category.comp_id]
    rw [hq]
    dsimp only [k]
    abel
  let r₃ : S.X₃ ⟶ S.X₃ := q ≫ section_ p ≫ S.g
  let D : S.X₃ ⟶ S.X₃ := e₃.hom + r₃
  have hr₃ : IsRadicalMorphism r₃ := by
    dsimp only [r₃]
    simpa only [Category.assoc] using
      isRadicalMorphism_precomp (q ≫ section_ p) hS.g_radical
  haveI : IsIso D := by
    dsimp only [D]
    exact isIso_add_of_isIso_of_isRadicalMorphism e₃.hom r₃ hr₃
  have hBg : B ≫ S.g = S.g ≫ D := by
    dsimp only [B, D, r₂, r₃]
    rw [Preadditive.add_comp, Preadditive.comp_add, he₃]
    simp only [Category.assoc]
  let eP : Arrow.mk p' ≅ Arrow.mk p :=
    Arrow.isoMk' p' p (asIso B) eZ.symm
      (by simpa only [asIso_hom, Iso.symm_hom] using hBp)
  let c : KernelFork p := KernelFork.ofι i hip
  let c' : KernelFork p' := KernelFork.ofι i' hip'
  let eQ : Q' ≅ Q := KernelFork.mapIsoOfIsLimit hi' hi eP
  have heQi : eQ.hom ≫ i = i' ≫ B := by
    change
      KernelFork.mapOfIsLimit c' hi eP.hom ≫ Fork.ι c =
        Fork.ι c' ≫ eP.hom.left
    exact KernelFork.mapOfIsLimit_ι c' hi eP.hom
  let eSucc : Arrow.mk (i' ≫ S.g) ≅ Arrow.mk (i ≫ S.g) :=
    Arrow.isoMk' (i' ≫ S.g) (i ≫ S.g) eQ (asIso D) (by
      simp only [asIso_hom]
      calc
        eQ.hom ≫ (i ≫ S.g) = (eQ.hom ≫ i) ≫ S.g :=
          (Category.assoc _ _ _).symm
        _ = (i' ≫ B) ≫ S.g := by rw [heQi]
        _ = i' ≫ (B ≫ S.g) := Category.assoc _ _ _
        _ = i' ≫ (S.g ≫ D) := by rw [hBg]
        _ = (i' ≫ S.g) ≫ D := (Category.assoc _ _ _).symm)
  exact ⟨eSucc.symm⟩

/-- Radical-power lifting through the second map of a tau-approximation. -/
theorem exists_factor_through_tau_g_of_mem_pow_succ
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : TauApproximation S)
    (n : ℕ) {W : C} {r : W ⟶ S.X₃}
    (hr : r ∈ (R.ideal.pow (n + 1)).hom W S.X₃) :
    ∃ b : W ⟶ S.X₂,
      b ∈ (R.ideal.pow n).hom W S.X₂ ∧ b ≫ S.g = r := by
  induction n generalizing W r with
  | zero =>
      have hrJ : r ∈ R.ideal.hom W S.X₃ := by simpa using hr
      obtain ⟨b, hb⟩ :=
        hS.factors_into_right r ((R.mem_ideal_iff r).mp hrJ)
      exact ⟨b, by simp, hb⟩
  | succ n ih =>
      have hr' :
          r ∈ (R.ideal ⋆ᵢ (R.ideal.pow (n + 1))).hom W S.X₃ := by
        simpa only [CategoricalIdeal.HomIdeal.pow_succ_eq_mul_pow] using hr
      change r ∈ AddSubgroup.closure
        (CategoricalIdeal.HomIdeal.compositeGenerators
          R.ideal (R.ideal.pow (n + 1)) W S.X₃) at hr'
      clear hr
      induction hr' using AddSubgroup.closure_induction with
      | mem r hr =>
          obtain ⟨V, u, v, hu, hv, rfl⟩ := hr
          obtain ⟨b, hb, hbg⟩ := ih hv
          refine ⟨u ≫ b, ?_, ?_⟩
          · rw [CategoricalIdeal.HomIdeal.pow_succ_eq_mul_pow]
            exact CategoricalIdeal.HomIdeal.comp_mem_mul hu hb
          · rw [Category.assoc, hbg]
      | zero =>
          exact ⟨0, zero_mem _, by simp⟩
      | add r s _ _ hr hs =>
          obtain ⟨b, hb, hbr⟩ := hr
          obtain ⟨c, hc, hcs⟩ := hs
          refine ⟨b + c, add_mem hb hc, ?_⟩
          rw [Preadditive.add_comp, hbr, hcs]
      | neg r _ hr =>
          obtain ⟨b, hb, hbr⟩ := hr
          refine ⟨-b, neg_mem hb, ?_⟩
          rw [Preadditive.neg_comp, hbr]

/-- A middle-term automorphism realizes a perturbation of the raw left
successor while changing the split cofactor in the same radical power. -/
theorem exists_middle_iso_lifting_left_successor_perturbation
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : LeftTauSequence S)
    {Z : C} (p : S.X₂ ⟶ Z) [IsSplitEpi p]
    (d : SplitEpiComplement p)
    (n : ℕ) (hn : 1 ≤ n)
    (r : d.complement ⟶ S.X₃)
    (hr : r ∈ (R.ideal.pow (n + 1)).hom d.complement S.X₃) :
    ∃ E : S.X₂ ≅ S.X₂,
      (S.f ≫ E.inv ≫ p - S.f ≫ p) ∈
          (R.ideal.pow (n + 1)).hom S.X₁ Z ∧
        d.inclusion ≫ E.hom ≫ S.g =
          d.inclusion ≫ S.g + r := by
  obtain ⟨t, ht, htg⟩ :=
    exists_factor_through_tau_g_of_mem_pow_succ
      R hS.toTauApproximation n hr
  have htRadMem : t ∈ R.ideal.hom d.complement S.X₂ := by
    cases n with
    | zero => omega
    | succ m =>
        exact CategoricalIdeal.HomIdeal.mul_le_right
          (R.ideal.pow m) R.ideal _ _ ht
  have htRad : IsRadicalMorphism t := (R.mem_ideal_iff t).mp htRadMem
  let A : S.X₂ ⟶ S.X₂ := 𝟙 S.X₂ + d.projection ≫ t
  have hApert : IsRadicalMorphism (d.projection ≫ t) :=
    isRadicalMorphism_precomp d.projection htRad
  haveI : IsIso A := by
    have hi : IsIso (𝟙 S.X₂ - (d.projection ≫ t) ≫ (-𝟙 S.X₂)) :=
      hApert (-𝟙 S.X₂)
    simpa [A] using hi
  let E : S.X₂ ≅ S.X₂ := asIso A
  have hInvAdd :
      inv A + d.projection ≫ t ≫ inv A = 𝟙 S.X₂ := by
    have h := IsIso.hom_inv_id A
    dsimp only [A] at h
    simpa only [Preadditive.add_comp, Category.id_comp,
      Category.assoc] using h
  have hInvSub :
      inv A - 𝟙 S.X₂ = -(d.projection ≫ t ≫ inv A) := by
    rw [← hInvAdd]
    abel
  have hfactorDiff :
      S.f ≫ E.inv ≫ p - S.f ≫ p =
        -(S.f ≫ d.projection) ≫ (t ≫ inv A ≫ p) := by
    dsimp only [E]
    simp only [asIso_inv]
    calc
      S.f ≫ inv A ≫ p - S.f ≫ p =
          (S.f ≫ (inv A - 𝟙 S.X₂)) ≫ p := by
            simp only [Preadditive.comp_sub, Preadditive.sub_comp,
              Category.comp_id, Category.assoc]
      _ = (S.f ≫ (-(d.projection ≫ t ≫ inv A))) ≫ p := by
        rw [hInvSub]
      _ = -(S.f ≫ d.projection) ≫ (t ≫ inv A ≫ p) := by
        simp only [Preadditive.comp_neg, Preadditive.neg_comp,
          Category.assoc]
  have hleft :
      -(S.f ≫ d.projection) ∈ R.ideal.hom S.X₁ d.complement := by
    apply neg_mem
    exact (R.mem_ideal_iff (S.f ≫ d.projection)).mpr
      (isRadicalMorphism_postcomp d.projection hS.f_radical)
  have hright :
      t ≫ inv A ≫ p ∈ (R.ideal.pow n).hom d.complement Z := by
    simpa only [Category.assoc] using
      (R.ideal.pow n).postcomp (inv A ≫ p) ht
  have hdiff :
      (S.f ≫ E.inv ≫ p - S.f ≫ p) ∈
          (R.ideal.pow (n + 1)).hom S.X₁ Z := by
    rw [hfactorDiff,
      CategoricalIdeal.HomIdeal.pow_succ_eq_mul_pow]
    simpa only [Preadditive.neg_comp, Category.assoc] using
      CategoricalIdeal.HomIdeal.comp_mem_mul hleft hright
  refine ⟨E, hdiff, ?_⟩
  calc
    d.inclusion ≫ E.hom ≫ S.g =
        (d.inclusion ≫ A) ≫ S.g := by
          simpa only [E, asIso_hom] using
            (Category.assoc d.inclusion A S.g).symm
    _ = (d.inclusion ≫
          (𝟙 S.X₂ + d.projection ≫ t)) ≫ S.g := rfl
    _ = (d.inclusion + d.inclusion ≫ d.projection ≫ t) ≫ S.g := by
      simp only [Preadditive.comp_add, Category.comp_id]
    _ = d.inclusion ≫ S.g +
        (d.inclusion ≫ d.projection ≫ t) ≫ S.g := by
      rw [Preadditive.add_comp]
    _ = d.inclusion ≫ S.g +
        (d.inclusion ≫ d.projection) ≫ (t ≫ S.g) := by
      simp only [Category.assoc]
    _ = d.inclusion ≫ S.g + r := by
      rw [d.inclusion_projection, htg, Category.id_comp]

/-- Representative form of the perturbation lift using a genuine kernel of
the perturbed split cofactor. -/
theorem exists_splitCofactor_kernel_lifting_left_successor_perturbation
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : LeftTauSequence S)
    {Z : C} (p : S.X₂ ⟶ Z) [IsSplitEpi p]
    (d : SplitEpiComplement p)
    (n : ℕ) (hn : 1 ≤ n)
    (r : d.complement ⟶ S.X₃)
    (hr : r ∈ (R.ideal.pow (n + 1)).hom d.complement S.X₃) :
    ∃ (p' : S.X₂ ⟶ Z) (i' : d.complement ⟶ S.X₂)
      (hip' : i' ≫ p' = 0)
      (_hi' : IsLimit (KernelFork.ofι i' hip')),
      IsSplitEpi p' ∧
        (S.f ≫ p' - S.f ≫ p) ∈
          (R.ideal.pow (n + 1)).hom S.X₁ Z ∧
        i' ≫ S.g = d.inclusion ≫ S.g + r := by
  obtain ⟨E, hdiff, hsucc⟩ :=
    exists_middle_iso_lifting_left_successor_perturbation
      R hS p d n hn r hr
  let p' : S.X₂ ⟶ Z := E.inv ≫ p
  have hp' : IsSplitEpi p' := inferInstance
  let i' : d.complement ⟶ S.X₂ := d.inclusion ≫ E.hom
  have hip' : i' ≫ p' = 0 := by
    simp [i', p']
  have hi' : IsLimit (KernelFork.ofι i' hip') := by
    letI : IsSplitMono d.inclusion :=
      IsSplitMono.mk'
        { retraction := d.projection
          id := d.inclusion_projection }
    haveI : Mono i' := by
      dsimp only [i']
      infer_instance
    apply KernelFork.IsLimit.ofι' i' hip'
    intro W x hx
    have hxold : (x ≫ E.inv) ≫ p = 0 := by
      simpa only [p', Category.assoc] using hx
    refine ⟨x ≫ E.inv ≫ d.projection, ?_⟩
    have hzero : (x ≫ E.inv) ≫ (p ≫ section_ p) = 0 := by
      rw [← Category.assoc, hxold, zero_comp]
    have hsplit :
        (x ≫ E.inv ≫ d.projection) ≫ d.inclusion =
          x ≫ E.inv := by
      calc
        (x ≫ E.inv ≫ d.projection) ≫ d.inclusion =
            (x ≫ E.inv) ≫ (d.projection ≫ d.inclusion) := by
          simp only [Category.assoc]
        _ = (x ≫ E.inv) ≫ (d.projection ≫ d.inclusion) +
            (x ≫ E.inv) ≫ (p ≫ section_ p) := by
          rw [hzero, add_zero]
        _ = (x ≫ E.inv) ≫
            (d.projection ≫ d.inclusion + p ≫ section_ p) := by
          rw [Preadditive.comp_add]
        _ = x ≫ E.inv := by rw [d.total, Category.comp_id]
    dsimp only [i']
    calc
      (x ≫ E.inv ≫ d.projection) ≫
          (d.inclusion ≫ E.hom) =
          ((x ≫ E.inv ≫ d.projection) ≫ d.inclusion) ≫
            E.hom := (Category.assoc _ _ _).symm
      _ = (x ≫ E.inv) ≫ E.hom := by rw [hsplit]
      _ = x := by simp
  refine ⟨p', i', hip', hi', hp', ?_, ?_⟩
  · simpa only [p', Category.assoc] using hdiff
  · simpa only [i', Category.assoc] using hsucc

/-- Iyama 3.6.1(2)(ii), in split-complement left-ladder form. -/
theorem isSpecial_rawComplementLeftSuccessor
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : LeftTauSequence S)
    {Z : C} (p : S.X₂ ⟶ Z) [IsSplitEpi p]
    (d : SplitEpiComplement p)
    (ha : IsSpecial R (S.f ≫ p)) :
    IsSpecial R (d.inclusion ≫ S.g) := by
  constructor
  · exact isRadicalMorphism_precomp d.inclusion hS.g_radical
  · intro r hr
    obtain ⟨p', i', hip', hi', hp', hdiff, hsucc⟩ :=
      exists_splitCofactor_kernel_lifting_left_successor_perturbation
        R hS p d 1 (by omega) r (by simpa using hr)
    letI : IsSplitEpi p' := hp'
    let c : KernelFork p :=
      KernelFork.ofι d.inclusion d.inclusion_g
    have hi : IsLimit c :=
      BinaryBicone.isLimitSndKernelFork
        d.isBilimitBinaryBicone.isLimit
    let a : S.X₁ ⟶ Z := S.f ≫ p
    let a' : S.X₁ ⟶ Z := S.f ≫ p'
    let s : S.X₁ ⟶ Z := a' - a
    have hs : s ∈ (R.ideal.pow 2).hom S.X₁ Z := by
      simpa only [s, a, a', Nat.reduceAdd] using hdiff
    have has : a + s = a' := by
      dsimp only [s]
      abel
    obtain ⟨ecur⟩ := ha.2 s hs
    let ecur' : Arrow.mk a ≅ Arrow.mk a' :=
      ecur.trans (eqToIso (congrArg Arrow.mk has))
    obtain ⟨esucc⟩ :=
      nonempty_successor_iso_of_splitCofactors_arrow_iso
        hS p p' d.inclusion i' d.inclusion_g hip' hi hi' ecur'
    exact ⟨esucc.trans (eqToIso (congrArg Arrow.mk hsucc))⟩

section FiniteTauCategory

universe w

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- Chosen-left-mesh form of complementary successor specialness. -/
theorem isSpecial_chosenLeftMesh_rawComplementSuccessor
    (T : FiniteTauCategoryData C Ind)
    {Y Z : C} (p : (T.leftMesh Y).X₂ ⟶ Z) [IsSplitEpi p]
    (ha : IsSpecial T.radical
      ((T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ p)) :
    IsSpecial T.radical
      ((splitEpiComplement p).inclusion ≫ (T.leftMesh Y).g) := by
  let a : Y ⟶ Z :=
    (T.leftTermIso Y).inv ≫ (T.leftMesh Y).f ≫ p
  let b : (T.leftMesh Y).X₁ ⟶ Z := (T.leftMesh Y).f ≫ p
  let e : Arrow.mk a ≅ Arrow.mk b :=
    Arrow.isoMk' a b (T.leftTermIso Y).symm (Iso.refl Z) (by
      dsimp only [a, b]
      simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id])
  have hb : IsSpecial T.radical b := by
    exact ha.of_iso T.radical e
  exact isSpecial_rawComplementLeftSuccessor T.radical (T.leftTau Y) p
    (splitEpiComplement p) (by simpa only [b] using hb)

end FiniteTauCategory

end MBDVendor.QSE.Iyama.LeftLadder
