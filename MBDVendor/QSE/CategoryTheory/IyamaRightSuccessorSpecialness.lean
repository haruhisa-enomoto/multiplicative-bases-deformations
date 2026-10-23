module

public import MBDVendor.QSE.CategoryTheory.IyamaRightLadderConstruction

/-!
# Special successors in Iyama right ladders

This file formalizes Iyama, *Tau-categories I*, 3.6.1(2)(i)--(ii), in the
split-complement language used by the right-ladder construction.  A
radical-power perturbation of the raw complement successor lifts to a
perturbation of the current split mesh factor in the same power.  Cokernel
transport proves that the successor depends only on the arrow-isomorphism
class of that factor, and hence a special current arrow has a special raw
successor.

Everything here is categorical; no module classification or concrete
algebra is used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.RightLadder

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

/-- Component-exposing form of right-tau-sequence endpoint uniqueness. -/
theorem exists_automorphisms_lifting_endpoint_iso
    {S : ShortComplex C} (hS : RightTauSequence S)
    (e₃ : S.X₃ ≅ S.X₃) :
    ∃ (e₁ : S.X₁ ≅ S.X₁) (e₂ : S.X₂ ≅ S.X₂),
      e₁.hom ≫ S.f = S.f ≫ e₂.hom ∧
        e₂.hom ≫ S.g = S.g ≫ e₃.hom := by
  have hSg : IsRadicalMorphism (S.g ≫ e₃.hom) :=
    isRadicalMorphism_postcomp e₃.hom hS.g_radical
  obtain ⟨a, ha⟩ := hS.factors_into_right (S.g ≫ e₃.hom) hSg
  have hSg' : IsRadicalMorphism (S.g ≫ e₃.inv) :=
    isRadicalMorphism_postcomp e₃.inv hS.g_radical
  obtain ⟨b, hb⟩ := hS.factors_into_right (S.g ≫ e₃.inv) hSg'
  have hab : (a ≫ b) ≫ S.g = S.g := by
    calc
      (a ≫ b) ≫ S.g = a ≫ (b ≫ S.g) := Category.assoc _ _ _
      _ = a ≫ (S.g ≫ e₃.inv) := by rw [hb]
      _ = (a ≫ S.g) ≫ e₃.inv := (Category.assoc _ _ _).symm
      _ = (S.g ≫ e₃.hom) ≫ e₃.inv := by rw [ha]
      _ = S.g := by simp
  have hba : (b ≫ a) ≫ S.g = S.g := by
    calc
      (b ≫ a) ≫ S.g = b ≫ (a ≫ S.g) := Category.assoc _ _ _
      _ = b ≫ (S.g ≫ e₃.hom) := by rw [ha]
      _ = (b ≫ S.g) ≫ e₃.hom := (Category.assoc _ _ _).symm
      _ = (S.g ≫ e₃.inv) ≫ e₃.hom := by rw [hb]
      _ = S.g := by simp
  letI : IsIso (a ≫ b) := hS.isRightMinimal_g (a ≫ b) hab
  letI : IsIso (b ≫ a) := hS.isRightMinimal_g (b ≫ a) hba
  letI : IsIso a := isIso_of_isIso_comp_both a b
  let e₂ : S.X₂ ≅ S.X₂ := asIso a
  have he₂ : e₂.hom = a := by simp [e₂]
  have hfa : (S.f ≫ a) ≫ S.g = 0 := by
    rw [Category.assoc, ha, ← Category.assoc, S.zero, zero_comp]
  obtain ⟨p, hp⟩ :=
    (ShortComplex.isWeakKernel_iff S).mp hS.minimalWeakKernel.1
      (S.f ≫ a) hfa
  have he₂inv : e₂.inv ≫ S.g = S.g ≫ e₃.inv := by
    rw [← cancel_epi e₂.hom]
    rw [e₂.hom_inv_id_assoc, ← Category.assoc, he₂, ha,
      Category.assoc, e₃.hom_inv_id, Category.comp_id]
  have hfinv : (S.f ≫ e₂.inv) ≫ S.g = 0 := by
    rw [Category.assoc, he₂inv, ← Category.assoc, S.zero, zero_comp]
  obtain ⟨q, hq⟩ :=
    (ShortComplex.isWeakKernel_iff S).mp hS.minimalWeakKernel.1
      (S.f ≫ e₂.inv) hfinv
  have hpq : (p ≫ q) ≫ S.f = S.f := by
    calc
      (p ≫ q) ≫ S.f = p ≫ (q ≫ S.f) := Category.assoc _ _ _
      _ = p ≫ (S.f ≫ e₂.inv) := by rw [hq]
      _ = (p ≫ S.f) ≫ e₂.inv := (Category.assoc _ _ _).symm
      _ = (S.f ≫ a) ≫ e₂.inv := by rw [hp]
      _ = S.f := by rw [← he₂]; simp
  have hqp : (q ≫ p) ≫ S.f = S.f := by
    calc
      (q ≫ p) ≫ S.f = q ≫ (p ≫ S.f) := Category.assoc _ _ _
      _ = q ≫ (S.f ≫ a) := by rw [hp]
      _ = (q ≫ S.f) ≫ a := (Category.assoc _ _ _).symm
      _ = (S.f ≫ e₂.inv) ≫ a := by rw [hq]
      _ = S.f := by rw [← he₂]; simp
  letI : IsIso (p ≫ q) := hS.minimalWeakKernel.2 (p ≫ q) hpq
  letI : IsIso (q ≫ p) := hS.minimalWeakKernel.2 (q ≫ p) hqp
  letI : IsIso p := isIso_of_isIso_comp_both p q
  refine ⟨asIso p, e₂, ?_, ?_⟩
  · simpa only [asIso_hom, he₂] using hp
  · simpa only [he₂] using ha

set_option backward.defeqAttrib.useBackward true in
/-- Invariant form of the well-definedness of Iyama's `l⁺` operation.

If two split factors through the second map of a right tau-sequence are
isomorphic as arrows, then the arrows induced on any chosen cokernels of the
split factors by the first map are isomorphic. -/
theorem nonempty_successor_iso_of_splitFactors_arrow_iso
    {S : ShortComplex C} (hS : RightTauSequence S)
    {Z Z' Q Q' : C}
    (j : Z ⟶ S.X₂) [IsSplitMono j]
    (j' : Z' ⟶ S.X₂)
    (p : S.X₂ ⟶ Q) (p' : S.X₂ ⟶ Q')
    (hjp : j ≫ p = 0) (hjp' : j' ≫ p' = 0)
    (hp : IsColimit (CokernelCofork.ofπ p hjp))
    (hp' : IsColimit (CokernelCofork.ofπ p' hjp'))
    (e : Arrow.mk (j ≫ S.g) ≅ Arrow.mk (j' ≫ S.g)) :
    Nonempty (Arrow.mk (S.f ≫ p) ≅ Arrow.mk (S.f ≫ p')) := by
  let eZ : Z ≅ Z' :=
    { hom := e.hom.left
      inv := e.inv.left
      hom_inv_id := by
        have h := congrArg Arrow.Hom.left e.hom_inv_id
        simpa only [Arrow.comp_left, Arrow.id_left, Arrow.mk_left] using h
      inv_hom_id := by
        have h := congrArg Arrow.Hom.left e.inv_hom_id
        simpa only [Arrow.comp_left, Arrow.id_left, Arrow.mk_left] using h }
  let eY : S.X₃ ≅ S.X₃ :=
    { hom := e.hom.right
      inv := e.inv.right
      hom_inv_id := by
        have h := congrArg Arrow.Hom.right e.hom_inv_id
        simpa only [Arrow.comp_right, Arrow.id_right, Arrow.mk_right] using h
      inv_hom_id := by
        have h := congrArg Arrow.Hom.right e.inv_hom_id
        simpa only [Arrow.comp_right, Arrow.id_right, Arrow.mk_right] using h }
  obtain ⟨e₁, e₂, he₁, he₂⟩ :=
    exists_automorphisms_lifting_endpoint_iso hS eY
  let k : Z ⟶ S.X₂ := eZ.hom ≫ j' - j ≫ e₂.hom
  have hkg : k ≫ S.g = 0 := by
    dsimp only [k]
    rw [Preadditive.sub_comp]
    have he : eZ.hom ≫ (j' ≫ S.g) =
        j ≫ (S.g ≫ eY.hom) := by
      have hw := e.hom.w
      change e.hom.left ≫ (j' ≫ S.g) =
        (j ≫ S.g) ≫ e.hom.right at hw
      simpa only [eZ, eY, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right,
        Category.assoc] using hw
    simp only [Category.assoc]
    rw [he, he₂, sub_self]
  obtain ⟨q, hq⟩ :=
    (ShortComplex.isWeakKernel_iff S).mp hS.minimalWeakKernel.1 k hkg
  let r₂ : S.X₂ ⟶ S.X₂ := retraction j ≫ q ≫ S.f
  let B : S.X₂ ⟶ S.X₂ := e₂.hom + r₂
  have hr₂ : IsRadicalMorphism r₂ := by
    dsimp only [r₂]
    simpa only [Category.assoc] using
      isRadicalMorphism_precomp (retraction j ≫ q) hS.f_radical
  haveI : IsIso B := by
    dsimp only [B]
    exact isIso_add_of_isIso_of_isRadicalMorphism e₂.hom r₂ hr₂
  have hjB : j ≫ B = eZ.hom ≫ j' := by
    dsimp only [B, r₂]
    rw [Preadditive.comp_add]
    simp only [IsSplitMono.id_assoc]
    rw [hq]
    dsimp only [k]
    abel
  let r₁ : S.X₁ ⟶ S.X₁ := S.f ≫ retraction j ≫ q
  let A : S.X₁ ⟶ S.X₁ := e₁.hom + r₁
  have hr₁ : IsRadicalMorphism r₁ := by
    dsimp only [r₁]
    exact isRadicalMorphism_postcomp (retraction j ≫ q) hS.f_radical
  haveI : IsIso A := by
    dsimp only [A]
    exact isIso_add_of_isIso_of_isRadicalMorphism e₁.hom r₁ hr₁
  have hAf : A ≫ S.f = S.f ≫ B := by
    dsimp only [A, B, r₁, r₂]
    rw [Preadditive.add_comp, Preadditive.comp_add, he₁]
    simp only [Category.assoc]
  let eJ : Arrow.mk j ≅ Arrow.mk j' :=
    Arrow.isoMk' j j' eZ (asIso B)
      (by simpa only [asIso_hom] using hjB.symm)
  let c : CokernelCofork j := CokernelCofork.ofπ p hjp
  let c' : CokernelCofork j' := CokernelCofork.ofπ p' hjp'
  let eQ : Q ≅ Q' := CokernelCofork.mapIsoOfIsColimit hp hp' eJ
  have hpB : p ≫ eQ.hom = B ≫ p' := by
    change
      (Cofork.π c) ≫
          CokernelCofork.mapOfIsColimit hp c' eJ.hom =
        eJ.hom.right ≫ Cofork.π c'
    exact CokernelCofork.π_mapOfIsColimit hp c' eJ.hom
  refine ⟨Arrow.isoMk' (S.f ≫ p) (S.f ≫ p') (asIso A) eQ ?_⟩
  simp only [asIso_hom, Category.assoc]
  calc
    A ≫ S.f ≫ p' = (A ≫ S.f) ≫ p' :=
      (Category.assoc _ _ _).symm
    _ = (S.f ≫ B) ≫ p' := by rw [hAf]
    _ = S.f ≫ (B ≫ p') := Category.assoc _ _ _
    _ = S.f ≫ (p ≫ eQ.hom) := by rw [hpB]
    _ = S.f ≫ p ≫ eQ.hom := rfl

/-- Radical-power lifting through the first map of a tau-approximation.

An element of `J^(n+1)` lifts with coefficient in `J^n`.  This is the
filtration-sensitive factorization in Iyama 3.6.1(2)(i). -/
theorem exists_factor_through_tau_f_of_mem_pow_succ
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : TauApproximation S)
    (n : ℕ) {W : C} {r : S.X₁ ⟶ W}
    (hr : r ∈ (R.ideal.pow (n + 1)).hom S.X₁ W) :
    ∃ b : S.X₂ ⟶ W,
      b ∈ (R.ideal.pow n).hom S.X₂ W ∧ S.f ≫ b = r := by
  induction n generalizing W r with
  | zero =>
      have hrJ : r ∈ R.ideal.hom S.X₁ W := by simpa using hr
      obtain ⟨b, hb⟩ :=
        hS.factors_from_left r ((R.mem_ideal_iff r).mp hrJ)
      exact ⟨b, by simp, hb⟩
  | succ n ih =>
      have hr' :
          r ∈ ((R.ideal.pow (n + 1)) ⋆ᵢ R.ideal).hom S.X₁ W := by
        simpa only [CategoricalIdeal.HomIdeal.pow_succ] using hr
      change r ∈ AddSubgroup.closure
        (CategoricalIdeal.HomIdeal.compositeGenerators
          (R.ideal.pow (n + 1)) R.ideal S.X₁ W) at hr'
      clear hr
      induction hr' using AddSubgroup.closure_induction with
      | mem r hr =>
          obtain ⟨V, u, v, hu, hv, rfl⟩ := hr
          obtain ⟨b, hb, hfb⟩ := ih hu
          refine ⟨b ≫ v, ?_, ?_⟩
          · exact CategoricalIdeal.HomIdeal.comp_mem_mul hb hv
          · rw [← Category.assoc, hfb]
      | zero =>
          exact ⟨0, zero_mem _, by simp⟩
      | add r s _ _ hr hs =>
          obtain ⟨b, hb, hbr⟩ := hr
          obtain ⟨c, hc, hcs⟩ := hs
          refine ⟨b + c, add_mem hb hc, ?_⟩
          rw [Preadditive.comp_add, hbr, hcs]
      | neg r _ hr =>
          obtain ⟨b, hb, hbr⟩ := hr
          refine ⟨-b, neg_mem hb, ?_⟩
          rw [Preadditive.comp_neg, hbr]

/-- The matrix lift of a `J^(n+1)` perturbation of the raw successor.

For `n ≥ 1`, an isomorphism of the mesh middle term changes the complement
successor by the prescribed `J^(n+1)` arrow while changing the split mesh
factor by another arrow in the same radical power. -/
theorem exists_middle_iso_lifting_successor_perturbation
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : RightTauSequence S)
    {Z : C} (j : Z ⟶ S.X₂) [IsSplitMono j]
    (d : SplitMonoComplement j)
    (n : ℕ) (hn : 1 ≤ n)
    (r : S.X₁ ⟶ d.complement)
    (hr : r ∈ (R.ideal.pow (n + 1)).hom S.X₁ d.complement) :
    ∃ E : S.X₂ ≅ S.X₂,
      (j ≫ E.inv ≫ S.g - j ≫ S.g) ∈
          (R.ideal.pow (n + 1)).hom Z S.X₃ ∧
        S.f ≫ E.hom ≫ d.projection =
          S.f ≫ d.projection + r := by
  obtain ⟨t, ht, hft⟩ :=
    exists_factor_through_tau_f_of_mem_pow_succ R hS.toTauApproximation n hr
  have htRadMem : t ∈ R.ideal.hom S.X₂ d.complement := by
    cases n with
    | zero => omega
    | succ m =>
        exact CategoricalIdeal.HomIdeal.mul_le_right
          (R.ideal.pow m) R.ideal _ _ ht
  have htRad : IsRadicalMorphism t := (R.mem_ideal_iff t).mp htRadMem
  let A : S.X₂ ⟶ S.X₂ := 𝟙 S.X₂ + t ≫ d.inclusion
  have hApert : IsRadicalMorphism (t ≫ d.inclusion) :=
    isRadicalMorphism_postcomp d.inclusion htRad
  haveI : IsIso A := by
    have hi : IsIso (𝟙 S.X₂ - (t ≫ d.inclusion) ≫ (-𝟙 S.X₂)) :=
      hApert (-𝟙 S.X₂)
    simpa [A] using hi
  let E : S.X₂ ≅ S.X₂ := asIso A
  have hInvAdd :
      inv A + inv A ≫ t ≫ d.inclusion = 𝟙 S.X₂ := by
    have h := IsIso.inv_hom_id_assoc A (𝟙 S.X₂)
    dsimp only [A] at h
    simpa only [Preadditive.comp_add, Category.comp_id,
      Category.assoc] using h
  have hInvSub :
      inv A - 𝟙 S.X₂ = -(inv A ≫ t ≫ d.inclusion) := by
    rw [← hInvAdd]
    abel
  have hfactorDiff :
      j ≫ E.inv ≫ S.g - j ≫ S.g =
        -(j ≫ inv A ≫ t) ≫ (d.inclusion ≫ S.g) := by
    dsimp only [E]
    simp only [asIso_inv]
    calc
      j ≫ inv A ≫ S.g - j ≫ S.g =
          (j ≫ (inv A - 𝟙 S.X₂)) ≫ S.g := by
            simp only [Preadditive.comp_sub, Preadditive.sub_comp,
              Category.comp_id, Category.assoc]
      _ = (j ≫ (-(inv A ≫ t ≫ d.inclusion))) ≫ S.g := by
        rw [hInvSub]
      _ = -(j ≫ inv A ≫ t) ≫ (d.inclusion ≫ S.g) := by
        simp only [Preadditive.comp_neg, Preadditive.neg_comp,
          Category.assoc]
  have hleft :
      -(j ≫ inv A ≫ t) ∈
          (R.ideal.pow n).hom Z d.complement := by
    simpa only [Category.assoc, Preadditive.neg_comp] using
      neg_mem ((R.ideal.pow n).precomp (j ≫ inv A) ht)
  have hright :
      d.inclusion ≫ S.g ∈ R.ideal.hom d.complement S.X₃ :=
    (R.mem_ideal_iff (d.inclusion ≫ S.g)).mpr
      (isRadicalMorphism_precomp d.inclusion hS.g_radical)
  have hdiff :
      (j ≫ E.inv ≫ S.g - j ≫ S.g) ∈
          (R.ideal.pow (n + 1)).hom Z S.X₃ := by
    rw [hfactorDiff, CategoricalIdeal.HomIdeal.pow_succ]
    simpa only [Category.assoc, Preadditive.neg_comp,
      Preadditive.comp_neg] using
        CategoricalIdeal.HomIdeal.comp_mem_mul hleft hright
  refine ⟨E, hdiff, ?_⟩
  calc
    S.f ≫ E.hom ≫ d.projection =
        (S.f ≫ A) ≫ d.projection := by
          simpa only [E, asIso_hom] using
            (Category.assoc S.f A d.projection).symm
    _ = (S.f ≫ (𝟙 S.X₂ + t ≫ d.inclusion)) ≫
        d.projection := rfl
    _ = (S.f + S.f ≫ t ≫ d.inclusion) ≫ d.projection := by
      simp only [Preadditive.comp_add, Category.comp_id]
    _ = S.f ≫ d.projection +
        (S.f ≫ t ≫ d.inclusion) ≫ d.projection := by
      rw [Preadditive.add_comp]
    _ = S.f ≫ d.projection + r := by
      simp only [Category.assoc, d.inclusion_projection,
        Category.comp_id, hft]

set_option backward.defeqAttrib.useBackward true in
/-- Representative form of Iyama 3.6.1(2)(i).

For source exponent `N = n + 1` with `n ≥ 1`, a prescribed `J^N`
perturbation of the complement successor is realized by another split mesh
factor whose current arrow differs in `J^N`.  The displayed map `p'` is a
genuine cokernel of the new split factor, not merely an annihilating map. -/
theorem exists_splitFactor_cokernel_lifting_successor_perturbation
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : RightTauSequence S)
    {Z : C} (j : Z ⟶ S.X₂) [IsSplitMono j]
    (d : SplitMonoComplement j)
    (n : ℕ) (hn : 1 ≤ n)
    (r : S.X₁ ⟶ d.complement)
    (hr : r ∈ (R.ideal.pow (n + 1)).hom S.X₁ d.complement) :
    ∃ (j' : Z ⟶ S.X₂) (p' : S.X₂ ⟶ d.complement)
      (hjp' : j' ≫ p' = 0)
      (_hp' : IsColimit (CokernelCofork.ofπ p' hjp')),
      IsSplitMono j' ∧
        (j' ≫ S.g - j ≫ S.g) ∈
          (R.ideal.pow (n + 1)).hom Z S.X₃ ∧
        S.f ≫ p' = S.f ≫ d.projection + r := by
  obtain ⟨E, hdiff, hsucc⟩ :=
    exists_middle_iso_lifting_successor_perturbation
      R hS j d n hn r hr
  let j' : Z ⟶ S.X₂ := j ≫ E.inv
  have hj' : IsSplitMono j' := inferInstance
  let p' : S.X₂ ⟶ d.complement := E.hom ≫ d.projection
  have hjp' : j' ≫ p' = 0 := by
    simp [j', p', Category.assoc]
  let c : CokernelCofork j :=
    CokernelCofork.ofπ d.projection d.f_projection
  have hp : IsColimit c :=
    BinaryBicone.isColimitInlCokernelCofork
      d.isBilimitBinaryBicone.isColimit
  have hp' : IsColimit (CokernelCofork.ofπ p' hjp') := by
    have h := CokernelCofork.isColimitOfIsColimitOfIff
      hp j' E (fun q ↦ by simp [j', Category.assoc])
    apply IsColimit.ofIsoColimit h
    exact Cofork.ext (Iso.refl _)
  refine ⟨j', p', hjp', hp', hj', ?_, ?_⟩
  · simpa only [j', Category.assoc] using hdiff
  · simpa only [p', Category.assoc] using hsucc

set_option backward.defeqAttrib.useBackward true in
/-- Iyama 3.6.1(2)(ii), in split-complement form.

If a split factor through the second map of a right tau-sequence is special,
then the raw successor obtained by composing the first map with the
complement projection is special. -/
theorem isSpecial_rawComplementSuccessor
    (R : NilpotentRadicalData C)
    {S : ShortComplex C} (hS : RightTauSequence S)
    {Z : C} (j : Z ⟶ S.X₂) [IsSplitMono j]
    (d : SplitMonoComplement j)
    (ha : IsSpecial R (j ≫ S.g)) :
    IsSpecial R (S.f ≫ d.projection) := by
  constructor
  · exact isRadicalMorphism_postcomp d.projection hS.f_radical
  · intro r hr
    obtain ⟨j', p', hjp', hp', hj', hdiff, hsucc⟩ :=
      exists_splitFactor_cokernel_lifting_successor_perturbation
        R hS j d 1 (by omega) r (by simpa using hr)
    letI : IsSplitMono j' := hj'
    let c : CokernelCofork j :=
      CokernelCofork.ofπ d.projection d.f_projection
    have hp : IsColimit c := by
      exact BinaryBicone.isColimitInlCokernelCofork
        (d.isBilimitBinaryBicone.isColimit)
    let a : Z ⟶ S.X₃ := j ≫ S.g
    let a' : Z ⟶ S.X₃ := j' ≫ S.g
    let s : Z ⟶ S.X₃ := a' - a
    have hs : s ∈ (R.ideal.pow 2).hom Z S.X₃ := by
      simpa only [s, a, a', Nat.reduceAdd] using hdiff
    have has : a + s = a' := by
      dsimp only [s]
      abel
    obtain ⟨ecur⟩ := ha.2 s hs
    let ecur' : Arrow.mk a ≅ Arrow.mk a' :=
      ecur.trans (eqToIso (congrArg Arrow.mk has))
    obtain ⟨esucc⟩ :=
      nonempty_successor_iso_of_splitFactors_arrow_iso
        hS j j' d.projection p' d.f_projection hjp' hp hp' ecur'
    exact ⟨esucc.trans (eqToIso (congrArg Arrow.mk hsucc))⟩

section FiniteTauCategory

universe w

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- Chosen-mesh form of successor specialness, matching the output of the
special split-factor normalization theorem. -/
theorem isSpecial_chosenRightMesh_rawComplementSuccessor
    (T : FiniteRightTauCategoryData C Ind)
    {Y Z : C} (j : Z ⟶ (T.rightMesh Y).X₂) [IsSplitMono j]
    (ha : IsSpecial T.radical
      (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom)) :
    IsSpecial T.radical
      ((T.rightMesh Y).f ≫ (splitMonoComplement j).projection) := by
  let a : Z ⟶ Y :=
    j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom
  let b : Z ⟶ (T.rightMesh Y).X₃ := j ≫ (T.rightMesh Y).g
  let e : Arrow.mk a ≅ Arrow.mk b :=
    Arrow.isoMk' a b (Iso.refl Z) (T.rightTermIso Y).symm (by
      dsimp only [a, b]
      simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
      rw [Category.assoc j
          ((T.rightMesh Y).g ≫ (T.rightTermIso Y).hom)
          (T.rightTermIso Y).inv,
        Category.assoc (T.rightMesh Y).g
          (T.rightTermIso Y).hom (T.rightTermIso Y).inv,
        (T.rightTermIso Y).hom_inv_id, Category.comp_id])
  have hb : IsSpecial T.radical b := by
    exact ha.of_iso T.radical e
  exact isSpecial_rawComplementSuccessor T.radical (T.rightTau Y) j
    (splitMonoComplement j) (by simpa only [b] using hb)

end FiniteTauCategory

end MBDVendor.QSE.Iyama.RightLadder
