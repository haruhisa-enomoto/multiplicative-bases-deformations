import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtConormalForm
import MBDVendor.QSE.CategoryTheory.IyamaLeftLadderBasic
import MBDVendor.QSE.CategoryTheory.IyamaRightSuccessorSpecialness

/-!
# Special-arrow target conormalization

This is the dual of Iyama's source-padded special normalization.  The file
uses the target split--radical normal form and produces the exact
`SpecialConormalization` expected by the finite left-ladder builder.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama.LeftLadder

open CategoricalRadical CategoricalIdeal

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- A special arrow with a radical-square complementary target component is
isomorphic to the same arrow with that component zeroed. -/
theorem IsSpecial.nonempty_iso_biprod_lift_zero
    (R : NilpotentRadicalData C)
    {X Z U : C} {b : X ⟶ Z} {q : X ⟶ U}
    (ha : IsSpecial R (biprod.lift b q))
    (hq : q ∈ (R.ideal.pow 2).hom X U) :
    Nonempty
      (Arrow.mk (biprod.lift b q) ≅
        Arrow.mk (biprod.lift b (0 : X ⟶ U))) := by
  let t : X ⟶ biprod Z U := biprod.lift 0 (-q)
  have ht : t ∈ (R.ideal.pow 2).hom X (biprod Z U) := by
    have hqneg : -q ∈ (R.ideal.pow 2).hom X U := neg_mem hq
    have hpost := (R.ideal.pow 2).postcomp
      (biprod.inr : U ⟶ biprod Z U) hqneg
    simpa [t, biprod.lift_eq] using hpost
  obtain ⟨e⟩ := ha.2 t ht
  refine ⟨e.trans (eqToIso ?_)⟩
  congr 1
  dsimp only [t]
  ext <;> simp

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Isomorphism-invariant target-padding absorption. -/
theorem IsSpecial.nonempty_iso_biprod_lift_zero_of_iso
    (R : NilpotentRadicalData C)
    {X Y Z U : C} {a : X ⟶ Y} {b : X ⟶ Z} {q : X ⟶ U}
    (ha : IsSpecial R a)
    (e : Arrow.mk a ≅ Arrow.mk (biprod.lift b q))
    (hq : q ∈ (R.ideal.pow 2).hom X U) :
    Nonempty
      (Arrow.mk a ≅
        Arrow.mk (biprod.lift b (0 : X ⟶ U))) := by
  obtain ⟨e'⟩ := IsSpecial.nonempty_iso_biprod_lift_zero
    R (ha.of_iso R e) hq
  exact ⟨e.trans e'⟩

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Zero-padded left-minimal arrows cancel their padded target summands. -/
theorem nonempty_arrow_iso_of_biprod_lift_zero_iso
    {X Z U X' Z' U' : C} {b : X ⟶ Z} {b' : X' ⟶ Z'}
    (hb : IsLeftMinimal b) (hb' : IsLeftMinimal b')
    (e :
      Arrow.mk (biprod.lift b (0 : X ⟶ U)) ≅
        Arrow.mk (biprod.lift b' (0 : X' ⟶ U'))) :
    Nonempty (Arrow.mk b ≅ Arrow.mk b') := by
  let eL : X ≅ X' := by simpa using Arrow.leftFunc.mapIso e
  let eR : biprod Z U ≅ biprod Z' U' := by
    simpa using Arrow.rightFunc.mapIso e
  have he :
      eL.hom ≫ biprod.lift b' (0 : X' ⟶ U') =
        biprod.lift b (0 : X ⟶ U) ≫ eR.hom :=
    e.hom.w
  have heInv :
      eL.inv ≫ biprod.lift b (0 : X ⟶ U) =
        biprod.lift b' (0 : X' ⟶ U') ≫ eR.inv :=
    e.inv.w
  let c : Z ⟶ Z' := biprod.inl ≫ eR.hom ≫ biprod.fst
  let d : Z' ⟶ Z := biprod.inl ≫ eR.inv ≫ biprod.fst
  have hc : b ≫ c = eL.hom ≫ b' := by
    have h := congrArg
      (fun q ↦ q ≫ (biprod.fst : biprod Z' U' ⟶ Z')) he
    have hlift :
        biprod.lift b (0 : X ⟶ U) = b ≫ biprod.inl := by
      ext <;> simp
    rw [hlift] at h
    simpa [c, Category.assoc] using h.symm
  have hd : b' ≫ d = eL.inv ≫ b := by
    have h := congrArg
      (fun q ↦ q ≫ (biprod.fst : biprod Z U ⟶ Z)) heInv
    have hlift :
        biprod.lift b' (0 : X' ⟶ U') = b' ≫ biprod.inl := by
      ext <;> simp
    rw [hlift] at h
    simpa [d, Category.assoc] using h.symm
  have hcd : b ≫ (c ≫ d) = b := by
    calc
      b ≫ (c ≫ d) = (b ≫ c) ≫ d :=
        (Category.assoc _ _ _).symm
      _ = (eL.hom ≫ b') ≫ d := by rw [hc]
      _ = eL.hom ≫ (b' ≫ d) := Category.assoc _ _ _
      _ = eL.hom ≫ (eL.inv ≫ b) := by rw [hd]
      _ = b := by simp
  have hdc : b' ≫ (d ≫ c) = b' := by
    calc
      b' ≫ (d ≫ c) = (b' ≫ d) ≫ c :=
        (Category.assoc _ _ _).symm
      _ = (eL.inv ≫ b) ≫ c := by rw [hd]
      _ = eL.inv ≫ (b ≫ c) := Category.assoc _ _ _
      _ = eL.inv ≫ (eL.hom ≫ b') := by rw [hc]
      _ = b' := by simp
  letI : IsIso (c ≫ d) := hb (c ≫ d) hcd
  letI : IsIso (d ≫ c) := hb' (d ≫ c) hdc
  letI : IsIso c := isIso_of_isIso_comp_both c d
  exact ⟨Arrow.isoMk' b b' eL (asIso c) (by simpa using hc.symm)⟩

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Specialness of a target-padded arrow descends to its left-minimal
essential component when its radical-square perturbations stay left
minimal. -/
theorem IsSpecial.cancel_biprod_lift_zero
    (R : NilpotentRadicalData C)
    {X Z U : C} {b : X ⟶ Z}
    (hpadded : IsSpecial R (biprod.lift b (0 : X ⟶ U)))
    (hb : IsLeftMinimal b)
    (hpert : ∀ (r : X ⟶ Z),
      r ∈ (R.ideal.pow 2).hom X Z → IsLeftMinimal (b + r)) :
    IsSpecial R b := by
  constructor
  · have hcomponent :=
      isRadicalMorphism_postcomp
        (biprod.fst : biprod Z U ⟶ Z) hpadded.1
    simpa using hcomponent
  · intro r hr
    let t : X ⟶ biprod Z U := biprod.lift r 0
    have ht : t ∈ (R.ideal.pow 2).hom X (biprod Z U) := by
      have hpost := (R.ideal.pow 2).postcomp
        (biprod.inl : Z ⟶ biprod Z U) hr
      simpa [t, biprod.lift_eq] using hpost
    obtain ⟨e⟩ := hpadded.2 t ht
    have heq :
        Arrow.mk (biprod.lift b (0 : X ⟶ U) + t) =
          Arrow.mk (biprod.lift (b + r) (0 : X ⟶ U)) := by
      congr 1
      dsimp only [t]
      ext <;> simp
    let e' :
        Arrow.mk (biprod.lift b (0 : X ⟶ U)) ≅
          Arrow.mk (biprod.lift (b + r) (0 : X ⟶ U)) :=
      e.trans (eqToIso heq)
    exact nonempty_arrow_iso_of_biprod_lift_zero_iso
      hb (hpert r hr) e'

omit [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [IsIdempotentComplete C] in
/-- Precomposition by an isomorphism preserves left minimality. -/
theorem IsLeftMinimal.precomp_iso
    {X Y Z : C} {g : Y ⟶ Z}
    (e : X ≅ Y) (hg : IsLeftMinimal g) :
    IsLeftMinimal (e.hom ≫ g) := by
  intro a ha
  apply hg a
  rw [← cancel_epi e.hom]
  simpa only [Category.assoc] using ha

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- Postcomposing a left-minimal map by a split epimorphism preserves left
minimality. -/
theorem IsLeftMinimal.postcomp_splitEpi
    {X Y Z : C} {g : X ⟶ Y}
    (hg : IsLeftMinimal g) (p : Y ⟶ Z) [IsSplitEpi p] :
    IsLeftMinimal (g ≫ p) := by
  intro e he
  let E : Y ⟶ Y :=
    p ≫ e ≫ section_ p +
      (𝟙 Y - p ≫ section_ p)
  have hmain :
      g ≫ p ≫ e ≫ section_ p =
        g ≫ p ≫ section_ p := by
    simpa only [Category.assoc] using
      congrArg (fun q ↦ q ≫ section_ p) he
  have hgE : g ≫ E = g := by
    dsimp only [E]
    simp only [Preadditive.comp_add, Preadditive.comp_sub,
      Category.comp_id]
    rw [hmain]
    simp [sub_eq_add_neg, add_left_comm]
  letI : IsIso E := hg E hgE
  have hEp : E ≫ p = p ≫ e := by
    simp [E, Category.assoc]
  have hsE : section_ p ≫ E = e ≫ section_ p := by
    simp [E]
  apply IsIso.mk
  refine ⟨section_ p ≫ inv E ≫ p, ?_, ?_⟩
  · calc
      e ≫ (section_ p ≫ inv E ≫ p) =
          (e ≫ section_ p) ≫ inv E ≫ p := by
            simp only [Category.assoc]
      _ = (section_ p ≫ E) ≫ inv E ≫ p := by rw [← hsE]
      _ = 𝟙 Z := by simp
  · calc
      (section_ p ≫ inv E ≫ p) ≫ e =
          section_ p ≫ inv E ≫ (p ≫ e) := by
            simp only [Category.assoc]
      _ = section_ p ≫ inv E ≫ (E ≫ p) := by rw [← hEp]
      _ = 𝟙 Z := by simp

/-- A split-epimorphic cofactor of a chosen left mesh map is left minimal. -/
theorem isLeftMinimal_splitCofactor_chosen_leftMesh
    (T : FiniteTauCategoryData C Ind)
    {X Z : C} (p : (T.leftMesh X).X₂ ⟶ Z) [IsSplitEpi p] :
    IsLeftMinimal
      ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p) := by
  simpa only [Iso.symm_hom, Category.assoc] using
    IsLeftMinimal.postcomp_splitEpi
      (IsLeftMinimal.precomp_iso (T.leftTermIso X).symm
        (T.leftTau X).isLeftMinimal_f) p

/-- Radical-square perturbations of a split-epimorphic chosen-left-mesh
cofactor remain left minimal. -/
theorem isLeftMinimal_add_mem_square_splitCofactor_chosen_leftMesh
    (T : FiniteTauCategoryData C Ind)
    {X Z : C} (p : (T.leftMesh X).X₂ ⟶ Z) [IsSplitEpi p]
    (r : X ⟶ Z)
    (hr : r ∈ (T.radical.ideal.pow 2).hom X Z) :
    IsLeftMinimal
      ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p + r) := by
  have hr' :
      (T.leftTermIso X).hom ≫ r ∈
        (T.radical.ideal.pow 2).hom (T.leftMesh X).X₁ Z :=
    (T.radical.ideal.pow 2).precomp (T.leftTermIso X).hom hr
  obtain ⟨s, hs, hsEq⟩ :=
    RightLadder.exists_factor_through_tau_f_of_mem_pow_succ
      T.radical (T.leftTau X).toTauApproximation 1 hr'
  have hsRad : IsRadicalMorphism s :=
    (T.radical.mem_ideal_iff s).1 (by simpa using hs)
  letI : IsSplitEpi (p + s) :=
    isSplitEpi_add_of_isRadicalMorphism p hsRad
  let μ : X ⟶ (T.leftMesh X).X₂ :=
    (T.leftTermIso X).inv ≫ (T.leftMesh X).f
  have hμs : μ ≫ s = r := by
    calc
      μ ≫ s =
          (T.leftTermIso X).inv ≫
            ((T.leftTermIso X).hom ≫ r) := by
              simpa only [μ, Category.assoc] using
                congrArg (fun q ↦ (T.leftTermIso X).inv ≫ q) hsEq
      _ = r := by simp
  have hsum :
      μ ≫ (p + s) = μ ≫ p + r := by
    rw [Preadditive.comp_add, hμs]
  have hminimal :=
    isLeftMinimal_splitCofactor_chosen_leftMesh T (p + s)
  have hminimal' : IsLeftMinimal (μ ≫ (p + s)) := by
    simpa only [μ, Category.assoc] using hminimal
  rw [hsum] at hminimal'
  simpa only [μ, Category.assoc] using hminimal'

/-- If a target-padded arrow defined by a split left-mesh cofactor is
special, its essential component is special. -/
theorem isSpecial_splitCofactor_of_isSpecial_padded
    (T : FiniteTauCategoryData C Ind)
    {X Z U : C} (p : (T.leftMesh X).X₂ ⟶ Z) [IsSplitEpi p]
    (hpadded : IsSpecial T.radical
      (biprod.lift
        ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p)
        (0 : X ⟶ U))) :
    IsSpecial T.radical
      ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p) := by
  apply IsSpecial.cancel_biprod_lift_zero T.radical hpadded
    (isLeftMinimal_splitCofactor_chosen_leftMesh T p)
  intro r hr
  exact isLeftMinimal_add_mem_square_splitCofactor_chosen_leftMesh
    T p r hr

/-- Every radical arrow out of `X` factors through the first map of the
chosen left mesh at `X`, after the recorded endpoint isomorphism. -/
theorem exists_factor_through_chosen_leftMesh
    (T : FiniteTauCategoryData C Ind)
    {X Y : C} (a : X ⟶ Y) (ha : IsRadicalMorphism a) :
    ∃ k : (T.leftMesh X).X₂ ⟶ Y,
      (T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ k = a := by
  have ha' :
      IsRadicalMorphism ((T.leftTermIso X).hom ≫ a) :=
    isRadicalMorphism_precomp (T.leftTermIso X).hom ha
  obtain ⟨k, hk⟩ :=
    (T.leftTau X).factors_from_left
      ((T.leftTermIso X).hom ≫ a) ha'
  refine ⟨k, ?_⟩
  calc
    (T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ k =
        (T.leftTermIso X).inv ≫
          ((T.leftTermIso X).hom ≫ a) := by
            simpa only [Category.assoc] using
              congrArg (fun q ↦ (T.leftTermIso X).inv ≫ q) hk
    _ = a := by simp

/-- Iyama's special-arrow target normalization: every special arrow is
isomorphic to a target-zero-padded split cofactor of the chosen left mesh,
and its essential component remains special. -/
theorem exists_special_splitCofactor_normalForm
    (T : FiniteTauCategoryData C Ind)
    {X Y : C} (a : X ⟶ Y) (ha : IsSpecial T.radical a) :
    ∃ (Z U : C) (p : (T.leftMesh X).X₂ ⟶ Z),
      IsSplitEpi p ∧
        IsSpecial T.radical
          ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p) ∧
        Nonempty
          (Arrow.mk a ≅
            Arrow.mk
              (biprod.lift
                ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p)
                (0 : X ⟶ U))) := by
  obtain ⟨k, hk⟩ := exists_factor_through_chosen_leftMesh T a ha.1
  obtain ⟨Z, U, eY, p, r, hp, hrRad, hnormal⟩ :=
    FiniteTauCategoryData.exists_splitEpi_radical_normalForm T k
  let μ : X ⟶ (T.leftMesh X).X₂ :=
    (T.leftTermIso X).inv ≫ (T.leftMesh X).f
  let b : X ⟶ Z :=
    (T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p
  let q : X ⟶ U := μ ≫ r
  have hk' : μ ≫ k = a := by
    simpa only [μ, Category.assoc] using hk
  have hraw : a ≫ eY.hom = biprod.lift b q := by
    calc
      a ≫ eY.hom = (μ ≫ k) ≫ eY.hom := by rw [hk']
      _ = μ ≫ (k ≫ eY.hom) := Category.assoc _ _ _
      _ = μ ≫ biprod.lift p r := by rw [hnormal]
      _ = biprod.lift b q := by
        apply biprod.hom_ext <;> simp [b, q, μ, Category.assoc]
  let eraw : Arrow.mk a ≅ Arrow.mk (biprod.lift b q) :=
    Arrow.isoMk' a (biprod.lift b q) (Iso.refl X) eY
      (by simpa using hraw.symm)
  have hμRad : IsRadicalMorphism μ := by
    exact isRadicalMorphism_precomp (T.leftTermIso X).inv
      (T.leftTau X).f_radical
  have hμMem :
      μ ∈ T.radical.ideal.hom X (T.leftMesh X).X₂ :=
    (T.radical.mem_ideal_iff μ).2 hμRad
  have hrMem : r ∈ T.radical.ideal.hom (T.leftMesh X).X₂ U :=
    (T.radical.mem_ideal_iff r).2 hrRad
  have hq : q ∈ (T.radical.ideal.pow 2).hom X U := by
    simpa [q] using CategoricalIdeal.HomIdeal.comp_mem_mul hμMem hrMem
  obtain ⟨epadded⟩ :=
    IsSpecial.nonempty_iso_biprod_lift_zero_of_iso T.radical ha eraw hq
  letI : IsSplitEpi p := hp
  have hpadded : IsSpecial T.radical
      (biprod.lift b (0 : X ⟶ U)) :=
    ha.of_iso T.radical epadded
  have hbSpecial : IsSpecial T.radical b := by
    exact isSpecial_splitCofactor_of_isSpecial_padded T p
      (by simpa only [b] using hpadded)
  refine ⟨Z, U, p, hp, ?_, ?_⟩
  · simpa only [b] using hbSpecial
  · exact ⟨by simpa only [b] using epadded⟩

/-- Choose the target conormalization of an arbitrary special arrow. -/
def chooseSpecialConormalization
    (T : FiniteTauCategoryData C Ind)
    {X Y : C} (a : X ⟶ Y) (ha : IsSpecial T.radical a) :
    SpecialConormalization T a := by
  let h := exists_special_splitCofactor_normalForm T a ha
  let Z := Classical.choose h
  let hZ := Classical.choose_spec h
  let U := Classical.choose hZ
  let hZU := Classical.choose_spec hZ
  let p := Classical.choose hZU
  let hpse := Classical.choose_spec hZU
  have hp : IsSplitEpi p := hpse.1
  have hb : IsSpecial T.radical
      ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p) :=
    hpse.2.1
  have e : Nonempty
      (Arrow.mk a ≅
        Arrow.mk
          (biprod.lift
            ((T.leftTermIso X).inv ≫ (T.leftMesh X).f ≫ p)
            (0 : X ⟶ U))) :=
    hpse.2.2
  letI : IsSplitEpi p := hp
  exact
    { state :=
        { Z := Z
          U := U
          p := p
          p_split := hp
          special := hb }
      arrowIso := e }

end MBDVendor.QSE.Iyama.LeftLadder
