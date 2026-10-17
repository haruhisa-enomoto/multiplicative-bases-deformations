import MBDVendor.QSE.CategoryTheory.IyamaLadderRadical
import MBDVendor.QSE.CategoryTheory.SplitMorphismComplement

/-!
# Krull--Schmidt split--radical normal form

In the finite Krull--Schmidt skeleton recorded by `FiniteTauCategoryData`,
every morphism becomes, after an isomorphism of its source, a row consisting
of a split monomorphism and a categorical-radical morphism.  The proof is a
finite induction over a chosen indecomposable decomposition.  Elementary
biproduct shears add each indecomposable either to the split part or to the
radical remainder.

This is the classification-free normal-form input in Iyama's special-arrow
right-ladder construction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MBDVendor.QSE.Iyama

universe v u w

open CategoricalRadical CategoricalIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]

def finTailProjection {n : ℕ} (F : Fin (n + 1) → C) :
    (⨁ F) ⟶ (⨁ fun i : Fin n ↦ F i.succ) :=
  biproduct.lift fun i ↦ biproduct.π F i.succ

def finTailInclusion {n : ℕ} (F : Fin (n + 1) → C) :
    (⨁ fun i : Fin n ↦ F i.succ) ⟶ (⨁ F) :=
  biproduct.desc fun i ↦ biproduct.ι F i.succ

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem fin_head_tailProjection {n : ℕ} (F : Fin (n + 1) → C) :
    biproduct.ι F 0 ≫ finTailProjection F = 0 := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, finTailProjection, biproduct.lift_π,
    biproduct.ι_π_ne F (Fin.succ_ne_zero j).symm,
    zero_comp]

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem fin_tailComponent_tailProjection {n : ℕ}
    (F : Fin (n + 1) → C) (j : Fin n) :
    biproduct.ι F j.succ ≫ finTailProjection F =
      biproduct.ι (fun i : Fin n ↦ F i.succ) j := by
  apply biproduct.hom_ext
  intro l
  rw [Category.assoc, finTailProjection, biproduct.lift_π]
  by_cases h : j = l
  · subst l
    simp
  · rw [biproduct.ι_π_ne F (fun e ↦ h (Fin.succ_injective n e)),
      biproduct.ι_π_ne _ h]

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem fin_tailInclusion_head {n : ℕ} (F : Fin (n + 1) → C) :
    finTailInclusion F ≫ biproduct.π F 0 = 0 := by
  apply biproduct.hom_ext'
  intro j
  rw [finTailInclusion, biproduct.ι_desc_assoc,
    biproduct.ι_π_ne F (Fin.succ_ne_zero j)]
  simp

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem fin_tailInclusion_component {n : ℕ}
    (F : Fin (n + 1) → C) (j : Fin n) :
    finTailInclusion F ≫ biproduct.π F j.succ =
      biproduct.π (fun i : Fin n ↦ F i.succ) j := by
  apply biproduct.hom_ext'
  intro l
  rw [finTailInclusion, biproduct.ι_desc_assoc]
  by_cases h : l = j
  · subst l
    simp
  · rw [biproduct.ι_π_ne F (fun e ↦ h (Fin.succ_injective n e)),
      biproduct.ι_π_ne _ h]

omit [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
theorem fin_tailInclusion_tailProjection {n : ℕ}
    (F : Fin (n + 1) → C) :
    finTailInclusion F ≫ finTailProjection F = 𝟙 _ := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, finTailProjection, biproduct.lift_π,
    fin_tailInclusion_component, Category.id_comp]

/-- Split off the first factor of a `Fin (n+1)`-indexed biproduct. -/
def finBiproductConsIso {n : ℕ} (F : Fin (n + 1) → C) :
    (⨁ F) ≅ biprod (F 0) (⨁ fun i : Fin n ↦ F i.succ) where
  hom := biprod.lift
    (biproduct.π F 0)
    (finTailProjection F)
  inv := biprod.desc
    (biproduct.ι F 0)
    (finTailInclusion F)
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext i j
    refine Fin.cases ?_ (fun i' ↦ ?_) i
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · simp [Category.assoc]
      · simp [Category.assoc]
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · simp [Category.assoc]
      · by_cases h : i' = j'
        · subst j'
          simp [Category.assoc]
        · simp [Category.assoc, Ne.symm h]
  inv_hom_id := by
    ext <;> simp [Category.assoc]

/-- An elementary upper shear of a binary biproduct. -/
def biprodShear {Z U : C} (c : U ⟶ Z) : biprod Z U ≅ biprod Z U where
  hom := biprod.lift (biprod.fst + biprod.snd ≫ c) biprod.snd
  inv := biprod.lift (biprod.fst - biprod.snd ≫ c) biprod.snd
  hom_inv_id := by
    apply biprod.hom_ext
    · simp [Category.assoc]
    · simp
  inv_hom_id := by
    apply biprod.hom_ext
    · simp [Category.assoc]
    · simp

omit [HasFiniteBiproducts C] in
@[reassoc]
theorem biprodShear_hom_desc {Z U M : C} (c : U ⟶ Z)
    (j : Z ⟶ M) (r : U ⟶ M) :
    (biprodShear c).hom ≫ biprod.desc j r =
      biprod.desc j (c ≫ j + r) := by
  apply biprod.hom_ext'
  · simp [biprodShear]
  · simp [biprodShear, Preadditive.add_comp, Category.assoc]

/-- Move the left factor past the first factor of a decomposed right term. -/
def moveLeftPastFirstIso {P Q Z U : C} (e : Q ≅ biprod Z U) :
    biprod P Q ≅ biprod Z (biprod P U) where
  hom := biprod.lift
    (biprod.snd ≫ e.hom ≫ biprod.fst)
    (biprod.lift biprod.fst
      (biprod.snd ≫ e.hom ≫ biprod.snd))
  inv := biprod.lift
    (biprod.snd ≫ biprod.fst)
    (biprod.lift biprod.fst (biprod.snd ≫ biprod.snd) ≫ e.inv)
  hom_inv_id := by
    apply biprod.hom_ext
    · simp [Category.assoc]
    · rw [← cancel_mono e.hom]
      apply biprod.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by cat_disch

omit [HasFiniteBiproducts C] in
theorem moveLeftPastFirstIso_inv_desc
    {P Q Z U M : C} (e : Q ≅ biprod Z U)
    (f : P ⟶ M) (q : Q ⟶ M) (j : Z ⟶ M) (r : U ⟶ M)
    (hq : e.inv ≫ q = biprod.desc j r) :
    (moveLeftPastFirstIso e).inv ≫ biprod.desc f q =
      biprod.desc j (biprod.desc f r) := by
  have hz : biprod.inl ≫ e.inv ≫ q = j := by
    have h := congrArg (fun a ↦ biprod.inl ≫ a) hq
    simpa [Category.assoc] using h
  have hu : biprod.inr ≫ e.inv ≫ q = r := by
    have h := congrArg (fun a ↦ biprod.inr ≫ a) hq
    simpa [Category.assoc] using h
  let B : biprod Z (biprod P U) ⟶ biprod Z U :=
    biprod.lift biprod.fst (biprod.snd ≫ biprod.snd)
  let A : biprod Z (biprod P U) ⟶ P :=
    biprod.snd ≫ biprod.fst
  have hAZ : biprod.inl ≫ A = 0 := by
    simp [A]
  have hAP : biprod.inl ≫ biprod.inr ≫ A = 𝟙 P := by
    simp [A]
  have hAU : biprod.inr ≫ biprod.inr ≫ A = 0 := by
    simp [A]
  have hBZ : biprod.inl ≫ B = biprod.inl := by
    apply biprod.hom_ext <;> simp [B, Category.assoc]
  have hBP : biprod.inl ≫ biprod.inr ≫ B = 0 := by
    apply biprod.hom_ext <;> simp [B, Category.assoc]
  have hBU : biprod.inr ≫ biprod.inr ≫ B = biprod.inr := by
    apply biprod.hom_ext <;> simp [B, Category.assoc]
  change
    biprod.lift A (B ≫ e.inv) ≫
        biprod.desc f q =
      biprod.desc j (biprod.desc f r)
  rw [biprod.lift_desc]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc, Preadditive.comp_add]
    calc
      biprod.inl ≫ A ≫ f +
            biprod.inl ≫ (B ≫ e.inv) ≫ q =
          (biprod.inl ≫ A) ≫ f +
            (biprod.inl ≫ B) ≫ e.inv ≫ q := by
            simp only [Category.assoc]
      _ = biprod.inl ≫ e.inv ≫ q := by
        rw [hAZ, hBZ, zero_comp, zero_add]
      _ = j := hz
  · apply biprod.hom_ext'
    · rw [biprod.inr_desc, biprod.inl_desc,
        Preadditive.comp_add, Preadditive.comp_add]
      calc
        biprod.inl ≫ biprod.inr ≫ A ≫ f +
              biprod.inl ≫ biprod.inr ≫ (B ≫ e.inv) ≫ q =
            (biprod.inl ≫ biprod.inr ≫ A) ≫ f +
              (biprod.inl ≫ biprod.inr ≫ B) ≫ e.inv ≫ q := by
              simp only [Category.assoc]
        _ = f := by
          rw [hAP, hBP, Category.id_comp, zero_comp, add_zero]
    · rw [biprod.inr_desc, biprod.inr_desc,
        Preadditive.comp_add, Preadditive.comp_add]
      calc
        biprod.inr ≫ biprod.inr ≫ A ≫ f +
              biprod.inr ≫ biprod.inr ≫ (B ≫ e.inv) ≫ q =
            (biprod.inr ≫ biprod.inr ≫ A) ≫ f +
              (biprod.inr ≫ biprod.inr ≫ B) ≫ e.inv ≫ q := by
              simp only [Category.assoc]
        _ = biprod.inr ≫ e.inv ≫ q := by
          rw [hAU, hBU, zero_comp, zero_add]
        _ = r := hu

structure SplitRadicalForm
    (R : NilpotentRadicalData C) {X M : C} (k : X ⟶ M) where
  Z : C
  U : C
  e : X ≅ biprod Z U
  j : Z ⟶ M
  r : U ⟶ M
  s : M ⟶ Z
  j_s : j ≫ s = 𝟙 Z
  r_s : r ≫ s = 0
  r_mem : r ∈ R.ideal.hom U M
  map_eq : e.inv ≫ k = biprod.desc j r

namespace SplitRadicalForm

/-- Transport a split--radical form along an isomorphism of source objects. -/
noncomputable def precomposeIso
    {R : NilpotentRadicalData C} {X Y M : C}
    {q : Y ⟶ M} (h : SplitRadicalForm R q)
    (e₀ : X ≅ Y) (k : X ⟶ M) (hk : e₀.inv ≫ k = q) :
    SplitRadicalForm R k where
  Z := h.Z
  U := h.U
  e := e₀.trans h.e
  j := h.j
  r := h.r
  s := h.s
  j_s := h.j_s
  r_s := h.r_s
  r_mem := h.r_mem
  map_eq := by
    rw [Iso.trans_inv, Category.assoc, hk, h.map_eq]

end SplitRadicalForm

omit [HasFiniteBiproducts C] in
theorem associator_hom_desc_desc {Z P U M : C}
    (j : Z ⟶ M) (a : P ⟶ M) (r : U ⟶ M) :
    (biprod.associator Z P U).hom ≫
        biprod.desc j (biprod.desc a r) =
      biprod.desc (biprod.desc j a) r := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext' <;>
      simp [biprod.associator, Category.assoc]
  · simp [biprod.associator, Category.assoc]

variable [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- A split monomorphism between two representatives in the finite right
tau skeleton is an isomorphism. -/
theorem FiniteRightTauCategoryData.isIso_of_isSplitMono_obj_obj
    (T : FiniteRightTauCategoryData C Ind)
    {p q : Ind} (f : T.obj p ⟶ T.obj q) [IsSplitMono f] :
    IsIso f := by
  let d := splitMonoComplement f
  let e : T.obj q ≅ T.obj p ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hcomp : IsZero d.complement :=
    ((T.obj_indec q).2 (T.obj p) d.complement e).resolve_left
      (T.obj_indec p).1
  apply IsIso.mk
  refine ⟨retraction f, IsSplitMono.id f, ?_⟩
  rw [← d.total]
  have hp : d.projection = 0 := hcomp.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hcomp.eq_of_src _ _
  rw [hp, hi, zero_comp, add_zero]

/-- Add one chosen indecomposable source summand to a split--radical
normal form. -/
noncomputable def splitRadicalForm_biprod_obj
    (T : FiniteRightTauCategoryData C Ind) (p : Ind)
    {Q M : C} (f : T.obj p ⟶ M) (q : Q ⟶ M)
    (hq : SplitRadicalForm T.radical q) :
    SplitRadicalForm T.radical (biprod.desc f q) := by
  let Z := hq.Z
  let U := hq.U
  let j := hq.j
  let r := hq.r
  let s := hq.s
  let eBase : biprod (T.obj p) Q ≅
      biprod Z (biprod (T.obj p) U) :=
    moveLeftPastFirstIso hq.e
  have hBase :
      eBase.inv ≫ biprod.desc f q =
        biprod.desc j (biprod.desc f r) :=
    moveLeftPastFirstIso_inv_desc hq.e f q j r hq.map_eq
  let c₁ : biprod (T.obj p) U ⟶ Z :=
    biprod.desc (-(f ≫ s)) 0
  let a : T.obj p ⟶ M := -(f ≫ s) ≫ j + f
  have ha_s : a ≫ s = 0 := by
    dsimp only [a]
    rw [Preadditive.add_comp, Preadditive.neg_comp,
      Category.assoc, hq.j_s, Category.comp_id,
      neg_add_cancel]
  have hc₁ :
      c₁ ≫ j + biprod.desc f r = biprod.desc a r := by
    apply biprod.hom_ext'
    · simp [c₁, a, Category.assoc]
    · simp [c₁]
  let e₁ : biprod (T.obj p) Q ≅
      biprod Z (biprod (T.obj p) U) :=
    eBase.trans (biprodShear c₁).symm
  have he₁ :
      e₁.inv ≫ biprod.desc f q =
        biprod.desc j (biprod.desc a r) := by
    dsimp only [e₁]
    rw [Iso.trans_inv, Iso.symm_inv, Category.assoc,
      hBase, biprodShear_hom_desc, hc₁]
  by_cases ha : IsRadicalMorphism a
  · refine
      { Z := Z
        U := biprod (T.obj p) U
        e := e₁
        j := j
        r := biprod.desc a r
        s := s
        j_s := hq.j_s
        r_s := ?_
        r_mem := ?_
        map_eq := he₁ }
    · apply biprod.hom_ext'
      · simpa [Category.assoc] using ha_s
      · simpa [Category.assoc] using hq.r_s
    · have ha_mem : a ∈ T.radical.ideal.hom (T.obj p) M :=
        (T.radical.mem_ideal_iff a).2 ha
      rw [show biprod.desc a r =
          biprod.fst ≫ a + biprod.snd ≫ r by
            apply biprod.hom_ext' <;> simp]
      exact (T.radical.ideal.hom _ _).add_mem
        (T.radical.ideal.precomp biprod.fst ha_mem)
        (T.radical.ideal.precomp biprod.snd hq.r_mem)
  · have hsplit : IsSplitMono a := by
      apply Classical.not_not.mp
      intro hnot
      exact ha
        ((FiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
          T a).2 hnot)
    letI : IsSplitMono a := hsplit
    let t : M ⟶ T.obj p := retraction a
    let t' : M ⟶ T.obj p := t - s ≫ j ≫ t
    have hj_t' : j ≫ t' = 0 := by
      dsimp only [t']
      rw [Preadditive.comp_sub]
      calc
        j ≫ t - j ≫ (s ≫ j ≫ t) =
            j ≫ t - (j ≫ s) ≫ j ≫ t := by
              simp only [Category.assoc]
        _ = 0 := by rw [hq.j_s, Category.id_comp, sub_self]
    have ha_t' : a ≫ t' = 𝟙 (T.obj p) := by
      dsimp only [t']
      rw [Preadditive.comp_sub]
      calc
        a ≫ t - a ≫ (s ≫ j ≫ t) =
            a ≫ t - (a ≫ s) ≫ j ≫ t := by
              simp only [Category.assoc]
        _ = a ≫ t := by rw [ha_s, zero_comp, sub_zero]
        _ = 𝟙 (T.obj p) := IsSplitMono.id a
    let j' : biprod Z (T.obj p) ⟶ M := biprod.desc j a
    let s' : M ⟶ biprod Z (T.obj p) := biprod.lift s t'
    have hj'_s' : j' ≫ s' = 𝟙 _ := by
      apply biprod.hom_ext'
      · apply biprod.hom_ext
        · simpa [j', s', Category.assoc] using hq.j_s
        · simpa [j', s', Category.assoc] using hj_t'
      · apply biprod.hom_ext
        · simpa [j', s', Category.assoc] using ha_s
        · simpa [j', s', Category.assoc] using ha_t'
    let c₂ : U ⟶ biprod Z (T.obj p) := -(r ≫ s')
    let r' : U ⟶ M := c₂ ≫ j' + r
    have hr'_s' : r' ≫ s' = 0 := by
      dsimp only [r', c₂]
      rw [Preadditive.add_comp, Category.assoc, hj'_s',
        Category.comp_id, neg_add_cancel]
    let eAssoc : biprod (T.obj p) Q ≅
        biprod (biprod Z (T.obj p)) U :=
      e₁.trans (biprod.associator Z (T.obj p) U).symm
    have heAssoc :
        eAssoc.inv ≫ biprod.desc f q = biprod.desc j' r := by
      dsimp only [eAssoc]
      rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, he₁]
      exact associator_hom_desc_desc j a r
    let e₂ : biprod (T.obj p) Q ≅
        biprod (biprod Z (T.obj p)) U :=
      eAssoc.trans (biprodShear c₂).symm
    have he₂ : e₂.inv ≫ biprod.desc f q = biprod.desc j' r' := by
      dsimp only [e₂]
      rw [Iso.trans_inv, Iso.symm_inv, Category.assoc,
        heAssoc, biprodShear_hom_desc]
    refine
      { Z := biprod Z (T.obj p)
        U := U
        e := e₂
        j := j'
        r := r'
        s := s'
        j_s := hj'_s'
        r_s := hr'_s'
        r_mem := ?_
        map_eq := he₂ }
    dsimp only [r', c₂]
    simpa only [U, r, Preadditive.neg_comp] using
      (T.radical.ideal.hom U M).add_mem
        (T.radical.ideal.postcomp j'
          (T.radical.ideal.postcomp s'
            ((T.radical.ideal.hom _ _).neg_mem hq.r_mem)))
        hq.r_mem

/-- Split--radical normal form for a morphism whose source is a displayed
finite biproduct of chosen indecomposables. -/
noncomputable def splitRadicalForm_finBiproduct
    (T : FiniteRightTauCategoryData C Ind) :
    ∀ (n : ℕ) (label : Fin n → Ind) (M : C)
      (k : (⨁ fun i ↦ T.obj (label i)) ⟶ M),
      SplitRadicalForm T.radical k := by
  intro n
  induction n with
  | zero =>
      intro label M k
      have hk : k = 0 := by
        apply biproduct.hom_ext'
        intro i
        exact Fin.elim0 i
      let e₀ : (⨁ fun i ↦ T.obj (label i)) ≅
          biprod (0 : C) (⨁ fun i ↦ T.obj (label i)) :=
        isoZeroBiprod (isZero_zero C)
      refine
        { Z := 0
          U := (⨁ fun i ↦ T.obj (label i))
          e := e₀
          j := 0
          r := k
          s := 0
          j_s := ?_
          r_s := ?_
          r_mem := ?_
          map_eq := ?_ }
      · exact (isZero_zero C).eq_of_src _ _
      · simp
      · rw [hk]
        exact (T.radical.ideal.hom _ _).zero_mem
      · rw [hk]
        apply biprod.hom_ext' <;> simp
  | succ n ih =>
      intro label M k
      let F : Fin (n + 1) → C := fun i ↦ T.obj (label i)
      let tailLabel : Fin n → Ind := fun i ↦ label i.succ
      let eCons : (⨁ F) ≅
          biprod (T.obj (label 0))
            (⨁ fun i ↦ T.obj (tailLabel i)) :=
        finBiproductConsIso F
      let k' :
          biprod (T.obj (label 0))
              (⨁ fun i ↦ T.obj (tailLabel i)) ⟶ M :=
        eCons.inv ≫ k
      let f : T.obj (label 0) ⟶ M := biprod.inl ≫ k'
      let q : (⨁ fun i ↦ T.obj (tailLabel i)) ⟶ M :=
        biprod.inr ≫ k'
      let hq : SplitRadicalForm T.radical q :=
        ih tailLabel M q
      let h' : SplitRadicalForm T.radical (biprod.desc f q) :=
        splitRadicalForm_biprod_obj T (label 0) f q hq
      have hk' : eCons.inv ≫ k = biprod.desc f q := by
        change k' = biprod.desc f q
        symm
        apply biprod.hom_ext'
        · simp [f]
        · simp [q]
      exact h'.precomposeIso eCons k hk'

/-- Every morphism in a finite tau-category has a Krull--Schmidt
split--radical normal form on its source. -/
noncomputable def FiniteRightTauCategoryData.splitRadicalForm
    (T : FiniteRightTauCategoryData C Ind) {X M : C} (k : X ⟶ M) :
    SplitRadicalForm T.radical k := by
  let n := (T.obj_decomposition X).choose
  let label := (T.obj_decomposition X).choose_spec.choose
  let eX : X ≅ (⨁ fun i ↦ T.obj (label i)) :=
    (T.obj_decomposition X).choose_spec.choose_spec.some
  let k' : (⨁ fun i ↦ T.obj (label i)) ⟶ M := eX.inv ≫ k
  let h' : SplitRadicalForm T.radical k' :=
    splitRadicalForm_finBiproduct T n label M k'
  exact h'.precomposeIso eX k rfl

/-- Existential form: after an isomorphism `X ≅ Z ⨞ U`, the map is
the pair of a split monomorphism and a categorical-radical morphism. -/
theorem FiniteRightTauCategoryData.exists_splitMono_radical_normalForm
    (T : FiniteRightTauCategoryData C Ind) {X M : C} (k : X ⟶ M) :
    ∃ (Z U : C) (e : X ≅ biprod Z U)
      (j : Z ⟶ M) (r : U ⟶ M),
      IsSplitMono j ∧ IsRadicalMorphism r ∧
        e.inv ≫ k = biprod.desc j r := by
  let h := FiniteRightTauCategoryData.splitRadicalForm T k
  refine ⟨h.Z, h.U, h.e, h.j, h.r, ?_, ?_, h.map_eq⟩
  · exact IsSplitMono.mk' { retraction := h.s, id := h.j_s }
  · exact (T.radical.mem_ideal_iff h.r).1 h.r_mem

end MBDVendor.QSE.Iyama
