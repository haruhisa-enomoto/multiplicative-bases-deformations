import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtNormalForm

/-!
# Target split--radical normal form

This is the categorical dual of the source normal form used in Iyama's
right-ladder construction.  No concrete algebra or module classification is
used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MBDVendor.QSE.Iyama.LeftLadder

open CategoricalRadical CategoricalIdeal

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]

omit [HasFiniteBiproducts C] in
/-- An elementary lower shear of a binary biproduct. -/
def biprodTargetShear {Z U : C} (c : Z ⟶ U) :
    biprod Z U ≅ biprod Z U where
  hom := biprod.desc (biprod.lift (𝟙 Z) c) biprod.inr
  inv := biprod.desc (biprod.lift (𝟙 Z) (-c)) biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp

omit [HasFiniteBiproducts C] in
@[reassoc]
theorem lift_biprodTargetShear_hom {M Z U : C} (c : Z ⟶ U)
    (p : M ⟶ Z) (r : M ⟶ U) :
    biprod.lift p r ≫ (biprodTargetShear c).hom =
      biprod.lift p (p ≫ c + r) := by
  apply biprod.hom_ext <;> simp [biprodTargetShear, Category.assoc]

omit [HasFiniteBiproducts C] in
/-- Target-side counterpart of `moveLeftPastFirstIso_inv_desc`. -/
theorem lift_moveLeftPastFirstIso_hom
    {M P Q Z U : C} (e : Q ≅ biprod Z U)
    (f : M ⟶ P) (q : M ⟶ Q) (p : M ⟶ Z) (r : M ⟶ U)
    (hq : q ≫ e.hom = biprod.lift p r) :
    biprod.lift f q ≫ (moveLeftPastFirstIso e).hom =
      biprod.lift p (biprod.lift f r) := by
  apply biprod.hom_ext
  · simpa [moveLeftPastFirstIso, Category.assoc] using
      congrArg (fun k ↦ k ≫ biprod.fst) hq
  · apply biprod.hom_ext
    · simp [moveLeftPastFirstIso, Category.assoc]
    · simpa [moveLeftPastFirstIso, Category.assoc] using
        congrArg (fun k ↦ k ≫ biprod.snd) hq

omit [HasFiniteBiproducts C] in
theorem lift_lift_associator_inv
    {M Z P U : C} (p : M ⟶ Z) (a : M ⟶ P) (r : M ⟶ U) :
    biprod.lift p (biprod.lift a r) ≫
        (biprod.associator Z P U).inv =
      biprod.lift (biprod.lift p a) r := by
  apply biprod.hom_ext
  · apply biprod.hom_ext <;>
      simp [biprod.associator, Category.assoc]
  · simp [biprod.associator, Category.assoc]

/-- A target split--radical form: after changing the target by an
isomorphism, a morphism is a column consisting of a split epimorphism and a
categorical-radical morphism. -/
structure CosplitRadicalForm
    (R : NilpotentRadicalData C) {M Y : C} (k : M ⟶ Y) where
  Z : C
  U : C
  e : Y ≅ biprod Z U
  p : M ⟶ Z
  r : M ⟶ U
  s : Z ⟶ M
  s_p : s ≫ p = 𝟙 Z
  s_r : s ≫ r = 0
  r_mem : r ∈ R.ideal.hom M U
  map_eq : k ≫ e.hom = biprod.lift p r

namespace CosplitRadicalForm

/-- Transport a target split--radical form along an isomorphism of targets. -/
noncomputable def postcomposeIso
    {R : NilpotentRadicalData C} {M X Y : C}
    {q : M ⟶ X} (h : CosplitRadicalForm R q)
    (e₀ : X ≅ Y) (k : M ⟶ Y) (hk : k ≫ e₀.inv = q) :
    CosplitRadicalForm R k where
  Z := h.Z
  U := h.U
  e := e₀.symm.trans h.e
  p := h.p
  r := h.r
  s := h.s
  s_p := h.s_p
  s_r := h.s_r
  r_mem := h.r_mem
  map_eq := by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hk, h.map_eq]

end CosplitRadicalForm

variable [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- A morphism into a chosen indecomposable is radical exactly when it is
not a split epimorphism. -/
theorem FiniteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
    (T : FiniteTauCategoryData C Ind)
    {x : Ind} {M : C} (f : M ⟶ T.obj x) :
    IsRadicalMorphism f ↔ ¬ IsSplitEpi f :=
  T.toFiniteRightTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj f

/-- Add one chosen indecomposable target summand to a target split--radical
normal form. -/
noncomputable def cosplitRadicalForm_biprod_obj
    (T : FiniteTauCategoryData C Ind) (x : Ind)
    {M Q : C} (f : M ⟶ T.obj x) (q : M ⟶ Q)
    (hq : CosplitRadicalForm T.radical q) :
    CosplitRadicalForm T.radical (biprod.lift f q) := by
  let Z := hq.Z
  let U := hq.U
  let p := hq.p
  let r := hq.r
  let s := hq.s
  let eBase : biprod (T.obj x) Q ≅
      biprod Z (biprod (T.obj x) U) :=
    moveLeftPastFirstIso hq.e
  have hBase :
      biprod.lift f q ≫ eBase.hom =
        biprod.lift p (biprod.lift f r) :=
    lift_moveLeftPastFirstIso_hom hq.e f q p r hq.map_eq
  let c₁ : Z ⟶ biprod (T.obj x) U :=
    biprod.lift (-(s ≫ f)) 0
  let a : M ⟶ T.obj x := p ≫ (-(s ≫ f)) + f
  have hs_a : s ≫ a = 0 := by
    dsimp only [a]
    rw [Preadditive.comp_add, ← Category.assoc, hq.s_p,
      Category.id_comp, neg_add_cancel]
  have hc₁ :
      p ≫ c₁ + biprod.lift f r = biprod.lift a r := by
    apply biprod.hom_ext
    · rw [Preadditive.add_comp, Category.assoc]
      dsimp only [c₁, a]
      rw [biprod.lift_fst, biprod.lift_fst, biprod.lift_fst]
    · simp [c₁]
  let e₁ : biprod (T.obj x) Q ≅
      biprod Z (biprod (T.obj x) U) :=
    eBase.trans (biprodTargetShear c₁)
  have he₁ :
      biprod.lift f q ≫ e₁.hom =
        biprod.lift p (biprod.lift a r) := by
    dsimp only [e₁]
    rw [Iso.trans_hom, ← Category.assoc, hBase,
      lift_biprodTargetShear_hom, hc₁]
  by_cases ha : IsRadicalMorphism a
  · refine
      { Z := Z
        U := biprod (T.obj x) U
        e := e₁
        p := p
        r := biprod.lift a r
        s := s
        s_p := hq.s_p
        s_r := ?_
        r_mem := ?_
        map_eq := he₁ }
    · apply biprod.hom_ext
      · simpa [Category.assoc] using hs_a
      · simpa [Category.assoc] using hq.s_r
    · have ha_mem : a ∈ T.radical.ideal.hom M (T.obj x) :=
        (T.radical.mem_ideal_iff a).2 ha
      rw [show biprod.lift a r =
          a ≫ biprod.inl + r ≫ biprod.inr by
            apply biprod.hom_ext <;> simp]
      exact (T.radical.ideal.hom _ _).add_mem
        (T.radical.ideal.postcomp biprod.inl ha_mem)
        (T.radical.ideal.postcomp biprod.inr hq.r_mem)
  · have hsplit : IsSplitEpi a := by
      apply Classical.not_not.mp
      intro hnot
      exact ha
        ((FiniteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
          T a).2 hnot)
    letI : IsSplitEpi a := hsplit
    let t : T.obj x ⟶ M := section_ a
    let t' : T.obj x ⟶ M := t - t ≫ p ≫ s
    have ht'_p : t' ≫ p = 0 := by
      dsimp only [t']
      rw [Preadditive.sub_comp]
      calc
        t ≫ p - (t ≫ p ≫ s) ≫ p =
            t ≫ p - t ≫ p ≫ (s ≫ p) := by
              simp only [Category.assoc]
        _ = 0 := by rw [hq.s_p, Category.comp_id, sub_self]
    have ht'_a : t' ≫ a = 𝟙 (T.obj x) := by
      dsimp only [t']
      rw [Preadditive.sub_comp]
      calc
        t ≫ a - (t ≫ p ≫ s) ≫ a =
            t ≫ a - t ≫ p ≫ (s ≫ a) := by
              simp only [Category.assoc]
        _ = t ≫ a := by simp only [hs_a, comp_zero, sub_zero]
        _ = 𝟙 (T.obj x) := IsSplitEpi.id a
    let p' : M ⟶ biprod Z (T.obj x) := biprod.lift p a
    let s' : biprod Z (T.obj x) ⟶ M := biprod.desc s t'
    have hs'_p' : s' ≫ p' = 𝟙 _ := by
      apply biprod.hom_ext'
      · apply biprod.hom_ext
        · simpa [p', s', Category.assoc] using hq.s_p
        · simpa [p', s', Category.assoc] using hs_a
      · apply biprod.hom_ext
        · simpa [p', s', Category.assoc] using ht'_p
        · simpa [p', s', Category.assoc] using ht'_a
    let c₂ : biprod Z (T.obj x) ⟶ U := -(s' ≫ r)
    let r' : M ⟶ U := p' ≫ c₂ + r
    have hs'_r' : s' ≫ r' = 0 := by
      dsimp only [r', c₂]
      rw [Preadditive.comp_add, ← Category.assoc, hs'_p',
        Category.id_comp, neg_add_cancel]
    let eAssoc : biprod (T.obj x) Q ≅
        biprod (biprod Z (T.obj x)) U :=
      e₁.trans (biprod.associator Z (T.obj x) U).symm
    have heAssoc :
        biprod.lift f q ≫ eAssoc.hom = biprod.lift p' r := by
      dsimp only [eAssoc]
      rw [Iso.trans_hom, ← Category.assoc, he₁,
        Iso.symm_hom]
      exact lift_lift_associator_inv p a r
    let e₂ : biprod (T.obj x) Q ≅
        biprod (biprod Z (T.obj x)) U :=
      eAssoc.trans (biprodTargetShear c₂)
    have he₂ :
        biprod.lift f q ≫ e₂.hom = biprod.lift p' r' := by
      dsimp only [e₂]
      rw [Iso.trans_hom, ← Category.assoc, heAssoc,
        lift_biprodTargetShear_hom]
    refine
      { Z := biprod Z (T.obj x)
        U := U
        e := e₂
        p := p'
        r := r'
        s := s'
        s_p := hs'_p'
        s_r := hs'_r'
        r_mem := ?_
        map_eq := he₂ }
    dsimp only [r', c₂]
    simpa only [U, r, Preadditive.comp_neg] using
      (T.radical.ideal.hom M U).add_mem
        (T.radical.ideal.precomp p'
          (T.radical.ideal.precomp s'
            ((T.radical.ideal.hom _ _).neg_mem hq.r_mem)))
        hq.r_mem

/-- Target split--radical normal form for a morphism whose target is a
displayed finite biproduct of chosen indecomposables. -/
noncomputable def cosplitRadicalForm_finBiproduct
    (T : FiniteTauCategoryData C Ind) :
    ∀ (n : ℕ) (label : Fin n → Ind) (M : C)
      (k : M ⟶ (⨁ fun i ↦ T.obj (label i))),
      CosplitRadicalForm T.radical k := by
  intro n
  induction n with
  | zero =>
      intro label M k
      have hk : k = 0 := by
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      let e₀ : (⨁ fun i ↦ T.obj (label i)) ≅
          biprod (0 : C) (⨁ fun i ↦ T.obj (label i)) :=
        isoZeroBiprod (isZero_zero C)
      refine
        { Z := 0
          U := (⨁ fun i ↦ T.obj (label i))
          e := e₀
          p := 0
          r := k
          s := 0
          s_p := ?_
          s_r := ?_
          r_mem := ?_
          map_eq := ?_ }
      · exact (isZero_zero C).eq_of_src _ _
      · simp
      · rw [hk]
        exact (T.radical.ideal.hom _ _).zero_mem
      · rw [hk]
        apply biprod.hom_ext <;> simp
  | succ n ih =>
      intro label M k
      let F : Fin (n + 1) → C := fun i ↦ T.obj (label i)
      let tailLabel : Fin n → Ind := fun i ↦ label i.succ
      let eCons : (⨁ F) ≅
          biprod (T.obj (label 0))
            (⨁ fun i ↦ T.obj (tailLabel i)) :=
        finBiproductConsIso F
      let k' : M ⟶
          biprod (T.obj (label 0))
            (⨁ fun i ↦ T.obj (tailLabel i)) :=
        k ≫ eCons.hom
      let f : M ⟶ T.obj (label 0) := k' ≫ biprod.fst
      let q : M ⟶ (⨁ fun i ↦ T.obj (tailLabel i)) :=
        k' ≫ biprod.snd
      let hq : CosplitRadicalForm T.radical q := ih tailLabel M q
      let h' : CosplitRadicalForm T.radical (biprod.lift f q) :=
        cosplitRadicalForm_biprod_obj T (label 0) f q hq
      have hk' : k ≫ eCons.hom = biprod.lift f q := by
        change k' = biprod.lift f q
        symm
        apply biprod.hom_ext
        · simp [f]
        · simp [q]
      exact h'.postcomposeIso eCons.symm k hk'

/-- Every morphism in a finite tau-category has a target split--radical
normal form. -/
noncomputable def FiniteTauCategoryData.cosplitRadicalForm
    (T : FiniteTauCategoryData C Ind) {M Y : C} (k : M ⟶ Y) :
    CosplitRadicalForm T.radical k := by
  let n := (T.obj_decomposition Y).choose
  let label := (T.obj_decomposition Y).choose_spec.choose
  let eY : Y ≅ (⨁ fun i ↦ T.obj (label i)) :=
    (T.obj_decomposition Y).choose_spec.choose_spec.some
  let k' : M ⟶ (⨁ fun i ↦ T.obj (label i)) := k ≫ eY.hom
  let h' : CosplitRadicalForm T.radical k' :=
    cosplitRadicalForm_finBiproduct T n label M k'
  exact h'.postcomposeIso eY.symm k rfl

/-- Existential target normal form: after an isomorphism `Y ≅ Z ⨞ U`,
the map is the pair of a split epimorphism and a categorical-radical
morphism. -/
theorem FiniteTauCategoryData.exists_splitEpi_radical_normalForm
    (T : FiniteTauCategoryData C Ind) {M Y : C} (k : M ⟶ Y) :
    ∃ (Z U : C) (e : Y ≅ biprod Z U)
      (p : M ⟶ Z) (r : M ⟶ U),
      IsSplitEpi p ∧ IsRadicalMorphism r ∧
        k ≫ e.hom = biprod.lift p r := by
  let h := FiniteTauCategoryData.cosplitRadicalForm T k
  refine ⟨h.Z, h.U, h.e, h.p, h.r, ?_, ?_, h.map_eq⟩
  · exact IsSplitEpi.mk' { section_ := h.s, id := h.s_p }
  · exact (T.radical.mem_ideal_iff h.r).1 h.r_mem

end MBDVendor.QSE.Iyama.LeftLadder
