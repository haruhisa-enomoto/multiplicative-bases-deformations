import MultiplicativeBasisDeformations.Foundations.StrictLayers
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtConormalForm
import MBDVendor.QSE.CategoryTheory.IyamaTauSequence

/-!
# Lemma 2.5 in the opposite category

`graded-category.tex:346–347`: "Applying these arguments to the opposite module
category proves exactness of the second sequence in (1) and the assertion at
injective labels." This file transfers the hypotheses of the abstract Lemma 2.5
(`StrictLayers.strict`) to `Cᵒᵖ`:

* the categorical radical and its powers are self-dual
  (`isRadicalMorphism_op_iff`, `mem_Ipow_op_iff`);
* the Krull–Schmidt target normal form of `C` (split epimorphism and radical
  map) is the source normal form of `Cᵒᵖ` (`hasSplitRadicalNormalForm_op`);
* a left tau-sequence `Y → E → T` with epic second map is a right radical
  approximation of `Y` in `Cᵒᵖ` (`approxOfLeftTau`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open MBDVendor.QSE.CategoricalRadical MBDVendor.QSE.CategoricalIdeal

namespace MultiplicativeBasisDeformations.StrictLayers

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem isRadicalMorphism_op_iff {X Y : C} (f : X ⟶ Y) :
    IsRadicalMorphism f.op ↔ IsRadicalMorphism f := by
  constructor
  · intro h g
    have h1 := h g.op
    have e : 𝟙 (op Y) - f.op ≫ g.op = (𝟙 Y - g ≫ f).op := by simp
    rw [e] at h1
    haveI : IsIso (𝟙 Y - g ≫ f) := isIso_of_op _
    exact isIso_one_sub_comp g f
  · intro h g
    haveI := h g.unop
    haveI : IsIso (𝟙 Y - g.unop ≫ f) := isIso_one_sub_comp f g.unop
    have e : 𝟙 (op Y) - f.op ≫ g = (𝟙 Y - g.unop ≫ f).op := by simp
    rw [e]
    infer_instance

theorem isRadicalMorphism_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsRadicalMorphism f.unop ↔ IsRadicalMorphism f :=
  (isRadicalMorphism_op_iff f.unop).symm

/-- The powers of the radical are self-dual. -/
theorem mem_Ipow_op_iff (n : ℕ) : ∀ {X Y : C} (f : X ⟶ Y),
    f.op ∈ (Ipow n : HomIdeal Cᵒᵖ).hom _ _ ↔ f ∈ (Ipow n : HomIdeal C).hom X Y := by
  induction n with
  | zero => intro X Y f; exact ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  | succ n ih =>
      intro X Y f
      constructor
      · intro hf
        rw [Ipow, HomIdeal.pow_succ] at hf
        rw [Ipow, HomIdeal.pow_succ_eq_mul_pow]
        suffices ∀ g : op Y ⟶ op X, g ∈ (HomIdeal.pow (homIdeal : HomIdeal Cᵒᵖ) n ⋆ᵢ homIdeal).hom _ _ →
            g.unop ∈ (homIdeal ⋆ᵢ HomIdeal.pow (homIdeal : HomIdeal C) n).hom X Y from this _ hf
        intro g hg
        induction hg using AddSubgroup.closure_induction with
        | mem g hg =>
            obtain ⟨M, a, b, ha, hb, rfl⟩ := hg
            apply AddSubgroup.subset_closure
            refine ⟨M.unop, b.unop, a.unop, ?_, ?_, rfl⟩
            · rw [mem_homIdeal_iff, isRadicalMorphism_unop_iff]; exact (mem_homIdeal_iff b).1 hb
            · exact (ih a.unop).1 ha
        | zero => simp
        | add a b _ _ ha hb => rw [unop_add]; exact add_mem ha hb
        | neg a _ ha => rw [unop_neg]; exact neg_mem ha
      · intro hf
        rw [Ipow, HomIdeal.pow_succ] at hf
        rw [Ipow, HomIdeal.pow_succ_eq_mul_pow]
        induction hf using AddSubgroup.closure_induction with
        | mem g hg =>
            obtain ⟨M, a, b, ha, hb, rfl⟩ := hg
            apply AddSubgroup.subset_closure
            refine ⟨op M, b.op, a.op, ?_, (ih a).2 ha, rfl⟩
            rw [mem_homIdeal_iff, isRadicalMorphism_op_iff]; exact (mem_homIdeal_iff b).1 hb
        | zero => simp
        | add a b _ _ ha hb => rw [op_add]; exact add_mem ha hb
        | neg a _ ha => rw [op_neg]; exact neg_mem ha

theorem mem_Ipow_unop_iff (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f.unop ∈ (Ipow n : HomIdeal C).hom _ _ ↔ f ∈ (Ipow n : HomIdeal Cᵒᵖ).hom X Y :=
  (mem_Ipow_op_iff n f.unop).symm

section NormalForm

variable [HasBinaryBiproducts C]

/-- The Krull–Schmidt target normal form: after an isomorphism of its target,
every map is a column of a split epimorphism and a radical map. -/
def HasSplitRadicalConormalForm (C : Type u) [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] : Prop :=
  ∀ {M Y : C} (u : M ⟶ Y), ∃ (Z U : C) (e : Y ≅ Z ⊞ U) (p : M ⟶ Z) (r : M ⟶ U),
    IsSplitEpi p ∧ IsRadicalMorphism r ∧ u ≫ e.hom = biprod.lift p r

/-- A biproduct decomposition in `C` gives one in `Cᵒᵖ`. -/
def opBiprodIso {Y Z U : C} (e : Y ≅ Z ⊞ U) : op Y ≅ op Z ⊞ op U where
  hom := biprod.lift (biprod.inl ≫ e.inv).op (biprod.inr ≫ e.inv).op
  inv := biprod.desc (e.hom ≫ biprod.fst).op (e.hom ≫ biprod.snd).op
  hom_inv_id := by
    rw [biprod.lift_desc, ← op_comp, ← op_comp, ← op_add]
    have : (e.hom ≫ biprod.fst) ≫ biprod.inl ≫ e.inv + (e.hom ≫ biprod.snd) ≫ biprod.inr ≫ e.inv =
        𝟙 Y := by
      rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, ← Category.assoc biprod.fst,
        ← Category.assoc biprod.snd, ← Preadditive.add_comp, biprod.total, Category.id_comp,
        Iso.hom_inv_id]
    rw [this, op_id]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · rw [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst, ← op_comp, Category.comp_id]
        simp
      · rw [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd, ← op_comp, Category.comp_id]
        simp
    · apply biprod.hom_ext
      · rw [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, ← op_comp, Category.comp_id]
        simp
      · rw [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd, ← op_comp, Category.comp_id]
        simp

theorem hasSplitRadicalNormalForm_op (h : HasSplitRadicalConormalForm C) :
    HasSplitRadicalNormalForm Cᵒᵖ := by
  intro U E u
  obtain ⟨Z, U', e, p, r, hp, hr, he⟩ := h u.unop
  refine ⟨op Z, op U', opBiprodIso e, p.op, r.op, ?_, (isRadicalMorphism_op_iff r).2 hr, ?_⟩
  · exact IsSplitMono.mk' ⟨(section_ p).op, by rw [← op_comp, IsSplitEpi.id, op_id]⟩
  · change biprod.desc (e.hom ≫ biprod.fst).op (e.hom ≫ biprod.snd).op ≫ u = _
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, biprod.inl_desc]
      rw [← Quiver.Hom.op_unop u, ← op_comp]
      all_goals rw [← Category.assoc, he, biprod.lift_fst]
    · rw [biprod.inr_desc_assoc, biprod.inr_desc]
      rw [← Quiver.Hom.op_unop u, ← op_comp]
      all_goals rw [← Category.assoc, he, biprod.lift_snd]

end NormalForm

/-- The weak cokernel property of the second map of a short complex. -/
def IsWeakCok (M : ShortComplex C) : Prop :=
  ∀ {W : C} (k : M.X₂ ⟶ W), M.f ≫ k = 0 → ∃ l : M.X₃ ⟶ W, M.g ≫ l = k

theorem isWeakCok_of_left (M : ShortComplex C) (hM : MBDVendor.QSE.Iyama.LeftTauSequence M) :
    IsWeakCok M :=
  fun k hk ↦ (MBDVendor.QSE.Iyama.ShortComplex.isWeakCokernel_iff M).1 hM.minimalWeakCokernel.1 k hk

theorem isWeakCok_of_iso {M N : ShortComplex C} (e : M ≅ N) (h : IsWeakCok N) : IsWeakCok M := by
  intro W k hk
  have hk' : N.f ≫ e.inv.τ₂ ≫ k = 0 := by
    rw [← Category.assoc, ← e.inv.comm₁₂, Category.assoc, hk, comp_zero]
  obtain ⟨l, hl⟩ := h _ hk'
  refine ⟨e.hom.τ₃ ≫ l, ?_⟩
  rw [← Category.assoc, ← e.hom.comm₂₃, Category.assoc, hl, ← Category.assoc,
    ← ShortComplex.comp_τ₂, e.hom_inv_id, ShortComplex.id_τ₂, Category.id_comp]

theorem epi_g_of_iso {M N : ShortComplex C} (e : M ≅ N) [Epi N.g] : Epi M.g := by
  have : M.g = e.hom.τ₂ ≫ N.g ≫ e.inv.τ₃ := by
    rw [← Category.assoc, e.hom.comm₂₃, Category.assoc, ← ShortComplex.comp_τ₃, e.hom_inv_id,
      ShortComplex.id_τ₃, Category.comp_id]
  rw [this]
  infer_instance

/-- A complex `Y → E → T` with the radical approximation property, whose epic
second map is a weak cokernel of the first (a left tau-sequence), is a right
radical approximation of `Y` in `Cᵒᵖ`: dually, every radical map out of `Y`
factors through `f`, and every map in `I²(T, Z)` is `q ∘ g` with `q` radical. -/
def approxOfLeftTau {Y : C} (M : ShortComplex C) (hM : MBDVendor.QSE.Iyama.TauApproximation M)
    (hcok : IsWeakCok M) (hepi : Epi M.g) (e : M.X₁ ≅ Y) : RightRadicalApprox (op Y) where
  E := op M.X₂
  p := (e.inv ≫ M.f).op
  T := op M.X₃
  i := M.g.op
  p_rad := (isRadicalMorphism_op_iff _).2 (isRadicalMorphism_precomp _ hM.f_radical)
  factors := by
    intro W g hg
    obtain ⟨b, hb⟩ := hM.factors_from_left (e.hom ≫ g.unop)
      (isRadicalMorphism_precomp _ ((isRadicalMorphism_unop_iff g).2 hg))
    refine ⟨b.op, ?_⟩
    rw [← op_comp, Category.assoc, hb, Iso.inv_hom_id_assoc, Quiver.Hom.op_unop]
  i_p := by rw [← op_comp, Category.assoc, M.zero, comp_zero, op_zero]
  lift := by
    intro W w hw
    have hw' : M.f ≫ w.unop = 0 := by
      have := congrArg Quiver.Hom.unop hw
      rw [unop_comp, Quiver.Hom.unop_op, unop_zero, Category.assoc] at this
      rw [← cancel_epi e.inv, this, comp_zero]
    obtain ⟨l, hl⟩ := hcok w.unop hw'
    exact ⟨l.op, by rw [← op_comp, hl, Quiver.Hom.op_unop]⟩
  i_mono := inferInstance
  i_rad := (isRadicalMorphism_op_iff _).2 hM.g_radical
  sq := by
    intro Z g hg
    rw [← mem_Ipow_unop_iff, Ipow, HomIdeal.pow_succ_eq_mul_pow] at hg
    suffices ∀ h : Z.unop ⟶ M.X₃, h ∈ (homIdeal ⋆ᵢ HomIdeal.pow homIdeal 1).hom _ _ →
        ∃ q : Z.unop ⟶ M.X₂, IsRadicalMorphism q ∧ q ≫ M.g = h by
      obtain ⟨q, hq, hqg⟩ := this _ hg
      exact ⟨q.op, (isRadicalMorphism_op_iff q).2 hq, by rw [← op_comp, hqg, Quiver.Hom.op_unop]⟩
    intro h hh
    induction hh using AddSubgroup.closure_induction with
    | mem h' hh' =>
        obtain ⟨N, u, v, hu, hv, rfl⟩ := hh'
        rw [HomIdeal.pow_one, mem_homIdeal_iff] at hv
        obtain ⟨b, hb⟩ := hM.factors_into_right v hv
        exact ⟨u ≫ b, isRadicalMorphism_postcomp b ((mem_homIdeal_iff u).1 hu),
          by rw [Category.assoc, hb]⟩
    | zero => exact ⟨0, isRadicalMorphism_zero, by simp⟩
    | add a b _ _ ha hb =>
        obtain ⟨q₁, hq₁, h₁⟩ := ha
        obtain ⟨q₂, hq₂, h₂⟩ := hb
        exact ⟨q₁ + q₂, isRadicalMorphism_add hq₁ hq₂, by rw [Preadditive.add_comp, h₁, h₂]⟩
    | neg a _ ha =>
        obtain ⟨q, hq, h⟩ := ha
        exact ⟨-q, isRadicalMorphism_neg hq, by rw [Preadditive.neg_comp, h]⟩

end MultiplicativeBasisDeformations.StrictLayers
