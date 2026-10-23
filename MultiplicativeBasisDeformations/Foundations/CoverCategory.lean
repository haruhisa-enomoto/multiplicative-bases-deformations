module

public import MultiplicativeBasisDeformations.Foundations.Thinness
public import MultiplicativeBasisDeformations.Foundations.Exhaustion

/-!
# The graded covering category as a thin category

Definition 4.5 (`def:graded-covering-category`): objects `(x, g)`, morphisms
`B(x, y)_{g⁻¹h}` from `(x, g)` to `(y, h)`. For a graded family with height
data (`HomGrading`, `HeightData`) and a representation-finite algebra this is a
thin directed `k`-linear category with a height and finitely many outgoing lines
at each object (`isThin`, `hgt_lt`, `succ_finite`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G] [DecidableEq G]
  (D : HomGrading (k := k) F G)

/-- The objects of the graded covering category. -/
@[nolint unusedArguments]
def CovObj (_D : HomGrading (k := k) F G) : Type := ι × G

variable {D}

/-- The morphism space `B(x, y)_{g⁻¹h}`. -/
abbrev CovHom (o o' : CovObj D) : Submodule k (F o.1 ⟶ F o'.1) := D.part (o.2⁻¹ * o'.2) o.1 o'.1

theorem covHom_comp {o o' o'' : CovObj D} {f : F o.1 ⟶ F o'.1} {g : F o'.1 ⟶ F o''.1}
    (hf : f ∈ CovHom o o') (hg : g ∈ CovHom o' o'') : f ≫ g ∈ CovHom o o'' := by
  rw [HomGrading.mem_part_iff] at *
  have := D.isHom_comp hf hg
  rwa [show o.2⁻¹ * o'.2 * (o'.2⁻¹ * o''.2) = o.2⁻¹ * o''.2 by group] at this

theorem covHom_id (o : CovObj D) : 𝟙 (F o.1) ∈ CovHom o o := by
  rw [HomGrading.mem_part_iff, inv_mul_cancel]; exact D.isHom_id _

instance : Category.{w} (CovObj D) where
  Hom o o' := CovHom o o'
  id o := ⟨𝟙 _, covHom_id o⟩
  comp f g := ⟨f.1 ≫ g.1, covHom_comp f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

@[simp] theorem cov_comp_val {o o' o'' : CovObj D} (f : o ⟶ o') (g : o' ⟶ o'') :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp] theorem cov_id_val (o : CovObj D) : (𝟙 o : o ⟶ o).1 = 𝟙 (F o.1) := rfl

instance : Preadditive (CovObj D) where
  homGroup o o' := inferInstanceAs (AddCommGroup (CovHom o o'))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance : Linear k (CovObj D) where
  homModule o o' := inferInstanceAs (Module k (CovHom o o'))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

@[simp] theorem cov_zero_val {o o' : CovObj D} : (0 : o ⟶ o').1 = 0 := rfl
@[simp] theorem cov_smul_val {o o' : CovObj D} (c : k) (f : o ⟶ o') : (c • f).1 = c • f.1 := rfl

theorem cov_ne_zero {o o' : CovObj D} {f : o ⟶ o'} : f ≠ 0 ↔ f.1 ≠ 0 :=
  ⟨fun h h' ↦ h (Subtype.ext h'), fun h h' ↦ h (congrArg Subtype.val h')⟩

variable (H : HeightData D)

include H in
/-- **The graded covering category is thin and directed** (Lemma 4.8, first
part, with the height). -/
theorem isThin [Infinite k] [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]
    (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ) : Thin.IsThin k (CovObj D) where
  fin o o' := inferInstanceAs (FiniteDimensional k (CovHom o o'))
  thin o o' := finrank_part_le_one H hF _ _ _
  endo o f := by
    have hf := (HomGrading.mem_part_iff (D := D)).1 f.2
    rw [inv_mul_cancel] at hf
    obtain ⟨c, hc⟩ := H.scalar_one hf
    exact ⟨c, Subtype.ext hc⟩
  dir o o' hne f g hf := by
    rw [cov_ne_zero] at hf
    by_contra hg
    replace hg : g.1 ≠ 0 := cov_ne_zero.1 hg
    have h1 := (HomGrading.mem_part_iff (D := D)).1 f.2
    have h2 := (HomGrading.mem_part_iff (D := D)).1 g.2
    rw [show o'.2⁻¹ * o.2 = (o.2⁻¹ * o'.2)⁻¹ by group] at h2
    refine hg (H.back_zero ?_ h1 hf h2)
    rintro ⟨h1', h2'⟩
    apply hne
    have : o'.2 = o.2 := by
      have := congrArg (o.2 * ·) h2'
      simpa using this
    exact Prod.ext h1' this.symm

/-- Height of an object. -/
def hgtC (o : CovObj D) : ℤ := H.hgt o.2

theorem hgt_lt {o o' : CovObj D} (h : Thin.Rl o o') : hgtC H o < hgtC H o' := by
  obtain ⟨hne, f, hf⟩ := h
  rw [cov_ne_zero] at hf
  have hf' := (HomGrading.mem_part_iff (D := D)).1 f.2
  have h0 := H.nonneg _ _ _ _ hf' hf
  have hmul : H.hgt o'.2 = H.hgt o.2 + H.hgt (o.2⁻¹ * o'.2) := by
    rw [← H.hgt_mul]; congr 1; group
  unfold hgtC
  rcases h0.lt_or_eq with h0 | h0
  · omega
  · exfalso
    obtain ⟨hx, hg, -⟩ := H.scalar _ _ _ _ hf' hf h0.symm
    apply hne
    have : o'.2 = o.2 := by
      have := congrArg (o.2 * ·) hg
      simpa using this
    exact Prod.ext hx this.symm

/-- Only finitely many degrees occur between two labels. -/
theorem finite_degrees [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (x y : ι) :
    {h : G | D.part h x y ≠ ⊥}.Finite := by
  classical
  let b := Module.finBasis k (F x ⟶ F y)
  choose sb hsb using fun i ↦ D.sum x y (b i)
  refine Set.Finite.subset (Finset.finite_toSet (Finset.univ.biUnion sb)) fun h hh ↦ ?_
  by_contra hnot
  apply hh
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have hfh := (HomGrading.mem_part_iff (D := D)).1 hf
  have hzero : ∀ i, D.proj h x y (b i) = 0 := by
    intro i
    rw [hsb i, map_sum]
    refine Finset.sum_eq_zero fun g hg ↦ ?_
    rw [D.proj_proj, if_neg]
    rintro rfl
    exact hnot (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hg⟩))
  rw [← hfh, ← b.sum_repr f, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, hzero, smul_zero]

/-- **Finitely many outgoing lines.** -/
theorem succ_finite [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (o : CovObj D) :
    {o' : CovObj D | Thin.Rl o o'}.Finite := by
  classical
  have hsub : {o' : CovObj D | Thin.Rl o o'} ⊆
      ⋃ y : ι, (fun h ↦ (show CovObj D from (y, o.2 * h))) '' {h | D.part h o.1 y ≠ ⊥} := by
    rintro ⟨y, g⟩ ⟨-, f, hf⟩
    refine Set.mem_iUnion.2 ⟨y, o.2⁻¹ * g, ?_, ?_⟩
    · intro hbot
      apply hf
      apply Subtype.ext
      have := f.2
      change f.1 ∈ D.part (o.2⁻¹ * g) o.1 y at this
      rw [hbot, Submodule.mem_bot] at this
      exact this
    · change (y, o.2 * (o.2⁻¹ * g)) = (y, g)
      simp
  exact Set.Finite.subset (Set.finite_iUnion fun y ↦ (finite_degrees (D := D) o.1 y).image _) hsub

end CatAlg

end MultiplicativeBasisDeformations
