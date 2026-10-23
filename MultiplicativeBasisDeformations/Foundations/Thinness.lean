module

public import MultiplicativeBasisDeformations.Foundations.GradedCover
public import MultiplicativeBasisDeformations.Foundations.RepFinite

/-!
# Thinness of the graded covering category

Lemma 4.8, first part (`lem:lifted-projective-evaluation`,
`scalar-normalization.tex`): "Height gives `End_L(x) = k`. By
Lemma 4.7, every full subcategory on two objects is representation-finite. It
is directed. Every subspace of its nonidentity morphism space is an ideal. By
Lemma 3.1(1), there are only finitely many such ideals. A space of dimension at
least two would have infinitely many lines, so that morphism space has
dimension at most one."

Height is a homomorphism `hgt : G → ℤ` such that nonzero homogeneous morphisms
have nonnegative height, and those of height zero are scalar multiples of
identities in degree one (`HeightData`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

/-- Over an infinite field, a finite-dimensional space with finitely many
subspaces has dimension at most one. -/
theorem finrank_le_one_of_finite_submodules {k : Type u} [Field k] [Infinite k] {V : Type v}
    [AddCommGroup V] [Module k V] (P : Submodule k V)
    (hfin : {W : Submodule k V | W ≤ P}.Finite) : Module.finrank k P ≤ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank k P)) k P) := by
    haveI : Module.Finite k P := Module.finite_of_finrank_pos (by omega)
    exact ⟨Module.finBasis k P⟩
  let u : V := b ⟨0, by omega⟩
  let v : V := b ⟨1, by omega⟩
  have hu : u ∈ P := (b ⟨0, by omega⟩).2
  have hv : v ∈ P := (b ⟨1, by omega⟩).2
  let L : k → Submodule k V := fun c ↦ k ∙ (u + c • v)
  have hL : Function.Injective L := by
    intro c d hcd
    have hmem : u + d • v ∈ L c := by rw [hcd]; exact Submodule.mem_span_singleton_self _
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
    have hind := b.linearIndependent
    have h2 : (t - 1) • (b ⟨0, by omega⟩ : P) + (t * c - d) • b ⟨1, by omega⟩ = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero]
      change (t - 1) • u + (t * c - d) • v = 0
      rw [sub_smul, sub_smul, mul_smul, one_smul]
      rw [smul_add] at ht
      rw [← sub_eq_zero] at ht
      rw [← ht]
      abel
    have hpair : LinearIndependent k ![(b ⟨0, by omega⟩ : P), b ⟨1, by omega⟩] := by
      have := hind.comp ![(⟨0, by omega⟩ : Fin (Module.finrank k P)), ⟨1, by omega⟩] (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff])
      convert this using 1
      ext i; fin_cases i <;> rfl
    obtain ⟨h1, h3⟩ := LinearIndependent.pair_iff.1 hpair (t - 1) (t * c - d) h2
    have ht1 : t = 1 := by linear_combination h1
    rw [ht1, one_mul] at h3
    linear_combination h3
  have hsub : ∀ c, L c ∈ {W : Submodule k V | W ≤ P} := fun c ↦ by
    change k ∙ (u + c • v) ≤ P
    rw [Submodule.span_singleton_le_iff_mem]
    exact P.add_mem hu (P.smul_mem c hv)
  exact Set.infinite_of_injective_forall_mem hL hsub hfin

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G] [DecidableEq G]
  (D : HomGrading (k := k) F G)

namespace HomGrading

/-- The degree-`g` part of `C(F x, F y)`. -/
def part (g : G) (x y : ι) : Submodule k (F x ⟶ F y) := LinearMap.range (D.proj g x y)

theorem mem_part_iff {g : G} {x y : ι} {f : F x ⟶ F y} : f ∈ D.part g x y ↔ D.IsHom g f := by
  constructor
  · rintro ⟨f', rfl⟩; exact D.isHom_proj g f'
  · intro h; exact ⟨f, h⟩

end HomGrading

/-- Height data for a grading. -/
structure HeightData where
  hgt : G → ℤ
  hgt_mul : ∀ a b, hgt (a * b) = hgt a + hgt b
  nonneg : ∀ (g : G) (x y : ι) (f : F x ⟶ F y), D.IsHom g f → f ≠ 0 → 0 ≤ hgt g
  scalar : ∀ (g : G) (x y : ι) (f : F x ⟶ F y), D.IsHom g f → f ≠ 0 → hgt g = 0 →
    ∃ h : x = y, g = 1 ∧ ∃ c : k, f = c • eqToHom (congrArg F h)

variable {D} (H : HeightData D)

namespace HeightData

theorem hgt_one : H.hgt 1 = 0 := by
  have := H.hgt_mul 1 1; simp only [mul_one] at this; omega

theorem hgt_inv (g : G) : H.hgt g⁻¹ = - H.hgt g := by
  have := H.hgt_mul g g⁻¹; rw [mul_inv_cancel, H.hgt_one] at this; omega

include H in
/-- Endomorphisms of degree one are scalars. -/
theorem scalar_one {x : ι} {f : F x ⟶ F x} (hf : D.IsHom 1 f) : ∃ c : k, f = c • 𝟙 (F x) := by
  by_cases h0 : f = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨h, -, c, hc⟩ := H.scalar 1 x x f hf h0 H.hgt_one
    exact ⟨c, by simpa using hc⟩

include H in
/-- **Directedness**: no nonzero morphisms back. -/
theorem back_zero {g : G} {x y : ι} (hxy : ¬ (x = y ∧ g = 1)) {f : F x ⟶ F y} (hf : D.IsHom g f)
    (hf0 : f ≠ 0) {f' : F y ⟶ F x} (hf' : D.IsHom g⁻¹ f') : f' = 0 := by
  by_contra hf'0
  have h1 := H.nonneg g x y f hf hf0
  have h2 := H.nonneg g⁻¹ y x f' hf' hf'0
  rw [H.hgt_inv] at h2
  obtain ⟨h, hg, -⟩ := H.scalar g x y f hf hf0 (by omega)
  exact hxy ⟨h, hg⟩

end HeightData

/-! ### The two-object subcategory -/

section TwoObjects

variable (x y : ι) (g : G)

/-- The objects `(x, 1)` and `(y, g)`. -/
def two : Bool → ι × G := fun b ↦ cond b (y, g) (x, 1)

variable {x y g}

/-- The element with the single entry `w` from `(x, 1)` to `(y, g)`. -/
def single01 (w : F x ⟶ F y) : Alg (F ∘ lab (two x y g)) := fun p q ↦
  match p, q with
  | false, true => w
  | _, _ => 0

theorem single01_mem {w : F x ⟶ F y} (hw : D.IsHom g w) :
    MulOpposite.op (single01 (g := g) w) ∈ cov D (two x y g) := by
  rintro (_ | _) (_ | _)
  · exact D.isHom_zero _
  · change D.IsHom (1⁻¹ * g) w; rwa [inv_one, one_mul]
  · exact D.isHom_zero _
  · exact D.isHom_zero _

variable (D) in
/-- The ideal of a subspace `W` of the degree-`g` part. -/
def idealOf (hback : ∀ a : cov D (two x y g), (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true false = 0)
    (hdiag0 : ∀ a : cov D (two x y g), ∃ c : k,
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false = c • 𝟙 _)
    (hdiag1 : ∀ a : cov D (two x y g), ∃ c : k,
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true = c • 𝟙 _)
    (W : Submodule k (F x ⟶ F y)) : TwoSidedIdeal (cov D (two x y g)) :=
  TwoSidedIdeal.mk'
    {a | (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false = 0 ∧
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true = 0 ∧
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false true ∈ W}
    ⟨rfl, rfl, W.zero_mem⟩
    (fun {a b} ha hb ↦ ⟨by
        change (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false +
          (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false = 0
        rw [ha.1, hb.1, add_zero], by
        change (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true +
          (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true = 0
        rw [ha.2.1, hb.2.1, add_zero], W.add_mem ha.2.2 hb.2.2⟩)
    (fun {a} ha ↦ ⟨by
        change -(a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false = 0
        rw [ha.1, neg_zero], by
        change -(a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true = 0
        rw [ha.2.1, neg_zero], W.neg_mem ha.2.2⟩)
    (fun {a b} hb ↦ by
      obtain ⟨c, hc⟩ := hdiag1 a
      have ha10 := hback a
      have hb10 := hback b
      refine ⟨?_, ?_, ?_⟩
      · change ∑ r, (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false r ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop r false = 0
        rw [Fintype.sum_bool, hb.1, ha10, Limits.zero_comp, Limits.comp_zero, add_zero]
      · change ∑ r, (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true r ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop r true = 0
        rw [Fintype.sum_bool, hb.2.1, hb10, Limits.zero_comp, Limits.zero_comp, add_zero]
      · change ∑ r, (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false r ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop r true ∈ W
        rw [Fintype.sum_bool, hb.1, Limits.zero_comp, add_zero]
        change (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false true ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true ∈ W
        rw [hc, Linear.comp_smul, Category.comp_id]
        exact W.smul_mem c hb.2.2)
    (fun {a b} ha ↦ by
      obtain ⟨c, hc⟩ := hdiag0 b
      have ha10 := hback a
      have hb10 := hback b
      refine ⟨?_, ?_, ?_⟩
      · change ∑ r, (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false r ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop r false = 0
        rw [Fintype.sum_bool, ha.1, ha10, Limits.comp_zero, Limits.comp_zero, add_zero]
      · change ∑ r, (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true r ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop r true = 0
        rw [Fintype.sum_bool, ha.2.1, hb10, Limits.zero_comp, Limits.comp_zero, add_zero]
      · change ∑ r, (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false r ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop r true ∈ W
        rw [Fintype.sum_bool, ha.2.1, Limits.comp_zero, zero_add]
        change (b : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false ≫
          (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false true ∈ W
        rw [hc, Linear.smul_comp, Category.id_comp]
        exact W.smul_mem c ha.2.2)

end TwoObjects

include H in
/-- **Thinness** (Lemma 4.8, first part): every graded piece has dimension at
most one. -/
theorem finrank_part_le_one [Infinite k] [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]
    (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ) (g : G) (x y : ι) :
    Module.finrank k (D.part g x y) ≤ 1 := by
  classical
  by_cases hxy : x = y ∧ g = 1
  · obtain ⟨rfl, rfl⟩ := hxy
    have hle : D.part 1 x x ≤ k ∙ 𝟙 (F x) := by
      intro f hf
      obtain ⟨c, rfl⟩ := H.scalar_one ((D.mem_part_iff).1 hf)
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    calc Module.finrank k (D.part 1 x x) ≤ Module.finrank k (k ∙ 𝟙 (F x)) :=
          Submodule.finrank_mono hle
      _ ≤ 1 := le_trans (finrank_span_le_card ({𝟙 (F x)} : Set (F x ⟶ F x))) (by simp)
  by_cases h0 : ∀ f ∈ D.part g x y, f = 0
  · have : D.part g x y = ⊥ := eq_bot_iff.2 fun f hf ↦ (Submodule.mem_bot k).2 (h0 f hf)
    rw [this, finrank_bot]; exact zero_le_one
  push Not at h0
  obtain ⟨f, hf, hf0⟩ := h0
  have hfh := (D.mem_part_iff).1 hf
  have hback : ∀ a : cov D (two x y g),
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true false = 0 := fun a ↦ by
    have ha := a.2 true false
    change D.IsHom (g⁻¹ * 1) _ at ha
    rw [mul_one] at ha
    exact H.back_zero hxy hfh hf0 ha
  have hdiag0 : ∀ a : cov D (two x y g), ∃ c : k,
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop false false = c • 𝟙 _ := fun a ↦ by
    have ha := a.2 false false
    change D.IsHom (1⁻¹ * 1) _ at ha
    rw [inv_one, one_mul] at ha
    exact H.scalar_one ha
  have hdiag1 : ∀ a : cov D (two x y g), ∃ c : k,
      (a : (Alg (F ∘ lab (two x y g)))ᵐᵒᵖ).unop true true = c • 𝟙 _ := fun a ↦ by
    have ha := a.2 true true
    change D.IsHom (g⁻¹ * g) _ at ha
    rw [inv_mul_cancel] at ha
    exact H.scalar_one ha
  have hrep := isRepresentationFinite_cov D (two x y g) hF
  have hideals := finite_twoSidedIdeals_of hrep
  apply finrank_le_one_of_finite_submodules
  refine Set.Finite.of_finite_image (f := idealOf D hback hdiag0 hdiag1)
    (hideals.subset (Set.subset_univ _)) ?_
  intro W hW W' hW' hWW'
  have key : ∀ {W W' : Submodule k (F x ⟶ F y)}, W ≤ D.part g x y →
      idealOf D hback hdiag0 hdiag1 W = idealOf D hback hdiag0 hdiag1 W' → W ≤ W' := by
    intro W W' hW h w hw
    let a : cov D (two x y g) := ⟨_, single01_mem (D := D) ((D.mem_part_iff).1 (hW hw))⟩
    have ha : a ∈ idealOf D hback hdiag0 hdiag1 W := by
      rw [idealOf, TwoSidedIdeal.mem_mk']
      exact ⟨rfl, rfl, hw⟩
    rw [h, idealOf, TwoSidedIdeal.mem_mk'] at ha
    exact ha.2.2
  exact le_antisymm (key hW hWW') (key hW' hWW'.symm)


end CatAlg

end MultiplicativeBasisDeformations
