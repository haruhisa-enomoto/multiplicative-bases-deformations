module

public import MultiplicativeBasisDeformations.Foundations.SupportPoset
public import MultiplicativeBasisDeformations.Foundations.WeightDivisibility
public import MultiplicativeBasisDeformations.Foundations.Twist

/-!
# Scalar automorphisms act trivially on module classes

Lemma 4.13, first step (`scalar-normalization.tex`): "A weight scales
morphism lines and thus defines an automorphism of `L`. These automorphisms act
on the indecomposable module classes with any fixed finite support […]. Their
permutation image is finite, abelian and divisible, hence trivial. Every scalar
automorphism consequently fixes each `V_X̃` up to isomorphism."

For a finite set of objects `s` of the graded covering category, a weight `d`
defines the automorphism `σ_d` of the covering algebra `cov D s` scaling the
`(p, q)`-entry by `d(s p, s q)` (`scaleEquiv`). By divisibility of weights
(Lemma 4.11(2)) `σ_d = σ_e^N` for the `N` of `twist_pow_iso`, so `σ_d` fixes
every finite-dimensional indecomposable class (`weight_twist_iso`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞]
  [Linear k 𝒞] {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G]
  [DecidableEq G] {D : HomGrading (k := k) F G}
  {κ : Type} [Fintype κ] [DecidableEq κ] (s : κ → CovObj D)

/-- An entry of a covering algebra element as a morphism of the cover. -/
def ent (a : cov D s) (p q : κ) : (s p : CovObj D) ⟶ s q :=
  ⟨(a : (Alg (F ∘ lab s))ᵐᵒᵖ).unop p q, (HomGrading.mem_part_iff (D := D)).2 (a.2 p q)⟩

variable {s}

theorem ent_ext {a b : cov D s} (h : ∀ p q, ent s a p q = ent s b p q) : a = b := by
  apply Subtype.ext; apply MulOpposite.unop_injective; apply CatAlg.ext; intro p q
  exact congrArg Subtype.val (h p q)

variable (s) in
/-- Scaling the entries by a function on pairs of objects. -/
def scale (d : CovObj D → CovObj D → k) (a : cov D s) : cov D s :=
  ⟨MulOpposite.op (fun p q ↦ d (s p) (s q) • (a : (Alg (F ∘ lab s))ᵐᵒᵖ).unop p q),
    fun p q ↦ D.isHom_smul _ (a.2 p q)⟩

theorem ent_scale (d : CovObj D → CovObj D → k) (a : cov D s) (p q : κ) :
    ent s (scale s d a) p q = d (s p) (s q) • ent s a p q := rfl

theorem ent_mul (a b : cov D s) (p r : κ) :
    ent s (a * b) p r = ∑ q, ent s b p q ≫ ent s a q r := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  rfl

theorem ent_one (p q : κ) : (ent s 1 p q).1 = idTo (F := F ∘ lab s) p q := rfl

variable {d : CovObj D → CovObj D → k} (hd : Thin.IsWeight (Set.range s) d)

include hd in
theorem scale_mul (a b : cov D s) : scale s d (a * b) = scale s d a * scale s d b := by
  apply ent_ext; intro p r
  rw [ent_scale, ent_mul, ent_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [ent_scale, ent_scale, Linear.smul_comp, Linear.comp_smul, smul_smul]
  by_cases h : ent s b p q ≫ ent s a q r = 0
  · rw [h, smul_zero, smul_zero]
  · rw [hd.mul _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ _ ⟨r, rfl⟩ _ _ h, mul_comm]

include hd in
theorem scale_one : scale s d (1 : cov D s) = 1 := by
  apply ent_ext; intro p q
  rw [ent_scale]
  apply Subtype.ext
  change d (s p) (s q) • idTo (F := F ∘ lab s) p q = idTo (F := F ∘ lab s) p q
  by_cases hpq : p = q
  · subst hpq
    rw [idTo_self]
    by_cases h1 : (𝟙 (s p) : (s p : CovObj D) ⟶ s p) = 0
    · have : 𝟙 ((F ∘ lab s) p) = 0 := congrArg Subtype.val h1
      rw [this, smul_zero]
    · rw [hd.self ⟨p, rfl⟩ h1, one_smul]
  · rw [idTo_ne hpq, smul_zero]

include hd in
theorem scale_inv_scale (a : cov D s) : scale s (fun o o' ↦ (d o o')⁻¹) (scale s d a) = a := by
  apply ent_ext; intro p q
  rw [ent_scale, ent_scale, smul_smul]
  by_cases h : ent s a p q = 0
  · rw [h, smul_zero]
  · rw [inv_mul_cancel₀ (hd.ne _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ _ h), one_smul]

include hd in
theorem scale_scale_inv (a : cov D s) : scale s d (scale s (fun o o' ↦ (d o o')⁻¹) a) = a := by
  apply ent_ext; intro p q
  rw [ent_scale, ent_scale, smul_smul]
  by_cases h : ent s a p q = 0
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (hd.ne _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ _ h), one_smul]

theorem scale_add (a b : cov D s) : scale s d (a + b) = scale s d a + scale s d b := by
  apply ent_ext; intro p q
  rw [ent_scale]
  change _ • (ent s a p q + ent s b p q) = ent s (scale s d a) p q + ent s (scale s d b) p q
  rw [ent_scale, ent_scale, smul_add]

theorem scale_smul (c : k) (a : cov D s) : scale s d (c • a) = c • scale s d a := by
  apply ent_ext; intro p q
  rw [ent_scale]
  change _ • (c • ent s a p q) = c • ent s (scale s d a) p q
  rw [ent_scale, smul_comm]

/-- **The scalar automorphism** `σ_d` of the covering algebra. -/
def scaleEquiv : cov D s ≃ₐ[k] cov D s where
  toFun := scale s d
  invFun := scale s (fun o o' ↦ (d o o')⁻¹)
  left_inv := scale_inv_scale hd
  right_inv := scale_scale_inv hd
  map_mul' := scale_mul hd
  map_add' := scale_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, scale_smul, scale_one hd]

theorem scaleEquiv_apply (a : cov D s) : scaleEquiv hd a = scale s d a := rfl

theorem scaleEquiv_pow (N : ℕ) (a : cov D s) :
    ((scaleEquiv hd) ^ N) a = scale s (fun o o' ↦ d o o' ^ N) a := by
  induction N with
  | zero =>
      apply ent_ext; intro p q
      rw [ent_scale, pow_zero]
      simp
  | succ N ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, scaleEquiv_apply]
      apply ent_ext; intro p q
      rw [ent_scale, ent_scale, ent_scale, smul_smul, pow_succ, mul_comm]

variable [Infinite k] [IsAlgClosed k] (H : HeightData D)
  [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ)

include H hF in
/-- **Weights fix every indecomposable class** (Lemma 4.13, first step). -/
theorem weight_twist_iso (M : RightModuleCat (cov D s))
    (hM : IsFiniteIndecomposable k (cov D s) M) : Nonempty (twist (scaleEquiv hd) M ≅ M) := by
  classical
  have hrep := isRepresentationFinite_cov D s hF
  obtain ⟨N, hN, hpow⟩ := twist_pow_iso hrep
  have hS : ((Finset.univ.image s : Finset (CovObj D)) : Set (CovObj D)) = Set.range s := by
    simp
  obtain ⟨e, he, hde⟩ := Thin.weight_divisible (isThin H hF) (hgtC H) (fun o o' h ↦ hgt_lt H h)
    (fun t S ↦ supRepFinite_src H hF t (Thin.supp t S) (Thin.fvec t) _) hN _
    (Finset.univ.image s) rfl d (by rw [hS]; exact hd)
  rw [hS] at he
  have hσ : scaleEquiv hd = (scaleEquiv he) ^ N := by
    ext a
    rw [scaleEquiv_pow he N, scaleEquiv_apply]
    apply congrArg Subtype.val
    apply ent_ext; intro p q
    rw [ent_scale, ent_scale]
    by_cases h : ent s a p q = 0
    · rw [h, smul_zero, smul_zero]
    · rw [hde _ (by simp) _ (by simp) _ h]
  rw [hσ]
  exact hpow _ M hM

end CatAlg

end MultiplicativeBasisDeformations
