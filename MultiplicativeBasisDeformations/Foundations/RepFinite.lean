import MultiplicativeBasisDeformations.Foundations.RightModules
import MBDVendor.Magnitude.Algebra.FiniteModuleDecomposition

/-!
# Representation-finite algebras: bounded modules and two-sided ideals

Lemma 3.1(1), first part (`projective-rays.tex`): "The annihilator of
the right module `A/I` is `I`. Finite representation type gives only finitely
many isomorphism classes of modules of dimension at most `dim_k A`."
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Every finite-dimensional right module over a representation-finite algebra
is a biproduct of at most `dim M` modules from the finite list. -/
theorem exists_labels_iso (hA : IsRepresentationFinite k A) :
    ∃ (N : ℕ) (X : Fin N → RightModuleCat A), (∀ i, IsFiniteIndecomposable k A (X i)) ∧
      ∀ (M : RightModuleCat A), Module.Finite k M →
        ∃ (n : ℕ) (l : Fin n → Fin N), n ≤ Module.finrank k M ∧
          Nonempty (M ≅ ⨁ fun j ↦ X (l j)) := by
  obtain ⟨N, X, hX, hcomp⟩ := hA
  refine ⟨N, X, hX, fun M hM ↦ ?_⟩
  haveI := hM
  haveI : Module.Finite k Aᵐᵒᵖ := inferInstance
  obtain ⟨d⟩ := MBDVendor.Magnitude.finiteIndecomposableDecomposition_module_exists
    (k := k) (A := Aᵐᵒᵖ) M
  have hsum : ∀ j, IsFiniteIndecomposable k A (d.summand j) := fun j ↦
    ⟨d.summand_finite hM j, d.indecomposable j⟩
  choose l hl using fun j ↦ hcomp (d.summand j) (hsum j)
  refine ⟨d.n, l, ?_, ⟨d.isoBiproduct ≪≫ biproduct.mapIso fun j ↦ (hl j).some⟩⟩
  have e : M ≃ₗ[Aᵐᵒᵖ] (∀ j, d.summand j) :=
    (d.isoBiproduct ≪≫ ModuleCat.biproductIsoPi _).toLinearEquiv
  haveI : ∀ j, Module.Finite k (d.summand j) := fun j ↦ (hsum j).1
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  calc d.n = ∑ _j : Fin d.n, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ ↦ by
      have hnz : ¬ IsZero (d.summand j) := (d.indecomposable j).1
      haveI : Nontrivial (d.summand j) := by
        rw [← not_subsingleton_iff_nontrivial]
        exact fun h ↦ hnz (ModuleCat.isZero_of_subsingleton _)
      exact Module.finrank_pos

/-- A two-sided ideal as a right submodule of `A_A`. -/
def TwoSidedIdeal.toRightSub (I : TwoSidedIdeal A) : Submodule Aᵐᵒᵖ A where
  carrier := {x | x ∈ I}
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' c x hx := I.mul_mem_right x c.unop hx

/-- The right module `A/I`. -/
def quotModule (I : TwoSidedIdeal A) : RightModuleCat A :=
  ModuleCat.of Aᵐᵒᵖ (A ⧸ TwoSidedIdeal.toRightSub I)

omit [FiniteDimensional k A] [Algebra k A] in
/-- The class of `x` in `A/I`. -/
def quotMk (I : TwoSidedIdeal A) (x : A) : quotModule I :=
  (Submodule.Quotient.mk x : A ⧸ TwoSidedIdeal.toRightSub I)

omit [FiniteDimensional k A] [Algebra k A] in
theorem quotMk_surjective (I : TwoSidedIdeal A) : Function.Surjective (quotMk I) :=
  Submodule.Quotient.mk_surjective (TwoSidedIdeal.toRightSub I)

omit [FiniteDimensional k A] [Algebra k A] in
theorem smul_quotMk (I : TwoSidedIdeal A) (a x : A) :
    MulOpposite.op a • quotMk I x = quotMk I (x * a) := rfl

omit [FiniteDimensional k A] [Algebra k A] in
theorem quotMk_eq_zero (I : TwoSidedIdeal A) (x : A) : quotMk I x = 0 ↔ x ∈ I :=
  Submodule.Quotient.mk_eq_zero _

omit [FiniteDimensional k A] [Algebra k A] in
/-- **The annihilator of `A/I` is `I`.** -/
theorem mem_iff_annihilates (I : TwoSidedIdeal A) (a : A) :
    a ∈ I ↔ ∀ m : quotModule I, MulOpposite.op a • m = 0 := by
  constructor
  · intro ha m
    obtain ⟨x, rfl⟩ := quotMk_surjective I m
    rw [smul_quotMk, quotMk_eq_zero]
    exact I.mul_mem_left x a ha
  · intro h
    have := h (quotMk I 1)
    rwa [smul_quotMk, quotMk_eq_zero, one_mul] at this

omit [FiniteDimensional k A] [Algebra k A] in
theorem eq_of_iso (I J : TwoSidedIdeal A) (e : quotModule I ≅ quotModule J) : I = J := by
  ext a
  rw [mem_iff_annihilates, mem_iff_annihilates]
  constructor
  · intro h m
    have := congrArg e.hom.hom (h (e.inv.hom m))
    rw [map_smul, map_zero] at this
    simpa using this
  · intro h m
    have := congrArg e.inv.hom (h (e.hom.hom m))
    rw [map_smul, map_zero] at this
    simpa using this

theorem quotModule_finite (I : TwoSidedIdeal A) :
    Module.Finite k (quotModule I) ∧ Module.finrank k (quotModule I) ≤ Module.finrank k A := by
  let f : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] quotModule I := LinearMap.toSpanSingleton Aᵐᵒᵖ _ (quotMk I 1)
  have hf : Function.Surjective f := by
    intro m
    obtain ⟨x, rfl⟩ := quotMk_surjective I m
    refine ⟨MulOpposite.op x, ?_⟩
    change MulOpposite.op x • quotMk I 1 = _
    rw [smul_quotMk, one_mul]
  haveI : Module.Finite k Aᵐᵒᵖ := inferInstance
  have hfk : Function.Surjective (f.restrictScalars k) := hf
  have h1 : Module.Finite k (quotModule I) := Module.Finite.of_surjective (f.restrictScalars k) hfk
  refine ⟨h1, ?_⟩
  calc Module.finrank k (quotModule I) ≤ Module.finrank k Aᵐᵒᵖ := by
        have := LinearMap.finrank_range_le (f.restrictScalars k)
        rwa [LinearMap.range_eq_top.2 hfk, finrank_top] at this
    _ = Module.finrank k A := (MulOpposite.opLinearEquiv k).finrank_eq.symm

/-- **Lemma 3.1(1)**, first part: a representation-finite algebra has finitely
many two-sided ideals. -/
theorem finite_twoSidedIdeals_of (hA : IsRepresentationFinite k A) :
    (Set.univ : Set (TwoSidedIdeal A)).Finite := by
  classical
  obtain ⟨N, X, -, hdec⟩ := exists_labels_iso hA
  have hc : ∀ I : TwoSidedIdeal A, ∃ p : Σ n : Fin (Module.finrank k A + 1), (Fin n → Fin N),
      Nonempty (quotModule I ≅ ⨁ fun j ↦ X (p.2 j)) := by
    intro I
    obtain ⟨hfin, hle⟩ := quotModule_finite (k := k) I
    obtain ⟨n, l, hn, ⟨e⟩⟩ := hdec _ hfin
    exact ⟨⟨⟨n, by omega⟩, l⟩, ⟨e⟩⟩
  choose φ hφ using hc
  have hinj : Function.Injective φ := by
    intro I J h
    apply eq_of_iso I J
    exact (hφ I).some ≪≫ eqToIso (by rw [h]) ≪≫ (hφ J).some.symm
  rw [Set.finite_univ_iff]
  exact Finite.of_injective φ hinj

end MultiplicativeBasisDeformations
