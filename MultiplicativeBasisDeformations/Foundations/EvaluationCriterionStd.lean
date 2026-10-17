import MultiplicativeBasisDeformations.Foundations.EvaluationCriterion

/-!
# Lemma 2.9 with the standard homological notions

The hypotheses of `projectiveEvaluationCriterion` are stated through what the proof uses:
`Ext¹`-vanishing in Yoneda form (`ExtVan`) and `gl.dim ≤ 2` as "kernels of maps between
projectives are projective" (`GlDimLeTwo`). Here they are derived from Mathlib's notions:
* `gl.dim R ≤ 2`: every `R`-module has projective dimension at most two
  (`GlobalDimLE2`, Mathlib's `HasProjectiveDimensionLE`), gives `GlDimLeTwo`
  (`glDimLeTwo_of_globalDim`, from the two short exact sequences of a map between projectives);
* `Ext¹_R(T, Q) = 0` for Mathlib's `Ext` (`ExtOneVan`) gives `ExtVan`
  (`extVan_of_extOneVan`, from the contravariant long exact sequence of `Ext`).
So Lemma 2.9 holds with the hypotheses as stated (`projectiveEvaluationCriterion_std`), and the
check on simples is `van_of_simple_std`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace EvalCriterion

open CategoryTheory Abelian

universe u

variable (k : Type u) [Field k] {R : Type u} [Ring R] [Algebra k R]

variable (R) in
/-- **`gl.dim R ≤ 2`**: every `R`-module has projective dimension at most two. -/
def GlobalDimLE2 : Prop := ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M 2

/-- **`gl.dim R ≤ 2` gives the form used by the proof**: the kernel of a map between projective
modules is projective. -/
theorem glDimLeTwo_of_globalDim (h : GlobalDimLE2 R) : GlDimLeTwo k (R := R) := by
  intro P₀ P₁ _ _ _ _ _ _ _ _ _ _ _ _ f
  -- `0 → im f → P₁ → coker f → 0`
  have S2 := LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective (LinearMap.range f))
  have hP₁ : Projective (ModuleCat.of R P₁) := (IsProjective.iff_projective P₁).1 inferInstance
  have hP₀ : Projective (ModuleCat.of R P₀) := (IsProjective.iff_projective P₀).1 inferInstance
  have hI : HasProjectiveDimensionLT
      (ModuleCat.of R (LinearMap.ker (LinearMap.range f).mkQ)) 2 :=
    S2.hasProjectiveDimensionLT_X₁ 2
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R P₁) 1 2 (by norm_num))
      (h (ModuleCat.of R (P₁ ⧸ LinearMap.range f)))
  have hI' : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.range f)) 2 :=
    hasProjectiveDimensionLT_of_iso
      (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ (LinearMap.range f))).toModuleIso 2
  -- `0 → ker f → P₀ → im f → 0`
  have S1 := LinearMap.shortExact_shortComplexKer (LinearMap.surjective_rangeRestrict f)
  have hK : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f.rangeRestrict)) 1 :=
    S1.hasProjectiveDimensionLT_X₁ 1 inferInstance hI'
  have : Projective (ModuleCat.of R (LinearMap.ker f.rangeRestrict)) := inferInstance
  have hproj : Module.Projective R (LinearMap.ker f.rangeRestrict) :=
    (IsProjective.iff_projective _).2 this
  exact Module.Projective.of_equiv (LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict f))

variable {k}

/-- **`Ext¹_R(T, Q) = 0`** (Mathlib's `Ext`) for every finite-dimensional `T` killed by `ε`. -/
def ExtOneVan (ε : R) (Q : Type u) [AddCommGroup Q] [Module R Q] : Prop :=
  ∀ (T : Type u) [AddCommGroup T] [Module k T] [Module R T] [IsScalarTower k R T]
    [FiniteDimensional k T], Killed ε T →
    ∀ e : Ext (ModuleCat.of R T) (ModuleCat.of R Q) 1, e = 0

/-- **Vanishing of `Ext¹` gives the Yoneda form**: every extension `0 → Q → E → T → 0` splits. -/
theorem splitsFor_of_ext {T Q : Type u} [AddCommGroup T] [Module R T] [AddCommGroup Q]
    [Module R Q] (h : ∀ e : Ext (ModuleCat.of R T) (ModuleCat.of R Q) 1, e = 0) :
    SplitsFor k R T Q := by
  intro E _ _ _ _ _ i p hi hp hex
  have S := LinearMap.shortExact_shortComplexKer hp
  -- `Q ≅ ker p` through `i`
  let φ : Q ≃ₗ[R] LinearMap.ker p :=
    (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex)
  have hφ : ∀ q, ((φ q : LinearMap.ker p) : E) = i q := fun q ↦ rfl
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ S (ModuleCat.of R Q)
    (Ext.mk₀ (ModuleCat.ofHom φ.symm.toLinearMap)) (n₁ := 1) (by norm_num) (h _)
  obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  have e := congrArg ModuleCat.Hom.hom ((Ext.mk₀_bijective _ _).1 hx₂)
  refine ⟨r.hom, LinearMap.ext fun q ↦ ?_⟩
  have := congrArg (fun g : LinearMap.ker p →ₗ[R] Q ↦ g (φ q)) e
  simpa [hφ] using this

/-- **`ExtOneVan` gives `ExtVan`.** -/
theorem extVan_of_extOneVan {ε : R} {Q : Type u} [AddCommGroup Q] [Module R Q]
    (h : ExtOneVan (k := k) ε Q) : ExtVan k ε Q :=
  fun T _ _ _ _ _ hT ↦ splitsFor_of_ext (h T hT)

section Std

variable [FiniteDimensional k R] {ε : R} (hε : IsIdempotentElem ε)

variable (k) in
/-- **Lemma 2.9** (`lem:projective-evaluation-criterion`) with the standard notions: assume
`Hom_R(T, R) = 0` and `Ext¹_R(T, R) = 0` (Mathlib's `Ext`) for all finite-dimensional `T` with
`εT = 0`. Then (1) `P ↦ εP` is fully faithful on finite-dimensional projectives; (2) if moreover
`gl.dim R ≤ 2` (every module has projective dimension `≤ 2`) and every finite-dimensional
injective `Λ_e`-module is `εQ` for a finite-dimensional projective `Q`, it is essentially
surjective onto finite-dimensional `Λ_e`-modules and `Λ_e` is representation-finite. -/
theorem projectiveEvaluationCriterion_std (h0 : HomVan k ε R) (h1 : ExtOneVan (k := k) ε R) :
    (∀ (M Q : Type u) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
      [FiniteDimensional k M] [AddCommGroup Q] [Module k Q] [Module R Q] [IsScalarTower k R Q]
      [FiniteDimensional k Q] [Module.Projective R Q],
      Function.Bijective (fun f : M →ₗ[R] Q ↦ EPmap hε f)) ∧
    (GlobalDimLE2 R → InjLift k hε →
      (∀ (X : Type u) [AddCommGroup X] [Module k X] [Module hε.Corner X]
        [IsScalarTower k hε.Corner X] [FiniteDimensional k X],
        ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module k P) (_ : Module R P)
          (_ : IsScalarTower k R P) (_ : FiniteDimensional k P) (_ : Module.Projective R P),
          Nonempty (EP hε P ≃ₗ[hε.Corner] X)) ∧
      ∃ (n : ℕ) (L : Fin n → Submodule R R),
        ∀ (X : Type u) [AddCommGroup X] [Module k X] [Module hε.Corner X]
          [IsScalarTower k hε.Corner X] [FiniteDimensional k X],
          MBDVendor.QSE.Foundation.IsIndecomposableModule hε.Corner X →
          ∃ i, Nonempty (EP hε (L i) ≃ₗ[hε.Corner] X)) := by
  obtain ⟨hff, h2⟩ := projectiveEvaluationCriterion k hε h0 (extVan_of_extOneVan h1)
  exact ⟨hff, fun hgl hinj ↦ h2 (glDimLeTwo_of_globalDim k hgl) hinj⟩

variable (k) in
/-- **It suffices to check the two vanishings on the simple modules killed by `ε`** (with
Mathlib's `Ext¹`): they give the hypotheses of `projectiveEvaluationCriterion`, hence its
conclusions. -/
theorem van_of_simple_std
    (h : ∀ (S : Type u) [AddCommGroup S] [Module k S] [Module R S] [IsScalarTower k R S]
      [FiniteDimensional k S], IsSimpleModule R S → Killed ε S →
      (∀ f : S →ₗ[R] R, f = 0) ∧ ∀ e : Ext (ModuleCat.of R S) (ModuleCat.of R R) 1, e = 0) :
    HomVan k ε R ∧ ExtVan k ε R :=
  projectiveEvaluationCriterion_of_simple k fun S _ _ _ _ _ hS hk ↦
    ⟨(h S hS hk).1, splitsFor_of_ext (h S hS hk).2⟩

end Std

end EvalCriterion

end MultiplicativeBasisDeformations
