import MultiplicativeBasisDeformations.Independent.MeshComparison
import MultiplicativeBasisDeformations.Statements.MainTheorems

/-!
# Standardness in the independent vocabulary

Under translate compatibility, standardness of the corresponding skeleton in
the proof library gives standardness of an independent family:

* the independent `k(Γ_A)` is equivalent to the all-one scalar mesh category
  (the two relation ideals agree);
* a gauge transformation (Lemma 4.4) identifies the all-one scalar mesh
  category with the one whose coefficients come from almost split sequences;
* the proof library supplies the equivalence of the latter with `ind(mod A)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra
open MultiplicativeBasisDeformations.CategoricalIdeal

namespace MultiplicativeBasisDeformations.Statement

universe u

section QuotientComparison

variable {C : Type*} [Category C] (r s : HomRel C) [Congruence r] [Congruence s]
  (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g ↔ s f g)

/-- The identity of `C` induces a functor between quotients by relations with
the same equivalent pairs. -/
def quotientComparison : CategoryTheory.Quotient r ⥤ CategoryTheory.Quotient s :=
  CategoryTheory.Quotient.lift r (CategoryTheory.Quotient.functor s)
    fun _ _ f g hfg ↦ CategoryTheory.Quotient.sound s ((h f g).1 hfg)

theorem quotientComparison_comp :
    quotientComparison r s h ⋙ quotientComparison s r (fun _ _ f g ↦ (h f g).symm) = 𝟭 _ := by
  apply CategoryTheory.Quotient.lift_unique'
  rw [← Functor.assoc, quotientComparison, CategoryTheory.Quotient.lift_spec,
    quotientComparison, CategoryTheory.Quotient.lift_spec, Functor.comp_id]

/-- Quotients by relations with the same equivalent pairs are equivalent. -/
def quotientEquivOfIff : CategoryTheory.Quotient r ≌ CategoryTheory.Quotient s :=
  CategoryTheory.Equivalence.mk (quotientComparison r s h) (quotientComparison s r (fun _ _ f g ↦ (h f g).symm))
    (eqToIso (quotientComparison_comp r s h).symm)
    (eqToIso (quotientComparison_comp s r (fun _ _ f g ↦ (h f g).symm)))

end QuotientComparison

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable {S : IndecomposableFamily k A}

/-- The all-one scalar mesh category of `Γ_A`. -/
abbrev OneMesh (S : IndecomposableFamily k A) :=
  ScalarMeshCategory k (toSkeleton S).arTranslationQuiver (oneCoeff S)

set_option maxHeartbeats 4000000 in
/-- The independent `k(Γ_A)` and the all-one scalar mesh category. -/
def toOneMesh (hτ : TranslateCompatible S) : MeshCategory S ≌ OneMesh S :=
  quotientEquivOfIff (meshRel S)
    (HomIdeal.linearSpan k
      (MultiplicativeBasisDeformations.meshRelations (k := k) (oneCoeff S))).rel
    (fun _ _ f g ↦ meshRel_iff hτ f g)

set_option maxHeartbeats 4000000 in
theorem toOneMesh_linear (hτ : TranslateCompatible S) : (toOneMesh hτ).functor.Linear k where
  map_smul {X Y} f r := by
    induction f using CategoryTheory.Quotient.induction with
    | h f =>
        rw [← Functor.map_smul]
        change (RelationCategory.functor k _).map (r • f) =
          r • (RelationCategory.functor k _).map f
        rw [Functor.map_smul]

section Gauge

variable (S)

/-- Under the gauge `c_{x,a} = η_x μ_{σa} μ_a` from all-one coefficients, the
gauge functor is an equivalence. -/
theorem gaugeQ_isEquivalence {c : MeshCoefficients k (toSkeleton S).arTranslationQuiver}
    (μ : ∀ {x y : (toSkeleton S).ARVertex}, (x ⟶ y) → kˣ)
    (η : (toSkeleton S).arTranslationQuiver.nonprojective → kˣ)
    (h : ∀ (x : (toSkeleton S).arTranslationQuiver.nonprojective) (y : (toSkeleton S).ARVertex)
      (a : y ⟶ x.1), c x y a = η x * oneCoeff S x y a *
        μ ((toSkeleton S).arTranslationQuiver.mate x y a) * μ a) :
    (ScalarMeshCategory.gaugeQ μ η (oneCoeff S) c h).IsEquivalence where
  faithful := ⟨fun {X Y} f g hfg ↦
    (ScalarMeshCategory.gaugeEquiv μ η (oneCoeff S) c h X.as Y.as).injective hfg⟩
  full := ⟨fun {X Y} g ↦ ⟨(ScalarMeshCategory.gaugeEquiv μ η (oneCoeff S) c h X.as Y.as).symm g,
    (ScalarMeshCategory.gaugeEquiv μ η (oneCoeff S) c h X.as Y.as).apply_symm_apply g⟩⟩
  essSurj := ⟨fun Y ↦ ⟨ScalarMeshCategory.obj (oneCoeff S) Y.as,
    ⟨eqToIso (ScalarMeshCategory.gaugeQ_obj μ η (oneCoeff S) c h Y.as)⟩⟩⟩

theorem gaugeQ_linear {c : MeshCoefficients k (toSkeleton S).arTranslationQuiver}
    (μ : ∀ {x y : (toSkeleton S).ARVertex}, (x ⟶ y) → kˣ)
    (η : (toSkeleton S).arTranslationQuiver.nonprojective → kˣ)
    (h : ∀ (x : (toSkeleton S).arTranslationQuiver.nonprojective) (y : (toSkeleton S).ARVertex)
      (a : y ⟶ x.1), c x y a = η x * oneCoeff S x y a *
        μ ((toSkeleton S).arTranslationQuiver.mate x y a) * μ a) :
    (ScalarMeshCategory.gaugeQ μ η (oneCoeff S) c h).Linear k where
  map_smul {X Y} f r := (ScalarMeshCategory.gaugeEquiv μ η (oneCoeff S) c h X.as Y.as).map_smul r f

end Gauge

/-- A `k`-linear functor in the sense of the proof library is `k`-linear. -/
theorem linear_of_isLinearFunctor {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [Linear k C] [Linear k D] {F : C ⥤ D} (hF : IsLinearFunctor (k := k) F) :
    F.Linear k where
  map_smul {X Y} f r := by
    have h0 : F.map (0 : X ⟶ Y) = 0 := by
      have e := hF X Y 1 0 0
      rw [one_smul, add_zero, one_smul] at e
      exact left_eq_add.mp e
    have e := hF X Y r f 0
    rwa [add_zero, h0, add_zero] at e

set_option maxHeartbeats 4000000 in
/-- **Standardness in the independent vocabulary**, from standardness of the
corresponding skeleton in the proof library. -/
theorem isStandardFor_of (hτ : TranslateCompatible S) (hstd : (toSkeleton S).IsStandard) :
    IsStandardFor S := by
  classical
  refine ⟨fun X Y ↦ (finrank_irr_eq S X Y).trans_le ((toSkeleton S).finrank_irr_le_one X Y), ?_⟩
  obtain ⟨b, F, hF, hlin, hobj⟩ := hstd
  obtain ⟨φ, ψ, hφ⟩ := unitMeshCoefficients (toSkeleton S) ((toSkeleton S).arCoefficients b)
  let μ : ∀ {x y : (toSkeleton S).ARVertex}, (x ⟶ y) → kˣ := fun {x y} a ↦ (φ ⟨x, y, a⟩)⁻¹
  have h : ∀ (x : (toSkeleton S).arTranslationQuiver.nonprojective) (y : (toSkeleton S).ARVertex)
      (a : y ⟶ x.1), (toSkeleton S).arCoefficients b x y a = ψ x * oneCoeff S x y a *
        μ ((toSkeleton S).arTranslationQuiver.mate x y a) * μ a := by
    intro x y a
    rw [← hφ x y a]
    simp only [oneCoeff, mul_one, μ]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  haveI := gaugeQ_isEquivalence S μ ψ h
  haveI := gaugeQ_linear S μ ψ h
  haveI := toOneMesh_linear hτ
  haveI := linear_of_isLinearFunctor hlin
  exact ⟨(toOneMesh hτ).functor ⋙ ScalarMeshCategory.gaugeQ μ ψ (oneCoeff S) _ h ⋙ F,
    inferInstance, inferInstance, fun i ↦ hobj i⟩

end MultiplicativeBasisDeformations.Statement
