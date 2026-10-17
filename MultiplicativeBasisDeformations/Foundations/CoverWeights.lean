import MultiplicativeBasisDeformations.Foundations.IntegralWeights
import MultiplicativeBasisDeformations.Foundations.SupportPoset

/-!
# Integral weights on the graded covering category (Proposition 7.2(2))

`weights-and-parameters.tex:62–100`: "Every additive weight on `L`, with values in
any abelian group, is a difference of object values." The generic statement
`Thin.addWeight_eq_diff` applied to the graded covering category, whose
exhaustion hypotheses are those of Lemma 4.12 (`cov_exists_multBasis`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations.CatAlg

open CategoryTheory Opposite

universe u v z

variable {k : Type u} [Field k] [Infinite k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞]
  [Linear k 𝒞] {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G]
  [DecidableEq G] {D : HomGrading (k := k) F G} (H : HeightData D)
  [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ)

attribute [local instance] Thin.opLinear

include H hF in
/-- **Proposition 7.2(2)** for the graded covering category: given Lemma 4.13
(`k*`-weights are object ratios), additive weights with values in any abelian
group are object differences. -/
theorem cov_addWeight_eq_diff [Countable G]
    (hratio : ∀ w' : CovObj D → CovObj D → Additive kˣ, Thin.IsAddWeight Set.univ w' →
      ∃ ζ : CovObj D → Additive kˣ, ∀ o o', Thin.Line o o' → w' o o' = ζ o' - ζ o)
    {M : Type z} [AddCommGroup M] (w' : CovObj D → CovObj D → M)
    (hw : Thin.IsAddWeight Set.univ w') :
    ∃ ζ : CovObj D → M, ∀ o o', Thin.Line o o' → w' o o' = ζ o' - ζ o := by
  classical
  by_cases hne : Nonempty (CovObj D)
  · haveI : Countable (CovObj D) := inferInstanceAs (Countable (ι × G))
    obtain ⟨e, he⟩ := exists_surjective_nat (CovObj D)
    exact Thin.addWeight_eq_diff (isThin H hF) (hgtC H) (fun o o' h ↦ hgt_lt H h)
      (fun s S ↦ supRepFinite_src H hF s (Thin.supp s S) (Thin.fvec s) _)
      (fun t S ↦ supRepFinite_snk H hF t (Thin.supp (op t) (S.map Thin.opEmb)) (Thin.fvec (op t)) _)
      (fun o ↦ succ_finite o) e he hratio w' hw
  · rw [not_nonempty_iff] at hne
    exact ⟨fun o ↦ isEmptyElim o, fun o ↦ isEmptyElim o⟩

end MultiplicativeBasisDeformations.CatAlg
