import MultiplicativeBasisDeformations.Foundations.ARMeshFinite

/-!
# Graded Hom dimensions

`eq:graded-hom-dimensions` (`graded-category.tex`):
`dim C(X, Y) = ∑_n dim J^n(X, Y)/J^{n+1}(X, Y) = dim Hom_A(X, Y)`, "from the
finite radical filtration". The first equality is the decomposition of the
Hom spaces of `k(Γ_A)` into finitely many degree parts together with
Proposition 2.6(3); the second is the telescoping of the radical filtration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- Telescoping the radical filtration. -/
theorem sum_finrank_layer (X Y : S.Ind) (N : ℕ) :
    ∑ d ∈ Finset.range N, Module.finrank k (S.layer d X Y) +
      Module.finrank k (S.radPow N X Y) = Module.finrank k (X ⟶ Y) := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      change Module.finrank k (⊤ : Submodule k (X ⟶ Y)) = _
      exact finrank_top k _
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih, add_assoc]
      congr 1
      have h1 := Submodule.finrank_quotient_add_finrank
        ((S.radPow (N + 1) X Y).comap (S.radPow N X Y).subtype)
      rw [← h1]
      congr 1
      exact (LinearEquiv.finrank_eq
        (Submodule.comapSubtypeEquivOfLe (S.radPow_succ_le N X Y))).symm

include S in
theorem sum_finrank_layer_eq (X Y : S.Ind) {N : ℕ} (hN : ∀ X Y : S.Ind, S.radPow N X Y = ⊥) :
    ∑ d ∈ Finset.range N, Module.finrank k (S.layer d X Y) = Module.finrank k (X ⟶ Y) := by
  have := S.sum_finrank_layer X Y N
  rwa [hN, finrank_bot, add_zero] at this

/-- **`eq:graded-hom-dimensions`**: `dim C(x, y) = dim Hom_A(x, y)`. -/
theorem finrank_meshHom (x y : S.ARVertex) :
    Module.finrank k (S.meshObj b x ⟶ S.meshObj b y) =
      Module.finrank k (S.label x ⟶ S.label y) := by
  classical
  obtain ⟨N, hN⟩ := S.exists_radPow_eq_bot
  let C : Fin N → Submodule k (S.meshObj b x ⟶ S.meshObj b y) := fun d ↦
    ScalarMeshCategory.degreePart (S.arCoefficients b) d x y
  have hind : iSupIndep C := by
    have h := (S.isInternal_degreePart b x y).submodule_iSupIndep
    exact iSupIndep.comp (t := fun d : ℕ ↦ ScalarMeshCategory.degreePart (S.arCoefficients b) d x y)
      h Fin.val_injective
  have htop : iSup C = ⊤ := by
    rw [eq_top_iff, ← (S.isInternal_degreePart b x y).submodule_iSup_eq_top]
    refine iSup_le fun d ↦ ?_
    by_cases hd : d < N
    · exact le_iSup_of_le (⟨d, hd⟩ : Fin N) le_rfl
    · rw [S.degreePart_eq_bot b hN (not_lt.1 hd)]
      exact bot_le
  have hint : DirectSum.IsInternal C :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap C) hint
  rw [← e.finrank_eq, Module.finrank_directSum, ← S.sum_finrank_layer_eq _ _ hN,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  exact (S.phi b d x y).finrank_eq

end MultiplicativeBasisDeformations.IndSkeleton
