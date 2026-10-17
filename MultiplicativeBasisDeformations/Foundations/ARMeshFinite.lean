import MultiplicativeBasisDeformations.Foundations.GradedRealizationIso

/-!
# `k(Γ_A)` is finite-dimensional

`graded-category.tex:211–212`, eq. (2.15) of the proof of Proposition 2.10:
"`dim C(X, Y) = ∑_n dim J^n(X, Y)/J^{n+1}(X, Y) = dim Hom_A(X, Y)`. It follows
from the finite radical filtration." By Proposition 2.6(3) the Hom spaces of
`k(Γ_A)` are the direct sums of their degree parts, which are the radical
layers; these vanish from the nilpotency index of the radical on.
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

instance finiteDimensional_degreePart (d : ℕ) (x y : S.ARVertex) :
    FiniteDimensional k (ScalarMeshCategory.degreePart (S.arCoefficients b) d x y) :=
  LinearEquiv.finiteDimensional (S.phi b d x y).symm

theorem degreePart_eq_bot {N : ℕ} (hN : ∀ X Y : S.Ind, S.radPow N X Y = ⊥) {d : ℕ} (hd : N ≤ d)
    (x y : S.ARVertex) : ScalarMeshCategory.degreePart (S.arCoefficients b) d x y = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Submodule.mem_bot]
  have hsub : Subsingleton (S.layer d (S.label x) (S.label y)) := by
    have hbot : S.radPow d (S.label x) (S.label y) = ⊥ :=
      le_bot_iff.1 ((S.radPow_anti hd _ _).trans (hN _ _).le)
    refine ⟨fun u v ↦ ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have hu : (u : S.label x ⟶ S.label y) = 0 := by
      have h := u.2; simp only [hbot, Submodule.mem_bot] at h; exact h
    have hv : (v : S.label x ⟶ S.label y) = 0 := by
      have h := v.2; simp only [hbot, Submodule.mem_bot] at h; exact h
    rw [Subtype.ext (hu.trans hv.symm)]
  have := (S.phi b d x y).injective
    (show S.phi b d x y ⟨g, hg⟩ = S.phi b d x y 0 from Subsingleton.elim _ _)
  exact congrArg Subtype.val this

/-- **The Hom spaces of `k(Γ_A)` are finite-dimensional.** -/
theorem finiteDimensional_meshHom (x y : S.ARVertex) :
    FiniteDimensional k (S.meshObj b x ⟶ S.meshObj b y) := by
  obtain ⟨N, hN⟩ := S.exists_radPow_eq_bot
  have htop : (⨆ d : Fin N, ScalarMeshCategory.degreePart (S.arCoefficients b) d x y) = ⊤ := by
    rw [eq_top_iff, ← (S.isInternal_degreePart b x y).submodule_iSup_eq_top]
    refine iSup_le fun d ↦ ?_
    by_cases hd : d < N
    · exact le_iSup_of_le ⟨d, hd⟩ le_rfl
    · rw [S.degreePart_eq_bot b hN (not_lt.1 hd)]
      exact bot_le
  have hfd : FiniteDimensional k
      (⨆ d : Fin N, ScalarMeshCategory.degreePart (S.arCoefficients b) d x y : Submodule k _) :=
    Submodule.finiteDimensional_iSup _
  have hfg : (⊤ : Submodule k (S.meshObj b x ⟶ S.meshObj b y)).FG := by
    rw [← htop]
    exact (Submodule.fg_iff_finiteDimensional _).2 hfd
  exact Module.finite_def.2 hfg

end MultiplicativeBasisDeformations.IndSkeleton
