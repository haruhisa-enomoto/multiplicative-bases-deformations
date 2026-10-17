import MultiplicativeBasisDeformations.Foundations.FamilyCriterionGen
import MultiplicativeBasisDeformations.Refinements.SplitRelative

/-!
# Proposition 2.10(2): `A₀` is basic

`prop:projective-evaluation` (2): "The algebra `A₀` is basic and representation-finite." The
vertex idempotents of `A₀` are primitive (`FpA0`); a corner element `e_i x e_j` with `i ≠ j` has
no degree-zero part (degree zero is spanned by the vertex idempotents, `VxG`), so an inverse pair
`x ∈ e_iA₀e_j`, `y ∈ e_jA₀e_i` would put `e_i = xy` in positive degree (`isBasic_A0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

local notation "Vx" => VxG D v₀ hF (lenW (Q := Q)) (AddMonoidHom.id ℤ) rfl

include v₀ hF in
/-- **`A₀` is basic** (Proposition 2.10(2)). -/
theorem isBasic_A0 : IsBasicAlgebra (Alg D.F0)ᵐᵒᵖ := by
  set G := lenA0 D (hfinObj (c := c))
  refine ⟨(FpA0 D v₀ hF).m, (FpA0 D v₀ hF).e, (FpA0 D v₀ hF).complete,
    (FpA0 D v₀ hF).primitive, fun i j ⟨x, y, hx, hy, hxy, hyx⟩ ↦ ?_⟩
  by_contra hij
  have he : ∀ l : Fin (FpA0 D v₀ hF).m, (Vx).e l = (FpA0 D v₀ hF).e l := fun l ↦ rfl
  -- the degree-zero part of `x` vanishes
  have h0 : G.proj 0 x = 0 := by
    have e1 : G.proj 0 x = (Vx).e i * G.proj 0 x * (Vx).e j := by
      conv_lhs => rw [← hx]
      rw [← he i, ← he j]
      have := PosFiltration.proj_mul_hom' ((Vx).deg0 j) ((Vx).e i * x) 0
      rw [zero_add] at this
      rw [this, show (0 : ℕ) = 0 + 0 from rfl, PosFiltration.proj_hom_mul' ((Vx).deg0 i) x 0]
    obtain ⟨cf, hcf⟩ := (Vx).span0 _ (G.isHom_proj 0 x)
    rw [e1, hcf, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc]
    by_cases hl : l = i
    · subst hl
      rw [((Vx).complete.idem l).eq, (Vx).complete.ortho hij, smul_zero]
    · rw [(Vx).complete.ortho (Ne.symm hl), zero_mul, smul_zero]
  have hx1 : G.Ge 1 x := fun d hd ↦ by
    obtain rfl : d = 0 := by omega
    exact h0
  have hprod := G.ge_mul hx1 (G.ge_zero y)
  have hei : G.proj 0 ((Vx).e i) = (Vx).e i := (Vx).deg0 i
  rw [he i, ← hxy] at hei
  rw [hprod 0 (by omega)] at hei
  exact ((FpA0 D v₀ hF).primitive i).2.1 (by rw [← hxy]; exact hei.symm)

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Proposition 2.10(2)** for a basic representation-finite algebra `A`: `A₀` is basic and
representation-finite. -/
theorem projectiveAlgebra_basic_repFinite (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    IsBasicAlgebra (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ ∧
      IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  exact ⟨MeshWalk.isBasic_A0 (S.arMeshData b) v₀ hF, hF⟩

end MultiplicativeBasisDeformations.IndSkeleton
