import MultiplicativeBasisDeformations.Foundations.ARMeshData
import MultiplicativeBasisDeformations.Foundations.GradedHomDimension
import MultiplicativeBasisDeformations.Foundations.ProjectiveIdempotents
import MultiplicativeBasisDeformations.Foundations.InjectiveLabels

/-!
# The labels `P_x, S_x, I_x` of `k(Γ_A)`

The data used in the paragraph "Injectives in the image" of the proof of
Proposition 2.10 (`graded-category.tex:504–523`): for a projective label `P_x`,
the original simple `S_x = P_x / rad P_x` and the original injective
`I_x = D(Ae_x)`, with

* `dim C(P_y, S_x) = dim Hom_A(P_y, S_x) = δ_{xy}`,
* `dim C(S_y, I_x) = dim Hom_A(S_y, I_x) = δ_{xy}`,
* `dim C(P_y, I_x) = dim I_x e_y = dim e_yAe_x = dim C(P_x, P_y)`,

all through `eq:graded-hom-dimensions` (`finrank_meshHom`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- `eq:graded-hom-dimensions` in `mod A`. -/
theorem finrank_meshHom_fg (x y : S.ARVertex) :
    Module.finrank k (S.meshObj b x ⟶ S.meshObj b y) =
      Module.finrank k (S.fg (S.index x) ⟶ S.fg (S.index y)) :=
  (S.finrank_meshHom b x y).trans (S.homEquivFG (S.label x) (S.label y)).finrank_eq

theorem projective_of_proj (p : (S.arMeshData b).PV) : Projective (S.fg (S.index p.1)) := by
  have := p.2
  change ¬ ¬ Projective (S.fg (S.index p.1)) at this
  exact not_not.1 this

/-- The label of the simple top of a projective label. -/
def topLabel (p : (S.arMeshData b).PV) : S.ARVertex :=
  S.vertex (Classical.choose (S.toVendor.fgObj_complete (S.top (S.index p.1))
    (S.top_indecomposable _ (S.projective_of_proj b p))))

def topLabelIso (p : (S.arMeshData b).PV) :
    S.top (S.index p.1) ≅ S.fg (S.index (S.topLabel b p)) :=
  (Classical.choose_spec (S.toVendor.fgObj_complete (S.top (S.index p.1))
    (S.top_indecomposable _ (S.projective_of_proj b p)))).some

/-- The injective label `I_x` of a projective label. -/
def injLabel (p : (S.arMeshData b).PV) : S.ARVertex :=
  S.vertex (Classical.choose (S.exists_injective_label _ (S.projective_of_proj b p)))

theorem finrank_hom_injLabel (p : (S.arMeshData b).PV) (M : ModCat A) :
    Module.finrank k (M ⟶ S.fg (S.index (S.injLabel b p))) =
      Module.finrank k (S.fg (S.index p.1) ⟶ M) :=
  Classical.choose_spec (S.exists_injective_label _ (S.projective_of_proj b p)) M

theorem pv_eq_iff (p q : (S.arMeshData b).PV) : q = p ↔ S.index q.1 = S.index p.1 :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext h⟩

theorem finrank_fg_top (p q : (S.arMeshData b).PV) :
    Module.finrank k (S.fg (S.index q.1) ⟶ S.fg (S.index (S.topLabel b p))) =
      if q = p then 1 else 0 := by
  rw [← (Linear.homCongr k (Iso.refl _) (S.topLabelIso b p)).finrank_eq,
    S.finrank_hom_top _ _ (S.projective_of_proj b p) (S.projective_of_proj b q)]
  simp only [S.pv_eq_iff b]

/-- **The labels of Proposition 2.10 for `k(Γ_A)`.** -/
def arInjData : CatAlg.MeshData.InjData (S.arMeshData b) where
  S := S.topLabel b
  I := S.injLabel b
  dimS p q := by
    change Module.finrank k (S.meshObj b q.1 ⟶ S.meshObj b (S.topLabel b p)) = _
    rw [S.finrank_meshHom_fg b]
    exact S.finrank_fg_top b p q
  dimSI p q := by
    change Module.finrank k (S.meshObj b (S.topLabel b q) ⟶ S.meshObj b (S.injLabel b p)) = _
    rw [S.finrank_meshHom_fg b, S.finrank_hom_injLabel b, S.finrank_fg_top b q p]
    simp only [eq_comm]
  dimI p q := by
    change Module.finrank k (S.meshObj b q.1 ⟶ S.meshObj b (S.injLabel b p)) =
      Module.finrank k (S.meshObj b p.1 ⟶ S.meshObj b q.1)
    rw [S.finrank_meshHom_fg b, S.finrank_hom_injLabel b, S.finrank_meshHom_fg b]

end MultiplicativeBasisDeformations.IndSkeleton
