import MultiplicativeBasisDeformations.Refinements.FamilyLifts
import MultiplicativeBasisDeformations.Refinements.LiftedCategory
import MultiplicativeBasisDeformations.Refinements.PathRealize

/-!
# Homogeneous lifts of morphisms at `t = 1` (Proposition 12.8, morphisms)

`deformation-refinements.tex:387–392`: "after lifting a homogeneous map of degree `r ≥ 0`
through correction degrees less than `q`, its next linearity defect is a one-cocycle of degree
`r + q`. The positive `Ext¹` vanishing removes it with the chosen right inverse."

At the fibre `t = 1` a morphism `φ` of `C` of degree `r` and weight `ρ` lifts to a morphism of
the lifted modules of order `r`, with leading term `φ`, all of whose components have relative
weights in the cone, and whose component of relative weight `0` is `φ` itself (`exists_liftHom`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration MGr

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {I : Type} [Fintype I] [DecidableEq I]
  {μ : I → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ} {qd : I → ℕ}
  (H : FamHyp D hfin μ qd)
  {Wt : Type} [AddCommGroup Wt] (W : MeshWt Q Wt) {χ : I → Wt} {coords : Wt →+ (I → ℤ)}
  (hχ : ∀ i, HasChar W hfin D (χ i) (μ i)) (J : D.InjData) (h1 : DegOne D)
  (hco : ∀ i, coords (χ i) = Pi.single i 1) [Infinite k]

/-- The lifted modules at the fibre `t = 1`. -/
abbrev Ls1 : Lifts D hfin (famPF H 1) := famLifts H W hχ J h1 hco 1

theorem famAct_one_ν (X : V) (n : ℕ) :
    (famAct H W hχ J h1 hco 1 X).ν n = (act1 H W hχ J h1 hco X).ν n :=
  twb_one (coords := coords) 0 _

theorem famAct_one_tot (X : V) :
    (famAct H W hχ J h1 hco 1 X).tot = (act1 H W hχ J h1 hco X).tot := by
  simp only [ActFam.tot, famAct_one_ν]

theorem Ls1_act (X : V) (m : Rep D.F0 (meshFam Q c X)) (x : Fib (famAM H 1)) :
    ((Ls1 H W hχ J h1 hco).L X).act m x = (act1 H W hχ J h1 hco X).tot m (Fib.toΛ _ x) := by
  change (famAct H W hχ J h1 hco 1 X).tot m _ = _
  rw [famAct_one_tot]; rfl

/-- **A homogeneous morphism of `C` lifts at `t = 1`** with homogeneous corrections. -/
theorem exists_liftHom {y x : V} (r : ℕ) (ρ : Wt) (φ : obj c y ⟶ obj c x)
    (hφd : φ ∈ degreePart c r y x) (hφw : φ ∈ wP c W ρ y x) :
    ∃ g : FB (Ls1 H W hχ J h1 hco) y ⟶ FB (Ls1 H W hχ J h1 hco) x,
      OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r (toLin g) ∧
      ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r (toLin g) = rs D φ ∧
      ConeLin (C := cone χ) (G := grEv W hfin D y) (G' := grEv W hfin D x) ρ (toLin g) ∧
      clin ⊥ (grEv W hfin D y) (grEv W hfin D x) ρ (toLin g) = rs D φ := by
  have hsh : ∀ β m, (grEv W hfin D y).IsHom β m → (grEv W hfin D x).IsHom (β + ρ) (rs D φ m) :=
    fun β m hm ↦ rs_shift W hfin D hφw β m hm
  obtain ⟨F, hF0, hF, hFa, hFc, hFb⟩ := exists_liftMap_cone (r := (r : ℤ))
    (wtCompat D hfin W y) (cone_pointed hco) (wtCompat D hfin W x) _
    (act1 H W hχ J h1 hco y) (act1 H W hχ J h1 hco x)
    (act1_cone H W hχ J h1 hco y) (act1_cone H W hχ J h1 hco x)
    (fun i hi β α m a hm ha ↦ act1_bottom H W hχ J h1 hco y i hi hm ha)
    (fun i hi β α m a hm ha ↦ act1_bottom H W hχ J h1 hco x i hi hm ha)
    (rs D φ) (fun m a ↦ rs_act φ m a) (fun p m hm ↦ repMap_isHom hfin hφd hm) hsh
    (Split.ofLen_nonneg _)
    (fun t ht ↦ extVanish_ev D hfin J h1 0 y x _ (Or.inr (by push_cast; omega)))
  set G := mapTot (gmodEv D hfin y) (gmodEv D hfin x) r F
  have hGlin : ∀ m b, G (((Ls1 H W hχ J h1 hco).L y).act m b) =
      ((Ls1 H W hχ J h1 hco).L x).act (G m) b := by
    intro m b
    rw [Ls1_act, Ls1_act]
    exact mapTot_comm (Split.ofLen_nonneg _) _ _ hF hFa m _
  refine ⟨ofLin _ G hGlin, ?_, ?_, ?_, ?_⟩
  · intro p m hm d hd
    simp only [toLin_ofLin, G, mapTot, LinearMap.coe_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [(gmodEv D hfin x).gr.proj_of_isHom (hF i p m hm), if_neg (by omega)]
  · rw [toLin_ofLin]
    refine (gmodEv D hfin y).gr.ext_of_hom fun p m hm ↦ ?_
    rw [ZGr.comp_hom _ _ _ hm]
    simp only [G, mapTot, LinearMap.coe_sum, Finset.sum_apply, map_sum]
    rw [Finset.sum_eq_single 0]
    · have h0 := hF 0 p m hm
      rw [Nat.cast_zero, add_zero, hF0] at h0
      rw [hF0, (gmodEv D hfin x).gr.proj_of_isHom h0, if_pos rfl]
    · intro i _ hi
      rw [(gmodEv D hfin x).gr.proj_of_isHom (hF i p m hm), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [toLin_ofLin]
    intro β m hm
    simp only [G, mapTot, LinearMap.coe_sum, Finset.sum_apply]
    exact ConeAt.sum _ fun i _ ↦ hFc i β m hm
  · rw [toLin_ofLin]
    refine (grEv W hfin D y).ext_of_hom fun β m hm ↦ ?_
    rw [clin_apply_hom ρ _ hm, cpart_bot]
    simp only [G, mapTot, LinearMap.coe_sum, Finset.sum_apply, map_sum]
    rw [Finset.sum_eq_single 0]
    · rw [hF0]; exact hsh β m hm
    · intro i _ hi; exact hFb i (by omega) β m hm
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

end MeshWalk

end MultiplicativeBasisDeformations
