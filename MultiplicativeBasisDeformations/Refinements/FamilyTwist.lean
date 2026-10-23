module

public import MultiplicativeBasisDeformations.Refinements.FamilyNormalForm

/-!
# The polynomial mesh relations (Proposition 12.8, `F_i(t) = a_i t_i`)

`deformation-refinements.tex`: "Give `t_i` total weight `−χ_i` […] The choices above, made
separately in each weight, make `F_j` homogeneous of coefficient weight `χ_j`. […]
Lemma 12.7 therefore gives `F_j = a_j t_j`."

The lifted arrows at `t = 1` (with the normal form `r_x = Σ_i λ_i R_i`) are twisted to every
fibre (`twArrow`): the twist of a component of relative weight `γ` is multiplied by `t^{coords γ}`.
The twisted arrows are morphisms of the lifted modules of the fibre `t`, realize every path by the
twist of its realization (`toLin_pathR_tw`), and satisfy `r_x = Σ_i λ_i t_i R_i` (`tw_relation`):
the retained coefficients are `F_i(t) = λ_i t_i`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration MGr PathReal

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)} [Fintype Q.nonprojective]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {I : Type} [Fintype I] [DecidableEq I]
  {μ : I → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ} {qd : I → ℕ}
  {H : FamHyp D hfin μ qd}
  {Wt : Type} [AddCommGroup Wt] {W : MeshWt Q Wt} {χ : I → Wt} {coords : Wt →+ (I → ℤ)}
  {hχ : ∀ i, HasChar W hfin D (χ i) (μ i)} {J : D.InjData} {h1 : DegOne D}
  {hco : ∀ i, coords (χ i) = Pi.single i 1} [Infinite k]

/-! ### The lifted actions at the fibre `t` -/

variable (H W hχ J h1 hco) in
theorem famAct_tot (t : I → k) (X : V) : (famAct H W hχ J h1 hco t X).tot =
    twb coords (grEv W hfin D X) (grA0 W hfin D) (grEv W hfin D X) t 0
      (act1 H W hχ J h1 hco X).tot := by
  simp only [ActFam.tot, twb_sum]
  rfl

theorem famLifts_act (t : I → k) (X : V) (m : Rep D.F0 (meshFam Q c X))
    (b : Fib (famAM H t)) :
    ((famLifts H W hχ J h1 hco t).L X).act m b =
      twb coords (grEv W hfin D X) (grA0 W hfin D) (grEv W hfin D X) t 0
        (act1 H W hχ J h1 hco X).tot m (Fib.toΛ _ b) := by
  change (famAct H W hχ J h1 hco t X).tot m _ = _
  rw [famAct_tot]
  rfl

theorem act1_tot_cone (X : V) : ConeBil (C := cone χ) (G := grEv W hfin D X)
    (G' := grA0 W hfin D) (G'' := grEv W hfin D X) 0 (act1 H W hχ J h1 hco X).tot :=
  coneBil_sum _ fun n _ ↦ act1_cone H W hχ J h1 hco X n

theorem toLin_act1 {y x : V} (f : FB (Ls1 H W hχ J h1 hco) y ⟶ FB (Ls1 H W hχ J h1 hco) x)
    (m : Rep D.F0 (meshFam Q c y)) (a : (Alg D.F0)ᵐᵒᵖ) :
    toLin f ((act1 H W hχ J h1 hco y).tot m a) = (act1 H W hχ J h1 hco x).tot (toLin f m) a := by
  have := toLin_act f m ((Fib.toΛ (famAM H 1)).symm a)
  rw [Ls1_act, Ls1_act, LinearEquiv.apply_symm_apply] at this
  exact this

/-! ### Twisted arrows -/

/-- **The twisted lifted arrow at the fibre `t`.** -/
def twArrow (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V} (a : y ⟶ x) :
    FB (famLifts H W hχ J h1 hco t) y ⟶ FB (famLifts H W hχ J h1 hco t) x :=
  ofLin _ (twl coords (grEv W hfin D y) (grEv W hfin D x) t (W.w a) (toLin (A.g a)))
    fun m b ↦ by
      rw [famLifts_act, famLifts_act]
      exact twl_lin (cone_nonneg hco) (A.cone a) (act1_tot_cone y) (act1_tot_cone x)
        (fun m a' ↦ toLin_act1 (A.g a) m a') t m _

theorem toLin_twArrow (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V} (a : y ⟶ x) :
    toLin (twArrow A t a) = twl coords (grEv W hfin D y) (grEv W hfin D x) t (W.w a)
      (toLin (A.g a)) := rfl

/-- **Twisted arrows realize paths by the twists of the realizations.** -/
theorem toLin_pathR_tw (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V}
    (p : Quiver.Path y x) :
    toLin (pathR (twArrow A t) p) =
      twl coords (grEv W hfin D y) (grEv W hfin D x) t (W.pw p) (toLin (pathR A.g p)) := by
  induction p with
  | nil =>
    rw [pathR_nil, pathR_nil, toLin_id, toLin_id,
      show W.pw (Quiver.Path.nil : Quiver.Path y y) = 0 by simp [MeshWt.pw]]
    exact (twl_id (wM := grEv W hfin D y) (coords := coords) t).symm
  | cons p a ih =>
    have hpw : W.pw (p.cons a) = W.pw p + W.w a := by
      change W.pw (p.comp a.toPath) = _
      rw [W.pw_comp, W.pw_toPath]
    rw [pathR_cons, pathR_cons, toLin_comp, toLin_comp, ih, toLin_twArrow, hpw,
      twl_comp (cone_nonneg hco) (pathR_props A p).2.2.1 (A.cone a)]

theorem toLin_realize_tw (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V} {γ : Wt} {d : ℕ}
    {F : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj x} (hF : F ∈ WPs W γ d y x) :
    toLin (realizeR k (twArrow A t) y x F) =
      twl coords (grEv W hfin D y) (grEv W hfin D x) t γ (toLin (realizeR k A.g y x F)) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, -, hw, rfl⟩ := hF
    rw [realizeR_path, realizeR_path, toLin_pathR_tw, hw]
  | zero => simp only [map_zero, toLin_zero, twl_zero]
  | add F G _ _ hF hG => rw [map_add, map_add, toLin_add, toLin_add, hF, hG, twl_add]
  | smul s F _ hF => rw [map_smul, map_smul, toLin_smul, toLin_smul, hF, twl_smul]

variable {Rw : I → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1}
  (hlen : ∀ i, (Rw i).2.length = qd i + 2) (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i)

include hlen hwt in
/-- **The polynomial mesh relations**: `r_x = Σ_i λ_i t_i R_i` at every fibre. -/
theorem tw_relation (A : ArrowL H W hχ J h1 hco) (lam : I → k) (hA : ∀ x, errE Rw A lam x = 0)
    (t : I → k) (x : Q.nonprojective) :
    realizeR k (twArrow A t) _ _ (meshRelation c x) =
      ∑ i, (lam i * t i) • realizeR k (twArrow A t) _ _ (rowQ (k := k) Rw i x) := by
  apply toLin_injective
  have hm : realizeR k A.g _ _ (meshRelation c x) =
      ∑ i, lam i • realizeR k A.g _ _ (rowQ (k := k) Rw i x) := sub_eq_zero.1 (hA x)
  rw [toLin_realize_tw A t (meshRelation_mem (W := W) (c := c) x), hm, toLin_sum, twl_sum,
    toLin_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hr := realize_props A (rowQ_mem (W := W) hlen hwt i x)
  rw [toLin_smul, twl_smul, toLin_smul,
    toLin_realize_tw A t (rowQ_mem (W := W) hlen hwt i x),
    twl_shift (cone_nonneg hco) hr.2.2.1 (AddSubmonoid.subset_closure ⟨i, rfl⟩), ch_χ hco,
    smul_smul]

end MeshWalk

end MultiplicativeBasisDeformations
