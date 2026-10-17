import MultiplicativeBasisDeformations.Foundations.WeightEv

/-!
# Homogeneous module and arrow lifts (Proposition 7.6, weights)

`weights-and-parameters.tex`: "Lift a basis of the integer ray weights to mesh
weights using Lemma 7.4. These give simultaneous gradings on the lifted modules. If `μ`
has character `χ`, give `ε` weight `−χ` and choose the homogeneous solutions in the
lemma. Then `z_v` has weight `χ` relative to its row."

The homogeneous solutions are obtained from arbitrary ones by taking weight parts: the
lifted action equations and the arrow-lifting equations are linear, and all fixed maps
in them shift weights, so the weight-`χ` parts of the corrections are again solutions
(`wLift`, `wLiftData`). Their mesh errors shift by `ν_x + χ` (`zE_wshift`), hence lie in
`C(τx, x)` of weight `ν_x + χ` (`exists_liftData_wt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}

/-- `μ` raises weights by `χ`. -/
def HasChar (χ : M) (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) : Prop :=
  ∀ α β a b, (grA0 W hfin D).IsHom α a → (grA0 W hfin D).IsHom β b →
    (grA0 W hfin D).IsHom (α + β + χ) (μ a b)

/-! ### Linear-map packaging -/

/-- The correction maps of a lifted action, linearly in the algebra element. -/
def nuL {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) :
    (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X)) where
  toFun a := Lx.ν (single a)
  map_add' := Lx.good.single_add
  map_smul' t a := Lx.good.single_smul t a

theorem nuL_apply {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) (a : (Alg D.F0)ᵐᵒᵖ)
    (m : Rep D.F0 (meshFam Q c X)) : nuL hfin D Lx a m = Lx.act m a := rfl

/-- The right action, linearly in the algebra element. -/
abbrev actL (X : V) :
    (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X)) :=
  (evAct D X).flip

/-- The weight part of an endomorphism of `M_X`, as a linear map. -/
def prL (X : V) (γ : M) :
    (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X)) →ₗ[k]
      (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X)) where
  toFun := MGr.pr (grEv W hfin D X) (grEv W hfin D X) γ
  map_add' := MGr.pr_add γ
  map_smul' := MGr.pr_smul γ

variable (χ : M)

/-- **The weight-`χ` part of a lifted action.** -/
def wnu {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) :
    (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X)) :=
  ∑ α ∈ wSupp W hfin, prL W hfin D X (α + χ) ∘ₗ nuL hfin D Lx ∘ₗ a0Proj W D α

theorem wnu_hom {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) {α : M}
    {a : (Alg D.F0)ᵐᵒᵖ} (ha : (grA0 W hfin D).IsHom α a) :
    wnu W hfin D χ Lx a = MGr.pr (grEv W hfin D X) (grEv W hfin D X) (α + χ) (Lx.ν (single a)) := by
  simp only [wnu, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  by_cases hα : α ∈ wSupp W hfin
  · rw [Finset.sum_eq_single α]
    · change MGr.pr _ _ _ (Lx.ν (single ((grA0 W hfin D).proj α a))) = _
      rw [ha]
    · intro β _ hβ
      change MGr.pr _ _ _ (Lx.ν (single ((grA0 W hfin D).proj β a))) = 0
      rw [(grA0 W hfin D).proj_of_isHom ha, if_neg (Ne.symm hβ)]
      change prL W hfin D X (β + χ) (nuL hfin D Lx 0) = 0
      rw [map_zero, map_zero]
    · intro h; exact absurd hα h
  · rw [(grA0 W hfin D).eq_zero_of_isHom_out ha hα]
    change _ = prL W hfin D X (α + χ) (nuL hfin D Lx 0)
    simp

variable {W hfin D χ}

theorem wnu_equation_hom (hμχ : HasChar W hfin D χ μ) {X : V}
    (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) {α β : M} {a b : (Alg D.F0)ᵐᵒᵖ}
    (ha : (grA0 W hfin D).IsHom α a) (hb : (grA0 W hfin D).IsHom β b) :
    wnu W hfin D χ Lx b ∘ₗ actL D X a - wnu W hfin D χ Lx (a * b) + actL D X b ∘ₗ wnu W hfin D χ Lx a =
      actL D X (μ a b) := by
  set G := grEv W hfin D X
  have hsa := act_shift W hfin D ha X
  have hsb := act_shift W hfin D hb X
  have e0 : Lx.ν (single b) ∘ₗ actL D X a - Lx.ν (single (a * b)) +
      actL D X b ∘ₗ Lx.ν (single a) = actL D X (μ a b) := by
    refine LinearMap.ext fun m ↦ ?_
    have := Lx.equation m a b
    simp only [ActLift.act] at this
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.flip_apply]
    exact this
  have hγ : MGr.Shift G G (α + β + χ) (actL D X (μ a b)) :=
    act_shift W hfin D (hμχ α β a b ha hb) X
  rw [wnu_hom W hfin D χ Lx ha, wnu_hom W hfin D χ Lx hb,
    wnu_hom W hfin D χ Lx (grA0_mul W hfin D ha hb),
    ← MGr.pr_comp_right _ hsa, ← MGr.pr_comp_left _ hsb]
  rw [show α + (β + χ) = α + β + χ by abel, show α + χ + β = α + β + χ by abel,
    ← MGr.pr_sub, ← MGr.pr_add, e0, MGr.pr_of_shift hγ]

/-- The defect of the lifted action equation, bilinearly. -/
def eqDefect {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) :
    (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k]
      (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X)) :=
  LinearMap.mk₂ k (fun a b ↦ wnu W hfin D χ Lx b ∘ₗ actL D X a - wnu W hfin D χ Lx (a * b) +
      actL D X b ∘ₗ wnu W hfin D χ Lx a - actL D X (μ a b))
    (fun a a' b ↦ by
      simp only [map_add, add_mul, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply]
      abel)
    (fun t a b ↦ by
      simp only [map_smul, smul_mul_assoc, LinearMap.comp_smul, LinearMap.smul_comp,
        LinearMap.smul_apply, smul_sub, smul_add])
    (fun a b b' ↦ by
      simp only [map_add, mul_add, LinearMap.comp_add, LinearMap.add_comp]
      abel)
    (fun t a b ↦ by
      simp only [map_smul, mul_smul_comm, LinearMap.comp_smul, LinearMap.smul_comp,
        smul_sub, smul_add])

theorem eqDefect_eq_zero (hμχ : HasChar W hfin D χ μ) {X : V}
    (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) : eqDefect (W := W) (hfin := hfin) (χ := χ) Lx = 0 := by
  refine (grA0 W hfin D).ext_of_hom fun α a ha ↦ ?_
  refine (grA0 W hfin D).ext_of_hom fun β b hb ↦ ?_
  simp only [eqDefect, LinearMap.mk₂_apply, LinearMap.zero_apply]
  rw [wnu_equation_hom hμχ Lx ha hb, sub_self]

theorem wnu_equation (hμχ : HasChar W hfin D χ μ) {X : V}
    (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) (a b : (Alg D.F0)ᵐᵒᵖ) :
    wnu W hfin D χ Lx b ∘ₗ actL D X a - wnu W hfin D χ Lx (a * b) + actL D X b ∘ₗ wnu W hfin D χ Lx a =
      actL D X (μ a b) := by
  have := LinearMap.congr_fun (LinearMap.congr_fun (eqDefect_eq_zero hμχ Lx) a) b
  simp only [eqDefect, LinearMap.mk₂_apply, LinearMap.zero_apply] at this
  exact sub_eq_zero.1 this

theorem wnu_zgr {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) {p d : ℤ}
    {a : (Alg D.F0)ᵐᵒᵖ} (ha : (galgA0 D hfin).gr.IsHom d a) {m : Rep D.F0 (meshFam Q c X)}
    (hm : (zgrEv D hfin X).IsHom p m) :
    (zgrEv D hfin X).IsHom (p + d + q) (wnu W hfin D χ Lx a m) := by
  simp only [wnu, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  refine ZGr.isHom_sum _ _ _ fun α _ ↦ ?_
  change (zgrEv D hfin X).IsHom _ (MGr.pr _ _ _ _ m)
  simp only [MGr.pr, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  refine ZGr.isHom_sum _ _ _ fun g _ ↦ evProj_zgr W hfin D ?_
  exact (Lx.act_deg (evProj_zgr W hfin D hm) (a0Proj_zgr W hfin D ha) :)

/-- **The homogeneous lifted action.** -/
def wLift (hμχ : HasChar W hfin D χ μ) {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X)) :
    ActLift μ (q : ℤ) (gmodEv D hfin X) where
  ν a := wnu W hfin D χ Lx (a 0)
  good := by
    refine ⟨fun a ↦ by simp [Bar.tr], fun a i x y hi ↦ ?_, fun a i t x hi ↦ ?_,
      fun a ds p m ha hm ↦ ?_⟩
    · obtain rfl : i = 0 := by omega
      simp only [Function.update_self, map_add]
    · obtain rfl : i = 0 := by omega
      simp only [Function.update_self, map_smul]
    · have := wnu_zgr (W := W) (χ := χ) Lx (ha 0 (by omega)) hm
      show (zgrEv D hfin X).IsHom (p + ∑ i ∈ Finset.range 1, ds i + q) _
      rw [Finset.sum_range_one]; exact this
  eq := by
    funext a
    rw [Bar.d_one_apply]
    refine LinearMap.ext fun m ↦ ?_
    have := LinearMap.congr_fun (wnu_equation hμχ Lx (a 0) (a 1)) m
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.flip_apply] at this
    have e1 : Bar.ct 0 a 0 = a 0 * a 1 := Bar.ct_apply_self 0 a
    have e2 : Bar.tr 1 a 0 = a 0 := Bar.tr_apply_lt (by omega) a
    change (homAct (gmodEv D hfin X) (gmodEv D hfin X)).l (a 0) (wnu W hfin D χ Lx (a 1)) m -
      wnu W hfin D χ Lx (Bar.ct 0 a 0) m +
      (homAct (gmodEv D hfin X) (gmodEv D hfin X)).r (a 1) (wnu W hfin D χ Lx (Bar.tr 1 a 0)) m = _
    rw [e1, e2, homAct_l, homAct_r, muCochain_apply]
    exact this

theorem wLift_act (hμχ : HasChar W hfin D χ μ) {X : V} (Lx : ActLift μ (q : ℤ) (gmodEv D hfin X))
    (m : Rep D.F0 (meshFam Q c X)) (a : (Alg D.F0)ᵐᵒᵖ) :
    (wLift hμχ Lx).act m a = wnu W hfin D χ Lx a m := by
  rfl

/-! ### Homogeneous arrow lifts -/

variable (W χ) in
/-- The weight part of an arrow lift. -/
def wg (Ld : LiftData D hfin q μ) {y x : V} (a : y ⟶ x) :
    Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x) :=
  MGr.pr (grEv W hfin D y) (grEv W hfin D x) (W.w a + χ) (Ld.g a)

variable (W) in
/-- The defect of the arrow-lifting equation, linearly in the algebra element. -/
def liftDefect (Ld : LiftData D hfin q μ) {y x : V} (a : y ⟶ x) :
    (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)) where
  toFun b := wg W χ Ld a ∘ₗ actL D y b - actL D x b ∘ₗ wg W χ Ld a -
    (wnu W hfin D χ (Ld.L x) b ∘ₗ fA D a - fA D a ∘ₗ wnu W hfin D χ (Ld.L y) b)
  map_add' b b' := by
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp]
    abel
  map_smul' t b := by
    simp only [map_smul, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply, smul_sub]

theorem liftDefect_eq_zero (Ld : LiftData D hfin q μ) {y x : V} (a : y ⟶ x) :
    liftDefect W (χ := χ) Ld a = 0 := by
  refine (grA0 W hfin D).ext_of_hom fun β b hb ↦ ?_
  have hsy := act_shift W hfin D hb y
  have hsx := act_shift W hfin D hb x
  have hfa := fA_shift W hfin D a
  have e0 : Ld.g a ∘ₗ actL D y b - actL D x b ∘ₗ Ld.g a -
      (nuL hfin D (Ld.L x) b ∘ₗ fA D a - fA D a ∘ₗ nuL hfin D (Ld.L y) b) = 0 := by
    refine LinearMap.ext fun m ↦ ?_
    have := (Ld.lift a).2 m b
    simp only [ActLift.act] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      LinearMap.zero_apply]
    rw [sub_eq_zero]
    exact this
  change wg W χ Ld a ∘ₗ actL D y b - actL D x b ∘ₗ wg W χ Ld a -
    (wnu W hfin D χ (Ld.L x) b ∘ₗ fA D a - fA D a ∘ₗ wnu W hfin D χ (Ld.L y) b) = 0
  rw [wnu_hom W hfin D χ _ hb, wnu_hom W hfin D χ _ hb, wg, ← MGr.pr_comp_right _ hsy,
    ← MGr.pr_comp_left _ hsx, ← MGr.pr_comp_right _ hfa, ← MGr.pr_comp_left _ hfa]
  rw [show β + (W.w a + χ) = W.w a + β + χ by abel, show W.w a + χ + β = W.w a + β + χ by abel,
    show W.w a + (β + χ) = W.w a + β + χ by abel, show β + χ + W.w a = W.w a + β + χ by abel,
    ← MGr.pr_sub, ← MGr.pr_sub, ← MGr.pr_sub]
  change MGr.pr _ _ _ (Ld.g a ∘ₗ actL D y b - actL D x b ∘ₗ Ld.g a -
      (nuL hfin D (Ld.L x) b ∘ₗ fA D a - fA D a ∘ₗ nuL hfin D (Ld.L y) b)) = 0
  rw [e0, MGr.pr_zero]

theorem wg_zgr (Ld : LiftData D hfin q μ) {y x : V} (a : y ⟶ x) (p : ℤ)
    (m : Rep D.F0 (meshFam Q c y)) (hm : (zgrEv D hfin y).IsHom p m) :
    (zgrEv D hfin x).IsHom (p + (1 + (q : ℤ))) (wg W χ Ld a m) := by
  simp only [wg, MGr.pr, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  refine ZGr.isHom_sum _ _ _ fun g _ ↦ evProj_zgr W hfin D ?_
  exact Ld.deg a p _ (evProj_zgr W hfin D hm)

variable (W χ) in
/-- **The homogeneous lift data.** -/
def wLiftData (hμχ : HasChar W hfin D χ μ) (Ld : LiftData D hfin q μ) : LiftData D hfin q μ where
  L X := wLift hμχ (Ld.L X)
  g a := wg W χ Ld a
  lift a := by
    refine ⟨(Ld.lift a).1, fun m b ↦ ?_⟩
    have := LinearMap.congr_fun (LinearMap.congr_fun (liftDefect_eq_zero (W := W) (χ := χ) Ld a) b) m
    change (wg W χ Ld a ∘ₗ actL D _ b - actL D _ b ∘ₗ wg W χ Ld a -
      (wnu W hfin D χ (Ld.L _) b ∘ₗ fA D a - fA D a ∘ₗ wnu W hfin D χ (Ld.L _) b)) m = 0 at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply] at this
    rw [wLift_act, wLift_act]
    exact sub_eq_zero.1 this
  deg a p m hm := wg_zgr Ld a p m hm

theorem wLiftData_g (hμχ : HasChar W hfin D χ μ) (Ld : LiftData D hfin q μ) {y x : V} (a : y ⟶ x) :
    (wLiftData W χ hμχ Ld).g a = wg W χ Ld a := rfl

/-- **The mesh errors of the homogeneous lift data shift by `ν_x + χ`.** -/
theorem zE_wshift (hμχ : HasChar W hfin D χ μ) (Ld : LiftData D hfin q μ) (x : Q.nonprojective) :
    MGr.Shift (grEv W hfin D (Q.tau x).1) (grEv W hfin D x.1) (W.ν x + χ)
      (zE (wLiftData W χ hμχ Ld) x) := by
  refine MGr.Shift.sum _ fun a _ ↦ (MGr.Shift.add ?_ ?_).smul _
  · refine ((fA_shift W hfin D a.2).comp (MGr.shift_pr _ _)).congr ?_
    rw [← W.mesh x a]; abel
  · refine ((MGr.shift_pr _ _).comp (fA_shift W hfin D _)).congr ?_
    rw [← W.mesh x a]; abel

variable [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- **Proposition 7.6, weights**: a cocycle of character `χ` has lift data whose mesh
errors have weight `χ` relative to their rows. -/
theorem zhat_wLiftData (hμχ : HasChar W hfin D χ μ) (Ld : LiftData D hfin q μ)
    (x : Q.nonprojective) :
    zhat (wLiftData W χ hμχ Ld) x ∈ wP c W (W.ν x + χ) (Q.tau x).1 x.1 := by
  refine mem_wP_of_shift W hfin D ?_
  have := zE_wshift hμχ Ld x
  rwa [zhat_spec] at this

end MeshWalk

end MultiplicativeBasisDeformations
