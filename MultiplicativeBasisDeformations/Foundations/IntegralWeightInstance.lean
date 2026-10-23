module

public import MultiplicativeBasisDeformations.Foundations.IntegralLifts
public import MultiplicativeBasisDeformations.Foundations.IntegralWeightLift
public import MultiplicativeBasisDeformations.Foundations.WeightEv
public import MultiplicativeBasisDeformations.Foundations.CoordGrading

/-!
# Weight-homogeneous lifts of the evaluated modules (Proposition 10.1)

`integral-deformations.tex`: "All these constructions can be chosen to preserve the
simultaneous integer weights: lifting a basis of `H_ℤ` to mesh weights by Lemma 7.4 gives the
modules `M_i⁽²⁾` compatible weight gradings, and the corrections can be chosen in each weight
component."

A mesh weight `W` of `C⁽²⁾` with values in an abelian group `M` grades `A⁽²⁾` and the evaluated
modules (`grA0`, `grEv`, `WeightEv.lean`). When it lifts the ray weights `hv` of the table `P`
(the rays `Θ(b_r)` are homogeneous of weight `hv r`, `hΘ`), each integer coordinate `φ : M →+ ℤ`
grades `A⁽²⁾` (`galgW`), `A⁽⁴⁾ = 𝒪P` (`galgOW`, by the ray weights) and the modules (`gwEv`),
compatibly with the reduction (`isRedW`), the actions (`actW`), the degree and each other. Then the
module lifts and arrow lifts of Proposition 10.1 can be chosen homogeneous for any finite family
of coordinates (`exists_modLiftW`, `exists_arrowLiftW`), by `exists_liftMod_weights` and
`exists_liftHom_weights`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift

attribute [local instance] Classical.decEq

theorem zrepr_eq_zero {k : Type*} [Field k] {N : Type*} [AddCommGroup N] [Module k N]
    (g : ZGr (R := k) N) {ι : Type*} [Fintype ι] (β : Module.Basis ι k N) (d : ι → ℤ)
    (hβ : ∀ i, g.IsHom (d i) (β i)) {p : ℤ} {m : N} (hm : g.IsHom p m) {i : ι} (hi : d i ≠ p) :
    β.repr m i = 0 := by
  classical
  have key : m = β.equivFun.symm (fun j ↦ if d j = p then β.repr m j else 0) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← hm, ← β.sum_repr m, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, g.proj_of_isHom (hβ j)]
    split_ifs <;> simp
  have := congrArg (fun z ↦ β.equivFun z i) key
  simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at this
  rw [this, if_neg hi]

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} (T : TabIso D P)
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)

/-! ### The weight gradings of `A⁽²⁾` and of the evaluated modules -/

theorem grA0_one : (grA0 W (hfin2 (c := c)) D).IsHom 0 (1 : (Alg D.F0)ᵐᵒᵖ) := by
  rw [grA0_isHom]
  intro p q
  change (1 : Alg D.F0) p q ∈ _
  rw [one_apply]
  by_cases h : p = q
  · subst h
    rw [idTo_self]
    have := pathMor_mem_wP (c := c) W (Quiver.Path.nil : Quiver.Path p.1 p.1)
    rw [pathMor_nil, show W.pw (Quiver.Path.nil : Quiver.Path p.1 p.1) = 0 by simp [MeshWt.pw]] at this
    exact this
  · rw [idTo_ne h]; exact Submodule.zero_mem _

variable (D) in
/-- **`A⁽²⁾` graded by a coordinate `φ` of the mesh weight.** -/
def galgW (φ : M →+ ℤ) : GAlg (R := 𝔽₂) (Alg D.F0)ᵐᵒᵖ where
  gr := (grA0 W (hfin2 (c := c)) D).coord φ
  mul_hom p q a b ha hb := by
    have ha' : ∑ g ∈ (grA0 W (hfin2 (c := c)) D).supp with φ g = p,
        (grA0 W (hfin2 (c := c)) D).proj g a = a := by
      rw [← MGr.coord_proj]; exact ha
    have hb' : ∑ g ∈ (grA0 W (hfin2 (c := c)) D).supp with φ g = q,
        (grA0 W (hfin2 (c := c)) D).proj g b = b := by
      rw [← MGr.coord_proj]; exact hb
    rw [← ha', ← hb', Finset.sum_mul]
    refine ZGr.isHom_sum _ _ _ fun g hg ↦ ?_
    rw [Finset.mul_sum]
    refine ZGr.isHom_sum _ _ _ fun h hh ↦ ?_
    have := MGr.coord_isHom _ (grA0_mul W (hfin2 (c := c)) D
      ((grA0 W (hfin2 (c := c)) D).isHom_proj g a)
      ((grA0 W (hfin2 (c := c)) D).isHom_proj h b)) φ
    rwa [map_add, (Finset.mem_filter.1 hg).2, (Finset.mem_filter.1 hh).2] at this
  one_hom := by simpa using MGr.coord_isHom _ (grA0_one W (D := D)) φ

variable (D) in
/-- **The evaluated module graded by a coordinate.** -/
abbrev gwEv (X : V) (φ : M →+ ℤ) : ZGr (R := 𝔽₂) (Rep D.F0 (meshFam Q c X)) :=
  (grEv W (hfin2 (c := c)) D X).coord φ

theorem coord_sum {N : Type*} [AddCommGroup N] [Module 𝔽₂ N] (G : MGr 𝔽₂ M N) (φ : M →+ ℤ)
    {p : ℤ} {x : N} (hx : (G.coord φ).IsHom p x) :
    ∑ g ∈ G.supp with φ g = p, G.proj g x = x := by
  rw [← MGr.coord_proj]; exact hx

/-- **The action shifts the coordinate weights.** -/
theorem actW (φ : M →+ ℤ) (X : V) (p q : ℤ) (m : Rep D.F0 (meshFam Q c X))
    (a : (Alg D.F0)ᵐᵒᵖ) (hm : (gwEv D W X φ).IsHom p m) (ha : (galgW D W φ).gr.IsHom q a) :
    (gwEv D W X φ).IsHom (p + q) ((gmodEv D (hfin2 (c := c)) X).act m a) := by
  rw [← coord_sum _ φ hm, ← coord_sum _ φ ha]
  simp only [map_sum, LinearMap.sum_apply]
  refine ZGr.isHom_sum _ _ _ fun α hα ↦ ZGr.isHom_sum _ _ _ fun β hβ ↦ ?_
  have := act_shift W (hfin2 (c := c)) D ((grA0 W (hfin2 (c := c)) D).isHom_proj α a) X β _
    ((grEv W (hfin2 (c := c)) D X).isHom_proj β m)
  have h2 := MGr.coord_isHom _ this φ
  rwa [map_add, (Finset.mem_filter.1 hβ).2, (Finset.mem_filter.1 hα).2] at h2

/-! ### The ray weights of `𝒪P` and the reduction -/

variable (hv : R → M) (hv_mul : ∀ a b t, P.mul a b = some t → hv t = hv a + hv b)
  (hv_e : ∀ x, hv (P.e x) = 0)

/-- **`𝒪P` graded by a coordinate of the ray weights.** -/
abbrev galgOW (φ : M →+ ℤ) : GAlg (R := ZMod 4) (P.Lin (ZMod 4)) :=
  P.galgLin (fun a ↦ φ (hv a)) (fun a b t h ↦ by simp only [hv_mul a b t h, map_add]) (ZMod 4)
    (fun x ↦ by simp only [hv_e, map_zero])

variable (hΘ : ∀ a, (grA0 W (hfin2 (c := c)) D).IsHom (hv a) (T.Θ (P.b 𝔽₂ a)))

include hΘ in
theorem repr_Θ_symm_eq_zero_w (φ : M →+ ℤ) {n : ℤ} {a : (Alg D.F0)ᵐᵒᵖ}
    (ha : (galgW D W φ).gr.IsHom n a) (r : R) (hr : φ (hv r) ≠ n) :
    (P.basis 𝔽₂).repr (T.Θ.symm a) r = 0 := by
  have e : ((P.basis 𝔽₂).map T.Θ.toLinearEquiv).repr a r =
      (P.basis 𝔽₂).repr (T.Θ.symm a) r := by
    rw [Module.Basis.map_repr]; rfl
  rw [← e]
  exact zrepr_eq_zero (galgW D W φ).gr ((P.basis 𝔽₂).map T.Θ.toLinearEquiv) (fun r ↦ φ (hv r))
    (fun r ↦ by
      rw [Module.Basis.map_apply, RaySys.Mult.basis_apply]
      exact MGr.coord_isHom _ (hΘ r) φ) ha hr

include hΘ in
/-- **The reduction `𝒪P → A⁽²⁾` respects the coordinate weights.** -/
theorem isRedW (φ : M →+ ℤ) : IsRed (galgOW hv hv_mul hv_e φ) (galgW D W φ) (πO T) where
  smul := πO_smul T
  deg p x hx := by
    have e := (P.basis (ZMod 4)).sum_repr x
    rw [← e, map_sum]
    refine ZGr.isHom_sum _ _ _ fun r _ ↦ ?_
    rw [πO_smul, RaySys.Mult.basis_apply, πO_b]
    by_cases hr : φ (hv r) = p
    · rw [← hr]; exact ZGr.isHom_smul _ _ (MGr.coord_isHom _ (hΘ r) φ)
    · rw [P.repr_eq_zero_of_isHom (fun a ↦ φ (hv a)) (ZMod 4) hx hr, map_zero, zero_smul]
      exact ZGr.isHom_zero _ _
  lift p a ha := by
    refine ⟨liftO T a, ZGr.isHom_sum _ _ _ fun r _ ↦ ?_, πO_liftO T a⟩
    by_cases hr : φ (hv r) = p
    · rw [← hr]
      exact ZGr.isHom_smul _ _ (P.grLin_b (fun a ↦ φ (hv a)) (ZMod 4) r)
    · rw [repr_Θ_symm_eq_zero_w T W hv hΘ φ ha r hr, Z4.lift_zero, zero_smul]
      exact ZGr.isHom_zero _ _
  ker := πO_ker T
  ann := πO_ann T

/-! ### Commutation of the gradings -/

theorem galgW_zgr (φ : M →+ ℤ) (v p : ℤ) (a : (Alg D.F0)ᵐᵒᵖ)
    (ha : (galgA0 D (hfin2 (c := c))).gr.IsHom p a) :
    (galgA0 D (hfin2 (c := c))).gr.IsHom p ((galgW D W φ).gr.proj v a) :=
  MGr.coord_preserve _ (P := (galgA0 D (hfin2 (c := c))).gr.IsHom p)
    (fun _ _ ↦ ZGr.isHom_add _) (ZGr.isHom_zero _ _)
    (fun _ _ hx ↦ a0Proj_zgr W (hfin2 (c := c)) D hx) φ v ha

theorem gwEv_zgr (X : V) (φ : M →+ ℤ) (u p : ℤ) (m : Rep D.F0 (meshFam Q c X))
    (hm : (zgrEv D (hfin2 (c := c)) X).IsHom p m) :
    (zgrEv D (hfin2 (c := c)) X).IsHom p ((gwEv D W X φ).proj u m) :=
  MGr.coord_preserve _ (P := (zgrEv D (hfin2 (c := c)) X).IsHom p)
    (fun _ _ ↦ ZGr.isHom_add _) (ZGr.isHom_zero _ _)
    (fun _ _ hx ↦ evProj_zgr W (hfin2 (c := c)) D hx) φ u hm

theorem comm_ev (X : V) (p : ℤ) (g : M) (m : Rep D.F0 (meshFam Q c X)) :
    (zgrEv D (hfin2 (c := c)) X).proj p ((grEv W (hfin2 (c := c)) D X).proj g m) =
      (grEv W (hfin2 (c := c)) D X).proj g ((zgrEv D (hfin2 (c := c)) X).proj p m) := by
  change (if 0 ≤ p then repProj D p.toNat X else 0) (evProj W D g X m) =
    evProj W D g X ((if 0 ≤ p then repProj D p.toNat X else 0) m)
  split_ifs
  · funext y
    rw [repProj_apply, evProj_apply, evProj_apply, repProj_apply, wπ_degProj]
  · simp

/-- **A basis of `M_X` homogeneous for the degree and the mesh weight.** -/
theorem exists_homBasis_w (X : V) : ∃ (n : ℕ) (β : Module.Basis (Fin n) 𝔽₂
    (Rep D.F0 (meshFam Q c X))) (dβ : Fin n → ℤ) (wβ : Fin n → M),
    ∀ j, (zgrEv D (hfin2 (c := c)) X).IsHom (dβ j) (β j) ∧
      (grEv W (hfin2 (c := c)) D X).IsHom (wβ j) (β j) := by
  obtain ⟨n, β, w, hw⟩ := MGr.exists_homBasis (MGr.comb (zgrEv D (hfin2 (c := c)) X)
    (grEv W (hfin2 (c := c)) D X) (comm_ev W X))
  exact ⟨n, β, fun j ↦ (w j).1, fun j ↦ (w j).2, fun j ↦ MGr.comb_isHom _ _ _ (hw j)⟩

/-! ### The arrow maps shift the coordinate weights -/

theorem fA_shiftW {y x : V} (a : y ⟶ x) (φ : M →+ ℤ) (p : ℤ) (m : Rep D.F0 (meshFam Q c y))
    (hm : (gwEv D W y φ).IsHom p m) : (gwEv D W x φ).IsHom (p + φ (W.w a)) (fA D a m) := by
  rw [← coord_sum _ φ hm, map_sum]
  refine ZGr.isHom_sum _ _ _ fun β hβ ↦ ?_
  have := fA_shift W (hfin2 (c := c)) D a β _
    ((grEv W (hfin2 (c := c)) D y).isHom_proj β m)
  have h2 := MGr.coord_isHom _ this φ
  rwa [map_add, (Finset.mem_filter.1 hβ).2] at h2

/-! ### Weight-homogeneous lifts -/

variable {r : ℕ} (φ : Fin r → M →+ ℤ)

/-- **A lift of an evaluated module, homogeneous for the coordinate weights.** -/
structure ModLiftW (X : V) extends ModLift T X where
  wβ : Fin r → Fin n → ℤ
  hβw : ∀ i j, (gwEv D W X (φ i)).IsHom (wβ i j) (β j)
  act_w : ∀ i p q (m : Fin n → ZMod 4) (b : P.Lin (ZMod 4)), (grF (wβ i)).IsHom p m →
    (galgOW hv hv_mul hv_e (φ i)).gr.IsHom q b → (grF (wβ i)).IsHom (p + q) (MM.act m b)

include hΘ in
/-- **Proposition 10.1, the module lifts, weight-homogeneous**: for a mesh weight lifting the
ray weights, every evaluated module lifts with an action homogeneous for the degree and for
every coordinate of the weight. -/
theorem exists_modLiftW (J : InjData D) (h1 : DegOne D) (X : V) :
    Nonempty (ModLiftW T W hv hv_mul hv_e φ X) := by
  obtain ⟨n, β, dβ, wv, hβ⟩ := exists_homBasis_w (D := D) W X
  have hExt : ExtVanish (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) X) 1 0 :=
    extVanish_ev D (hfin2 (c := c)) J h1 1 X X 0 (Or.inr (by norm_num))
  obtain ⟨MM', hL, hgr, hw⟩ := exists_liftMod_weights (β := β) (dβ := dβ)
    (bΛ := P.basis (ZMod 4)) (hπ := isRed_πO T) (dΛ := T.d)
    (hbΛ := fun r ↦ by rw [RaySys.Mult.basis_apply]; exact P.grLin_b T.d (ZMod 4) r)
    (hβ := fun j ↦ (hβ j).1)
    (hπw := fun i ↦ isRedW T W hv hv_mul hv_e hΘ (φ i))
    (gw := fun i ↦ gwEv D W X (φ i))
    (hgw := fun i p q m b hm hb ↦ actW W (φ i) X p q m b hm hb)
    (wβ := fun i j ↦ φ i (wv j)) (hβw := fun i j ↦ MGr.coord_isHom _ (hβ j).2 (φ i))
    (wΛ := fun i r ↦ φ i (hv r))
    (hbΛw := fun i r ↦ by
      rw [RaySys.Mult.basis_apply]; exact P.grLin_b (fun a ↦ φ i (hv a)) (ZMod 4) r)
    (hΛc := fun i v p b hb ↦ galgW_zgr W (φ i) v p b hb)
    (hMc := fun i u p m hm ↦ gwEv_zgr W X (φ i) u p m hm)
    (hΛcw := fun i j v p b hb ↦ MGr.coord_coord _ (φ i) (φ j) v p hb)
    (hMcw := fun i j u p m hm ↦ MGr.coord_coord _ (φ i) (φ j) u p hm) hExt
  exact ⟨⟨⟨n, β, dβ, fun j ↦ (hβ j).1, MM', hL, hgr⟩, fun i j ↦ φ i (wv j),
    fun i j ↦ MGr.coord_isHom _ (hβ j).2 (φ i), hw⟩⟩

include hΘ in
/-- **Proposition 10.1, the arrow lifts, weight-homogeneous**: the arrow maps lift to maps of
degree one, homogeneous of the weight of the arrow for every coordinate. -/
theorem exists_arrowLiftW (J : InjData D) (h1 : DegOne D)
    (N : ∀ X, ModLiftW T W hv hv_mul hv_e φ X) {y x : V} (a : y ⟶ x) :
    ∃ f : (Fin (N y).n → ZMod 4) →ₗ[ZMod 4] (Fin (N x).n → ZMod 4),
      (∀ m b, f ((N y).MM.act m b) = (N x).MM.act (f m) b) ∧
      (∀ m, ρF (N x).β (f m) = fA D a (ρF (N y).β m)) ∧
      (∀ p m, (N y).MM.gr.IsHom p m → (N x).MM.gr.IsHom (p + 1) (f m)) ∧
      ∀ i p m, (grF ((N y).wβ i)).IsHom p m →
        (grF ((N x).wβ i)).IsHom (p + φ i (W.w a)) (f m) := by
  have hExt : ExtVanish (gmodEv D (hfin2 (c := c)) y) (gmodEv D (hfin2 (c := c)) x) 0 1 :=
    extVanish_ev D (hfin2 (c := c)) J h1 0 y x 1 (Or.inr (by norm_num))
  let gM : Fin r → ZGr (R := 𝔽₂) (Rep D.F0 (meshFam Q c y)) := fun i ↦ gwEv D W y (φ i)
  let gN : Fin r → ZGr (R := 𝔽₂) (Rep D.F0 (meshFam Q c x)) := fun i ↦ gwEv D W x (φ i)
  have hgM : ∀ i p q m b, (gM i).IsHom p m → (galgW D W (φ i)).gr.IsHom q b →
      (gM i).IsHom (p + q) ((gmodEv D (hfin2 (c := c)) y).act m b) :=
    fun i p q m b hm hb ↦ actW W (φ i) y p q m b hm hb
  have hgN : ∀ i p q m b, (gN i).IsHom p m → (galgW D W (φ i)).gr.IsHom q b →
      (gN i).IsHom (p + q) ((gmodEv D (hfin2 (c := c)) x).act m b) :=
    fun i p q m b hm hb ↦ actW W (φ i) x p q m b hm hb
  have HMw : ∀ i, IsLift (regrade (N y).MM (grF ((N y).wβ i)) ((N y).act_w i))
      (regrade (gmodEv D (hfin2 (c := c)) y) (gM i) (hgM i)) (πO T) (ρF (N y).β) := fun i ↦
    { smul := ρF_smul (N y).β
      act := (N y).lift.act
      deg := fun p m hm ↦ ρF_isHom (MM := regrade (gmodEv D (hfin2 (c := c)) y) (gM i) (hgM i))
        (N y).β ((N y).wβ i) ((N y).hβw i) hm
      lift := fun p m hm ↦ ⟨lv (N y).β m,
        lv_isHom (MM := regrade (gmodEv D (hfin2 (c := c)) y) (gM i) (hgM i))
          (N y).β ((N y).wβ i) ((N y).hβw i) hm, ρF_lv (N y).β m⟩
      ker := fun m h ↦ ker_ρF (N y).β h
      ann := fun m h ↦ ann_ρF (N y).β h }
  have HNw : ∀ i, IsLift (regrade (N x).MM (grF ((N x).wβ i)) ((N x).act_w i))
      (regrade (gmodEv D (hfin2 (c := c)) x) (gN i) (hgN i)) (πO T) (ρF (N x).β) := fun i ↦
    { smul := ρF_smul (N x).β
      act := (N x).lift.act
      deg := fun p m hm ↦ ρF_isHom (MM := regrade (gmodEv D (hfin2 (c := c)) x) (gN i) (hgN i))
        (N x).β ((N x).wβ i) ((N x).hβw i) hm
      lift := fun p m hm ↦ ⟨lv (N x).β m,
        lv_isHom (MM := regrade (gmodEv D (hfin2 (c := c)) x) (gN i) (hgN i))
          (N x).β ((N x).wβ i) ((N x).hβw i) hm, ρF_lv (N x).β m⟩
      ker := fun m h ↦ ker_ρF (N x).β h
      ann := fun m h ↦ ann_ρF (N x).β h }
  refine exists_liftHom_weights (isRed_πO T) (N y).lift (N x).lift
    (fun i ↦ isRedW T W hv hv_mul hv_e hΘ (φ i)) gM hgM gN hgN
    (fun i ↦ grF ((N y).wβ i)) (fun i ↦ (N y).act_w i) (fun i ↦ grF ((N x).wβ i))
    (fun i ↦ (N x).act_w i) HMw HNw
    (fun i u p m hm ↦ gwEv_zgr W y (φ i) u p m hm) (fun i u p m hm ↦ gwEv_zgr W x (φ i) u p m hm)
    (fun i j u p m hm ↦ MGr.coord_coord _ (φ i) (φ j) u p hm)
    (fun i j u p m hm ↦ MGr.coord_coord _ (φ i) (φ j) u p hm)
    (fA D a) (fA_act D a) (fun i ↦ φ i (W.w a)) hExt
    (linLift (N y).β (N x).β (fA D a)) (ρF_linLift _ _ _) (fun p m hm ↦ ?_) (fun i p m hm ↦ ?_)
  · rw [(N y).gr] at hm
    rw [(N x).gr]
    exact linLift_isHom (MM := gmodEv D (hfin2 (c := c)) y) (NN := gmodEv D (hfin2 (c := c)) x)
      (N y).β (N x).β (N y).dβ (N x).dβ (N y).hβ (N x).hβ (fA D a)
      (fun p m hm ↦ fA_deg D (hfin2 (c := c)) a hm) hm
  · exact linLift_isHom (MM := regrade (gmodEv D (hfin2 (c := c)) y) (gM i) (hgM i))
      (NN := regrade (gmodEv D (hfin2 (c := c)) x) (gN i) (hgN i))
      (N y).β (N x).β ((N y).wβ i) ((N x).wβ i) ((N y).hβw i) ((N x).hβw i) (fA D a)
      (fun p m hm ↦ fA_shiftW W a (φ i) p m hm) hm

end MeshWalk

end MultiplicativeBasisDeformations
