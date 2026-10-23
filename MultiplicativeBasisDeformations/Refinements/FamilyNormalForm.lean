module

public import MultiplicativeBasisDeformations.Refinements.FamilyArrows
public import MultiplicativeBasisDeformations.Refinements.FamilySpan
public import MultiplicativeBasisDeformations.Refinements.LiftedMeshData
public import MultiplicativeBasisDeformations.Refinements.LiftedCorner
public import MultiplicativeBasisDeformations.Refinements.LiftedRadical
public import MultiplicativeBasisDeformations.Foundations.PsiInjective

/-!
# Retained mesh coefficients at `t = 1` (Proposition 12.8, mesh presentations)

`deformation-refinements.tex`: "Lift the arrows using these bases. In each path degree
`q ≥ 3`, decompose their current mesh errors into the image of the original derivative and the
span of the retained `p_i` of that degree. The chosen splitting removes the image part by an arrow
correction of degree `q − 1`. […] these corrections do not change earlier coefficients, so the
procedure is triangular and finite. It produces polynomials `F_i(t)` in the mesh relations."

At the fibre `t = 1`: lifted arrows (`ArrowL`) are realized on paths (`pathR`); their realizations
have the expected order, leading term, weights in the cone and bottom part (`pathR_props`).
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
  (H : FamHyp D hfin μ qd)
  {Wt : Type} [AddCommGroup Wt] (W : MeshWt Q Wt) {χ : I → Wt} {coords : Wt →+ (I → ℤ)}
  (hχ : ∀ i, HasChar W hfin D (χ i) (μ i)) (J : D.InjData) (h1 : DegOne D)
  (hco : ∀ i, coords (χ i) = Pi.single i 1) [Infinite k]

/-! ### Weight and degree projections commute -/

variable (D hfin) in
theorem evProj_zproj (X : V) (γ : Wt) (d : ℤ) (v : Rep D.F0 (meshFam Q c X)) :
    (grEv W hfin D X).proj γ ((zgrEv D hfin X).proj d v) =
      (zgrEv D hfin X).proj d ((grEv W hfin D X).proj γ v) := by
  conv_rhs => rw [(zgrEv D hfin X).sum v, map_sum, map_sum]
  have hhom : ∀ e, (zgrEv D hfin X).IsHom e ((grEv W hfin D X).proj γ ((zgrEv D hfin X).proj e v)) :=
    fun e ↦ evProj_zgr W hfin D ((zgrEv D hfin X).isHom_proj e v)
  by_cases hd : d ∈ (zgrEv D hfin X).supp
  · rw [Finset.sum_eq_single d]
    · rw [(zgrEv D hfin X).proj_of_isHom (hhom d), if_pos rfl]
    · intro e _ he; rw [(zgrEv D hfin X).proj_of_isHom (hhom e), if_neg he]
    · intro h; exact absurd hd h
  · rw [(zgrEv D hfin X).proj_out d hd]
    simp

variable (D hfin) in
/-- **Weight parts commute with degree components.** -/
theorem pr_zcomp {y x : V} (δ : Wt) (r : ℤ)
    (u : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)) :
    MGr.pr (grEv W hfin D y) (grEv W hfin D x) δ (ZGr.comp (zgrEv D hfin y) (zgrEv D hfin x) r u) =
      ZGr.comp (zgrEv D hfin y) (zgrEv D hfin x) r (MGr.pr (grEv W hfin D y) (grEv W hfin D x) δ u) := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [MGr.pr, ZGr.comp, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  rw [evProj_zproj D hfin W x (β + δ) (p + r), ← evProj_zproj D hfin W y β p v]

/-! ### Lifted arrows and their realizations on paths -/

/-- Lifted arrows at `t = 1`: order `1`, leading term the arrow, relative weights in the cone,
bottom part the arrow. -/
structure ArrowL where
  g : ∀ {y x : V}, (y ⟶ x) → (FB (Ls1 H W hχ J h1 hco) y ⟶ FB (Ls1 H W hχ J h1 hco) x)
  ord : ∀ {y x : V} (a : y ⟶ x), OrderGe (gmodEv D hfin y) (gmodEv D hfin x) 1 (toLin (g a))
  lead : ∀ {y x : V} (a : y ⟶ x),
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr 1 (toLin (g a)) = rs D (arrowMor c a)
  cone : ∀ {y x : V} (a : y ⟶ x),
    ConeLin (C := cone χ) (G := grEv W hfin D y) (G' := grEv W hfin D x) (W.w a) (toLin (g a))
  bot : ∀ {y x : V} (a : y ⟶ x),
    clin ⊥ (grEv W hfin D y) (grEv W hfin D x) (W.w a) (toLin (g a)) = rs D (arrowMor c a)

variable {H W hχ J h1 hco}

theorem toLin_pathR_cons (A : ArrowL H W hχ J h1 hco) {x y z : V} (p : Quiver.Path x y)
    (a : y ⟶ z) : toLin (pathR A.g (p.cons a)) = toLin (A.g a) ∘ₗ toLin (pathR A.g p) := by
  rw [pathR_cons, toLin_comp]

/-- **The realization of a path**: order, leading term, cone and bottom part. -/
theorem pathR_props (A : ArrowL H W hχ J h1 hco) {y x : V} (p : Quiver.Path y x) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) p.length (toLin (pathR A.g p)) ∧
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr p.length (toLin (pathR A.g p)) =
      rs D (pathMor c p) ∧
    ConeLin (C := cone χ) (G := grEv W hfin D y) (G' := grEv W hfin D x) (W.pw p)
      (toLin (pathR A.g p)) ∧
    clin ⊥ (grEv W hfin D y) (grEv W hfin D x) (W.pw p) (toLin (pathR A.g p)) =
      rs D (pathMor c p) := by
  induction p with
  | nil =>
    simp only [pathR_nil, toLin_id, Quiver.Path.length_nil, Nat.cast_zero, MeshWt.pw]
    refine ⟨fun p m hm d hd ↦ ?_, ?_, ?_, ?_⟩
    · rw [LinearMap.id_apply, (gmodEv D hfin y).gr.proj_of_isHom hm, if_neg (by omega)]
    · rw [ZGr.comp_eq_self_of_hom _ _ (fun p m hm ↦ by simpa using hm), pathMor_nil, rs_id]
    · exact ConeLin.of_shift fun β m hm ↦ by simpa using hm
    · rw [clin_bot_of_shift (fun β m hm ↦ by simpa using hm), pathMor_nil, rs_id]
  | cons p a ih =>
    obtain ⟨h1', h2, h3, h4⟩ := ih
    have hpw : W.pw (p.cons a) = W.pw p + W.w a := by
      change W.pw (p.comp a.toPath) = _
      rw [W.pw_comp, W.pw_toPath]
    rw [toLin_pathR_cons, Quiver.Path.length_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := OrderGe.comp h1' (A.ord a)
      exact_mod_cast this
    · have := comp_comp_lead h1' (A.ord a)
      push_cast at this ⊢
      rw [this, h2, A.lead, rs_comp, pathMor_cons]
    · rw [hpw]; exact ConeLin.comp h3 (A.cone a)
    · rw [hpw, clin_bot_comp (cone_pointed hco) h3 (A.cone a), h4, A.bot, rs_comp, pathMor_cons]

/-! ### Orders and leading terms -/

section Orders

variable {y x : V}

theorem orderGe_succ_of_comp {r : ℤ} {u : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (hu : OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r u)
    (h0 : ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r u = 0) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) (r + 1) u := by
  intro p m hm d hd
  rcases lt_or_eq_of_le (show d ≤ p + r by omega) with h | rfl
  · exact hu p m hm d h
  · have := congrArg (fun v ↦ v m) h0
    simp only [LinearMap.zero_apply] at this
    rwa [ZGr.comp_hom _ _ _ hm] at this

theorem OrderGe.sub' {r : ℤ} {u v : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (hu : OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r u)
    (hv : OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r v) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r (u - v) := by
  intro p m hm d hd
  rw [LinearMap.sub_apply, map_sub, hu p m hm d hd, hv p m hm d hd, sub_zero]

theorem comp_eq_zero_of_orderGe {r s : ℤ}
    {u : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (hu : OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r u) (hs : s < r) :
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr s u = 0 :=
  (gmodEv D hfin y).gr.ext_of_hom fun p m hm ↦ by
    rw [ZGr.comp_hom _ _ _ hm, LinearMap.zero_apply]; exact hu p m hm _ (by omega)

theorem OrderGe.sum' {r : ℤ} {ι : Type*} (s : Finset ι)
    {u : ι → Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (hu : ∀ i ∈ s, OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r (u i)) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r (∑ i ∈ s, u i) := by
  intro p m hm d hd
  rw [LinearMap.coe_sum, Finset.sum_apply, map_sum]
  exact Finset.sum_eq_zero fun i hi ↦ hu i hi p m hm d hd

theorem comp_sum' {r : ℤ} {ι : Type*} (s : Finset ι)
    (u : ι → Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)) :
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r (∑ i ∈ s, u i) =
      ∑ i ∈ s, ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comp_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comp_add', ih]

end Orders

/-! ### Realizing homogeneous morphisms of `kQ` -/

variable (W) in
/-- The span of the paths of length `d` and weight `γ`. -/
def WPs (γ : Wt) (d : ℕ) (y x : V) : Submodule k (LinearPaths.obj (k := k) y ⟶ LinearPaths.obj x) :=
  Submodule.span k {F | ∃ p : Quiver.Path y x, p.length = d ∧ W.pw p = γ ∧ F = LinearPaths.path p}

theorem realize_props (A : ArrowL H W hχ J h1 hco) {y x : V} {γ : Wt} {d : ℕ}
    {F : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj x} (hF : F ∈ WPs W γ d y x) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) d (toLin (realizeR k A.g y x F)) ∧
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr d (toLin (realizeR k A.g y x F)) =
      rs D (img (c := c) F) ∧
    ConeLin (C := cone χ) (G := grEv W hfin D y) (G' := grEv W hfin D x) γ
      (toLin (realizeR k A.g y x F)) ∧
    clin ⊥ (grEv W hfin D y) (grEv W hfin D x) γ (toLin (realizeR k A.g y x F)) =
      rs D (img (c := c) F) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, hl, hw, rfl⟩ := hF
    rw [realizeR_path, img_path, ← hl, ← hw]
    exact pathR_props A p
  | zero =>
    simp only [map_zero, toLin_zero, img_zero]
    refine ⟨OrderGe.zero _, ?_, ConeLin.zero _, ?_⟩
    · rw [comp_zero', rs_zero]
    · rw [rs_zero]
      exact (grEv W hfin D y).ext_of_hom fun β m hm ↦ by
        rw [clin_bot_apply _ _ hm]; simp
  | add F G _ _ hF hG =>
    obtain ⟨a1, a2, a3, a4⟩ := hF
    obtain ⟨b1, b2, b3, b4⟩ := hG
    rw [map_add, toLin_add, img_add', rs_add]
    exact ⟨a1.add b1, by rw [comp_add', a2, b2], a3.add b3, by rw [clin_bot_add, a4, b4]⟩
  | smul t F _ hF =>
    obtain ⟨a1, a2, a3, a4⟩ := hF
    rw [map_smul, toLin_smul, img_smul', rs_smul]
    exact ⟨a1.smul t, by rw [comp_smul, a2], a3.smul t, by rw [clin_bot_smul, a4]⟩

theorem pathR_sub (A A' : ArrowL H W hχ J h1 hco) {m : ℕ} (hm : 1 ≤ m)
    (hAA : ∀ {y x : V} (a : y ⟶ x),
      OrderGe (gmodEv D hfin y) (gmodEv D hfin x) m (toLin (A'.g a - A.g a)))
    {y x : V} (p : Quiver.Path y x) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) ((p.length : ℤ) + m - 1)
      (toLin (pathR A'.g p - pathR A.g p)) := by
  induction p with
  | nil => simp only [pathR_nil, sub_self, toLin_zero]; exact OrderGe.zero _
  | cons p a ih =>
    have e : pathR A'.g (p.cons a) - pathR A.g (p.cons a) =
        (pathR A'.g p - pathR A.g p) ≫ A'.g a + pathR A.g p ≫ (A'.g a - A.g a) := by
      simp only [pathR_cons, Preadditive.sub_comp, Preadditive.comp_sub]; abel
    rw [e, toLin_add, toLin_comp, toLin_comp, Quiver.Path.length_cons]
    refine OrderGe.add ?_ ?_
    · have := OrderGe.comp ih (A'.ord a)
      refine this.mono ?_; push_cast; omega
    · have := OrderGe.comp (pathR_props A p).1 (hAA a)
      refine this.mono ?_; push_cast; omega

theorem realize_sub (A A' : ArrowL H W hχ J h1 hco) {m : ℕ} (hm : 1 ≤ m)
    (hAA : ∀ {y x : V} (a : y ⟶ x),
      OrderGe (gmodEv D hfin y) (gmodEv D hfin x) m (toLin (A'.g a - A.g a)))
    {y x : V} {γ : Wt} {d : ℕ} {F : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj x}
    (hF : F ∈ WPs W γ d y x) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) ((d : ℤ) + m - 1)
      (toLin (realizeR k A'.g y x F - realizeR k A.g y x F)) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, hl, -, rfl⟩ := hF
    rw [realizeR_path, realizeR_path, ← hl]
    exact pathR_sub A A' hm hAA p
  | zero => simp only [map_zero, sub_self, toLin_zero]; exact OrderGe.zero _
  | add F G _ _ hF hG =>
    rw [map_add, map_add, add_sub_add_comm, toLin_add]; exact hF.add hG
  | smul t F _ hF =>
    rw [map_smul, map_smul, ← smul_sub, toLin_smul]; exact hF.smul t

/-! ### The mesh errors relative to the retained rows -/

variable (Rw : I → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)

/-- The retained row `R_i`, as a family in `kQ`. -/
def rowQ (i : I) (x : Q.nonprojective) :
    LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj (k := k) x.1 :=
  Pi.single (M := fun x : Q.nonprojective ↦
    (LinearPaths.obj (k := k) (Q.tau x).1 ⟶ LinearPaths.obj (k := k) x.1))
    (Rw i).1 (LinearPaths.path (k := k) (V := V) (Rw i).2) x

/-- **The mesh error relative to the retained rows** `r_x − Σ_i λ_i R_i`, realized. -/
def errE (A : ArrowL H W hχ J h1 hco) (lam : I → k) (x : Q.nonprojective) :
    FB (Ls1 H W hχ J h1 hco) (Q.tau x).1 ⟶ FB (Ls1 H W hχ J h1 hco) x.1 :=
  realizeR k A.g _ _ (meshRelation c x) - ∑ i, lam i • realizeR k A.g _ _ (rowQ Rw i x)

variable {Rw}

omit [Infinite k] in
theorem meshRelation_mem (x : Q.nonprojective) :
    meshRelation c x ∈ WPs W (W.ν x) 2 (Q.tau x).1 x.1 := by
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨_, ?_, ?_, rfl⟩
  · simp [Quiver.Path.length_comp]
  · rw [W.pw_comp, W.pw_toPath, W.pw_toPath, W.mesh x a]

omit [Infinite k] in
theorem rowQ_mem (hlen : ∀ i, (Rw i).2.length = qd i + 2)
    (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i) (i : I) (x : Q.nonprojective) :
    rowQ (k := k) Rw i x ∈ WPs W (W.ν x + χ i) (qd i + 2) (Q.tau x).1 x.1 := by
  by_cases hx : x = (Rw i).1
  · subst hx
    simp only [rowQ, Pi.single_eq_same]
    exact Submodule.subset_span ⟨_, hlen i, hwt i, rfl⟩
  · simp only [rowQ, Pi.single_eq_of_ne hx]; exact zero_mem _

omit [Infinite k] in
theorem img_rowQ (i : I) (x : Q.nonprojective) :
    img (c := c) (rowQ (k := k) Rw i x) = row c (Rw i).1 (Rw i).2 x := by
  by_cases hx : x = (Rw i).1
  · subst hx; simp only [rowQ, row, Pi.single_eq_same, img_path]
  · simp only [rowQ, row, Pi.single_eq_of_ne hx, img_zero]

variable (hlen : ∀ i, (Rw i).2.length = qd i + 2) (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i)

include hlen hwt in
/-- The errors have relative weights in the cone, with no bottom part. -/
theorem errE_cone (A : ArrowL H W hχ J h1 hco) (lam : I → k) (x : Q.nonprojective) :
    ConeLin (C := cone χ) (G := grEv W hfin D (Q.tau x).1) (G' := grEv W hfin D x.1) (W.ν x)
      (toLin (errE Rw A lam x)) ∧
    clin ⊥ (grEv W hfin D (Q.tau x).1) (grEv W hfin D x.1) (W.ν x) (toLin (errE Rw A lam x)) = 0 := by
  have hm := realize_props A (meshRelation_mem (W := W) (c := c) x)
  have hr := fun i ↦ realize_props A (rowQ_mem (W := W) hlen hwt i x)
  have hχC : ∀ i, χ i ∈ cone χ := fun i ↦ AddSubmonoid.subset_closure ⟨i, rfl⟩
  simp only [errE, toLin_sub, toLin_sum, toLin_smul]
  refine ⟨hm.2.2.1.sub (ConeLin.sum _ fun i _ ↦ ((hr i).2.2.1.mono (hχC i)).smul _), ?_⟩
  rw [clin_bot_sub, clin_bot_sum, hm.2.2.2, img_meshRelation, rs_zero, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [clin_bot_smul, clin_bot_of_pos (cone_pointed hco) (hr i).2.2.1 (hχC i)
    (χ_ne_zero hco i), smul_zero]

/-! ### Weight decomposition of the leading terms -/

omit [Infinite k] in
theorem pr_eq_clin_bot {y x : V} (ρ : Wt) (f : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)) :
    MGr.pr (grEv W hfin D y) (grEv W hfin D x) ρ f = clin ⊥ (grEv W hfin D y) (grEv W hfin D x) ρ f :=
  (grEv W hfin D y).ext_of_hom fun β m hm ↦ by
    rw [MGr.pr_apply_hom _ _ hm, clin_bot_apply _ _ hm]

include hlen hwt in
/-- **The leading term of an error has weights in `ν x + (C ∖ 0)`.** -/
theorem lead_wπ_zero (A : ArrowL H W hχ J h1 hco) (lam : I → k) {r : ℕ} (x : Q.nonprojective)
    {ε : obj c (Q.tau x).1 ⟶ obj c x.1}
    (hε : ZGr.comp (gmodEv D hfin (Q.tau x).1).gr (gmodEv D hfin x.1).gr r
      (toLin (errE Rw A lam x)) = rs D ε) (γ : Wt) (hγ : ¬ (γ ∈ cone χ ∧ γ ≠ 0)) :
    wπ c W (W.ν x + γ) _ _ ε = 0 := by
  obtain ⟨hc, hb⟩ := errE_cone hlen hwt A lam x
  have hpr : MGr.pr (grEv W hfin D (Q.tau x).1) (grEv W hfin D x.1) (W.ν x + γ)
      (toLin (errE Rw A lam x)) = 0 := by
    by_cases h0 : γ = 0
    · rw [h0, add_zero, pr_eq_clin_bot, hb]
    · have hC : γ ∉ cone χ := fun h ↦ hγ ⟨h, h0⟩
      refine (grEv W hfin D (Q.tau x).1).ext_of_hom fun β m hm ↦ ?_
      rw [MGr.pr_apply_hom _ _ hm, LinearMap.zero_apply]
      exact hc β m hm _ (by rwa [show β + (W.ν x + γ) - (β + W.ν x) = γ by abel])
  apply rs_inj (D := D)
  rw [rs_zero, ← pr_rs W hfin D, ← hε]
  change MGr.pr (grEv W hfin D (Q.tau x).1) (grEv W hfin D x.1) (W.ν x + γ)
    (ZGr.comp (zgrEv D hfin (Q.tau x).1) (zgrEv D hfin x.1) r (toLin (errE Rw A lam x))) = 0
  rw [pr_zcomp D hfin W, hpr, comp_zero']

variable (W hfin) in
/-- The finite set of relative weights that can occur. -/
def relWts : Finset Wt :=
  Finset.univ.biUnion fun x : Q.nonprojective ↦ (wSupp W hfin).image (· - W.ν x)

omit [Infinite k] in
theorem eq_sum_relWts (x : Q.nonprojective) (f : obj c (Q.tau x).1 ⟶ obj c x.1) :
    f = ∑ γ ∈ relWts hfin W, wπ c W (W.ν x + γ) _ _ f := by
  conv_lhs => rw [eq_sum_wπ W hfin f]
  have hinj : Set.InjOn (· - W.ν x) (wSupp W hfin : Set Wt) := fun a _ b _ h ↦ by
    simpa using h
  have hsub : (wSupp W hfin).image (· - W.ν x) ⊆ relWts hfin W := fun γ hγ ↦
    Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, hγ⟩
  rw [← Finset.sum_subset hsub (fun γ _ hγ ↦ ?_), Finset.sum_image (fun a ha b hb h ↦ hinj ha hb h)]
  · exact Finset.sum_congr rfl fun g _ ↦ by rw [add_sub_cancel]
  · rw [wπ_out W hfin (fun h ↦ hγ (Finset.mem_image.2 ⟨_, h, by abel⟩)), LinearMap.zero_apply]

/-- The retained-row coefficients of a family realize the rows. -/
theorem realize_meshRelation (A : ArrowL H W hχ J h1 hco) (x : Q.nonprojective) :
    realizeR k A.g _ _ (meshRelation c x) = ∑ a : Σ y : V, y ⟶ x.1,
      ((c x a.1 a.2 : kˣ) : k) • (A.g (Q.mate x a.1 a.2) ≫ A.g a.2) := by
  simp only [meshRelation, map_sum, map_smul, realizeR_path, pathR_comp, pathR_toPath]

/-! ### The correction step -/

variable (hS : CokerSpan c (Set.range Rw))

include hlen hwt hS in
set_option maxHeartbeats 3200000 in
/-- **The correction step**: if the errors relative to the retained rows have order `m + 1`
(`m ≥ 2`), a correction of the lifted arrows in degree `m` with homogeneous components of
relative weights in `C ∖ 0`, and of the retained coefficients in degree `m + 1`, raises it to
`m + 2`. -/
theorem exists_correction (A : ArrowL H W hχ J h1 hco) (lam : I → k) {m : ℕ} (hm : 2 ≤ m)
    (hE : ∀ x, OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((m + 1 : ℕ) : ℤ)
      (toLin (errE Rw A lam x))) :
    ∃ (A' : ArrowL H W hχ J h1 hco) (lam' : I → k), ∀ x,
      OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((m + 2 : ℕ) : ℤ)
        (toLin (errE Rw A' lam' x)) := by
  classical
  -- leading terms and their weight decomposition
  choose ε hεd hε using fun x ↦
    exists_lead (Ls1 H W hχ J h1 hco) (vxIdem D hfin) (m + 1) (errE Rw A lam x) (hE x)
  set Tp := (relWts hfin W).filter (fun γ ↦ γ ∈ cone χ ∧ γ ≠ 0) with hTp
  have hεT : ∀ x, ε x = ∑ γ ∈ Tp, wπ c W (W.ν x + γ) _ _ (ε x) := by
    intro x
    conv_lhs => rw [eq_sum_relWts (hfin := hfin) (W := W) x (ε x)]
    rw [hTp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    split_ifs with h
    · rfl
    · exact lead_wπ_zero hlen hwt A lam x (hε x) γ h
  -- the decomposition of each weight part
  let gfam : Wt → MeshFamily c := fun γ x ↦ -wπ c W (W.ν x + γ) _ _ (ε x)
  have hg : ∀ γ x, gfam γ x ∈ degreePart c (m + 1) _ _ := fun γ x ↦
    neg_mem (wπ_mem_degreePart W _ (hεd x))
  have hgw : ∀ γ x, gfam γ x ∈ wP c W (W.ν x + γ) _ _ := fun γ x ↦ neg_mem (wπ_mem W _ _)
  choose f hf cc hcc hdec using fun γ ↦ exists_span_wt W hfin hS hwt hm γ (gfam γ) (hg γ) (hgw γ)
  -- the lifted corrections
  choose hl hlo hll hlc hlb using fun (γ : Wt) (a : Σ y x : V, y ⟶ x) ↦
    exists_liftHom H W hχ J h1 hco m (W.w a.2.2 + γ) (f γ a) (hf γ a).1 (hf γ a).2
  let hs : ∀ {y x : V}, (y ⟶ x) →
      (FB (Ls1 H W hχ J h1 hco) y ⟶ FB (Ls1 H W hχ J h1 hco) x) :=
    fun {y x} a ↦ ∑ γ ∈ Tp, hl γ ⟨y, x, a⟩
  let ftot : ArrowFamily c := fun a ↦ ∑ γ ∈ Tp, f γ a
  have hso : ∀ {y x : V} (a : y ⟶ x),
      OrderGe (gmodEv D hfin y) (gmodEv D hfin x) m (toLin (hs a)) := fun a ↦ by
    simp only [hs, toLin_sum]; exact OrderGe.sum' _ fun γ _ ↦ hlo γ ⟨_, _, a⟩
  have hsl : ∀ {y x : V} (a : y ⟶ x),
      ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr m (toLin (hs a)) = rs D (ftot ⟨y, x, a⟩) :=
    fun a ↦ by
      simp only [hs, ftot, toLin_sum, comp_sum', rs_sum]
      exact Finset.sum_congr rfl fun γ _ ↦ hll γ ⟨_, _, a⟩
  have hsc : ∀ {y x : V} (a : y ⟶ x), ConeLin (C := cone χ) (G := grEv W hfin D y)
      (G' := grEv W hfin D x) (W.w a) (toLin (hs a)) := fun a ↦ by
    simp only [hs, toLin_sum]
    exact ConeLin.sum _ fun γ hγ ↦ (hlc γ ⟨_, _, a⟩).mono (Finset.mem_filter.1 hγ).2.1
  have hsb : ∀ {y x : V} (a : y ⟶ x),
      clin ⊥ (grEv W hfin D y) (grEv W hfin D x) (W.w a) (toLin (hs a)) = 0 := fun a ↦ by
    simp only [hs, toLin_sum, clin_bot_sum]
    refine Finset.sum_eq_zero fun γ hγ ↦ ?_
    exact clin_bot_of_pos (cone_pointed hco) (hlc γ ⟨_, _, a⟩) (Finset.mem_filter.1 hγ).2.1
      (Finset.mem_filter.1 hγ).2.2
  -- the new lifted arrows
  let A' : ArrowL H W hχ J h1 hco :=
    { g := fun a ↦ A.g a + hs a
      ord := fun a ↦ by
        rw [toLin_add]; exact (A.ord a).add ((hso a).mono (by omega))
      lead := fun a ↦ by
        rw [toLin_add, comp_add', A.lead, comp_eq_zero_of_orderGe (hso a) (by omega), add_zero]
      cone := fun a ↦ by rw [toLin_add]; exact (A.cone a).add (hsc a)
      bot := fun a ↦ by rw [toLin_add, clin_bot_add, A.bot, hsb, add_zero] }
  have hAA : ∀ {y x : V} (a : y ⟶ x),
      OrderGe (gmodEv D hfin y) (gmodEv D hfin x) m (toLin (A'.g a - A.g a)) := fun a ↦ by
    change OrderGe _ _ _ (toLin (A.g a + hs a - A.g a))
    rw [add_sub_cancel_left]; exact hso a
  refine ⟨A', lam - ∑ γ ∈ Tp, cc γ, fun x ↦ ?_⟩
  set coef : I → k := fun i ↦ ∑ γ ∈ Tp, cc γ i with hcoef
  -- the decomposition of the new error
  have e1 : errE Rw A' (lam - ∑ γ ∈ Tp, cc γ) x = errE Rw A lam x +
      (realizeR k A'.g _ _ (meshRelation c x) - realizeR k A.g _ _ (meshRelation c x)) -
      ∑ i, lam i • (realizeR k A'.g _ _ (rowQ Rw i x) - realizeR k A.g _ _ (rowQ Rw i x)) +
      ∑ i, coef i • realizeR k A'.g _ _ (rowQ Rw i x) := by
    simp only [errE, hcoef, Pi.sub_apply, Finset.sum_apply, sub_smul, smul_sub,
      Finset.sum_sub_distrib]
    abel
  -- the mesh part
  have eM : realizeR k A'.g _ _ (meshRelation c x) - realizeR k A.g _ _ (meshRelation c x) =
      ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
        (hs (Q.mate x a.1 a.2) ≫ A.g a.2 + A.g (Q.mate x a.1 a.2) ≫ hs a.2 +
          hs (Q.mate x a.1 a.2) ≫ hs a.2) := by
    rw [realize_meshRelation, realize_meshRelation, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← smul_sub]
    congr 1
    change (A.g _ + hs _) ≫ (A.g _ + hs _) - _ = _
    simp only [Preadditive.add_comp, Preadditive.comp_add]
    abel
  have hM1 : OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((m + 1 : ℕ) : ℤ)
      (toLin (realizeR k A'.g _ _ (meshRelation c x) - realizeR k A.g _ _ (meshRelation c x))) := by
    have := realize_sub A A' (by omega) hAA (meshRelation_mem (W := W) (c := c) x)
    refine this.mono ?_; push_cast; omega
  have hM2 : ZGr.comp (gmodEv D hfin (Q.tau x).1).gr (gmodEv D hfin x.1).gr ((m + 1 : ℕ) : ℤ)
      (toLin (realizeR k A'.g _ _ (meshRelation c x) - realizeR k A.g _ _ (meshRelation c x))) =
      rs D (meshDerivative c ftot x) := by
    rw [eM, toLin_sum, comp_sum', meshDerivative, rs_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [toLin_smul, comp_smul, rs_smul]
    congr 1
    rw [toLin_add, toLin_add, toLin_comp, toLin_comp, toLin_comp, comp_add', comp_add', rs_add]
    have t1 := comp_comp_lead (hso (Q.mate x a.1 a.2)) (A.ord a.2)
    have t2 := comp_comp_lead (A.ord (Q.mate x a.1 a.2)) (hso a.2)
    have t3 := OrderGe.comp (hso (Q.mate x a.1 a.2)) (hso a.2)
    have e1' : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have e2' : ((m + 1 : ℕ) : ℤ) = 1 + (m : ℤ) := by push_cast; ring
    have z3 := comp_eq_zero_of_orderGe (s := ((m + 1 : ℕ) : ℤ)) t3 (by push_cast; omega)
    rw [z3, add_zero]
    conv_lhs => arg 1; rw [e1', t1]
    conv_lhs => arg 2; rw [e2', t2]
    rw [hsl, hsl, A.lead, A.lead, rs_comp, rs_comp]
  -- the retained rows: the old coefficients
  have hR1 : OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((m + 2 : ℕ) : ℤ)
      (toLin (∑ i, lam i • (realizeR k A'.g _ _ (rowQ Rw i x) -
        realizeR k A.g _ _ (rowQ Rw i x)))) := by
    rw [toLin_sum]
    refine OrderGe.sum' _ fun i _ ↦ ?_
    rw [toLin_smul]
    refine OrderGe.smul _ ?_
    have := realize_sub A A' (by omega) hAA (rowQ_mem (W := W) hlen hwt i x)
    have hq := H.q_pos i
    refine this.mono ?_; push_cast; omega
  -- the retained rows: the new coefficients
  have hcoef : ∀ i, coef i ≠ 0 → qd i + 2 = m + 1 := by
    intro i hi
    obtain ⟨γ, _, hγ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    rw [← hlen i]; exact (hcc γ i hγ).1
  have hN1 : OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((m + 1 : ℕ) : ℤ)
      (toLin (∑ i, coef i • realizeR k A'.g _ _ (rowQ Rw i x))) := by
    rw [toLin_sum]
    refine OrderGe.sum' _ fun i _ ↦ ?_
    rw [toLin_smul]
    by_cases hi : coef i = 0
    · rw [hi, zero_smul]; exact OrderGe.zero _
    · refine OrderGe.smul _ ?_
      have := (realize_props A' (rowQ_mem (W := W) hlen hwt i x)).1
      rwa [hcoef i hi] at this
  have hN2 : ZGr.comp (gmodEv D hfin (Q.tau x).1).gr (gmodEv D hfin x.1).gr ((m + 1 : ℕ) : ℤ)
      (toLin (∑ i, coef i • realizeR k A'.g _ _ (rowQ Rw i x))) =
      rs D (∑ i, coef i • row c (Rw i).1 (Rw i).2 x) := by
    rw [toLin_sum, comp_sum', rs_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [toLin_smul, comp_smul, rs_smul]
    by_cases hi : coef i = 0
    · rw [hi, zero_smul, zero_smul]
    · have := (realize_props A' (rowQ_mem (W := W) hlen hwt i x)).2.1
      rw [hcoef i hi, img_rowQ] at this
      rw [this]
  -- the leading terms cancel
  have hsum : ε x + meshDerivative c ftot x + ∑ i, coef i • row c (Rw i).1 (Rw i).2 x = 0 := by
    have hD : meshDerivative c ftot x = ∑ γ ∈ Tp, meshDerivative c (f γ) x := by
      have : ftot = ∑ γ ∈ Tp, f γ := funext fun a ↦ by simp only [ftot, Finset.sum_apply]
      rw [this, ← meshDerivativeₗ_apply, map_sum, Finset.sum_apply]
      rfl
    have hC : ∑ i, coef i • row c (Rw i).1 (Rw i).2 x =
        ∑ γ ∈ Tp, ∑ i, cc γ i • row c (Rw i).1 (Rw i).2 x := by
      simp only [coef, Finset.sum_smul]
      exact Finset.sum_comm
    have hG : ∀ γ, gfam γ x = meshDerivative c (f γ) x + ∑ i, cc γ i • row c (Rw i).1 (Rw i).2 x :=
      fun γ ↦ by
        have := congrFun (hdec γ) x
        simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply] using this
    rw [hD, hC, add_assoc, ← Finset.sum_add_distrib]
    simp only [← hG, gfam, Finset.sum_neg_distrib]
    rw [← hεT x, add_neg_cancel]
  -- conclusion
  have h1' : OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((m + 1 : ℕ) : ℤ)
      (toLin (errE Rw A' (lam - ∑ γ ∈ Tp, cc γ) x)) := by
    rw [e1, toLin_add, toLin_sub, toLin_add]
    exact (OrderGe.sub' ((hE x).add hM1) (hR1.mono (by push_cast; omega))).add hN1
  have h2' : ZGr.comp (gmodEv D hfin (Q.tau x).1).gr (gmodEv D hfin x.1).gr ((m + 1 : ℕ) : ℤ)
      (toLin (errE Rw A' (lam - ∑ γ ∈ Tp, cc γ) x)) = 0 := by
    rw [e1, toLin_add, toLin_sub, toLin_add, comp_add', comp_sub, comp_add', hε, hM2, hN2,
      comp_eq_zero_of_orderGe hR1 (by push_cast; omega), sub_zero, ← rs_add, ← rs_add, hsum,
      rs_zero]
  have := orderGe_succ_of_comp h1' h2'
  exact_mod_cast this

/-! ### The normal form at `t = 1` -/

variable (H W hχ J h1 hco) in
/-- The initial lifted arrows. -/
def arrowL0 : ArrowL H W hχ J h1 hco where
  g a := (exists_liftHom H W hχ J h1 hco 1 (W.w a) (arrowMor c a) (arrowMor_mem_degreePart a)
    (arrowMor_mem_wP W a)).choose
  ord a := by
    have := (exists_liftHom H W hχ J h1 hco 1 (W.w a) (arrowMor c a) (arrowMor_mem_degreePart a)
      (arrowMor_mem_wP W a)).choose_spec.1
    exact_mod_cast this
  lead a := (exists_liftHom H W hχ J h1 hco 1 (W.w a) (arrowMor c a) (arrowMor_mem_degreePart a)
    (arrowMor_mem_wP W a)).choose_spec.2.1
  cone a := (exists_liftHom H W hχ J h1 hco 1 (W.w a) (arrowMor c a) (arrowMor_mem_degreePart a)
    (arrowMor_mem_wP W a)).choose_spec.2.2.1
  bot a := (exists_liftHom H W hχ J h1 hco 1 (W.w a) (arrowMor c a) (arrowMor_mem_degreePart a)
    (arrowMor_mem_wP W a)).choose_spec.2.2.2

include hlen hwt hS in
/-- Successive corrections: errors of order `n + 3`. -/
theorem exists_errE_order (n : ℕ) :
    ∃ (A : ArrowL H W hχ J h1 hco) (lam : I → k), ∀ x,
      OrderGe (gmodEv D hfin (Q.tau x).1) (gmodEv D hfin x.1) ((n + 3 : ℕ) : ℤ)
        (toLin (errE Rw A lam x)) := by
  induction n with
  | zero =>
    refine ⟨arrowL0 H W hχ J h1 hco, 0, fun x ↦ ?_⟩
    have hp := realize_props (arrowL0 H W hχ J h1 hco) (meshRelation_mem (W := W) (c := c) x)
    simp only [errE, Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero]
    have := orderGe_succ_of_comp hp.1 (by rw [hp.2.1, img_meshRelation, rs_zero])
    exact_mod_cast this
  | succ n ih =>
    obtain ⟨A, lam, hA⟩ := ih
    obtain ⟨A', lam', hA'⟩ := exists_correction hlen hwt hS A lam (m := n + 2) (by omega) hA
    exact ⟨A', lam', hA'⟩

include hlen hwt hS in
/-- **The normal form at `t = 1`**: lifted arrows satisfying `r_x = Σ_i λ_i R_i` exactly in the
lifted category. -/
theorem exists_normalForm_one :
    ∃ (A : ArrowL H W hχ J h1 hco) (lam : I → k), ∀ x, errE Rw A lam x = 0 := by
  classical
  set N := Finset.univ.sup fun X : V ↦ degBound (gmodEv D hfin X).gr
  obtain ⟨A, lam, hA⟩ := exists_errE_order hlen hwt hS (2 * N)
  refine ⟨A, lam, fun x ↦ toLin_injective ?_⟩
  rw [toLin_zero]
  refine orderGe_eq_zero_of_large (hA x) ?_
  have h1' : degBound (gmodEv D hfin (Q.tau x).1).gr ≤ N :=
    Finset.le_sup (f := fun X : V ↦ degBound (gmodEv D hfin X).gr) (Finset.mem_univ _)
  have h2' : degBound (gmodEv D hfin x.1).gr ≤ N :=
    Finset.le_sup (f := fun X : V ↦ degBound (gmodEv D hfin X).gr) (Finset.mem_univ _)
  push_cast; omega

end MeshWalk

end MultiplicativeBasisDeformations
