import MultiplicativeBasisDeformations.Refinements.FamilyTwist
import MultiplicativeBasisDeformations.Refinements.FlatPerturbationDim
import MultiplicativeBasisDeformations.Refinements.MeshNormalForm

/-!
# The mesh presentation of every fibre (Proposition 12.8, presentations)

`deformation-refinements.tex`: "Let `ℬ` be that mesh presentation with a path cutoff
above the top degree of `C`. Its arrow map to `ℳ` is surjective by degree induction. Leading
relations give surjections `C ⊗ K → gr ℬ → gr ℳ = C ⊗ K` whose composite fixes every arrow and
object, hence is the identity. Both maps are isomorphisms."

At each fibre `t`, the twisted lifted arrows realize `kQ` onto the morphisms of the lifted modules
(`realize_tw_surjective`, by degree induction on leading terms).
-/

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

/-! ### Twisting, orders and leading terms -/

theorem twl_orderGe {y x : V} (t : I → k) (ρ : Wt) {r : ℤ}
    {u : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (hu : OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r u) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r
      (twl coords (grEv W hfin D y) (grEv W hfin D x) t ρ u) := by
  intro p m hm d hd
  simp only [twl, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_sum, map_smul]
  refine Finset.sum_eq_zero fun β _ ↦ Finset.sum_eq_zero fun δ _ ↦ ?_
  change _ • (zgrEv D hfin x).proj d ((grEv W hfin D x).proj δ (u ((grEv W hfin D y).proj β m))) = 0
  rw [← evProj_zproj D hfin W, show (zgrEv D hfin x).proj d (u ((grEv W hfin D y).proj β m)) = 0
    from hu p _ (evProj_zgr W hfin D hm) d hd, map_zero, smul_zero]

theorem comp_twl {y x : V} (t : I → k) (ρ : Wt) (r : ℤ)
    (u : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)) :
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r
        (twl coords (grEv W hfin D y) (grEv W hfin D x) t ρ u) =
      twl coords (grEv W hfin D y) (grEv W hfin D x) t ρ
        (ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r u) := by
  simp only [twl, comp_sum', comp_smul]
  refine Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun δ _ ↦ ?_
  congr 1
  have e1 := ZGr.comp_comp_left (zgrEv D hfin y) (zgrEv D hfin x) (zgrEv D hfin x) r
    (u ∘ₗ (grEv W hfin D y).proj β) ((grEv W hfin D x).proj δ)
    (fun p m hm ↦ evProj_zgr W hfin D hm)
  have e2 := ZGr.comp_comp_right (zgrEv D hfin y) (zgrEv D hfin x) (zgrEv D hfin y) r u
    ((grEv W hfin D y).proj β) (fun p m hm ↦ evProj_zgr W hfin D hm)
  exact e1.trans (by rw [e2]; rfl)

omit [Fintype Q.nonprojective] [Infinite k] in
theorem twl_of_shift {y x : V} (t : I → k) {ρ : Wt}
    {f : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (hf : Shift (grEv W hfin D y) (grEv W hfin D x) ρ f) :
    twl coords (grEv W hfin D y) (grEv W hfin D x) t ρ f = f :=
  (grEv W hfin D y).ext_of_hom fun β v hv ↦ by
    rw [twl_hom _ _ _ _ _ hv, sum_smul_proj_hom _ _ (hf β v hv),
      show β + ρ - β - ρ = (0 : Wt) by abel, ch_zero', one_smul]

/-- **Twisted paths**: order and leading term. -/
theorem pathR_tw_props (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V}
    (p : Quiver.Path y x) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) p.length (toLin (pathR (twArrow A t) p)) ∧
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr p.length
      (toLin (pathR (twArrow A t) p)) = rs D (pathMor c p) := by
  obtain ⟨h1', h2, -, -⟩ := pathR_props A p
  rw [toLin_pathR_tw]
  exact ⟨twl_orderGe t _ h1', by rw [comp_twl, h2, twl_of_shift t (rs_shift W hfin D
    (pathMor_mem_wP W p))]⟩

/-- **Twisted realizations of homogeneous morphisms of `kQ`**: order and leading term. -/
theorem realize_tw_props (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V} {r : ℕ}
    {F : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj x}
    (hF : F ∈ LinearPaths.degreePart (k := k) r y x) :
    OrderGe (gmodEv D hfin y) (gmodEv D hfin x) r (toLin (realizeR k (twArrow A t) y x F)) ∧
    ZGr.comp (gmodEv D hfin y).gr (gmodEv D hfin x).gr r
      (toLin (realizeR k (twArrow A t) y x F)) = rs D (img (c := c) F) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, hl, rfl⟩ := hF
    rw [realizeR_path, img_path, ← hl]
    exact pathR_tw_props A t p
  | zero =>
    simp only [map_zero, toLin_zero, img_zero, rs_zero]
    exact ⟨OrderGe.zero _, comp_zero' _⟩
  | add F G _ _ hF hG =>
    rw [map_add, toLin_add, img_add', rs_add]
    exact ⟨hF.1.add hG.1, by rw [comp_add', hF.2, hG.2]⟩
  | smul s F _ hF =>
    rw [map_smul, toLin_smul, img_smul', rs_smul]
    exact ⟨hF.1.smul s, by rw [comp_smul, hF.2]⟩

/-! ### Surjectivity -/

/-- **The twisted arrows generate**: every morphism of the lifted modules of the fibre `t` is
realized by a morphism of `kQ`. -/
theorem realize_tw_surjective (A : ArrowL H W hχ J h1 hco) (t : I → k) {y x : V}
    (f : FB (famLifts H W hχ J h1 hco t) y ⟶ FB (famLifts H W hχ J h1 hco t) x) :
    ∃ F, realizeR k (twArrow A t) y x F = f := by
  set B := degBound (gmodEv D hfin y).gr + degBound (gmodEv D hfin x).gr + 1
  have step : ∀ n : ℕ, ∀ f : FB (famLifts H W hχ J h1 hco t) y ⟶ FB (famLifts H W hχ J h1 hco t) x,
      OrderGe (gmodEv D hfin y) (gmodEv D hfin x) ((B - n : ℕ) : ℤ) (toLin f) →
        ∃ F, realizeR k (twArrow A t) y x F = f := by
    intro n
    induction n with
    | zero =>
      intro f hf
      refine ⟨0, toLin_injective ?_⟩
      rw [map_zero, toLin_zero]
      exact (orderGe_eq_zero_of_large hf (by simp [B])).symm
    | succ n ih =>
      intro f hf
      rcases Nat.lt_or_ge n B with hn | hn
      · set r := B - (n + 1)
        obtain ⟨φ, hφ, hlead⟩ := exists_lead (famLifts H W hχ J h1 hco t) (vxIdem D hfin) r f hf
        obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.1 hφ
        have hp := realize_tw_props A t hF
        have hdiff : OrderGe (gmodEv D hfin y) (gmodEv D hfin x) ((B - n : ℕ) : ℤ)
            (toLin (f - realizeR k (twArrow A t) y x F)) := by
          have := orderGe_succ_of_comp (OrderGe.sub' hf hp.1) (by
            rw [comp_sub, hlead, hp.2, sub_eq_zero]; rfl)
          rwa [show ((r : ℕ) : ℤ) + 1 = ((B - n : ℕ) : ℤ) by simp only [r]; omega] at this
        obtain ⟨F', hF'⟩ := ih _ hdiff
        exact ⟨F + F', by rw [map_add, hF', add_sub_cancel]⟩
      · exact ih f (by
          rw [show B - (n + 1) = B - n by omega] at hf; exact hf)
  exact step B f (by simpa using order0 (Ls := famLifts H W hχ J h1 hco t) (vxIdem D hfin) f)

/-! ### The kernel: the perturbed mesh ideal -/

open FlatPert

variable {Rw : I → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1}
  (hlen : ∀ i, (Rw i).2.length = qd i + 2) (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i)

variable (Rw) in
/-- **The retained perturbation at the fibre `t`**: `f_x = Σ_i λ_i t_i R_i`. -/
def ftp (lam t : I → k) : ∀ x (tt : (meshPres c).T x), Hm k ((meshPres c).src x tt) x :=
  fun x tt ↦ ∑ i, (lam i * t i) • rowQ (k := k) Rw i ⟨x, tt.2⟩

omit [Infinite k] in
include H hlen hwt in
theorem ftp_mem (lam t : I → k) :
    ∀ x tt, ftp (c := c) Rw lam t x tt ∈ geSpan k ((meshPres c).deg x tt + 1) _ x := by
  intro x tt
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
  have h := rowQ_mem (W := W) (k := k) hlen hwt i ⟨x, tt.2⟩
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨p, hl, -, rfl⟩
  exact Submodule.subset_span ⟨p, by
    change 2 + 1 ≤ p.length; have := H.q_pos i; omega, rfl⟩

omit [Fintype Q.nonprojective] [Infinite k] in
/-- The kernel of `kQ → C` is the mesh ideal. -/
theorem ker_img (y x : V) :
    LinearMap.ker ((RelationCategory.functor k (meshRelations c)).mapLinearMap k
      (X := LinearPaths.obj y) (Y := LinearPaths.obj x)) = ctxSpan (meshPres c) (meshPres c).r y x := by
  ext F
  rw [LinearMap.mem_ker]
  change (RelationCategory.functor k (meshRelations c)).map F = 0 ↔ _
  rw [RelationCategory.functor_map_eq_zero_iff, ctxSpan_meshPres]
  rfl

omit [Fintype Q.nonprojective] [Infinite k] in
theorem finrank_idealC (y x : V) :
    Module.finrank k (FlatPert.Q (idealC (meshPres c)) y x) = Module.finrank k (obj c y ⟶ obj c x) := by
  have hs : Function.Surjective ((RelationCategory.functor k (meshRelations c)).mapLinearMap k
      (X := LinearPaths.obj (k := k) y) (Y := LinearPaths.obj x)) := fun g ↦
    RelationCategory.functor_map_surjective (meshRelations c) g
  have e := (LinearMap.quotKerEquivOfSurjective _ hs)
  rw [ker_img] at e
  exact e.finrank_eq

include hlen hwt in
/-- **The presentation of each fibre**: the realization by the twisted arrows has kernel exactly
`(𝔪^{N+1}, r_x − Σ_i λ_i t_i R_i)` (`N` beyond the degrees). -/
theorem realize_tw_ker (A : ArrowL H W hχ J h1 hco) (lam : I → k) (hA : ∀ x, errE Rw A lam x = 0)
    (t : I → k) (N : ℕ) (hN1 : Nb hfin ≤ N)
    (hN2 : ∀ X Y : V, degBound (gmodEv D hfin X).gr + degBound (gmodEv D hfin Y).gr < N + 1)
    {y x : V} (F : Hm k y x) :
    realizeR k (twArrow A t) y x F = 0 ↔
      F ∈ (idealB (meshPres c) (ftp Rw lam t) (ftp_mem (H := H) hlen hwt lam t) N).I y x := by
  classical
  let _ : ∀ a b : V, Fintype (a ⟶ b) := fun a b ↦ Fintype.ofInjective
    (fun f : a ⟶ b ↦ (⟨a, f⟩ : Σ z : V, z ⟶ b)) (fun f g h ↦ eq_of_heq (Sigma.mk.inj_iff.1 h).2)
  set IB := idealB (meshPres c) (ftp Rw lam t) (ftp_mem (H := H) hlen hwt lam t) N
  -- the ideal is in the kernel
  have hle : ∀ a b, IB.I a b ≤ LinearMap.ker (realizeR k (twArrow A t) a b) := by
    intro a b
    refine sup_le ?_ ?_
    · rw [ctxSpan, Submodule.span_le]
      rintro _ ⟨z, tt, u, v, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, realizeR_comp, realizeR_comp]
      have hrel := tw_relation hlen hwt A lam hA t ⟨z, tt.2⟩
      have : realizeR k (twArrow A t) _ _ (rf (meshPres c) (ftp Rw lam t) z tt) = 0 := by
        rw [rf, map_sub, sub_eq_zero]
        change realizeR k (twArrow A t) _ _ (meshRelation c ⟨z, tt.2⟩) = _
        rw [hrel, ftp, map_sum]
        simp only [map_smul]
      rw [this, Limits.zero_comp, Limits.comp_zero]
    · rw [geSpan, Submodule.span_le]
      rintro _ ⟨p, hp, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, realizeR_path]
      apply toLin_injective
      rw [toLin_zero]
      exact orderGe_eq_zero_of_large (pathR_tw_props A t p).1 (by have := hN2 a b; omega)
  refine ⟨fun hF ↦ ?_, fun hF ↦ hle y x hF⟩
  -- dimensions
  have hN : ∀ w z (p : Quiver.Path w z), N ≤ p.length → LinearPaths.path (k := k) p ∈ ctxSpan (meshPres c)
      (meshPres c).r w z := by
    intro w z p hp
    rw [← ker_img, LinearMap.mem_ker]
    have := pathMor_mem_degreePart c p
    rw [Nb_spec hfin _ _ _ (by omega), Submodule.mem_bot] at this
    exact this
  haveI := finiteDimensional_Q IB (geSpan_le_B (meshPres c) (ftp Rw lam t) (ftp_mem (H := H) hlen hwt lam t) N) y x
  let φ := (IB.I y x).liftQ (realizeR k (twArrow A t) y x) (hle y x)
  have hφs : Function.Surjective φ := by
    intro f
    obtain ⟨G, hG⟩ := realize_tw_surjective A t f
    exact ⟨Submodule.Quotient.mk G, hG⟩
  have hdim : Module.finrank k (FlatPert.Q IB y x) =
      Module.finrank k (FB (famLifts H W hχ J h1 hco t) y ⟶ FB (famLifts H W hχ J h1 hco t) x) := by
    refine le_antisymm ?_ (LinearMap.finrank_le_finrank_of_surjective hφs)
    rw [finrank_FB (famLifts H W hχ J h1 hco t) J h1 (vxIdem D hfin) y x, ← finrank_idealC]
    exact finrank_B_le (meshPres c) (ftp Rw lam t) (ftp_mem (H := H) hlen hwt lam t) N hN y x
  have hφi : Function.Injective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hφs
  have : φ (Submodule.Quotient.mk F) = 0 := hF
  have h0 := hφi (this.trans (map_zero φ).symm)
  exact (Submodule.Quotient.mk_eq_zero _).1 h0

end MeshWalk

end MultiplicativeBasisDeformations
