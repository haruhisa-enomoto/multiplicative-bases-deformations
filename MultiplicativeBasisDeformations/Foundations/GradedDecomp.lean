module

public import MultiplicativeBasisDeformations.Foundations.ExtProjective

/-!
# Graded decomposition (Lemma 6.3(1))

`positive-deformations.tex`: "Every finite graded `A₀`-module is a sum of
shifts of the `M_i`. […] Decompose its underlying ungraded module into normalized
modules `M_i`. Write the projections and inclusions as `p_a` and `j_a`, so
`1_X = Σ_a p_a j_a`. Taking homogeneous degree-zero parts gives
`1_X = Σ_{a,r} (p_a)_r (j_a)_{-r}`."

Deviation in the proof: instead of the locality of `End_gr(X)` for a graded
indecomposable `X`, we split off one shifted `M_W` at a time from a graded
idempotent `e` (`exists_summand`). Some composite `(p_a)_r (j_b)_{-r}` of equal
level is nonzero, hence invertible by `eq:normalized-hom-degrees` (`exists_inv`);
otherwise the level sums `E_r` satisfy `E_r E_s = 0` for `r ≤ s` and force `e = 0`.
The result (`exists_gdecomp`) is a finite family of graded inclusions and
projections with `Σ inc_a pr_a = 1`, which is the input of `extVanish_of_decomp`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

include hfd in
/-- **A nonzero degree-zero map between evaluated modules is invertible.** -/
theorem exists_inv {Y Z : V} (u : Rep D.F0 (meshFam Q c Y) →ₗ[k] Rep D.F0 (meshFam Q c Z))
    (hu : ∀ m a, u (evAct D Y m a) = evAct D Z (u m) a)
    (hdeg : ∀ p m, (zgrEv D hfin Y).IsHom p m → (zgrEv D hfin Z).IsHom (p + 0) (u m))
    (hne : u ≠ 0) :
    ∃ v : Rep D.F0 (meshFam Q c Z) →ₗ[k] Rep D.F0 (meshFam Q c Y),
      (∀ m a, v (evAct D Z m a) = evAct D Y (v m) a) ∧
      (∀ p m, (zgrEv D hfin Z).IsHom p m → (zgrEv D hfin Y).IsHom (p + 0) (v m)) ∧
      u ∘ₗ v = LinearMap.id := by
  have hself := GExt.ZGr.comp_eq_self_of_hom (zgrEv D hfin Y) (zgrEv D hfin Z) hdeg
  by_cases hYZ : Y = Z
  · subst hYZ
    obtain ⟨t, ht⟩ := hom_comp_zero_self D hfin u hu
    rw [hself] at ht
    have ht0 : t ≠ 0 := by rintro rfl; exact hne (by rw [ht, zero_smul])
    refine ⟨t⁻¹ • LinearMap.id, fun m a ↦ ?_, fun p m hm ↦ ?_, ?_⟩
    · simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.smul_apply]
    · rw [add_zero]
      exact (zgrEv D hfin Y).isHom_smul _ hm
    · rw [ht, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, smul_smul,
        mul_inv_cancel₀ ht0, one_smul]
  · exact absurd (by rw [← hself]; exact hom_comp_zero_ne D hfin hYZ u hu) hne

variable {X : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  (XX : GExt.GMod (galgA0 D hfin) X)

/-- A graded `A₀`-linear endomorphism of degree zero. -/
structure IsGE (f : X →ₗ[k] X) : Prop where
  act : ∀ m a, f (XX.act m a) = XX.act (f m) a
  deg : ∀ p m, XX.gr.IsHom p m → XX.gr.IsHom (p + 0) (f m)

variable {D hfin XX}

theorem IsGE.deg' {f : X →ₗ[k] X} (hf : IsGE D hfin XX f) (p : ℤ) (m : X) (hm : XX.gr.IsHom p m) :
    XX.gr.IsHom p (f m) := by
  simpa using hf.deg p m hm

variable (D hfin XX)

include hfd in
/-- **One shifted `M_W` splits off a nonzero graded idempotent.** -/
theorem exists_summand (J : InjData D) {e : X →ₗ[k] X} (he : IsGE D hfin XX e)
    (hee : e ∘ₗ e = e) (hne : e ≠ 0) :
    ∃ (W : V) (r : ℤ) (α : Rep D.F0 (meshFam Q c W) →ₗ[k] X)
      (β : X →ₗ[k] Rep D.F0 (meshFam Q c W)),
      (∀ m a, α (evAct D W m a) = XX.act (α m) a) ∧ (∀ m a, β (XX.act m a) = evAct D W (β m) a) ∧
      (∀ p m, (zgrEv D hfin W).IsHom p m → XX.gr.IsHom (p + r) (α m)) ∧
      (∀ p m, XX.gr.IsHom p m → (zgrEv D hfin W).IsHom (p + -r) (β m)) ∧
      β ∘ₗ α = LinearMap.id ∧ e ∘ₗ α = α ∧ β ∘ₗ e = β ∧ ∃ m, α m ≠ 0 := by
  classical
  have : FiniteDimensional k (GExt.Left XX) := inferInstanceAs (FiniteDimensional k X)
  obtain ⟨μ, _, _, W, ⟨ψ⟩⟩ := J.essSurj (X := GExt.Left XX)
  let π : ∀ j, X →ₗ[k] Rep D.F0 (meshFam Q c (W j)) := fun j ↦
    (((LinearMap.proj j : D.EZ W →ₗ[Alg D.F0] _).comp ψ.toLinearMap).restrictScalars k :
      GExt.Left XX →ₗ[k] _)
  let ι : ∀ j, Rep D.F0 (meshFam Q c (W j)) →ₗ[k] X := fun j ↦
    ((ψ.symm.toLinearMap.comp
      (LinearMap.single (Alg D.F0) (fun j ↦ Rep D.F0 (meshFam Q c (W j))) j)).restrictScalars k :
      _ →ₗ[k] GExt.Left XX)
  have hπ : ∀ j m a, π j (XX.act m a) = evAct D (W j) (π j m) a := fun j m a ↦
    ((LinearMap.proj j : D.EZ W →ₗ[Alg D.F0] _).comp ψ.toLinearMap).map_smul a.unop m
  have hι : ∀ j m a, ι j (evAct D (W j) m a) = XX.act (ι j m) a := fun j m a ↦
    (ψ.symm.toLinearMap.comp
      (LinearMap.single (Alg D.F0) (fun j ↦ Rep D.F0 (meshFam Q c (W j))) j)).map_smul a.unop m
  have hsum : ∑ j, ι j ∘ₗ π j = LinearMap.id := by
    refine LinearMap.ext fun m ↦ ?_
    rw [LinearMap.sum_apply]
    change ∑ j, ψ.symm (Pi.single j (ψ m j)) = m
    rw [← map_sum, Finset.univ_sum_single]
    exact ψ.symm_apply_apply m
  let gX := XX.gr
  let gW := fun j ↦ zgrEv D hfin (W j)
  let Rs : Finset ℤ := Finset.univ.biUnion fun j ↦ GExt.ZGr.compDegs gX (gW j)
  let P : ∀ a : μ × ℤ, X →ₗ[k] Rep D.F0 (meshFam Q c (W a.1)) := fun a ↦
    GExt.ZGr.comp gX (gW a.1) a.2 (π a.1 ∘ₗ e)
  let I : ∀ a : μ × ℤ, Rep D.F0 (meshFam Q c (W a.1)) →ₗ[k] X := fun a ↦
    GExt.ZGr.comp (gW a.1) gX (-a.2) (e ∘ₗ ι a.1)
  let T : Finset (μ × ℤ) := Finset.univ ×ˢ Rs
  have heq : e = ∑ a ∈ T, I a ∘ₗ P a := by
    have h0 : e = GExt.ZGr.comp gX gX 0 e :=
      (GExt.ZGr.comp_eq_self_of_hom gX gX he.deg).symm
    have h1 : e = ∑ j, (e ∘ₗ ι j) ∘ₗ (π j ∘ₗ e) := by
      simp only [LinearMap.comp_assoc]
      rw [← GExt.lcomp_sum]
      simp only [← LinearMap.comp_assoc]
      rw [← GExt.lsum_comp, hsum, LinearMap.id_comp, hee]
    rw [h0]
    conv_lhs => rw [h1]
    rw [GExt.ZGr.comp_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [GExt.ZGr.comp_zero_comp gX (gW j)]
    refine Finset.sum_subset (Finset.subset_biUnion_of_mem
      (fun j ↦ GExt.ZGr.compDegs gX (gW j)) (Finset.mem_univ j)) fun r _ hr ↦ ?_
    change GExt.ZGr.comp (gW j) gX (-r) (e ∘ₗ ι j) ∘ₗ GExt.ZGr.comp gX (gW j) r (π j ∘ₗ e) = 0
    rw [GExt.ZGr.comp_out gX (gW j) hr, LinearMap.comp_zero]
  have hPe : ∀ a, P a ∘ₗ e = P a := fun a ↦ by
    change GExt.ZGr.comp gX (gW a.1) a.2 (π a.1 ∘ₗ e) ∘ₗ e = _
    rw [← GExt.ZGr.comp_comp_right gX (gW a.1) gX a.2 _ e (fun p m hm ↦ he.deg' p m hm),
      LinearMap.comp_assoc, hee]
  have heI : ∀ a, e ∘ₗ I a = I a := fun a ↦ by
    change e ∘ₗ GExt.ZGr.comp (gW a.1) gX (-a.2) (e ∘ₗ ι a.1) = _
    rw [← GExt.ZGr.comp_comp_left (gW a.1) gX gX (-a.2) _ e (fun p m hm ↦ he.deg' p m hm),
      ← LinearMap.comp_assoc, hee]
  have hPΛ : ∀ a m x, P a (XX.act m x) = evAct D (W a.1) (P a m) x := fun a m x ↦
    GExt.comp_act (XX := XX) (YY := gmodEv D hfin (W a.1)) a.2
      (u := π a.1 ∘ₗ e) (fun m x ↦ by
        rw [LinearMap.comp_apply, he.act, hπ]; rfl) m x
  have hIΛ : ∀ a m x, I a (evAct D (W a.1) m x) = XX.act (I a m) x := fun a m x ↦
    GExt.comp_act (XX := gmodEv D hfin (W a.1)) (YY := XX) (-a.2)
      (u := e ∘ₗ ι a.1) (fun m x ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        exact (congrArg e (hι a.1 m x)).trans (he.act _ _)) m x
  have hPdeg : ∀ a p m, gX.IsHom p m → (gW a.1).IsHom (p + a.2) (P a m) := fun a p m hm ↦
    GExt.ZGr.comp_isHom gX (gW a.1) _ hm
  have hIdeg : ∀ a p m, (gW a.1).IsHom p m → gX.IsHom (p + -a.2) (I a m) := fun a p m hm ↦
    GExt.ZGr.comp_isHom (gW a.1) gX _ hm
  have hPIΛ : ∀ a b m x, (P a ∘ₗ I b) (evAct D (W b.1) m x) =
      evAct D (W a.1) ((P a ∘ₗ I b) m) x := fun a b m x ↦ by
    rw [LinearMap.comp_apply, hIΛ, hPΛ]; rfl
  have hPIdeg : ∀ a b p m, (gW b.1).IsHom p m →
      (gW a.1).IsHom (p + (a.2 - b.2)) ((P a ∘ₗ I b) m) := fun a b p m hm ↦ by
    have := hPdeg a _ _ (hIdeg b p m hm)
    rwa [show p + -b.2 + a.2 = p + (a.2 - b.2) by ring] at this
  by_cases hex : ∃ a ∈ T, ∃ b ∈ T, a.2 = b.2 ∧ P a ∘ₗ I b ≠ 0
  · obtain ⟨a, -, b, -, hab, hne'⟩ := hex
    obtain ⟨v, hvΛ, hvdeg, huv⟩ := exists_inv D hfin (P a ∘ₗ I b) (hPIΛ a b)
      (fun p m hm ↦ by simpa [hab] using hPIdeg a b p m hm) hne'
    refine ⟨W a.1, -b.2, I b ∘ₗ v, P a, fun m x ↦ ?_, hPΛ a, fun p m hm ↦ ?_, fun p m hm ↦ ?_,
      ?_, ?_, hPe a, ?_⟩
    · rw [LinearMap.comp_apply, hvΛ, hIΛ]; rfl
    · have := hIdeg b _ _ (hvdeg p m hm)
      rwa [add_zero] at this
    · have := hPdeg a p m hm
      rwa [neg_neg, ← hab]
    · rw [← LinearMap.comp_assoc, huv]
    · rw [← LinearMap.comp_assoc, heI]
    · obtain ⟨m₀, hm₀⟩ : ∃ m₀, (P a ∘ₗ I b) m₀ ≠ 0 := by
        by_contra h
        push Not at h
        exact hne' (LinearMap.ext h)
      refine ⟨(P a ∘ₗ I b) m₀, fun h ↦ hm₀ ?_⟩
      have := LinearMap.congr_fun huv ((P a ∘ₗ I b) m₀)
      rw [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [← this]
      change P a ((I b ∘ₗ v) _) = 0
      rw [h, map_zero]
  · exfalso
    apply hne
    push Not at hex
    have hzero : ∀ a ∈ T, ∀ b ∈ T, a.2 ≤ b.2 → P a ∘ₗ I b = 0 := by
      intro a ha b hb hab
      rcases hab.lt_or_eq with hlt | heq'
      · rw [← GExt.ZGr.comp_eq_self_of_hom (gW b.1) (gW a.1) (hPIdeg a b)]
        exact hom_comp_neg D hfin _ (hPIΛ a b) (by omega)
      · exact hex a ha b hb heq'
    let E : ℤ → X →ₗ[k] X := fun r ↦ ∑ a ∈ T with a.2 = r, I a ∘ₗ P a
    have heE : e = ∑ r ∈ Rs, E r := by
      rw [heq]
      exact (Finset.sum_fiberwise_of_maps_to (g := Prod.snd)
        (fun a ha ↦ (Finset.mem_product.1 ha).2) _).symm
    have hEe : ∀ r, E r ∘ₗ e = E r := fun r ↦ by
      simp only [E, GExt.lsum_comp, LinearMap.comp_assoc, hPe]
    have hEE : ∀ r s, r ≤ s → E r ∘ₗ E s = 0 := fun r s hrs ↦ by
      simp only [E, GExt.lsum_comp, GExt.lcomp_sum]
      refine Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun b hb ↦ ?_
      rw [Finset.mem_filter] at ha hb
      rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (P a) (I a) (P b),
        hzero b hb.1 a ha.1 (by rw [hb.2, ha.2]; exact hrs), LinearMap.zero_comp,
        LinearMap.comp_zero]
    suffices h : ∀ S : Finset ℤ, e = ∑ r ∈ S, E r → e = 0 from h Rs heE
    intro S
    induction S using Finset.induction_on_min with
    | empty => intro h; rw [h, Finset.sum_empty]
    | insert a s hlt ih =>
      intro h
      have has : a ∉ s := fun h' ↦ lt_irrefl a (hlt a h')
      rw [Finset.sum_insert has] at h
      have hEa : E a = 0 := by
        rw [← hEe a, h, LinearMap.comp_add, hEE a a le_rfl, zero_add, GExt.lcomp_sum]
        exact Finset.sum_eq_zero fun x hx ↦ hEE a x (hlt x hx).le
      rw [hEa, zero_add] at h
      exact ih h

/-- **A graded decomposition** of a graded idempotent `e` into shifted evaluated
modules: `e = Σ_a inc_a pr_a` with `inc_a : M_{W a}⟨s_a⟩ → X` and
`pr_a : X → M_{W a}⟨s_a⟩` graded `A₀`-linear of degree zero. -/
structure GDecomp (e : X →ₗ[k] X) where
  μ : Type
  [fin : Fintype μ]
  W : μ → V
  s : μ → ℤ
  inc : ∀ a, Rep D.F0 (meshFam Q c (W a)) →ₗ[k] X
  pr : ∀ a, X →ₗ[k] Rep D.F0 (meshFam Q c (W a))
  inc_act : ∀ a m x, inc a (evAct D (W a) m x) = XX.act (inc a m) x
  pr_act : ∀ a m x, pr a (XX.act m x) = evAct D (W a) (pr a m) x
  inc_deg : ∀ a p m, (zgrEv D hfin (W a)).IsHom p m → XX.gr.IsHom (p + s a) (inc a m)
  pr_deg : ∀ a p m, XX.gr.IsHom p m → (zgrEv D hfin (W a)).IsHom (p + -s a) (pr a m)
  sum : ∑ a, inc a ∘ₗ pr a = e
  pr_inc : ∀ a, pr a ∘ₗ inc a = LinearMap.id

attribute [instance] GDecomp.fin

include hfd in
theorem exists_gdecomp_of_idem (J : InjData D) (e : X →ₗ[k] X) (he : IsGE D hfin XX e)
    (hee : e ∘ₗ e = e) : Nonempty (GDecomp D hfin XX e) := by
  classical
  induction hn : Module.finrank k (LinearMap.range e) using Nat.strong_induction_on
    generalizing e with
  | _ n ih =>
  by_cases hne : e = 0
  · subst hne
    exact ⟨{ μ := Empty
             W := Empty.elim
             s := Empty.elim
             inc := fun a ↦ a.elim
             pr := fun a ↦ a.elim
             inc_act := fun a ↦ a.elim
             pr_act := fun a ↦ a.elim
             inc_deg := fun a ↦ a.elim
             pr_deg := fun a ↦ a.elim
             sum := by simp
             pr_inc := fun a ↦ a.elim }⟩
  obtain ⟨W0, r, α, β, hαΛ, hβΛ, hαdeg, hβdeg, hβα, heα, hβe, m₀, hm₀⟩ :=
    exists_summand D hfin XX J he hee hne
  set e' := e - α ∘ₗ β with he'def
  have he' : IsGE D hfin XX e' := by
    refine ⟨fun m a ↦ ?_, fun p m hm ↦ ?_⟩
    · simp only [he'def, LinearMap.sub_apply, LinearMap.comp_apply, he.act, hβΛ, hαΛ, map_sub,
        LinearMap.sub_apply]
    · rw [add_zero]
      have h1 := he.deg' p m hm
      have h2 := hαdeg _ _ (hβdeg p m hm)
      rw [neg_add_cancel_right] at h2
      simp only [he'def, LinearMap.sub_apply, LinearMap.comp_apply]
      rw [sub_eq_add_neg]
      exact XX.gr.isHom_add h1 (XX.gr.isHom_neg h2)
  have h1 : e ∘ₗ (α ∘ₗ β) = α ∘ₗ β := by rw [← LinearMap.comp_assoc, heα]
  have h2 : (α ∘ₗ β) ∘ₗ e = α ∘ₗ β := by rw [LinearMap.comp_assoc, hβe]
  have h3 : (α ∘ₗ β) ∘ₗ (α ∘ₗ β) = α ∘ₗ β := by
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc β α β, hβα, LinearMap.id_comp]
  have hee' : e' ∘ₗ e' = e' := by
    simp only [he'def, LinearMap.comp_sub, LinearMap.sub_comp, hee, h1, h2, h3]
    abel
  have hee'' : e ∘ₗ e' = e' := by
    simp only [he'def, LinearMap.comp_sub, hee, h1]
  have hlt : Module.finrank k (LinearMap.range e') < n := by
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ fun h ↦ ?_)
    · rintro _ ⟨y, rfl⟩
      exact ⟨e' y, by rw [← LinearMap.comp_apply, hee'']⟩
    · have hmem : α m₀ ∈ LinearMap.range e := ⟨α m₀, by rw [← LinearMap.comp_apply, heα]⟩
      rw [← h] at hmem
      obtain ⟨y, hy⟩ := hmem
      apply hm₀
      have hb : β (α m₀) = 0 := by
        rw [← hy]
        simp only [he'def, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rw [← LinearMap.comp_apply β e, hβe, ← LinearMap.comp_apply β α, hβα, LinearMap.id_apply,
          sub_self]
      rw [← LinearMap.comp_apply, hβα, LinearMap.id_apply] at hb
      rw [hb, map_zero]
  obtain ⟨d⟩ := ih _ hlt e' he' hee' rfl
  refine ⟨{ μ := Option d.μ
            W := fun o ↦ (match o with | none => W0 | some a => d.W a)
            s := fun o ↦ (match o with | none => r | some a => d.s a)
            inc := fun o ↦ (match o with | none => α | some a => d.inc a)
            pr := fun o ↦ (match o with | none => β | some a => d.pr a)
            inc_act := fun o ↦ (match o with | none => hαΛ | some a => d.inc_act a)
            pr_act := fun o ↦ (match o with | none => hβΛ | some a => d.pr_act a)
            inc_deg := fun o ↦ (match o with | none => hαdeg | some a => d.inc_deg a)
            pr_deg := fun o ↦ (match o with | none => hβdeg | some a => d.pr_deg a)
            sum := ?_
            pr_inc := fun o ↦ (match o with | none => hβα | some a => d.pr_inc a) }⟩
  rw [Fintype.sum_option]
  change α ∘ₗ β + ∑ a, d.inc a ∘ₗ d.pr a = e
  rw [d.sum, he'def, add_sub_cancel]

include hfd in
/-- **Lemma 6.3(1)**: every finite graded `A₀`-module is a finite sum of shifts of
evaluated modules. -/
theorem exists_gdecomp (J : InjData D) : Nonempty (GDecomp D hfin XX LinearMap.id) :=
  exists_gdecomp_of_idem D hfin XX J LinearMap.id
    ⟨fun _ _ ↦ rfl, fun p m hm ↦ by simpa using hm⟩ (LinearMap.id_comp _)

end MeshWalk

end MultiplicativeBasisDeformations
