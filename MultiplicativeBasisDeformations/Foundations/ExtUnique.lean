module

public import MultiplicativeBasisDeformations.Foundations.ExtExtensions
public import MultiplicativeBasisDeformations.Foundations.ExtHigher

/-!
# Uniqueness of the graded `Ext` of Lemma 6.3

The formalization works with `Ext^{n+1}(M, N)_t = 0` in the bar form (`GExt.ExtVanish`); its
agreement with the manuscript's `Ext` (from graded projective resolutions) is
`GRes.extVanish_iff` in `ExtResolutions.lean`. This file shows in addition that the definition is
forced: any notion of graded `Ext`
vanishing with the standard properties gives the same answer for all the groups
`Ext^{n+1}_{A₀}(M_i, M_j)_t` of Lemma 6.3 (`extVanish_unique`). The properties are:
* `Ext¹(M, N)_t = 0` exactly when every graded extension `0 → N⟨−t⟩ → E → M → 0` splits;
* higher `Ext` of a projective `M_p` vanishes;
* dimension shifting along the graded projective cover `0 → K_i → P_i → M_i → 0`:
  `Ext^{n+2}(M_i, N)_t = 0 ↔ Ext^{n+1}(K_i, N)_t = 0`;
* additivity over a graded decomposition of `K_i` into shifted `M_j`.
The bar `Ext` has them all: extensions (`extVanish_zero_iff`), projectives (`extVanish_proj`),
dimension shifting in both directions (`extVanish_shift`, `extVanish_unshift`), additivity in
both directions (`extVanish_of_decomp`, `extVanish_of_retract`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {MM : GMod GΛ M} {NN : GMod GΛ N}

/-- **Dimension shifting, converse**: along an `R`-split exact sequence `0 → K → P → M → 0` of
graded modules with `Ext^{n+1}(P, N)_t = 0`, `Ext^{n+2}(M, N)_t = 0` gives
`Ext^{n+1}(K, N)_t = 0`. -/
theorem extVanish_unshift {K P : Type*} [AddCommGroup K] [Module R K] [AddCommGroup P] [Module R P]
    {KK : GMod GΛ K} {PP : GMod GΛ P} (ι : K →ₗ[R] P) (π : P →ₗ[R] M) (s : M →ₗ[R] P)
    (ρ : P →ₗ[R] K) (hι : ∀ m a, ι (KK.act m a) = PP.act (ι m) a)
    (hπ : ∀ m a, π (PP.act m a) = MM.act (π m) a)
    (hι_deg : ∀ p m, KK.gr.IsHom p m → PP.gr.IsHom (p + 0) (ι m))
    (hπ_deg : ∀ p m, PP.gr.IsHom p m → MM.gr.IsHom (p + 0) (π m))
    (hs_deg : ∀ p m, MM.gr.IsHom p m → PP.gr.IsHom (p + 0) (s m))
    (hρ_deg : ∀ p m, PP.gr.IsHom p m → KK.gr.IsHom (p + 0) (ρ m))
    (hπs : π ∘ₗ s = LinearMap.id) (hρι : ρ ∘ₗ ι = LinearMap.id)
    (hsplit : ι ∘ₗ ρ + s ∘ₗ π = LinearMap.id) (hπι : π ∘ₗ ι = 0) {n : ℕ} {t : ℤ}
    (hP : ExtVanish PP NN n t) (hM : ExtVanish MM NN (n + 1) t) :
    ExtVanish KK NN n t := by
  intro z hz hdz
  -- extend `z` to `P` along `ρ`
  set w := pull ρ z
  have hw : Good PP NN (n + 1) t w := by
    have := hz.pull hρ_deg; rwa [add_zero] at this
  have hdw := hw.d
  -- `d w` vanishes on `K`, so it comes from a cocycle on `M`
  have hιdw : pull ι (Bar.d (homAct PP NN) (n + 1) w) = 0 := by
    rw [← d_pull hι, pull_comp, hρι, pull_id, hdz]
  set y := pull s (Bar.d (homAct PP NN) (n + 1) w)
  have hy : Good MM NN (n + 2) t y := by
    have := hdw.pull hs_deg; rwa [add_zero] at this
  have hπy : pull π y = Bar.d (homAct PP NN) (n + 1) w := by
    have hsπ : s ∘ₗ π = LinearMap.id - ι ∘ₗ ρ := by rw [← hsplit]; abel
    rw [pull_comp, hsπ, pull_map_sub, pull_id, ← pull_comp, hιdw, pull_zero, sub_zero]
  have hpinj : ∀ G : Bar.Cochain Λ (M →ₗ[R] N), pull π G = 0 → G = 0 := by
    intro G hG
    have : pull s (pull π G) = G := by rw [pull_comp, hπs, pull_id]
    rw [← this, hG, pull_zero]
  have hdy : Bar.d (homAct MM NN) (n + 2) y = 0 := by
    apply hpinj
    rw [← d_pull hπ, hπy, Bar.d_d]
  obtain ⟨x, hx, hdx⟩ := hM y hy hdy
  -- `w − π^*x` is a cocycle on `P`
  set w' := w - pull π x
  have hx' := hx.pull hπ_deg
  rw [add_zero] at hx'
  have hw' : Good PP NN (n + 1) t w' := by
    have h := hw.add' (hx'.zsmul' (-1))
    have he : w' = w + (-1 : ℤ) • pull π x := by simp [w', sub_eq_add_neg]
    rwa [he]
  have hdw' : Bar.d (homAct PP NN) (n + 1) w' = 0 := by
    simp only [w', map_sub, d_pull hπ, hdx, hπy, sub_self]
  obtain ⟨v, hv, hdv⟩ := hP w' hw' hdw'
  refine ⟨pull ι v, by have := hv.pull hι_deg; rwa [add_zero] at this, ?_⟩
  have hz' : z = pull ι w := by rw [pull_comp, hρι, pull_id]
  rw [d_pull hι, hdv, hz']
  simp only [w', pull_sub, pull_comp, hπι, pull_zero_map, sub_zero]

/-- **A graded direct summand inherits `Ext` vanishing.** -/
theorem extVanish_of_retract {M' : Type*} [AddCommGroup M'] [Module R M'] {MM' : GMod GΛ M'}
    (inc : M' →ₗ[R] M) (pr : M →ₗ[R] M') (s : ℤ)
    (hinc : ∀ m x, inc (MM'.act m x) = MM.act (inc m) x)
    (hpr : ∀ m x, pr (MM.act m x) = MM'.act (pr m) x)
    (hinc_deg : ∀ p m, MM'.gr.IsHom p m → MM.gr.IsHom (p + s) (inc m))
    (hpr_deg : ∀ p m, MM.gr.IsHom p m → MM'.gr.IsHom (p + -s) (pr m))
    (hpi : pr ∘ₗ inc = LinearMap.id) {n : ℕ} {t : ℤ} (h : ExtVanish MM NN n t) :
    ExtVanish MM' NN n (t + s) := by
  intro F hF hdF
  have hF' := hF.pull hpr_deg
  rw [show t + s + -s = t by ring] at hF'
  obtain ⟨H, hH, hdH⟩ := h (pull pr F) hF' (by rw [d_pull hpr, hdF]; rfl)
  refine ⟨pull inc H, hH.pull hinc_deg, ?_⟩
  rw [d_pull hinc, hdH, pull_comp, hpi, pull_id]

end GExt

namespace MeshWalk

universe u

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- **Dimension shifting along the cover of `M_i`, both directions.** -/
theorem extVanish_cover_iff (i : V) {N : Type*} [AddCommGroup N] [Module k N]
    (NN : GExt.GMod (galgA0 D hfin) N) (n : ℕ) (t : ℤ) :
    GExt.ExtVanish (gmodEv D hfin i) NN (n + 1) t ↔ GExt.ExtVanish (KK D hfin i) NN n t := by
  let ρ : CP D hfin i →ₗ[k] LinearMap.ker (cπ D hfin i) :=
    (LinearMap.id - cs D hfin i ∘ₗ cπ D hfin i).codRestrict _ fun x ↦ by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
        ← LinearMap.comp_apply (cπ D hfin i), ← LinearMap.comp_assoc, cπ_cs,
        LinearMap.id_comp, sub_self]
  have hπι : cπ D hfin i ∘ₗ (LinearMap.ker (cπ D hfin i)).subtype = 0 :=
    LinearMap.ext fun x ↦ x.2
  have hι_deg : ∀ p (x : LinearMap.ker (cπ D hfin i)), (KK D hfin i).gr.IsHom p x →
      (gCP D hfin i).gr.IsHom (p + 0) ((LinearMap.ker (cπ D hfin i)).subtype x) :=
    fun p x hx ↦ by rw [add_zero]; exact (KK_isHom D hfin i _ _).1 hx
  have hρ_deg : ∀ p x, (gCP D hfin i).gr.IsHom p x → (KK D hfin i).gr.IsHom (p + 0) (ρ x) := by
    intro p x hx
    rw [add_zero, KK_isHom]
    change (gCP D hfin i).gr.IsHom p (x - cs D hfin i (cπ D hfin i x))
    have h2 := cs_deg D hfin i _ _ (cπ_deg D hfin i p x hx)
    simp only [add_zero] at h2
    rw [sub_eq_add_neg]
    exact (gCP D hfin i).gr.isHom_add hx ((gCP D hfin i).gr.isHom_neg h2)
  have hρι : ρ ∘ₗ (LinearMap.ker (cπ D hfin i)).subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Subtype.ext (by
      change (x : CP D hfin i) - cs D hfin i (cπ D hfin i x) = x
      rw [LinearMap.mem_ker.1 x.2, map_zero, sub_zero])
  have hsplit : (LinearMap.ker (cπ D hfin i)).subtype ∘ₗ ρ + cs D hfin i ∘ₗ cπ D hfin i =
      LinearMap.id :=
    LinearMap.ext fun x ↦ by
      change (x - cs D hfin i (cπ D hfin i x)) + cs D hfin i (cπ D hfin i x) = x
      rw [sub_add_cancel]
  have hP : ∀ m, GExt.ExtVanish (gCP D hfin i) NN m t := fun m ↦
    GExt.extVanish_pi _ _ _ _ fun ℓ ↦ extVanish_proj D hfin ℓ.1 _ _ _
  constructor
  · intro h
    exact GExt.extVanish_unshift (KK := KK D hfin i) (PP := gCP D hfin i)
      (LinearMap.ker (cπ D hfin i)).subtype (cπ D hfin i) (cs D hfin i) ρ
      (fun _ _ ↦ rfl) (cπ_act D hfin i) hι_deg (cπ_deg D hfin i) (cs_deg D hfin i) hρ_deg
      (cπ_cs D hfin i) hρι hsplit hπι (hP n) h
  · intro h
    exact GExt.extVanish_shift (KK := KK D hfin i) (PP := gCP D hfin i)
      (LinearMap.ker (cπ D hfin i)).subtype (cπ D hfin i) (cs D hfin i) ρ
      (fun _ _ ↦ rfl) (cπ_act D hfin i) hι_deg (cπ_deg D hfin i) (cs_deg D hfin i) hρ_deg
      (cπ_cs D hfin i) hρι hsplit hπι (hP (n + 1)) h

/-- **Additivity over a graded decomposition, both directions.** -/
theorem extVanish_decomp_iff {X : Type u} [AddCommGroup X] [Module k X]
    {XX : GExt.GMod (galgA0 D hfin) X} (d : GDecomp D hfin XX LinearMap.id)
    {N : Type*} [AddCommGroup N] [Module k N] (NN : GExt.GMod (galgA0 D hfin) N) (n : ℕ) (t : ℤ) :
    GExt.ExtVanish XX NN n t ↔
      ∀ a, d.inc a ≠ 0 → GExt.ExtVanish (gmodEv D hfin (d.W a)) NN n (t + d.s a) := by
  constructor
  · intro h a _
    exact GExt.extVanish_of_retract (MM := XX) (MM' := gmodEv D hfin (d.W a)) (d.inc a) (d.pr a)
      (d.s a) (d.inc_act a) (d.pr_act a) (d.inc_deg a) (d.pr_deg a) (d.pr_inc a) h
  · intro h
    exact GExt.extVanish_of_decomp (MM := XX) (fun a ↦ gmodEv D hfin (d.W a)) d.s d.inc d.pr
      d.inc_act d.pr_act d.inc_deg d.pr_deg
      (fun m ↦ by
        have := LinearMap.congr_fun d.sum m
        simpa [LinearMap.sum_apply] using this)
      n t h

include hfd in
/-- **Uniqueness of the graded `Ext` of Lemma 6.3**: any notion `E` of graded `Ext^{n+1}(−, M_j)_t`
vanishing on graded `A₀`-modules such that
* `E(M_i, 0, t)` holds exactly when every graded extension of `M_i` by `M_j⟨−t⟩` splits,
* `E(M_p, n, t)` holds at projective labels,
* `E(M_i, n+1, t) ↔ E(K_i, n, t)` along the graded projective cover `K_i ↪ P_i ↠ M_i`,
* `E(K, n, t) ↔ ∀ a, E(M_{W a}, n, t + s_a)` for a graded decomposition `K ≅ ⊕_a M_{W a}⟨s_a⟩`,
agrees with the bar-complex `Ext` on every `Ext^{n+1}_{A₀}(M_i, M_j)_t`. -/
theorem extVanish_unique (J : InjData D) (j : V)
    (E : ∀ {X : Type u} [AddCommGroup X] [Module k X], GExt.GMod (galgA0 D hfin) X → ℕ → ℤ → Prop)
    (hE0 : ∀ i t, E (gmodEv D hfin i) 0 t ↔
      ∀ X : GExt.GExtn (gmodEv D hfin i) (gmodEv D hfin j) t
        (Rep D.F0 (meshFam Q c j) × Rep D.F0 (meshFam Q c i)), X.Splits)
    (hEproj : ∀ (p : D.PV) n t, E (gmodEv D hfin p.1) n t)
    (hEshift : ∀ i, ¬ D.proj i → ∀ n t, E (gmodEv D hfin i) (n + 1) t ↔ E (KK D hfin i) n t)
    (hEdecomp : ∀ i (d : GDecomp D hfin (KK D hfin i) LinearMap.id) n t, E (KK D hfin i) n t ↔
      ∀ a, d.inc a ≠ 0 → E (gmodEv D hfin (d.W a)) n (t + d.s a)) :
    ∀ n i t, E (gmodEv D hfin i) n t ↔
      GExt.ExtVanish (gmodEv D hfin i) (gmodEv D hfin j) n t := by
  intro n
  induction n with
  | zero =>
    intro i t
    rw [hE0, GExt.extVanish_zero_iff (fun q ↦ inferInstance)]
  | succ n ih =>
    intro i t
    by_cases hi : D.proj i
    · exact ⟨fun _ ↦ extVanish_proj D hfin ⟨i, hi⟩ _ _ t, fun _ ↦ hEproj ⟨i, hi⟩ _ t⟩
    obtain ⟨d⟩ := exists_gdecomp D hfin (KK D hfin i) J
    have h1 := hEshift i hi n t
    have h2 := hEdecomp i d n t
    have h3 := extVanish_cover_iff D hfin i (gmodEv D hfin j) n t
    have h4 := extVanish_decomp_iff D hfin d (gmodEv D hfin j) n t
    exact h1.trans (h2.trans ((forall_congr' fun a ↦ imp_congr_right fun _ ↦ ih _ _).trans
      (h4.symm.trans h3.symm)))

end MeshWalk

end MultiplicativeBasisDeformations
