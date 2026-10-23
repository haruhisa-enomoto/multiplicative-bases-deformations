module

public import MultiplicativeBasisDeformations.Foundations.GradedExt

/-!
# Graded `Ext` by the bar complex and graded extensions

Lemma 6.3 and Propositions 6.5, 6.6 use the graded groups `Ext^n_Λ(M, N)_t`. The
formalization works with their vanishing in the bar form (`GExt.ExtVanish`): every
degree-`t` bar `(n+1)`-cocycle `M ⊗ Λ^{⊗(n+1)} → N` is a coboundary. Over a field the bar complex
`M ⊗ Λ^{⊗•} ⊗ Λ` is a graded free resolution of `M` and `Hom_Λ(M ⊗ Λ^{⊗n} ⊗ Λ, N) =
Hom(M ⊗ Λ^{⊗n}, N)`, so this is the usual graded `Ext` (Cartan–Eilenberg, Chapter IX). The
identification with the paper's definition (degree-`t` maps out of any graded projective
resolution) is proved in `ExtResolutions.lean` (`GRes.extVanish_iff`); this file records the
extension form the paper uses.

* **`Ext¹` is the group of graded extensions**: `Ext¹(M, N)_t = 0` in the bar sense if and only if
  every graded extension `0 → N⟨−t⟩ → E → M → 0` splits (`split_of_extVanish`,
  `extVanish_of_split`, `extVanish_zero_iff`). The paper's proof of Lemma 6.3 for `n = 1` argues
  with such extensions (`ExtOne.lean`).
* **Higher `Ext` by dimension shifting**: along an `R`-split exact sequence `0 → K → P → M → 0`
  with `Ext^{n+1}(P, −) = 0`, `Ext^{n+1}(K, N)_t = 0` gives `Ext^{n+2}(M, N)_t = 0`
  (`extVanish_shift`), and graded cyclic projectives have no higher `Ext` (`CycProj.extVanish`);
  these are the two properties used in the paper's proof of Lemma 6.3(2) (`ExtHigher.lean`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (MM : GMod GΛ M) (NN : GMod GΛ N)

/-- **A graded extension** `0 → N⟨−t⟩ → E → M → 0` of graded right `Λ`-modules. -/
structure GExtn (t : ℤ) (E : Type*) [AddCommGroup E] [Module R E] where
  EE : GMod GΛ E
  i : N →ₗ[R] E
  p : E →ₗ[R] M
  i_act : ∀ n a, i (NN.act n a) = EE.act (i n) a
  p_act : ∀ e a, p (EE.act e a) = MM.act (p e) a
  i_inj : Function.Injective i
  p_surj : Function.Surjective p
  exact : LinearMap.range i = LinearMap.ker p
  i_hom : ∀ q n, NN.gr.IsHom (q + t) n → EE.gr.IsHom q (i n)
  p_hom : ∀ q e, EE.gr.IsHom q e → MM.gr.IsHom q (p e)

variable {MM NN}

/-- The extension splits: a graded `Λ`-linear section of `p`. -/
def GExtn.Splits {t : ℤ} {E : Type*} [AddCommGroup E] [Module R E] (X : GExtn MM NN t E) : Prop :=
  ∃ σ : M →ₗ[R] E, (∀ m, X.p (σ m) = m) ∧ (∀ m a, σ (MM.act m a) = X.EE.act (σ m) a) ∧
    ∀ q m, MM.gr.IsHom q m → X.EE.gr.IsHom q (σ m)

/-- A graded linear map commutes with the projections. -/
theorem ZGr.map_proj' {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (gX : ZGr (R := R) X) (gY : ZGr (R := R) Y) (f : X →ₗ[R] Y)
    (hf : ∀ p x, gX.IsHom p x → gY.IsHom p (f x)) (p : ℤ) (x : X) :
    f (gX.proj p x) = gY.proj p (f x) := by
  conv_rhs => rw [gX.sum x]
  rw [map_sum, map_sum, Finset.sum_eq_single p]
  · exact (hf p _ (gX.isHom_proj p x)).symm
  · intro e _ he; rw [gY.proj_of_isHom (hf e _ (gX.isHom_proj e x)), if_neg he]
  · intro hp; rw [gX.proj_out p hp]; simp

theorem ZGr.mem_range_proj' {X : Type*} [AddCommGroup X] [Module R X] (g : ZGr (R := R) X)
    {p : ℤ} {x : X} : x ∈ LinearMap.range (g.proj p) ↔ g.IsHom p x :=
  ⟨fun ⟨y, hy⟩ ↦ hy ▸ g.isHom_proj p y, fun h ↦ ⟨x, h⟩⟩

/-- **A graded `R`-linear section** of a graded surjection onto `M`, when the graded pieces of `M`
are projective (always over a field). -/
theorem exists_graded_section {E : Type*} [AddCommGroup E] [Module R E] (gE : ZGr (R := R) E)
    (p : E →ₗ[R] M) (hp : Function.Surjective p) (hph : ∀ q e, gE.IsHom q e → MM.gr.IsHom q (p e))
    (hproj : ∀ q, Module.Projective R (LinearMap.range (MM.gr.proj q))) :
    ∃ s : M →ₗ[R] E, (∀ m, p (s m) = m) ∧ ∀ q m, MM.gr.IsHom q m → gE.IsHom q (s m) := by
  classical
  have hq : ∀ q, ∃ h : LinearMap.range (MM.gr.proj q) →ₗ[R] LinearMap.range (gE.proj q),
      ∀ y, p (h y) = y := by
    intro q
    let f : LinearMap.range (gE.proj q) →ₗ[R] LinearMap.range (MM.gr.proj q) :=
      LinearMap.codRestrict _ (p ∘ₗ (LinearMap.range (gE.proj q)).subtype) fun e ↦
        (ZGr.mem_range_proj' MM.gr).2 (hph q _ ((ZGr.mem_range_proj' gE).1 e.2))
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨e, rfl⟩ := hp y
      refine ⟨⟨gE.proj q e, LinearMap.mem_range_self _ _⟩, Subtype.ext ?_⟩
      change p (gE.proj q e) = p e
      rw [ZGr.map_proj' gE MM.gr p hph]; exact (ZGr.mem_range_proj' MM.gr).1 hy
    obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
    exact ⟨h, fun y ↦ congrArg Subtype.val (LinearMap.congr_fun hh y)⟩
  choose h hh using hq
  refine ⟨∑ q ∈ MM.gr.supp, (LinearMap.range (gE.proj q)).subtype ∘ₗ h q ∘ₗ
      (MM.gr.proj q).rangeRestrict, fun m ↦ ?_, fun q m hm ↦ ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Submodule.subtype_apply]
    conv_rhs => rw [MM.gr.sum m]
    exact Finset.sum_congr rfl fun q _ ↦ hh q _
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    refine gE.isHom_sum _ _ fun e _ ↦ ?_
    by_cases he : e = q
    · subst he; exact (ZGr.mem_range_proj' gE).1 (h e _).2
    · have : (MM.gr.proj e).rangeRestrict m = 0 :=
        Subtype.ext (by rw [LinearMap.codRestrict_apply, MM.gr.proj_of_isHom hm, if_neg (Ne.symm he)]; rfl)
      rw [this, map_zero]; exact gE.isHom_zero _

/-! ### Splitting from `Ext¹ = 0` -/

section Split

variable {t : ℤ} {E : Type*} [AddCommGroup E] [Module R E]

/-- A map of degree `−t` commutes with the projections, up to the shift. -/
theorem map_proj_shift {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (gX : ZGr (R := R) X) (gY : ZGr (R := R) Y) (f : X →ₗ[R] Y)
    (hf : ∀ q x, gX.IsHom (q + t) x → gY.IsHom q (f x)) (q : ℤ) (x : X) :
    f (gX.proj (q + t) x) = gY.proj q (f x) := by
  conv_rhs => rw [gX.sum x]
  rw [map_sum, map_sum, Finset.sum_eq_single (q + t)]
  · exact (hf q _ (gX.isHom_proj _ x)).symm
  · intro e _ he
    have h := hf (e - t) (gX.proj e x) (by rw [sub_add_cancel]; exact gX.isHom_proj e x)
    rw [gY.proj_of_isHom h, if_neg (by omega)]
  · intro hq; rw [gX.proj_out _ hq]; simp

theorem GExtn.i_reflect (X : GExtn MM NN t E) {q : ℤ} {n : N} (h : X.EE.gr.IsHom q (X.i n)) :
    NN.gr.IsHom (q + t) n := by
  apply X.i_inj
  rw [map_proj_shift NN.gr X.EE.gr X.i X.i_hom q n]
  exact h

variable (X : GExtn MM NN t E) {s : M →ₗ[R] E} (hs : ∀ m, X.p (s m) = m)

/-- The defect `m ↦ s(m)a − s(ma)` of a linear section, as a map to `N`. -/
def defect (s : M →ₗ[R] E) (hs : ∀ m, X.p (s m) = m) (a : Λ) : M →ₗ[R] N :=
  (LinearEquiv.ofInjective X.i X.i_inj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range X.i) (X.EE.act.flip a ∘ₗ s - s ∘ₗ MM.act.flip a)
      (fun m ↦ by
        rw [X.exact, LinearMap.mem_ker]
        simp [X.p_act, hs])

theorem i_defect (a : Λ) (m : M) :
    X.i (defect X s hs a m) = X.EE.act (s m) a - s (MM.act m a) := by
  simp only [defect, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_symm_apply]
  simp

theorem defect_add (a b : Λ) : defect X s hs (a + b) = defect X s hs a + defect X s hs b := by
  ext m
  apply X.i_inj
  simp only [LinearMap.add_apply, map_add, i_defect]
  abel

theorem defect_smul (c : R) (a : Λ) : defect X s hs (c • a) = c • defect X s hs a := by
  ext m
  apply X.i_inj
  simp only [LinearMap.smul_apply, map_smul, i_defect, smul_sub]

/-- The cocycle of the extension. -/
def defectCochain : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦ defect X s hs (a 0)

include hs in
theorem defectCochain_good (hsh : ∀ q m, MM.gr.IsHom q m → X.EE.gr.IsHom q (s m)) :
    Good MM NN 1 t (defectCochain X hs) := by
  refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds q m ha hm ↦ ?_⟩
  · simp [defectCochain, Bar.tr]
  · obtain rfl : i = 0 := by omega
    simp only [defectCochain, Function.update_self, defect_add]
  · obtain rfl : i = 0 := by omega
    simp only [defectCochain, Function.update_self, defect_smul]
  · have ha0 := ha 0 (by norm_num)
    have h1 := X.EE.act_hom _ _ _ _ (hsh q m hm) ha0
    have h2 := hsh _ _ (MM.act_hom _ _ _ _ hm ha0)
    have h3 : X.EE.gr.IsHom (q + ds 0) (X.i (defect X s hs (a 0) m)) := by
      rw [i_defect, sub_eq_add_neg]; exact X.EE.gr.isHom_add h1 (X.EE.gr.isHom_neg h2)
    have h4 := X.i_reflect h3
    simpa [defectCochain] using h4

theorem defectCochain_d : Bar.d (homAct MM NN) 1 (defectCochain X hs) = 0 := by
  funext a
  ext m
  apply X.i_inj
  rw [Bar.d_one_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r, Pi.zero_apply,
    LinearMap.zero_apply, map_zero, map_add, map_sub, LinearMap.comp_apply, LinearMap.flip_apply]
  simp only [defectCochain, Bar.sh, Bar.ct, Bar.tr]
  norm_num
  rw [X.i_act, i_defect, i_defect, i_defect, MM.act_mul, map_sub, LinearMap.sub_apply,
    X.EE.act_mul]
  abel

include hs in
/-- **`Ext¹(M, N)_t = 0` makes every graded extension split** (given a graded linear section, e.g.
over a field). -/
theorem split_of_extVanish (hsh : ∀ q m, MM.gr.IsHom q m → X.EE.gr.IsHom q (s m))
    (h : ExtVanish MM NN 0 t) : X.Splits := by
  obtain ⟨H, hH, hdH⟩ := h (defectCochain X hs) (defectCochain_good X hs hsh)
    (defectCochain_d X hs)
  set hh := H (fun _ ↦ 0)
  have hH0 : ∀ a, H a = hh := fun a ↦ by
    rw [hH.tr a]; congr 1
  have hdef : ∀ m a, hh (MM.act m a) - NN.act (hh m) a = defect X s hs a m := by
    intro m a
    have := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (single a) m) hdH
    simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r, hH0] at this
    simpa [defectCochain, single, Bar.cons] using this
  have hpi : ∀ n, X.p (X.i n) = 0 := fun n ↦ by
    have : X.i n ∈ LinearMap.ker X.p := X.exact ▸ LinearMap.mem_range_self X.i n
    exact this
  refine ⟨s + X.i ∘ₗ hh, fun m ↦ ?_, fun m a ↦ ?_, fun q m hm ↦ ?_⟩
  · simp [hs, hpi]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
    rw [← X.i_act]
    have e := congrArg X.i (hdef m a)
    rw [i_defect, map_sub] at e
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at e
    rw [show s (MM.act m a) + X.i (hh (MM.act m a)) - (X.EE.act (s m) a + X.i (NN.act (hh m) a)) =
      X.i (hh (MM.act m a)) - X.i (NN.act (hh m) a) - (X.EE.act (s m) a - s (MM.act m a)) by abel]
    exact e
  · simp only [LinearMap.add_apply, LinearMap.comp_apply]
    refine X.EE.gr.isHom_add (hsh q m hm) (X.i_hom q _ ?_)
    have := hH.deg (fun _ ↦ 0) (fun _ ↦ 0) q m (fun i hi ↦ absurd hi (by omega)) hm
    simpa using this

end Split

/-! ### `Ext¹ = 0` from splitting -/

/-- **If every graded extension of `M` by `N⟨−t⟩` splits, `Ext¹(M, N)_t = 0`** (the extensions on
`N × M` given by the cocycles suffice). -/
theorem extVanish_of_split {t : ℤ} (h : ∀ X : GExtn MM NN t (N × M), X.Splits) :
    ExtVanish MM NN 0 t := by
  intro F hF hd
  have hF' : Good MM NN 1 t F := hF
  have hd' : Bar.d (homAct MM NN) 1 F = 0 := hd
  let X : GExtn MM NN t (N × M) :=
    { EE := twist F hF' hd'
      i := LinearMap.inl R N M
      p := LinearMap.snd R N M
      i_act := fun n a ↦ by ext <;> simp [twist]
      p_act := fun e a ↦ rfl
      i_inj := LinearMap.inl_injective
      p_surj := fun m ↦ ⟨(0, m), rfl⟩
      exact := LinearMap.range_inl R N M
      i_hom := fun q n hn ↦ (twistGr_isHom (MM := MM) (NN := NN)).2 ⟨hn, MM.gr.isHom_zero _⟩
      p_hom := fun q e he ↦ ((twistGr_isHom (MM := MM) (NN := NN)).1 he).2 }
  obtain ⟨σ, hσ2, hσ, hσdeg⟩ := h X
  exact coboundary_of_section hF' hd' σ hσ2 hσ hσdeg

/-- **`Ext¹(M, N)_t` in the bar sense vanishes iff every graded extension splits** (the graded
pieces of `M` projective over `R`, e.g. over a field); for extensions on any carrier see
`split_of_extVanish`. -/
theorem extVanish_zero_iff {t : ℤ}
    (hproj : ∀ q, Module.Projective R (LinearMap.range (MM.gr.proj q))) :
    ExtVanish MM NN 0 t ↔ ∀ X : GExtn MM NN t (N × M), X.Splits := by
  constructor
  · intro h X
    obtain ⟨s, hs, hsh⟩ := exists_graded_section X.EE.gr X.p X.p_surj X.p_hom hproj
    exact split_of_extVanish X hs hsh h
  · exact extVanish_of_split

end GExt

end MultiplicativeBasisDeformations
