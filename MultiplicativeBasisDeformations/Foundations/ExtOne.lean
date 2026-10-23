module

public import MultiplicativeBasisDeformations.Foundations.A0Graded

/-!
# `Ext¹` between normalized modules (Lemma 6.3, `n = 1`)

`positive-deformations.tex`: "At a nonprojective label `i`, Lemma 2.9 and
Proposition 2.6 give an exact sequence of representable functors […] We obtain a
short exact sequence with terms `M_{τi}`, the middle mesh summands, and `M_i`,
and both maps have degree one. […] It is right almost split […] Shifting its
terms to make its maps degree zero gives
`0 → M_{τi}⟨2⟩ → ⊕_{Y→i} M_Y⟨1⟩ → M_i → 0`. Suppose that
`0 → M_j⟨-t⟩ → X → M_i → 0` is a nonsplit graded extension with `t > -2`. It
remains nonsplit after forgetting the grading […] Thus `v` factors through the
right almost split map. Taking the degree-zero part makes this factorization
graded. The induced map on kernels from `M_j⟨-t⟩` to `M_{τi}⟨2⟩` has underlying
degree `-t-2`, so it is zero […] The factorization therefore descends to a
section of the right almost split map, a contradiction."

Here: the evaluated mesh maps `πE`, `ιτ` (`exact_E`, `ιτ_injective`), the right
almost split property (`exists_factor`, `not_retraction`), and the vanishing
(`extOne_vanish`).
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

/-- The middle term `⊕_a M_{mid a}` of the mesh at `x`. -/
abbrev Emid (x : V) := ∀ a : D.Mid x, Rep D.F0 (meshFam Q c (D.mid x a))

/-- The evaluated right mesh map `⊕_a M_{mid a} → M_x`. -/
def πE (x : V) : Emid D x →ₗ[Alg D.F0] Rep D.F0 (meshFam Q c x) :=
  ∑ a, (repMap (F := D.F0) (D.p x a)).comp (LinearMap.proj a)

theorem πE_apply (x : V) (m : Emid D x) (y : D.PV) :
    πE D x m y = ∑ a, m a y ≫ D.p x a := by
  rw [πE, LinearMap.sum_apply, Rep.sum_apply]
  rfl

/-- The evaluated left mesh map `M_{τx} → ⊕_a M_{mid a}`. -/
def ιτ (x : V) (hx : ¬ D.proj x) : Rep D.F0 (meshFam Q c (D.tau x hx)) →ₗ[Alg D.F0] Emid D x :=
  LinearMap.pi fun a ↦ repMap (F := D.F0) (D.q x hx a)

theorem ιτ_apply (x : V) (hx : ¬ D.proj x) (m : Rep D.F0 (meshFam Q c (D.tau x hx))) (a : D.Mid x)
    (y : D.PV) : ιτ D x hx m a y = m y ≫ D.q x hx a := rfl

theorem ιτ_injective (x : V) (hx : ¬ D.proj x) : Function.Injective (ιτ D x hx) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro r hr
  rw [LinearMap.mem_ker] at hr
  rw [Submodule.mem_bot]
  ext y
  exact D.cov_mono x hx y.1 (r y) fun a ↦ by
    have := congrFun (congrFun hr a) y
    simpa [ιτ] using this

theorem πE_ιτ (x : V) (hx : ¬ D.proj x) (m : Rep D.F0 (meshFam Q c (D.tau x hx))) :
    πE D x (ιτ D x hx m) = 0 := by
  ext y
  rw [πE_apply]
  simp only [ιτ_apply, Category.assoc]
  rw [← Preadditive.comp_sum, D.comp_zero, Limits.comp_zero]
  rfl

/-- **Exactness at the middle term.** -/
theorem exact_E (x : V) (hx : ¬ D.proj x) {m : Emid D x} (hm : πE D x m = 0) :
    ∃ r, ιτ D x hx r = m := by
  choose z hz using fun y : D.PV ↦ D.cov_exact x hx y.1 (fun a ↦ m a y) (by
    have := congrFun hm y
    rwa [πE_apply] at this)
  refine ⟨fun y ↦ z y, ?_⟩
  ext a y
  exact (hz y a).symm

variable [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

include hfd in
/-- **`πE` is not a retraction**: its components are radical. -/
theorem not_retraction (x : V) (w : Rep D.F0 (meshFam Q c x) →ₗ[Alg D.F0] Emid D x)
    (hw : (πE D x).comp w = LinearMap.id) : False := by
  choose h hh using fun a ↦ D.hom_eq_repMap x (D.mid x a) ((LinearMap.proj a).comp w)
  have hsum : ∑ a, h a ≫ D.p x a = 𝟙 _ := by
    have h0 : ∀ m : Rep D.F0 (meshFam Q c x),
        repMap (F := D.F0) (∑ a, h a ≫ D.p x a - 𝟙 _) m = 0 := by
      intro m
      ext y
      have hy := congrFun (LinearMap.congr_fun hw m) y
      rw [LinearMap.comp_apply, πE_apply, LinearMap.id_apply] at hy
      have h1 : ∀ a, w m a y = m y ≫ h a := fun a ↦ by
        have := congrFun (hh a m) y
        simpa using this
      simp only [h1] at hy
      rw [repMap_apply, Preadditive.comp_sub, Preadditive.comp_sum, Category.comp_id]
      simp only [← Category.assoc]
      rw [hy, sub_self]
      rfl
    exact sub_eq_zero.1 (D.repMap_eq_zero x x _ h0)
  apply L.id_not_mem x
  rw [← hsum]
  exact Submodule.sum_mem _ fun a _ ↦ L.comp_left _ (D.p_rad x a)

variable {D} (J : InjData D)

include J hfd in
/-- **`πE` is right almost split**: a non-retraction into `M_x` factors through it. -/
theorem exists_factor {X : Type*} [AddCommGroup X] [Module k X] [Module (Alg D.F0) X]
    [IsScalarTower k (Alg D.F0) X] [FiniteDimensional k X] (x : V)
    (g : X →ₗ[Alg D.F0] Rep D.F0 (meshFam Q c x))
    (hg : ¬ ∃ s : Rep D.F0 (meshFam Q c x) →ₗ[Alg D.F0] X, g.comp s = LinearMap.id) :
    ∃ u : X →ₗ[Alg D.F0] Emid D x, (πE D x).comp u = g := by
  classical
  obtain ⟨μ, _, _, W, ⟨ψ⟩⟩ := J.essSurj (X := X)
  obtain ⟨f, hf⟩ := D.evMap_surjective (Z := W) (Z' := uZ x)
    ((D.eU (meshFam Q c x)).toLinearMap.comp (g.comp ψ.symm.toLinearMap))
  have hg' : ∀ m, g (ψ.symm m) = ∑ j, repMap (F := D.F0) (f j ()) (m j) := fun m ↦ by
    have := congrFun (LinearMap.congr_fun hf m) ()
    rw [evMap_apply] at this
    exact this.symm
  -- every component is radical
  have hrad : ∀ j, f j () ∈ L.rad (W j) x := by
    intro j
    by_contra hnot
    have hW : W j = x := by
      by_contra hne
      exact hnot (L.mem_of_ne hne _)
    set f' : meshFam Q c x ⟶ meshFam Q c x := eqToHom (congrArg (meshFam Q c) hW.symm) ≫ f j ()
    have hf' : f' ∉ L.rad x x := fun h ↦ hnot (by
      have := L.comp_left (eqToHom (congrArg (meshFam Q c) hW)) h
      rwa [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at this)
    obtain ⟨u0, hu0⟩ := L.isUnit_of_not_mem hf'
    apply hg
    set g0 : meshFam Q c x ⟶ meshFam Q c (W j) :=
      (u0⁻¹ : (End (meshFam Q c x))ˣ).1 ≫ eqToHom (congrArg (meshFam Q c) hW.symm)
    refine ⟨ψ.symm.toLinearMap.comp ((LinearMap.single (Alg D.F0)
      (fun j ↦ Rep D.F0 (meshFam Q c (W j))) j).comp (repMap (F := D.F0) g0)), ?_⟩
    ext m y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [hg', Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj'])
      (fun h ↦ absurd (Finset.mem_univ j) h)]
    simp only [LinearMap.coe_single, Pi.single_eq_same, repMap_apply, Category.assoc]
    have h1 : g0 ≫ f j () = 𝟙 _ := by
      simp only [g0, Category.assoc]
      change (u0⁻¹ : (End (meshFam Q c x))ˣ).1 ≫ f' = 𝟙 _
      rw [← hu0]
      exact u0.mul_inv
    rw [h1, Category.comp_id]
  choose G hG using fun j ↦ D.image x (W j) (f j ()) (hrad j)
  refine ⟨LinearMap.pi (fun a ↦ ∑ j, (repMap (F := D.F0) (G j a)).comp
    ((LinearMap.proj j).comp ψ.toLinearMap)), ?_⟩
  ext z y
  rw [LinearMap.comp_apply, πE_apply]
  conv_rhs => rw [← ψ.symm_apply_apply z, hg']
  simp only [LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe, Rep.sum_apply, repMap_apply, Preadditive.sum_comp, Category.assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hG j, Preadditive.comp_sum]

include hfd in
theorem πE_injective (x : V) (hx : D.proj x) : Function.Injective (πE D x) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  rw [Submodule.mem_bot]
  funext a y
  exact D.proj_mono x hx y.1 (fun a ↦ m a y) (by
    have := congrFun hm y
    rwa [πE_apply] at this) a

/-! ### Degrees of the mesh maps -/

theorem repMap_isHom {X Y : V} {s : ℕ} {f : obj c X ⟶ obj c Y} (hf : f ∈ degreePart c s X Y)
    {p : ℤ} {m : Rep D.F0 (meshFam Q c X)} (hm : (zgrEv D hfin X).IsHom p m) :
    (zgrEv D hfin Y).IsHom (p + s) (repMap (F := D.F0) f m) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [(zgrEv_isHom_neg D hfin X hp m).1 hm, map_zero]; exact GExt.ZGr.isHom_zero _ _
  obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [zgrEv_isHom] at hm
  rw [show (p' : ℤ) + s = ((p' + s : ℕ) : ℤ) by push_cast; ring, zgrEv_isHom]
  intro y
  exact comp_mem_degreePart' c (hm y) hf

variable (D) in
/-- The middle term `⊕_a M_{mid a}⟨1⟩` as a graded module. -/
def gE (x : V) : GExt.GMod (galgA0 D hfin) (Emid D x) :=
  GExt.GMod.pi (fun a ↦ gmodEv D hfin (D.mid x a)) (fun _ ↦ 1)

variable (D) in
/-- The mesh maps have degree one. -/
structure DegOne : Prop where
  p : ∀ x a, D.p x a ∈ degreePart c 1 (D.mid x a) x
  q : ∀ x hx a, D.q x hx a ∈ degreePart c 1 (D.tau x hx) (D.mid x a)

theorem πE_isHom (h1 : DegOne D) (x : V) (p : ℤ) (m : Emid D x)
    (hm : (gE D hfin x).gr.IsHom p m) : (zgrEv D hfin x).IsHom (p + 0) (πE D x m) := by
  have hm' := (GExt.ZGr.piShift_isHom _ _ _ _).1 hm
  rw [πE]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine GExt.ZGr.isHom_sum _ _ _ fun a _ ↦ ?_
  have := repMap_isHom hfin (h1.p x a) (hm' a)
  rwa [show p - 1 + ((1 : ℕ) : ℤ) = p + 0 by push_cast; ring] at this

theorem ιτ_isHom (h1 : DegOne D) (x : V) (hx : ¬ D.proj x) (p : ℤ)
    (m : Rep D.F0 (meshFam Q c (D.tau x hx))) (hm : (zgrEv D hfin _).IsHom p m) :
    (gE D hfin x).gr.IsHom (p + 2) (ιτ D x hx m) := by
  refine (GExt.ZGr.piShift_isHom _ _ _ _).2 fun a ↦ ?_
  have := repMap_isHom hfin (h1.q x hx a) hm
  rwa [show p + ((1 : ℕ) : ℤ) = p + 2 - 1 by push_cast; ring] at this

/-! ### The vanishing -/

include J in
/-- **Lemma 6.3(2), `n = 1`**: `Ext¹_{A₀}(M_i, M_j)_t = 0` for `t > -2`. -/
theorem extOne_vanish (h1 : DegOne D) (i j : V) {t : ℤ} (ht : -2 < t) :
    GExt.ExtVanish (gmodEv D hfin i) (gmodEv D hfin j) 0 t := by
  intro F hF hd
  set MM := gmodEv D hfin i
  set NN := gmodEv D hfin j
  set XX := GExt.twist F hF hd
  let gT := GExt.twistGr (MM := MM) (NN := NN) t
  have hsnd : ∀ p x, gT.IsHom p x → MM.gr.IsHom (p + 0) (LinearMap.snd k _ _ x) := fun p x hx ↦ by
    rw [add_zero]; exact (GExt.twistGr_isHom.1 hx).2
  suffices hσ : ∃ σ : Rep D.F0 (meshFam Q c i) →ₗ[k] Rep D.F0 (meshFam Q c j) × Rep D.F0 (meshFam Q c i),
      (∀ m, (σ m).2 = m) ∧ (∀ m a, σ (MM.act m a) = XX.act (σ m) a) ∧
      ∀ p m, MM.gr.IsHom p m → gT.IsHom p (σ m) by
    obtain ⟨σ, hσ1, hσ2, hσ3⟩ := hσ
    exact GExt.coboundary_of_section hF hd σ hσ1 hσ2 hσ3
  -- an ungraded section gives a graded one
  suffices hs : ∃ s : Rep D.F0 (meshFam Q c i) →ₗ[k]
      Rep D.F0 (meshFam Q c j) × Rep D.F0 (meshFam Q c i),
      (∀ m, (s m).2 = m) ∧ ∀ m a, s (MM.act m a) = XX.act (s m) a by
    obtain ⟨s, hs1, hs2⟩ := hs
    refine ⟨GExt.ZGr.comp MM.gr gT 0 s, fun m ↦ ?_, fun m a ↦ ?_, fun p m hm ↦ ?_⟩
    · have h := GExt.ZGr.comp_comp_left MM.gr gT MM.gr 0 s (LinearMap.snd k _ _)
        (fun p x hx ↦ (GExt.twistGr_isHom.1 hx).2)
      have hid : LinearMap.snd k _ _ ∘ₗ s = LinearMap.id := LinearMap.ext hs1
      rw [hid, GExt.ZGr.comp_eq_self_of_hom MM.gr MM.gr (s := 0) (fun p m hm ↦ by rwa [add_zero])]
        at h
      exact (LinearMap.congr_fun h m).symm
    · exact GExt.comp_act (XX := MM) (YY := XX) 0 hs2 m a
    · have := GExt.ZGr.comp_isHom MM.gr gT (r := 0) s hm
      rwa [add_zero] at this
  by_contra hns
  have : FiniteDimensional k (GExt.Left XX) :=
    inferInstanceAs (FiniteDimensional k (Rep D.F0 (meshFam Q c j) × Rep D.F0 (meshFam Q c i)))
  let g : GExt.Left XX →ₗ[Alg D.F0] Rep D.F0 (meshFam Q c i) :=
    { toFun := fun x ↦ (show Rep D.F0 (meshFam Q c j) × Rep D.F0 (meshFam Q c i) from x).2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hg : ¬ ∃ s' : Rep D.F0 (meshFam Q c i) →ₗ[Alg D.F0] GExt.Left XX,
      g.comp s' = LinearMap.id := by
    rintro ⟨s', hs'⟩
    exact hns ⟨s'.restrictScalars k, fun m ↦ LinearMap.congr_fun hs' m,
      fun m a ↦ s'.map_smul a.unop m⟩
  obtain ⟨u, hu⟩ := exists_factor J i g hg
  let gEE := (gE D hfin i).gr
  let uk : Rep D.F0 (meshFam Q c j) × Rep D.F0 (meshFam Q c i) →ₗ[k] Emid D i :=
    (u.restrictScalars k : GExt.Left XX →ₗ[k] Emid D i)
  have huΛ : ∀ x a, uk (XX.act x a) = (gE D hfin i).act (uk x) a := fun x a ↦ u.map_smul a.unop x
  set u0 := GExt.ZGr.comp gT gEE 0 uk with hu0def
  have hu0Λ : ∀ x a, u0 (XX.act x a) = (gE D hfin i).act (u0 x) a :=
    GExt.comp_act (XX := XX) (YY := gE D hfin i) 0 huΛ
  have hu0deg : ∀ p x, gT.IsHom p x → gEE.IsHom (p + 0) (u0 x) := fun p x hx ↦
    GExt.ZGr.comp_isHom gT gEE uk hx
  have hπu0 : ∀ x, πE D i (u0 x) = x.2 := by
    have h := GExt.ZGr.comp_comp_left gT gEE (zgrEv D hfin i) 0 uk ((πE D i).restrictScalars k)
      (fun p e he ↦ by simpa using πE_isHom hfin h1 i p e he)
    have h' : (πE D i).restrictScalars k ∘ₗ uk = LinearMap.snd k _ _ :=
      LinearMap.ext fun x ↦ LinearMap.congr_fun hu x
    rw [h', GExt.ZGr.comp_eq_self_of_hom gT (zgrEv D hfin i) (s := 0) hsnd] at h
    intro x
    exact (LinearMap.congr_fun h x).symm
  -- the restriction to `M_j` vanishes
  have hinl : ∀ n, u0 (n, 0) = 0 := by
    by_cases hx : D.proj i
    · intro n
      apply πE_injective i hx
      rw [hπu0, map_zero]
    · have hmem : ∀ n, (u0 ∘ₗ LinearMap.inl k _ _) n ∈
          LinearMap.range ((ιτ D i hx).restrictScalars k) := fun n ↦ by
        obtain ⟨r, hr⟩ := exact_E D i hx (m := u0 (n, 0)) (by rw [hπu0])
        exact ⟨r, hr⟩
      let e := LinearEquiv.ofInjective ((ιτ D i hx).restrictScalars k) (ιτ_injective D i hx)
      let w : Rep D.F0 (meshFam Q c j) →ₗ[k] Rep D.F0 (meshFam Q c (D.tau i hx)) :=
        e.symm.toLinearMap ∘ₗ (u0 ∘ₗ LinearMap.inl k _ _).codRestrict _ hmem
      have hw : ∀ n, ιτ D i hx (w n) = u0 (n, 0) := fun n ↦
        congrArg Subtype.val (e.apply_symm_apply ⟨u0 (n, 0), hmem n⟩)
      have hwΛ : ∀ n a, w (evAct D j n a) = evAct D (D.tau i hx) (w n) a := fun n a ↦
        ιτ_injective D i hx (by
          rw [hw]
          change _ = ιτ D i hx (a.unop • w n)
          rw [map_smul, hw]
          have h := hu0Λ (n, 0) a
          have hx0 : XX.act (n, 0) a = (NN.act n a, 0) := by
            simp [XX, GExt.twist, MM]
          rw [hx0] at h
          exact h)
      have hwdeg : ∀ p n, (zgrEv D hfin j).IsHom p n →
          (zgrEv D hfin (D.tau i hx)).IsHom (p + (-t - 2)) (w n) := fun p n hn ↦ by
        have hT : gT.IsHom (p - t) (n, 0) :=
          GExt.twistGr_isHom.2 ⟨by rwa [sub_add_cancel], GExt.ZGr.isHom_zero _ _⟩
        have h2 := hu0deg _ _ hT
        rw [← hw] at h2
        exact GExt.ZGr.isHom_of_injective (zgrEv D hfin (D.tau i hx)) gEE (s := 2)
          (u := (ιτ D i hx).restrictScalars k) (ιτ_isHom hfin h1 i hx) (ιτ_injective D i hx)
          (by rwa [show p + (-t - 2) + 2 = p - t + 0 by ring])
      have hw0 : w = 0 := by
        rw [← GExt.ZGr.comp_eq_self_of_hom (zgrEv D hfin j) (zgrEv D hfin (D.tau i hx)) hwdeg]
        exact hom_comp_neg D hfin w hwΛ (by omega)
      intro n
      rw [← hw, hw0, LinearMap.zero_apply, map_zero]
  -- hence `u₀` descends to a section of `πE`
  let ub : Rep D.F0 (meshFam Q c i) →ₗ[Alg D.F0] Emid D i :=
    { toFun := fun m ↦ u0 (0, m)
      map_add' := fun m m' ↦ by
        rw [← map_add, Prod.mk_add_mk, zero_add]
      map_smul' := fun b m ↦ by
        have h := hu0Λ (0, m) (MulOpposite.op b)
        have hx0 : XX.act (0, m) (MulOpposite.op b) =
            (F (GExt.single (MulOpposite.op b)) m, 0) + (0, b • m) := by
          simp only [XX, GExt.twist, LinearMap.mk₂_apply, map_zero, LinearMap.zero_apply,
            zero_add, Prod.mk_add_mk, add_zero]
          rfl
        rw [hx0, map_add, hinl, zero_add] at h
        exact h }
  exact not_retraction D i ub (LinearMap.ext fun m ↦ hπu0 (0, m))

end MeshWalk

end MultiplicativeBasisDeformations
