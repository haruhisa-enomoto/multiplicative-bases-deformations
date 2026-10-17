import MultiplicativeBasisDeformations.Foundations.FilteredNormalForm
import MultiplicativeBasisDeformations.Refinements.FlatPerturbation

/-!
# Proposition 12.2: normal forms for filtered mesh categories

`deformation-refinements.tex` (`prop:characteristic-two-normal-form`). Let `C = kQ/(r_v)`
be a finite-dimensional graded category with homogeneous quadratic relations, and choose, in each
degree `q ≥ 3`, homogeneous tuples `p_i` of degree `d_i = q` whose classes represent the cokernel
of `D_{q-1}`. Every finite filtered `E` with `gr E = C` has a presentation
`E ≅ kQ/(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)` inducing the identification on `gr`.

As for Proposition 5.4 (`FilteredNormalForm.lean`), we prove the proposition for
`E = ind(mod A)` filtered by the radical powers, `C = k(Γ_A)` and the identification of
Proposition 2.6(3). The hypothesis is in spanning form: the image of `D_{q-1}` and the classes
of the retained tuples of degree `q` span all degree-`q` mesh families. The proof is the
source's: correct the arrow lifts degree by degree, retaining a combination of the `p_i` in each
degree (`Lifts.exists_retained_correction`); the filtration is finite. The resulting lifts realize
`kQ → ind(mod A)` surjectively, with kernel exactly `(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)`
(`normalForm`), and agree with the identification on every radical layer.

Deviation in the injectivity step: the source compares associated gradings; we show directly,
degree by degree, that a morphism realized to zero lies in the perturbed ideal, using the
injectivity of Proposition 2.6(3) and the homogeneous parts of the mesh ideal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations

/-! ### The mesh relations as a presentation -/

namespace FlatPert

open LinearPaths

variable {k : Type*} [CommRing k] {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- **The mesh presentation**: one quadratic relation `r_x : τ x → x` at each nonprojective
vertex. -/
abbrev meshPres (c : MeshCoefficients k Q) : Pres k V where
  T x := {_u : Unit // x ∈ Q.nonprojective}
  fin _ := Fintype.ofFinite _
  src x t := (Q.tau ⟨x, t.2⟩).1
  deg _ _ := 2
  r x t := meshRelation c ⟨x, t.2⟩
  hom x t := meshRelation_mem_degreePart c ⟨x, t.2⟩
  two _ _ := le_rfl

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] in
/-- **The mesh ideal is the span of the contextual mesh relations.** -/
theorem ctxSpan_meshPres (c : MeshCoefficients k Q) (x y : V) :
    ctxSpan (meshPres c) (meshPres c).r x y =
      CategoricalIdeal.HomIdeal.generatedHomSubmodule k (meshRelations c)
        (LinearPaths.obj (k := k) x) (LinearPaths.obj y) := by
  apply le_antisymm
  · rw [ctxSpan, Submodule.span_le]
    rintro _ ⟨z, t, u, v, rfl⟩
    refine Submodule.subset_span ⟨_, _, meshRelation c ⟨z, t.2⟩, ⟨⟨z, t.2⟩, rfl, rfl, ?_⟩,
      path u, path v, rfl⟩
    simp
  · rw [CategoricalIdeal.HomIdeal.generatedHomSubmodule, Submodule.span_le]
    rintro _ ⟨X, Y, r, ⟨z, hX, hY, rfl⟩, a, a', rfl⟩
    subst hX hY
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact ctx_mem (meshPres c) (meshPres c).r (x := z.1) ⟨(), z.2⟩ a a'

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] in
/-- The part of degree `n` of an element of `𝔪^n` agrees with it modulo `𝔪^{n+1}`. -/
theorem sub_proj_mem_geSpan {n : ℕ} {x y : V} {h : Hm k x y} (hh : h ∈ geSpan k n x y) :
    h - proj (k := k) n x y h ∈ geSpan k (n + 1) x y := by
  induction hh using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    rw [proj_path]
    split_ifs with h
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact Submodule.subset_span ⟨p, by omega, rfl⟩
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, add_sub_add_comm]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c ha

end FlatPert

namespace IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-! ### Retained tuples -/

/-- **Retained tuples** `p_i = ((p_i)_v)_v`, homogeneous of degree `d_i ≥ 3`. -/
structure Retained where
  I : Type
  [fin : Fintype I]
  d : I → ℕ
  three : ∀ i, 3 ≤ d i
  p : I → ∀ x : S.arTranslationQuiver.nonprojective,
    LinearPaths.obj (k := k) (S.arTranslationQuiver.tau x).1 ⟶ LinearPaths.obj x.1
  hom : ∀ i x, p i x ∈ LinearPaths.degreePart (k := k) (d i) _ _

attribute [instance] Retained.fin

variable {S}

/-- **The cokernel hypothesis** (spanning form): in each degree `q = m + 1 ≥ 3`, the image of
`D_m` and the classes of the retained tuples of degree `q` span all mesh families of degree `q`. -/
def Retained.Spans (R : S.Retained) : Prop :=
  ∀ m, 2 ≤ m → ∀ g : ScalarMeshCategory.MeshFamily (S.arCoefficients b),
    (∀ x, g x ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) (m + 1)
      (S.arTranslationQuiver.tau x).1 x.1) →
    ∃ f : ScalarMeshCategory.ArrowFamily (S.arCoefficients b),
      (∀ a, f a ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) m a.1 a.2.1) ∧
      ∃ c : R.I → k, (∀ i, R.d i ≠ m + 1 → c i = 0) ∧
        ∀ x, g x = ScalarMeshCategory.meshDerivative (S.arCoefficients b) f x +
          ∑ i, c i • (S.meshQuot b).map (R.p i x)

variable {b}

namespace Lifts

/-- The relation errors relative to the retained terms: `r_v − Σ_i λ_i (p_i)_v`, realized. -/
def errRet (L : S.Lifts b) (R : S.Retained) (lam : R.I → k)
    (x : S.arTranslationQuiver.nonprojective) :
    S.label (S.arTranslationQuiver.tau x).1 ⟶ S.label x.1 :=
  L.error x - ∑ i, lam i • L.realize _ _ (R.p i x)

/-- Two lift families differing in `J^m` on the arrows realize a path of length `ℓ` up to
`J^{ℓ+m-1}`. -/
theorem pathMap_sub_pathMap {m : ℕ} (hm : 1 ≤ m) (L L' : S.Lifts b)
    (hLL : ∀ {x y : S.ARVertex} (a : x ⟶ y), L'.L a - L.L a ∈ S.radPow m _ _)
    {x y : S.ARVertex} (p : Quiver.Path x y) :
    L'.pathMap p - L.pathMap p ∈ S.radPow (p.length + m - 1) _ _ := by
  induction p with
  | nil => simp
  | cons p a ih =>
    rw [pathMap_cons, pathMap_cons, Quiver.Path.length_cons]
    have e : L'.pathMap p ≫ L'.L a - L.pathMap p ≫ L.L a =
        (L'.pathMap p - L.pathMap p) ≫ L'.L a + L.pathMap p ≫ (L'.L a - L.L a) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub]; abel
    rw [e]
    refine add_mem ?_ ?_
    · have := S.comp_mem_radPow ih (L'.mem_one a)
      rwa [show p.length + m - 1 + 1 = p.length + 1 + m - 1 by omega] at this
    · have := S.comp_mem_radPow (L.pathMap_mem p) (hLL a)
      exact S.radPow_anti (by omega) _ _ this

theorem realize_sub_realize {m d : ℕ} (hm : 1 ≤ m) (L L' : S.Lifts b)
    (hLL : ∀ {x y : S.ARVertex} (a : x ⟶ y), L'.L a - L.L a ∈ S.radPow m _ _)
    {x y : S.ARVertex} {F : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hF : F ∈ LinearPaths.degreePart (k := k) d x y) :
    L'.realize x y F - L.realize x y F ∈ S.radPow (d + m - 1) _ _ := by
  induction hF using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, rfl, rfl⟩ := hg
    rw [realize_path, realize_path]
    exact pathMap_sub_pathMap hm L L' hLL p
  | zero => simp
  | add a c _ _ ha hc =>
    rw [map_add, map_add, add_sub_add_comm]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul, map_smul, ← smul_sub]; exact Submodule.smul_mem _ c ha

end Lifts

variable (b) in
set_option maxHeartbeats 1600000 in
/-- **The correction step** of Proposition 12.2: if the relation errors relative to the
retained terms lie in `J^{m+1}` (`m ≥ 2`), a change of the lifts in degree `m` and of the
coefficients of the retained tuples of degree `m + 1` moves them into `J^{m+2}`. -/
theorem Lifts.exists_retained_correction (R : S.Retained) (hR : R.Spans b) {m : ℕ} (hm : 2 ≤ m)
    (L : S.Lifts b) (lam : R.I → k) (hL : ∀ x, L.errRet R lam x ∈ S.radPow (m + 1) _ _) :
    ∃ (L' : S.Lifts b) (lam' : R.I → k), ∀ x, L'.errRet R lam' x ∈ S.radPow (m + 2) _ _ := by
  classical
  -- the error classes, pulled back to `C_{m+1}`
  let g : ScalarMeshCategory.MeshFamily (S.arCoefficients b) := fun x ↦
    -((S.phi b (m + 1) _ _).symm (S.layerClass (L.errRet R lam x) (hL x))).1
  have hg : ∀ x, g x ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) (m + 1)
      (S.arTranslationQuiver.tau x).1 x.1 := fun x ↦ neg_mem (Subtype.prop _)
  obtain ⟨f, hf, c, hc, hDf⟩ := hR m hm g hg
  -- lift the corrections to the path category and realize them
  have hex : ∀ a : Σ x y : S.ARVertex, x ⟶ y, ∃ F : LinearPaths.obj (k := k) a.1 ⟶
      LinearPaths.obj a.2.1, F ∈ LinearPaths.degreePart (k := k) m a.1 a.2.1 ∧
        (S.meshQuot b).map F = f a := by
    intro a
    obtain ⟨F, hF, h⟩ := hf a
    exact ⟨F, hF, h⟩
  choose Ft hFt hqFt using hex
  let F : ∀ {x y : S.ARVertex} (a : x ⟶ y), S.label x ⟶ S.label y :=
    fun {x y} a ↦ S.realize b x y (Ft ⟨x, y, a⟩)
  have hFm : ∀ {x y : S.ARVertex} (a : x ⟶ y), F a ∈ S.radPow m _ _ :=
    fun {x y} a ↦ S.realize_mem b (hFt ⟨x, y, a⟩)
  have hF2 : ∀ {x y : S.ARVertex} (a : x ⟶ y), F a ∈ S.radPow 2 _ _ :=
    fun a ↦ S.radPow_anti hm _ _ (hFm a)
  let L' : S.Lifts b :=
    { L := fun a ↦ L.L a + F a
      sub_mem := fun a ↦ by
        have : L.L a + F a - S.rep b a = (L.L a - S.rep b a) + F a := by abel
        rw [this]; exact add_mem (L.sub_mem a) (hF2 a) }
  have hLL : ∀ {x y : S.ARVertex} (a : x ⟶ y), L'.L a - L.L a ∈ S.radPow m _ _ := by
    intro x y a
    have : L'.L a - L.L a = F a := by simp [L']
    rw [this]; exact hFm a
  refine ⟨L', lam - c, fun x ↦ ?_⟩
  -- the derivative of the corrections, in the path category
  let T : LinearPaths.obj (k := k) (S.arTranslationQuiver.tau x).1 ⟶ LinearPaths.obj x.1 :=
    ∑ a : Σ y : S.ARVertex, y ⟶ x.1, ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
      (Ft ⟨_, a.1, S.arTranslationQuiver.mate x a.1 a.2⟩ ≫ LinearPaths.arrow a.2 +
        LinearPaths.arrow (S.arTranslationQuiver.mate x a.1 a.2) ≫ Ft ⟨a.1, x.1, a.2⟩)
  have hT : T ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := by
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem ?_ ?_)
    · exact LinearPaths.comp_arrow_mem_degreePart
        (hFt ⟨_, a.1, S.arTranslationQuiver.mate x a.1 a.2⟩) a.2
    · have := LinearPaths.comp_mem_degreePart
        (LinearPaths.arrow_mem_degreePart (k := k) (S.arTranslationQuiver.mate x a.1 a.2))
        (hFt ⟨a.1, x.1, a.2⟩)
      rwa [add_comm] at this
  -- the derivative plus the retained terms
  let T2 := T + ∑ i, c i • R.p i x
  have hT2 : T2 ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := by
    refine add_mem hT (Submodule.sum_mem _ fun i _ ↦ ?_)
    by_cases hi : R.d i = m + 1
    · exact Submodule.smul_mem _ _ (hi ▸ R.hom i x)
    · rw [hc i hi, zero_smul]; exact zero_mem _
  have hqT2 : (S.meshQuot b).map T2 = g x := by
    rw [hDf x]
    simp only [T2, T, ScalarMeshCategory.meshDerivative, Functor.map_add, Functor.map_sum,
      Functor.map_smul, Functor.map_comp, hqFt]
    rfl
  -- the class of `realize T2` is minus the class of the error
  have hclass : L.errRet R lam x + S.realize b _ _ T2 ∈ S.radPow (m + 2) _ _ := by
    have h1 : S.phi b (m + 1) _ _ (S.qd b (m + 1) _ _ ⟨T2, hT2⟩) =
        -S.layerClass (L.errRet R lam x) (hL x) := by
      have e : S.qd b (m + 1) _ _ ⟨T2, hT2⟩ =
          -((S.phi b (m + 1) _ _).symm (S.layerClass (L.errRet R lam x) (hL x))) :=
        Subtype.ext hqT2
      rw [e, map_neg, LinearEquiv.apply_symm_apply]
    rw [S.phi_qd] at h1
    have h2 : S.layerClass (L.errRet R lam x + S.realize b _ _ T2)
        (add_mem (hL x) (S.realize_mem b hT2)) = 0 := by
      have e : S.layerClass (L.errRet R lam x + S.realize b _ _ T2)
          (add_mem (hL x) (S.realize_mem b hT2)) =
          S.layerClass (L.errRet R lam x) (hL x) + S.psi b (m + 1) _ _ ⟨T2, hT2⟩ := rfl
      rw [e, h1, add_neg_cancel]
    exact (S.layerClass_eq_zero_iff _).1 h2
  -- the new mesh error differs from `error + realize T` by terms in `J^{m+2}`
  have hrealT : S.realize b _ _ T = ∑ a : Σ y : S.ARVertex, y ⟶ x.1,
      ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
        (F (S.arTranslationQuiver.mate x a.1 a.2) ≫ S.rep b a.2 +
          S.rep b (S.arTranslationQuiver.mate x a.1 a.2) ≫ F a.2) := by
    simp only [T, map_sum, map_smul, map_add, S.realize_comp, S.realize_arrow]
    rfl
  have hdiff : L'.error x - (L.error x + S.realize b _ _ T) =
      ∑ a : Σ y : S.ARVertex, y ⟶ x.1, ((S.arCoefficients b x a.1 a.2 : kˣ) : k) •
        (F (S.arTranslationQuiver.mate x a.1 a.2) ≫ (L.L a.2 - S.rep b a.2) +
          (L.L (S.arTranslationQuiver.mate x a.1 a.2) -
            S.rep b (S.arTranslationQuiver.mate x a.1 a.2)) ≫ F a.2 +
          F (S.arTranslationQuiver.mate x a.1 a.2) ≫ F a.2) := by
    rw [Lifts.error_eq, Lifts.error_eq, hrealT, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← smul_add, ← smul_sub]
    congr 1
    simp only [L', Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp,
      Preadditive.comp_sub]
    abel
  have hmem : L'.error x - (L.error x + S.realize b _ _ T) ∈ S.radPow (m + 2) _ _ := by
    rw [hdiff]
    refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem (add_mem ?_ ?_) ?_)
    · exact S.comp_mem_radPow (hFm (S.arTranslationQuiver.mate x a.1 a.2)) (L.sub_mem a.2)
    · have := S.comp_mem_radPow (L.sub_mem (S.arTranslationQuiver.mate x a.1 a.2)) (hFm a.2)
      rwa [add_comm] at this
    · exact S.radPow_anti (by omega) _ _
        (S.comp_mem_radPow (hFm (S.arTranslationQuiver.mate x a.1 a.2)) (hFm a.2))
  -- the retained terms
  have hlam : ∑ i, lam i • (L'.realize _ _ (R.p i x) - L.realize _ _ (R.p i x)) ∈
      S.radPow (m + 2) _ _ := by
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    have := Lifts.realize_sub_realize (by omega) L L' hLL (R.hom i x)
    exact S.radPow_anti (by have := R.three i; omega) _ _ this
  have hcS : ∑ i, c i • (L'.realize _ _ (R.p i x) - S.realize b _ _ (R.p i x)) ∈
      S.radPow (m + 2) _ _ := by
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : R.d i = m + 1
    · refine Submodule.smul_mem _ _ ?_
      have := L'.realize_sub_mem (R.hom i x)
      rwa [hi] at this
    · rw [hc i hi, zero_smul]; exact zero_mem _
  have halg : L'.errRet R (lam - c) x - (L.errRet R lam x + S.realize b _ _ T2) =
      (L'.error x - (L.error x + S.realize b _ _ T)) -
        ∑ i, lam i • (L'.realize _ _ (R.p i x) - L.realize _ _ (R.p i x)) +
        ∑ i, c i • (L'.realize _ _ (R.p i x) - S.realize b _ _ (R.p i x)) := by
    simp only [Lifts.errRet, T2, Pi.sub_apply, sub_smul, smul_sub, Finset.sum_sub_distrib,
      map_add, map_sum, map_smul]
    abel
  have := add_mem (add_mem (_root_.sub_mem hmem hlam) hcS) hclass
  rwa [← halg, sub_add_cancel] at this

variable (b) in
/-- Successive correction: lifts and retained coefficients with errors in `J^{n+3}`. -/
theorem exists_lifts_errRet_mem (R : S.Retained) (hR : R.Spans b) :
    ∀ n : ℕ, ∃ (L : S.Lifts b) (lam : R.I → k), ∀ x, L.errRet R lam x ∈ S.radPow (n + 3) _ _ := by
  intro n
  induction n with
  | zero =>
    refine ⟨Lifts.ofRep, 0, fun x ↦ ?_⟩
    simp only [Lifts.errRet, Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero]
    exact Lifts.ofRep.error_mem_three x
  | succ n ih =>
    obtain ⟨L, lam, hL⟩ := ih
    exact Lifts.exists_retained_correction b R hR (m := n + 2) (by omega) L lam hL

variable (b) in
/-- The process terminates: lifts satisfying `r_v = Σ_i λ_i (p_i)_v` exactly. -/
theorem exists_lifts_errRet_eq_zero (R : S.Retained) (hR : R.Spans b) :
    ∃ (L : S.Lifts b) (lam : R.I → k), ∀ x, L.errRet R lam x = 0 := by
  obtain ⟨N, hN⟩ := S.exists_radPow_eq_bot
  obtain ⟨L, lam, hL⟩ := S.exists_lifts_errRet_mem b R hR N
  refine ⟨L, lam, fun x ↦ ?_⟩
  have := S.radPow_anti (show N ≤ N + 3 by omega) _ _ (hL x)
  rwa [hN, Submodule.mem_bot] at this

/-! ### The presentation -/

open FlatPert

variable (b)

/-- The retained perturbation `f_v = Σ_i λ_i (p_i)_v` of the mesh relations. -/
def Retained.pert (R : S.Retained) (lam : R.I → k) :
    ∀ x (t : (meshPres (S.arCoefficients b)).T x),
      Hm k ((meshPres (S.arCoefficients b)).src x t) x :=
  fun x t ↦ ∑ i, lam i • R.p i ⟨x, t.2⟩

theorem Retained.pert_mem (R : S.Retained) (lam : R.I → k) :
    ∀ x t, R.pert b lam x t ∈ geSpan k ((meshPres (S.arCoefficients b)).deg x t + 1)
      ((meshPres (S.arCoefficients b)).src x t) x := fun x t ↦
  Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (geSpan_anti (R.three i) _ _ (degreePart_le_geSpan _ _ _ (R.hom i ⟨x, t.2⟩)))

variable {b}

theorem Lifts.realize_geSpan (L : S.Lifts b) {d : ℕ} {x y : S.ARVertex}
    {g : Hm k x y} (hg : g ∈ geSpan k d x y) : L.realize x y g ∈ S.radPow d _ _ := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    rw [Lifts.realize_path]
    exact S.radPow_anti hp _ _ (L.pathMap_mem p)
  | zero => simp
  | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

variable (R : S.Retained) (lam : R.I → k) (N : ℕ)

/-- The ideal `(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)`. -/
abbrev idealRet : IdealFam k S.ARVertex :=
  idealB (meshPres (S.arCoefficients b)) (R.pert b lam) (R.pert_mem b lam) N

theorem Lifts.realize_eq_zero_of_memRet (L : S.Lifts b) (hL : ∀ x, L.errRet R lam x = 0)
    (hN : ∀ X Y : S.Ind, S.radPow N X Y = ⊥) {x y : S.ARVertex} {G : Hm k x y}
    (hG : G ∈ (idealRet R lam N (b := b)).I x y) : L.realize x y G = 0 := by
  suffices h : (idealRet R lam N (b := b)).I x y ≤ LinearMap.ker (L.realize x y) from h hG
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨z, t, u, v, rfl⟩
    have e : L.realize _ _ (rf (meshPres (S.arCoefficients b)) (R.pert b lam) z t) =
        L.errRet R lam ⟨z, t.2⟩ := by
      simp only [rf, map_sub, Retained.pert, map_sum, map_smul]
      rfl
    rw [SetLike.mem_coe, LinearMap.mem_ker, L.realize_comp, L.realize_comp, e, hL, zero_comp,
      comp_zero]
  · rintro _ ⟨q, hq, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Lifts.realize_path]
    have := S.radPow_anti (show N ≤ q.length by omega) _ _ (L.pathMap_mem q)
    rwa [hN, Submodule.mem_bot] at this

/-- Homogeneous contextual mesh relations lie in the perturbed ideal modulo `𝔪^{n+1}`. -/
theorem hctx_le_ret (n : ℕ) (x y : S.ARVertex) :
    hctx (meshPres (S.arCoefficients b)) n x y ≤
      (idealRet R lam N (b := b)).I x y ⊔ geSpan k (n + 1) x y := by
  rw [hctx, Submodule.span_le]
  rintro _ ⟨z, t, u, v, hdeg, rfl⟩
  have h2 : (meshPres (S.arCoefficients b)).deg z t = 2 := rfl
  have e : LinearPaths.path (k := k) u ≫ (meshPres (S.arCoefficients b)).r z t ≫
      LinearPaths.path v =
      LinearPaths.path u ≫ rf (meshPres (S.arCoefficients b)) (R.pert b lam) z t ≫
        LinearPaths.path v + LinearPaths.path u ≫ R.pert b lam z t ≫ LinearPaths.path v := by
    simp [rf, Preadditive.sub_comp, Preadditive.comp_sub]
  rw [SetLike.mem_coe, e]
  refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left
    (ctx_mem (meshPres (S.arCoefficients b)) _ t _ _))) (Submodule.mem_sup_right ?_)
  have := path_comp_geSpan u v (R.pert_mem b lam z t)
  exact geSpan_anti (by rw [h2] at hdeg ⊢; omega) _ _ this

/-- **Injectivity**: a morphism of `kQ` realized to zero lies in the perturbed ideal. -/
theorem Lifts.mem_of_realize_eq_zero (L : S.Lifts b) (hL : ∀ x, L.errRet R lam x = 0)
    (hN : ∀ X Y : S.Ind, S.radPow N X Y = ⊥) {x y : S.ARVertex} {G : Hm k x y}
    (hG : L.realize x y G = 0) : G ∈ (idealRet R lam N (b := b)).I x y := by
  classical
  set IB := idealRet R lam N (b := b)
  have key : ∀ n (G : Hm k x y), L.realize x y G = 0 → G ∈ IB.I x y ⊔ geSpan k n x y := by
    intro n
    induction n with
    | zero => intro G _; exact Submodule.mem_sup_right (mem_geSpan_zero G)
    | succ n ih =>
      intro G hG
      obtain ⟨i, hi, h, hh, rfl⟩ := Submodule.mem_sup.1 (ih G hG)
      have hrh : L.realize x y h = 0 := by
        rw [map_add, L.realize_eq_zero_of_memRet R lam N hL hN hi, zero_add] at hG
        exact hG
      have hh' := sub_proj_mem_geSpan hh
      have hL1 : L.realize x y (LinearPaths.proj n x y h) ∈ S.radPow (n + 1) _ _ := by
        have e : L.realize x y (LinearPaths.proj n x y h) =
            -L.realize x y (h - LinearPaths.proj n x y h) := by
          rw [map_sub, hrh]; abel
        rw [e]
        exact neg_mem (L.realize_geSpan hh')
      have hS : S.realize b x y (LinearPaths.proj n x y h) ∈ S.radPow (n + 1) _ _ := by
        have := _root_.sub_mem hL1 (L.realize_sub_mem (LinearPaths.proj_mem h))
        rwa [sub_sub_cancel] at this
      have hmesh := S.mem_meshIdeal_of_realize_mem b n (LinearPaths.proj_mem h) hS
      have hctxm : LinearPaths.proj n x y h ∈
          ctxSpan (meshPres (S.arCoefficients b)) (meshPres (S.arCoefficients b)).r x y := by
        rw [ctxSpan_meshPres]; exact hmesh
      have hhc := proj_ctx (meshPres (S.arCoefficients b)) n hctxm
      rw [LinearPaths.proj_of_mem (LinearPaths.proj_mem h), if_pos rfl] at hhc
      obtain ⟨i', hi', e', he', hsum⟩ := Submodule.mem_sup.1 (hctx_le_ret R lam N n x y hhc)
      have : i + h = (i + i') + (e' + (h - LinearPaths.proj n x y h)) := by
        rw [← add_assoc, add_assoc i, hsum]; abel
      rw [this]
      exact add_mem (Submodule.mem_sup_left (add_mem hi hi'))
        (Submodule.mem_sup_right (add_mem he' hh'))
  obtain ⟨i, hi, e, he, rfl⟩ := Submodule.mem_sup.1 (key (N + 1) G hG)
  exact add_mem hi (Submodule.mem_sup_right he)

variable (b) in
/-- **Proposition 12.2** for `E = ind(mod A)` filtered by the radical powers, `C = k(Γ_A)` and
the identification of Proposition 2.6(3): given retained tuples whose classes span the cokernels
of the derivatives, there are coefficients `λ` and arrow lifts realizing
`kQ/(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v) ≅ ind(mod A)` — the realization is surjective with exactly
this kernel — and inducing the prescribed identification on every radical layer. -/
theorem normalForm (hR : R.Spans b) (hN : ∀ X Y : S.Ind, S.radPow N X Y = ⊥) :
    ∃ (lam : R.I → k) (L : S.Lifts b),
      (∀ x, L.error x = ∑ i, lam i • L.realize _ _ (R.p i x)) ∧
      (∀ (x y : S.ARVertex) (G : Hm k x y),
        L.realize x y G = 0 ↔ G ∈ (idealRet R lam N (b := b)).I x y) ∧
      (∀ (x y : S.ARVertex) (f : S.label x ⟶ S.label y), ∃ G, L.realize x y G = f) ∧
      ∀ (d : ℕ) (x y : S.ARVertex) {F : Hm k x y},
        F ∈ LinearPaths.degreePart (k := k) d x y →
          L.realize x y F - S.realize b x y F ∈ S.radPow (d + 1) _ _ := by
  obtain ⟨L, lam, hL⟩ := S.exists_lifts_errRet_eq_zero b R hR
  refine ⟨lam, L, fun x ↦ sub_eq_zero.1 (hL x), fun x y G ↦
    ⟨L.mem_of_realize_eq_zero R lam N hL hN, L.realize_eq_zero_of_memRet R lam N hL hN⟩,
    fun x y f ↦ L.exists_realize_eq f, fun d x y F hF ↦ L.realize_sub_mem hF⟩

end IndSkeleton

end MultiplicativeBasisDeformations
