import MultiplicativeBasisDeformations.Refinements.LiftedCompleteness
import MultiplicativeBasisDeformations.Refinements.LiftedRadical
import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows
import MultiplicativeBasisDeformations.Foundations.Char2Basic

/-!
# Corollary 12.1: the radical grading of `ind(mod B)` is `C`

`deformation-refinements.tex`: "The Hom normalization makes the `M_i^B` indecomposable and
pairwise nonisomorphic. Proposition 6.5(3) identifies their categorical radical grading with `C`."

Formalization. The hypotheses of Proposition 6.5(3) hold for the evaluated modules of `A₀`
(`liftHyp`, and the graded Hom category is generated in degree one, `hgen`), so the `q`th power
of the categorical radical of the lifted modules is the filtration order `≥ q`
(`mem_radPow_lifted`). Leading terms identify `rad^q / rad^{q+1}` with the degree-`q` part of
`C` (`leadL`: surjective, kernel `rad^{q+1}`), compatibly with composition (`leadC_comp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {B : Type u} [Ring B] [Algebra k B] {P : PosFiltration (lenA0 D hfin) B}
  (Ls : Lifts D hfin P) (Vx : LenGrading.Vertices (lenA0 D hfin)) (J : D.InjData) (h1 : DegOne D)

/-! ### The hypotheses of Proposition 6.5(3) -/

theorem rs_zero' {X Y : V} : rs D (0 : obj c X ⟶ obj c Y) = 0 := by
  rw [← sub_self (0 : obj c X ⟶ obj c Y), rs_sub, sub_self]

theorem rs_isGrHom {X Y : V} {r : ℕ} {φ : obj c X ⟶ obj c Y} (hφ : φ ∈ degreePart c r X Y) :
    IsGrHom (MM := gmodEv D hfin) X Y r (rs D φ) :=
  ⟨fun m a ↦ rs_act φ m a, fun _ _ hm ↦ repMap_isHom hfin hφ hm⟩

theorem exists_rs_of_isGrHom {X Y : V} {r : ℕ} {f : Rep D.F0 (meshFam Q c X) →ₗ[k]
    Rep D.F0 (meshFam Q c Y)} (hf : IsGrHom (MM := gmodEv D hfin) X Y r f) :
    ∃ φ ∈ degreePart c r X Y, f = rs D φ := by
  obtain ⟨φ, hφ⟩ := exists_repMap D f hf.1
  refine ⟨φ, mem_degreePart_of_repMap D hfin fun p m hm ↦ ?_, hφ⟩
  rw [← hφ]
  exact hf.2 p m hm

include J h1 in
theorem liftHyp : LiftHyp (gmodEv D hfin) where
  neg i j r hr f hf := hneg i j r hr f hf.1 hf.2
  off i j hij f hf := by
    obtain ⟨φ, hφ, rfl⟩ := exists_rs_of_isGrHom (r := 0) (by simpa using hf)
    rw [degreePart_zero_ne hij hφ, rs_zero']
  diag i f hf := by
    obtain ⟨φ, hφ, rfl⟩ := exists_rs_of_isGrHom (r := 0) (by simpa using hf)
    obtain ⟨t, rfl⟩ := degreePart_zero_eq c hφ
    exact ⟨t, by rw [rs_smul, rs_id]⟩
  ext i j r t ht := extVanish_ev D hfin J h1 0 i j _ (Or.inr (by push_cast; omega))
  nontriv i := nontrivial_rep i

theorem rs_mem_grPow : ∀ (n : ℕ) (X Y : V) (φ : obj c X ⟶ obj c Y),
    φ ∈ degreePart c (n + 1) X Y → rs D φ ∈ grPow (MM := gmodEv D hfin) n X Y := by
  intro n
  induction n with
  | zero =>
    intro X Y φ hφ
    exact rs_isGrHom (by simpa using hφ)
  | succ n ih =>
    intro X Y φ hφ
    rw [degreePart_eq_span] at hφ
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      cases p with
      | nil => simp at hp
      | cons p' a =>
        rw [Quiver.Path.length_cons] at hp
        rw [pathMor_cons, ← rs_comp]
        refine Submodule.subset_span ⟨_, rs D (pathMor c p'), rs D (arrowMor c a),
          ih _ _ _ ?_, rs_isGrHom ?_, rfl⟩
        · have := pathMor_mem_degreePart c p'; rwa [show p'.length = n + 1 by omega] at this
        · have := pathMor_mem_degreePart c (Quiver.Hom.toPath a)
          rwa [pathMor_toPath] at this
    | zero => rw [rs_zero']; exact Submodule.zero_mem _
    | add f g _ _ hf hg => rw [rs_add]; exact Submodule.add_mem _ hf hg
    | smul t f _ hf => rw [rs_smul]; exact Submodule.smul_mem _ t hf

theorem hgen (n : ℕ) (X Y : V) (f : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y))
    (hf : IsGrHom (MM := gmodEv D hfin) X Y (n + 1 : ℕ) f) :
    f ∈ grPow (MM := gmodEv D hfin) n X Y := by
  obtain ⟨φ, hφ, rfl⟩ := exists_rs_of_isGrHom hf
  exact rs_mem_grPow n X Y φ hφ

include Vx J h1 in
/-- **The radical powers of `ind(mod B)` are the filtration orders** (Proposition 6.5(3)). -/
theorem mem_radPow_lifted (q : ℕ) {X Y : V} (g : FB Ls X ⟶ FB Ls Y) :
    toLin g ∈ radPow Ls.L q X Y ↔ g ∈ filB Ls X Y q := by
  rw [mem_radPow_iff Ls.L (P.nonempty_split Vx) (liftHyp J h1) hgen]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun m b ↦ toLin_act g m b, h⟩⟩

/-! ### Leading terms -/

variable {X Y Z : V}

include Vx in
theorem exists_lead' (r : ℕ) (f : filB Ls X Y r) :
    ∃ φ : obj c X ⟶ obj c Y, φ ∈ degreePart c r X Y ∧
      ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f.1) = rs D φ :=
  exists_lead Ls Vx r f.1 f.2

/-- **The leading term** of a map of order `≥ r`, a morphism of `C` of degree `r`. -/
def leadC (r : ℕ) (f : filB Ls X Y r) : degreePart c r X Y :=
  ⟨(exists_lead' Ls Vx r f).choose, (exists_lead' Ls Vx r f).choose_spec.1⟩

theorem rs_leadC (r : ℕ) (f : filB Ls X Y r) :
    rs D (leadC Ls Vx r f).1 = ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f.1) :=
  (exists_lead' Ls Vx r f).choose_spec.2.symm

theorem leadC_eq (r : ℕ) (f : filB Ls X Y r) {φ : obj c X ⟶ obj c Y}
    (h : ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f.1) = rs D φ) :
    (leadC Ls Vx r f).1 = φ :=
  rs_inj (by rw [rs_leadC, h])

/-- The leading-term map `rad^r(M_X^B, M_Y^B) → C_r(X, Y)`. -/
def leadL (r : ℕ) : filB Ls X Y r →ₗ[k] degreePart c r X Y where
  toFun := leadC Ls Vx r
  map_add' f g := Subtype.ext (leadC_eq Ls Vx r _ (by
    simp only [Submodule.coe_add, toLin_add, comp_add']
    rw [rs_add, rs_leadC, rs_leadC]))
  map_smul' t f := Subtype.ext (leadC_eq Ls Vx r _ (by
    simp only [Submodule.coe_smul, toLin_smul, comp_smul]
    rw [RingHom.id_apply, rs_smul, rs_leadC]))

include J h1 in
theorem leadL_surjective (r : ℕ) : Function.Surjective (leadL Ls Vx (X := X) (Y := Y) r) := by
  intro φ
  obtain ⟨g, hg, hord, hlead⟩ := fLift_map Vx (Ls.L X) (Ls.L Y) r (rs D φ.1) (rs_act φ.1)
    (fun p m hm ↦ repMap_isHom hfin φ.2 hm)
    (fun t _ ↦ extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega)))
  exact ⟨⟨ofLin Ls g hg, hord⟩, Subtype.ext (leadC_eq Ls Vx r _ hlead)⟩

include J h1 in
theorem leadL_eq_zero_iff (r : ℕ) (f : filB Ls X Y r) :
    leadL Ls Vx r f = 0 ↔ f.1 ∈ filB Ls X Y (r + 1) := by
  have := (fLift_gr_hom Vx (Ls.L X) (Ls.L Y) r (fun t _ ↦
    extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega)))).1 (toLin f.1) f.2
  have e : leadL Ls Vx r f = 0 ↔
      ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f.1) = 0 := by
    constructor
    · intro h
      rw [← rs_leadC Ls Vx]
      change rs D (leadL Ls Vx r f).1 = 0
      rw [h]; exact rs_zero'
    · intro h
      exact Subtype.ext (leadC_eq Ls Vx r f (h.trans rs_zero'.symm))
  rw [e]
  constructor
  · intro hf
    change OrderGe _ _ _ _
    exact_mod_cast this.1 hf
  · intro hf
    change OrderGe _ _ _ _ at hf
    exact this.2 (by exact_mod_cast hf)

theorem comp_mem_filB {r s : ℕ} {f : FB Ls X ⟶ FB Ls Y} {g : FB Ls Y ⟶ FB Ls Z}
    (hf : f ∈ filB Ls X Y r) (hg : g ∈ filB Ls Y Z s) : f ≫ g ∈ filB Ls X Z (r + s) := by
  change OrderGe _ _ _ (toLin (f ≫ g))
  rw [toLin_comp]
  have := OrderGe.comp hf hg
  exact_mod_cast this

/-- **Leading terms are multiplicative**: `gr_J ind(mod B) ≅ C` as categories. -/
theorem leadC_comp {r s : ℕ} (f : filB Ls X Y r) (g : filB Ls Y Z s) :
    (leadC Ls Vx (r + s) ⟨f.1 ≫ g.1, comp_mem_filB Ls f.2 g.2⟩).1 =
      (leadC Ls Vx r f).1 ≫ (leadC Ls Vx s g).1 := by
  apply leadC_eq
  have := comp_comp_lead (MM := gmodEv D hfin X) (NN := gmodEv D hfin Y) (XX := gmodEv D hfin Z)
    f.2 g.2
  simp only [toLin_comp]
  rw [← rs_comp, rs_leadC, rs_leadC, ← this]
  push_cast; rfl

/-! ### Corollary 12.1 -/

variable (P) in
include J h1 in
/-- **Corollary 12.1** (`cor:positive-deformation-completeness`) for mesh data whose positive
degrees are radical. Every positive filtered deformation `B` of `A₀` is representation-finite;
the lifted modules `M_x^B` (which exist, Proposition 6.5) are indecomposable, pairwise
nonisomorphic and exhaust the indecomposable `B`-modules; the `q`th radical power of
`ind(mod B)` is the filtration order `≥ q`, and leading terms identify `rad^q / rad^{q+1}` with
`C_q`, compatibly with composition: `gr_J ind(mod B) ≅ C` with these labels. -/
theorem positiveDeformationCompleteness
    (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y) :
    Nonempty (Lifts D hfin P) ∧ IsRepresentationFinite k B ∧
    ∀ Ls : Lifts D hfin P,
      (∀ x, IsFiniteIndecomposable k B (FB Ls x)) ∧
      (∀ x y, Nonempty (FB Ls x ≅ FB Ls y) → x = y) ∧
      (∀ M : RightModuleCat B, IsFiniteIndecomposable k B M → ∃ x, Nonempty (M ≅ FB Ls x)) ∧
      (∀ (q : ℕ) (x y : V) (g : FB Ls x ⟶ FB Ls y),
        toLin g ∈ radPow Ls.L q x y ↔ g ∈ filB Ls x y q) ∧
      (∀ (r : ℕ) (x y : V), Function.Surjective (leadL Ls (vxIdem D hfin) (X := x) (Y := y) r) ∧
        ∀ f, leadL Ls (vxIdem D hfin) r f = 0 ↔ f.1 ∈ filB Ls x y (r + 1)) ∧
      ∀ (r s : ℕ) (x y z : V) (f : filB Ls x y r) (g : filB Ls y z s),
        (leadC Ls (vxIdem D hfin) (r + s) ⟨f.1 ≫ g.1, comp_mem_filB Ls f.2 g.2⟩).1 =
          (leadC Ls (vxIdem D hfin) r f).1 ≫ (leadC Ls (vxIdem D hfin) s g).1 := by
  obtain ⟨S, hS⟩ := PosFiltration.exists_split_left P (vxIdem D hfin)
  have hL : Nonempty (Lifts D hfin P) := nonempty_lifts D hfin P J h1 (vxIdem D hfin)
  refine ⟨hL, isRepresentationFinite_B hL.some S hS (vxIdem D hfin) J h1 hrad, fun Ls ↦
    ⟨isFiniteIndecomposable_FB Ls (vxIdem D hfin), fun x y h ↦ eq_of_iso_FB Ls (vxIdem D hfin) h.some,
      exists_iso_FB Ls S hS (vxIdem D hfin) J h1 hrad,
      fun q x y g ↦ mem_radPow_lifted Ls (vxIdem D hfin) J h1 q g,
      fun r x y ↦ ⟨leadL_surjective Ls (vxIdem D hfin) J h1 r,
        leadL_eq_zero_iff Ls (vxIdem D hfin) J h1 r⟩,
      fun r s x y z f g ↦ leadC_comp Ls (vxIdem D hfin) f g⟩⟩

end MeshWalk

namespace IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- In `k(Γ_A)`, morphisms of positive degree are radical. -/
theorem arHrad (x y : S.ARVertex) (d : ℕ) (hd : 1 ≤ d)
    (f : S.meshObj b x ⟶ S.meshObj b y)
    (hf : f ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) d x y) :
    f ∈ (S.arLocal b).rad x y := by
  rw [ScalarMeshCategory.degreePart_eq_span] at hf
  refine Submodule.span_le.2 ?_ hf
  rintro _ ⟨p, hp, rfl⟩
  exact ScalarMeshCategory.pathMor_mem_radN _ p (by omega)

theorem finiteDimensional_meshFam (x y : S.ARVertex) : FiniteDimensional k
    (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
      MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
  S.finiteDimensional_meshHom b x y

attribute [local instance] finiteDimensional_meshFam

open MeshWalk in
/-- **Corollary 12.1** for the algebra `A₀` of a basic representation-finite algebra `A`
(Construction 2.8): every positive filtered deformation `B` of `A₀` is representation-finite,
the lifted modules `M_x^B` are a skeleton of `ind(mod B)`, and `gr_J ind(mod B) ≅ k(Γ_A)` with
these labels. -/
theorem positiveDeformationCompleteness_ar {B : Type w} [Ring B] [Algebra k B]
    (P : PosFiltration (lenA0 (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y)) B) :
    Nonempty (Lifts (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y) P) ∧
    IsRepresentationFinite k B ∧
    ∀ Ls : Lifts (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y) P,
      (∀ x, IsFiniteIndecomposable k B (FB Ls x)) ∧
      (∀ x y, Nonempty (FB Ls x ≅ FB Ls y) → x = y) ∧
      (∀ M : RightModuleCat B, IsFiniteIndecomposable k B M → ∃ x, Nonempty (M ≅ FB Ls x)) ∧
      (∀ (q : ℕ) (x y : S.ARVertex) (g : FB Ls x ⟶ FB Ls y),
        toLin g ∈ PosFiltration.radPow Ls.L q x y ↔ g ∈ filB Ls x y q) ∧
      (∀ (r : ℕ) (x y : S.ARVertex),
        Function.Surjective (leadL Ls (vxIdem (S.arMeshData b)
          (fun x y ↦ S.finiteDimensional_meshHom b x y)) (X := x) (Y := y) r) ∧
        ∀ f, leadL Ls (vxIdem (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y)) r f
          = 0 ↔ f.1 ∈ filB Ls x y (r + 1)) ∧
      ∀ (r s : ℕ) (x y z : S.ARVertex) (f : filB Ls x y r) (g : filB Ls y z s),
        (leadC Ls (vxIdem (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y)) (r + s)
            ⟨f.1 ≫ g.1, comp_mem_filB Ls f.2 g.2⟩).1 =
          (leadC Ls (vxIdem (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y))
            r f).1 ≫
          (leadC Ls (vxIdem (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y))
            s g).1 :=
  positiveDeformationCompleteness P (S.arInjData b) (S.arDegOne b) (S.arHrad b)

end IndSkeleton

end MultiplicativeBasisDeformations
