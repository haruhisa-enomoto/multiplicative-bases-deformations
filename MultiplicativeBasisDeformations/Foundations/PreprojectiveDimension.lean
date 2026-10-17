import MultiplicativeBasisDeformations.Foundations.TreeRepetition
import MultiplicativeBasisDeformations.Foundations.SectionalTree
import Mathlib.Data.Set.Finite.List

/-!
# The dimension inequality for `Π(Δ)`

Proof of Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex`):
"For each vertex `i` of `Δ`, put `P_i = e_i Π(Δ)`, `n_i = dim_k P_i` ... There is
an exact sequence `P_i → ⊕_{j∼i} P_j → P_i → S_i → 0`. The map onto `rad P_i`
prefixes outgoing arrows. To identify its kernel, express a relation among the
prefixed paths in the free path algebra as a sum of contextual defining
relations. A nonempty initial context gives zero in the coefficient module after
its first arrow. An empty initial context gives a right multiple of the single
relation at `i`. These are exactly the images of the first map. ... dimensions
give `2n_i - ∑_{j∼i} n_j = 1 + dim K_i > 0`."

We work with `S i`, the formal combinations of all paths starting at `i`, and
its subspace `I i` spanned by the contextual relations starting at `i`, so that
`P_i = S i / I i`. Only the inequality `∑_{j∼i} n_j ≤ 2 n_i - 1` is used later.

This file: first-arrow decompositions of paths.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe v w

namespace Quiver.Path

variable {V : Type v} [Quiver.{w} V]

/-- A path is empty or begins with an arrow. -/
theorem nil_or_first {i : V} : ∀ {v : V} (u : Quiver.Path i v),
    (∃ h : i = v, u = h ▸ Quiver.Path.nil) ∨
      ∃ (j : V) (a : i ⟶ j) (u' : Quiver.Path j v), u = a.toPath.comp u' := by
  intro v u
  by_cases hl : u.length = 0
  · left
    obtain rfl := Quiver.Path.eq_of_length_zero u hl
    exact ⟨rfl, (Quiver.Path.length_eq_zero_iff u).1 hl⟩
  · right
    obtain ⟨j, p₁, p₂, rfl, h1⟩ := u.exists_eq_comp_of_le_length (n := 1) (by omega)
    cases p₁ with
    | nil => simp at h1
    | cons p a =>
        cases p with
        | nil => exact ⟨_, a, p₂, rfl⟩
        | cons p b => simp at h1

theorem toPath_comp_vertices {i j v : V} (a : i ⟶ j) (u : Quiver.Path j v) :
    (a.toPath.comp u).vertices = i :: u.vertices := by
  rw [Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath]
  rfl

/-- The first arrow and the rest are determined by the path. -/
theorem toPath_comp_inj {i j j' v : V} (a : i ⟶ j) (a' : i ⟶ j') (u : Quiver.Path j v)
    (u' : Quiver.Path j' v) (h : a.toPath.comp u = a'.toPath.comp u') :
    (⟨j, a, u⟩ : Σ j, (i ⟶ j) × Quiver.Path j v) = ⟨j', a', u'⟩ := by
  have hl := congrArg Quiver.Path.arrowList h
  simp only [Quiver.Path.arrowList_comp, Quiver.Path.arrowList_toPath, List.singleton_append,
    List.cons.injEq] at hl
  obtain ⟨h1, h2⟩ := hl
  cases h1
  have := Quiver.Path.arrowList_injective u u' h2
  cases this
  rfl

end Quiver.Path

namespace MultiplicativeBasisDeformations

universe u

namespace OrientedTree

open RelSystem

variable {D : Type v} (T : OrientedTree D) (k : Type u) [Field k]

/-- Formal combinations of the paths of `Δ̄` starting at `i`. -/
abbrev Sp (i : T.Dbl) := StarSpace (k := k) i

instance instAddCommGroupSp (i : T.Dbl) : AddCommGroup (T.Sp k i) := Finsupp.instAddCommGroup

/-- The contextual relations of `Π(Δ)` starting at `i`; `P_i = Sp i / Ist i`. -/
def Ist [DecidableRel T.orient] [Fintype D] [DecidableEq D] (i : T.Dbl) : Submodule k (T.Sp k i) :=
  Submodule.span k {F | ∃ (Y : T.Dbl) (f : LinearPaths.obj (k := k) i ⟶ LinearPaths.obj Y),
    f ∈ (T.preproj k).ideal _ _ ∧ F = toStar Y f}

variable {T k}

/-- Prefixing an arrow `a : i → j`. -/
def pre {i j : T.Dbl} (a : i ⟶ j) : T.Sp k j →ₗ[k] T.Sp k i :=
  Finsupp.lmapDomain k k fun e : Quiver.PathStar j ↦
    (⟨e.1, a.toPath.comp e.2⟩ : Quiver.PathStar i)

theorem pre_toStar {i j : T.Dbl} (a : i ⟶ j) {Y : T.Dbl}
    (f : LinearPaths.obj (k := k) j ⟶ LinearPaths.obj Y) :
    pre a (toStar Y f) = toStar Y (LinearPaths.arrow a ≫ f) := by
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, Preadditive.comp_add, map_add]
  | hsingle p c =>
      rw [map_smul, map_smul, Linear.comp_smul, map_smul, toStar_path, LinearPaths.arrow,
        LinearPaths.path_comp_path, toStar_path]
      simp [pre]

variable [DecidableRel T.orient] [Fintype D] [DecidableEq D]

theorem pre_mem {i j : T.Dbl} (a : i ⟶ j) {F : T.Sp k j} (hF : F ∈ T.Ist k j) :
    pre a F ∈ T.Ist k i := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨Y, f, hf, rfl⟩ := hF
      rw [pre_toStar]
      exact Submodule.subset_span ⟨Y, _, (T.preproj k).comp_mem_ideal _ hf, rfl⟩
  | zero => simp
  | add F G _ _ hF hG => rw [map_add]; exact add_mem hF hG
  | smul c F _ hF => rw [map_smul]; exact Submodule.smul_mem _ c hF

/-- An arrow out of `i`, with its target. -/
abbrev OutArrow (T : OrientedTree D) (i : T.Dbl) := Σ y : T.Dbl, i ⟶ y

/-- The reverse of an arrow. -/
def rev {i : T.Dbl} (e : T.OutArrow i) : e.1 ⟶ i := ⟨e.2.down.symm⟩

open Classical in
/-- Removing the first arrow `e`: a left inverse of `pre e.2`. -/
def strip {i : T.Dbl} (e : T.OutArrow i) : T.Sp k i →ₗ[k] T.Sp k e.1 :=
  Finsupp.linearCombination k fun p : Quiver.PathStar i ↦
    if h : ∃ q : Quiver.Path e.1 p.1, p.2 = e.2.toPath.comp q then
      Finsupp.single ⟨p.1, h.choose⟩ 1 else 0

theorem strip_pre_single {i : T.Dbl} (e e' : T.OutArrow i) (p : Quiver.PathStar e'.1) (c : k) :
    strip e (pre e'.2 (Finsupp.single p c)) =
      if h : e' = e then h ▸ Finsupp.single p c else 0 := by
  classical
  obtain ⟨y, a⟩ := e
  obtain ⟨y', a'⟩ := e'
  obtain ⟨z, p⟩ := p
  simp only [pre, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, strip,
    Finsupp.linearCombination_single]
  by_cases h : (⟨y', a'⟩ : T.OutArrow i) = ⟨y, a⟩
  · cases h
    rw [dif_pos ⟨p, rfl⟩, dif_pos rfl]
    have hq := (⟨p, rfl⟩ : ∃ q : Quiver.Path y z, a.toPath.comp p = a.toPath.comp q).choose_spec
    have := Quiver.Path.toPath_comp_inj _ _ _ _ hq
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at this
    rw [← this]
    simp
  · rw [dif_neg h, dif_neg, smul_zero]
    rintro ⟨q, hq⟩
    have := Quiver.Path.toPath_comp_inj _ _ _ _ hq
    apply h
    cases this
    rfl

theorem strip_pre {i : T.Dbl} (e e' : T.OutArrow i) (X : T.Sp k e'.1) :
    strip e (pre e'.2 X) = if h : e' = e then h ▸ X else 0 := by
  induction X using Finsupp.induction_linear with
  | zero => split_ifs with h <;> [subst h; skip] <;> simp
  | add X Y hX hY =>
      rw [map_add, map_add, hX, hY]
      split_ifs with h
      · subst h; rfl
      · simp
  | single p c => exact strip_pre_single e e' p c

/-- Prefixing the outgoing arrows: `⊕_{j∼i} P_j → P_i`, on formal paths. -/
def gmap (i : T.Dbl) : (∀ e : T.OutArrow i, T.Sp k e.1) →ₗ[k] T.Sp k i :=
  ∑ e : T.OutArrow i, (pre e.2).comp (LinearMap.proj e)

theorem strip_gmap {i : T.Dbl} (e : T.OutArrow i) (X : ∀ e : T.OutArrow i, T.Sp k e.1) :
    strip e (gmap i X) = X e := by
  classical
  simp only [gmap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, strip_pre]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ he'; rw [dif_neg he']
  · simp

theorem gmap_injective (i : T.Dbl) : Function.Injective (gmap (T := T) (k := k) i) := by
  intro X Y h
  funext e
  rw [← strip_gmap (T := T) (k := k) e X, ← strip_gmap (T := T) (k := k) e Y, h]

theorem gmap_single {i : T.Dbl} (e : T.OutArrow i) (x : T.Sp k e.1) :
    gmap i (Pi.single e x) = pre e.2 x := by
  classical
  simp only [gmap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ he'; rw [Pi.single_eq_of_ne he', map_zero]
  · simp

/-- Prefixing the reversed arrows, with the signs of the relation:
`P_i → ⊕_{j∼i} P_j`. -/
def fmap (i : T.Dbl) : T.Sp k i →ₗ[k] (∀ e : T.OutArrow i, T.Sp k e.1) :=
  LinearMap.pi fun e ↦ ((T.sgn k i e.1 : kˣ) : k) • pre (rev e)

theorem gmap_fmap_toStar {i : T.Dbl} {Y : T.Dbl}
    (f : LinearPaths.obj (k := k) i ⟶ LinearPaths.obj Y) :
    gmap i (fmap i (toStar Y f)) = toStar Y (T.preprojRel k i ≫ f) := by
  simp only [gmap, fmap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.smul_apply, map_smul, pre_toStar,
    preprojRel, Preadditive.sum_comp, map_sum, Linear.smul_comp]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  congr 2
  rw [← Category.assoc, LinearPaths.arrow, LinearPaths.arrow, LinearPaths.path_comp_path]
  rfl

theorem path_nil_cast {a b : T.Dbl} (h : a = b) :
    LinearPaths.path (k := k) (h ▸ (Quiver.Path.nil : Quiver.Path a a)) =
      eqToHom (congrArg _ h) := by
  subst h; rfl

theorem eqToHom_preprojRel {a b : T.Dbl} (h : a = b) :
    eqToHom (congrArg (LinearPaths.obj (k := k)) h) ≫ (T.preproj k).rel b =
      T.preprojRel k a ≫ eqToHom (congrArg _ h) := by
  subst h; simp; rfl

/-- **First-arrow decomposition of the relations**: a relation starting at `i`
is a right multiple of `ρ_i` (empty initial context) plus prefixed relations
(nonempty initial context). -/
theorem exists_decomp {i Y : T.Dbl} {f : LinearPaths.obj (k := k) i ⟶ LinearPaths.obj Y}
    (hf : f ∈ (T.preproj k).ideal _ _) :
    ∃ (W : T.Sp k i) (R : ∀ e : T.OutArrow i, T.Sp k e.1), (∀ e, R e ∈ T.Ist k e.1) ∧
      toStar Y f = gmap i (fmap i W) + gmap i R := by
  classical
  refine (T.preproj k).ideal_induction (P := fun f ↦ ∃ (W : T.Sp k i)
    (R : ∀ e : T.OutArrow i, T.Sp k e.1), (∀ e, R e ∈ T.Ist k e.1) ∧
      toStar Y f = gmap i (fmap i W) + gmap i R) ?_ ?_ ?_ ?_ hf
  · exact ⟨0, 0, fun _ ↦ zero_mem _, by simp⟩
  · rintro f g ⟨W, R, hR, hf⟩ ⟨W', R', hR', hg⟩
    refine ⟨W + W', R + R', fun e ↦ add_mem (hR e) (hR' e), ?_⟩
    rw [map_add, hf, hg, map_add, map_add, map_add]
    abel
  · rintro c f ⟨W, R, hR, hf⟩
    refine ⟨c • W, c • R, fun e ↦ Submodule.smul_mem _ c (hR e), ?_⟩
    rw [map_smul, hf, map_smul, map_smul, map_smul, smul_add]
  · intro ι u w
    rcases Quiver.Path.nil_or_first u with ⟨h, rfl⟩ | ⟨j, a, u', rfl⟩
    · refine ⟨toStar Y (eqToHom (congrArg _ h) ≫ LinearPaths.path w), 0, fun _ ↦ zero_mem _, ?_⟩
      rw [map_zero, add_zero, gmap_fmap_toStar, path_nil_cast, ← Category.assoc,
        ← Category.assoc]
      congr 2
      exact eqToHom_preprojRel h
    · refine ⟨0, Pi.single ⟨j, a⟩ (toStar Y (LinearPaths.path u' ≫ (T.preproj k).rel ι ≫
        LinearPaths.path w)), fun e ↦ ?_, ?_⟩
      · by_cases he : e = ⟨j, a⟩
        · subst he
          rw [Pi.single_eq_same]
          exact Submodule.subset_span ⟨Y, _, (T.preproj k).comp_rel_comp_mem ι _ _, rfl⟩
        · rw [Pi.single_eq_of_ne he]; exact zero_mem _
      · rw [map_zero, map_zero, zero_add, gmap_single, pre_toStar, LinearPaths.arrow,
          ← LinearPaths.path_comp_path]
        simp only [Category.assoc]

theorem exists_decomp_Ist {i : T.Dbl} {F : T.Sp k i} (hF : F ∈ T.Ist k i) :
    ∃ (W : T.Sp k i) (R : ∀ e : T.OutArrow i, T.Sp k e.1), (∀ e, R e ∈ T.Ist k e.1) ∧
      F = gmap i (fmap i W) + gmap i R := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨Y, f, hf, rfl⟩ := hF
      exact exists_decomp hf
  | zero => exact ⟨0, 0, fun _ ↦ zero_mem _, by simp⟩
  | add F G _ _ hF hG =>
      obtain ⟨W, R, hR, rfl⟩ := hF
      obtain ⟨W', R', hR', rfl⟩ := hG
      refine ⟨W + W', R + R', fun e ↦ add_mem (hR e) (hR' e), ?_⟩
      rw [map_add, map_add, map_add]
      abel
  | smul c F _ hF =>
      obtain ⟨W, R, hR, rfl⟩ := hF
      exact ⟨c • W, c • R, fun e ↦ Submodule.smul_mem _ c (hR e), by
        rw [map_smul, map_smul, map_smul, smul_add]⟩

/-- **Exactness at the middle term**, on formal paths. -/
theorem exact_star {i : T.Dbl} (H : ∀ e : T.OutArrow i, T.Sp k e.1)
    (hH : gmap i H ∈ T.Ist k i) :
    ∃ (W : T.Sp k i) (R : ∀ e : T.OutArrow i, T.Sp k e.1), (∀ e, R e ∈ T.Ist k e.1) ∧
      H = fmap i W + R := by
  obtain ⟨W, R, hR, h⟩ := exists_decomp_Ist hH
  refine ⟨W, R, hR, gmap_injective (T := T) (k := k) i ?_⟩
  rw [h, map_add]

variable (T k) in
/-- `P_i = e_i Π(Δ)`. -/
abbrev Pq (i : T.Dbl) := T.Sp k i ⧸ T.Ist k i

/-- `⊕_{j∼i} P_j → P_i`. -/
def gbar (i : T.Dbl) : (∀ e : T.OutArrow i, T.Pq k e.1) →ₗ[k] T.Pq k i :=
  ∑ e : T.OutArrow i, ((T.Ist k e.1).mapQ (T.Ist k i) (pre e.2) (fun _ h ↦ pre_mem e.2 h)).comp
    (LinearMap.proj e)

/-- `P_i → ⊕_{j∼i} P_j`. -/
def fbar (i : T.Dbl) : T.Pq k i →ₗ[k] (∀ e : T.OutArrow i, T.Pq k e.1) :=
  LinearMap.pi fun e ↦ ((T.sgn k i e.1 : kˣ) : k) •
    (T.Ist k i).mapQ (T.Ist k e.1) (pre (rev e)) (fun _ h ↦ pre_mem _ h)

theorem gbar_mk {i : T.Dbl} (H : ∀ e : T.OutArrow i, T.Sp k e.1) :
    gbar i (fun e ↦ Submodule.Quotient.mk (H e)) = Submodule.Quotient.mk (gmap i H) := by
  simp only [gbar, gmap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.mapQ_apply]
  rw [← Submodule.mkQ_apply, map_sum]
  rfl

theorem fbar_mk {i : T.Dbl} (W : T.Sp k i) :
    fbar i (Submodule.Quotient.mk W) = fun e ↦ Submodule.Quotient.mk (fmap i W e) := by
  funext e
  simp [fbar, fmap, Submodule.mapQ_apply]

/-- **Exactness** of `P_i → ⊕_{j∼i} P_j → P_i` at the middle term (one
inclusion, the one used). -/
theorem ker_gbar_le (i : T.Dbl) : LinearMap.ker (gbar (T := T) (k := k) i) ≤
    LinearMap.range (fbar i) := by
  intro x hx
  choose H hH using fun e ↦ Submodule.Quotient.mk_surjective _ (x e)
  have hx' : x = fun e ↦ Submodule.Quotient.mk (H e) := funext fun e ↦ (hH e).symm
  rw [LinearMap.mem_ker, hx', gbar_mk, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨W, R, hR, h⟩ := exact_star H hx
  refine ⟨Submodule.Quotient.mk W, ?_⟩
  rw [fbar_mk, hx']
  funext e
  rw [h, Pi.add_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 (hR e),
    add_zero]

open Classical in
/-- The coefficient of the paths of length zero. -/
def psi0 (i : T.Dbl) : T.Sp k i →ₗ[k] k :=
  Finsupp.linearCombination k fun e : Quiver.PathStar i ↦ if e.2.length = 0 then (1 : k) else 0

theorem psi0_toStar_path {i Y : T.Dbl} (p : Quiver.Path i Y) :
    psi0 (T := T) (k := k) i (toStar Y (LinearPaths.path p)) = if p.length = 0 then 1 else 0 := by
  classical
  rw [toStar_path, psi0, Finsupp.linearCombination_single, one_smul]

theorem psi0_ideal {i Y : T.Dbl} {f : LinearPaths.obj (k := k) i ⟶ LinearPaths.obj Y}
    (hf : f ∈ (T.preproj k).ideal _ _) : psi0 (T := T) (k := k) i (toStar Y f) = 0 := by
  refine (T.preproj k).ideal_induction (P := fun f ↦ psi0 (T := T) (k := k) i (toStar Y f) = 0)
    (by simp) (fun f g hf hg ↦ by rw [map_add, map_add, hf, hg, add_zero])
    (fun c f hf ↦ by rw [map_smul, map_smul, hf, smul_zero]) (fun ι u w ↦ ?_) hf
  change psi0 i (toStar Y (_ ≫ T.preprojRel k _ ≫ _)) = 0
  simp only [preprojRel, Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp,
    Linear.comp_smul, LinearPaths.path_comp_path, map_sum, map_smul, psi0_toStar_path]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [if_neg]
  · simp
  · simp

theorem Ist_le_ker_psi0 (i : T.Dbl) : T.Ist k i ≤ LinearMap.ker (psi0 (T := T) (k := k) i) :=
  Submodule.span_le.2 fun F ⟨Y, f, hf, hF⟩ ↦ by rw [hF]; exact psi0_ideal hf

theorem psi0_pre {i j : T.Dbl} (a : i ⟶ j) (X : T.Sp k j) : psi0 (T := T) (k := k) i (pre a X) = 0 := by
  classical
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X Y hX hY => rw [map_add, map_add, hX, hY, add_zero]
  | single p c =>
      simp only [pre, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, psi0,
        Finsupp.linearCombination_single]
      rw [if_neg]
      · simp
      · simp

theorem finite_short_paths (i : T.Dbl) (N : ℕ) :
    Finite {e : Quiver.PathStar i // e.2.length < N} := by
  haveI : ∀ u v : T.Dbl, Finite (u ⟶ v) := fun _ _ ↦ Finite.of_subsingleton
  haveI : Finite T.Dbl := inferInstanceAs (Finite D)
  haveI : Finite {l : List (Σ u v : T.Dbl, u ⟶ v) // l.length < N} :=
    (List.finite_length_lt (Σ u v : T.Dbl, u ⟶ v) N).to_subtype
  refine Finite.of_injective (β := {l : List (Σ u v : T.Dbl, u ⟶ v) // l.length < N})
    (fun e ↦ ⟨e.1.2.arrowList, by rw [Quiver.Path.length_arrowList]; exact e.2⟩) ?_
  intro e e' h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Quiver.Path.arrowList_injective _ _ h)

/-- With long paths vanishing, `P_i` is finite-dimensional. -/
theorem finiteDimensional_Pq (N : ℕ)
    (hN : ∀ (v Y : T.Dbl) (P : Quiver.Path v Y), N ≤ P.length →
      LinearPaths.path (k := k) P ∈ (T.preproj k).ideal _ _) (i : T.Dbl) :
    FiniteDimensional k (T.Pq k i) := by
  haveI := finite_short_paths (T := T) i N
  let Φ : ({e : Quiver.PathStar i // e.2.length < N} →₀ k) →ₗ[k] T.Pq k i :=
    Finsupp.linearCombination k fun e ↦ Submodule.Quotient.mk (Finsupp.single e.1 1)
  refine Module.Finite.of_surjective Φ ?_
  intro x
  obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction F using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add F G hF hG =>
      obtain ⟨a, ha⟩ := hF
      obtain ⟨b, hb⟩ := hG
      exact ⟨a + b, by rw [map_add, ha, hb, Submodule.Quotient.mk_add]⟩
  | single e c =>
      by_cases he : e.2.length < N
      · refine ⟨Finsupp.single ⟨e, he⟩ c, ?_⟩
        simp only [Φ, Finsupp.linearCombination_single]
        rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      · refine ⟨0, ?_⟩
        rw [map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]
        obtain ⟨Y, P⟩ := e
        have h1 := hN i Y P (not_lt.1 he)
        have : Finsupp.single (⟨Y, P⟩ : Quiver.PathStar i) c =
            c • toStar Y (LinearPaths.path P) := by
          rw [toStar_path, Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨Y, _, h1, rfl⟩)


/-- **The dimension inequality** `∑_{j∼i} n_j ≤ 2 n_i - 1`
(`periodic-mesh-calculations.tex`). -/
theorem sum_finrank_add_one_le (N : ℕ)
    (hN : ∀ (v Y : T.Dbl) (P : Quiver.Path v Y), N ≤ P.length →
      LinearPaths.path (k := k) P ∈ (T.preproj k).ideal _ _) (i : T.Dbl) :
    (∑ e : T.OutArrow i, Module.finrank k (T.Pq k e.1)) + 1 ≤
      2 * Module.finrank k (T.Pq k i) := by
  haveI := fun j ↦ finiteDimensional_Pq (T := T) (k := k) N hN j
  -- the length-zero functional on `P_i`
  let φ := (T.Ist k i).liftQ (psi0 (T := T) (k := k) i) (Ist_le_ker_psi0 i)
  have hφsurj : Function.Surjective φ := by
    intro c
    refine ⟨c • Submodule.Quotient.mk (Finsupp.single ⟨i, Quiver.Path.nil⟩ 1), ?_⟩
    rw [map_smul]
    simp [φ, psi0, Finsupp.linearCombination_single]
  have hφ : Module.finrank k (LinearMap.ker φ) + 1 = Module.finrank k (T.Pq k i) := by
    have := LinearMap.finrank_range_add_finrank_ker (K := k) φ
    rw [LinearMap.range_eq_top.2 hφsurj, finrank_top, Module.finrank_self] at this
    have e : Module.finrank k (T.Pq k i) = Module.finrank k (T.Sp k i ⧸ T.Ist k i) := rfl
    omega
  have hrange : LinearMap.range (gbar (T := T) (k := k) i) ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    choose H hH using fun e ↦ Submodule.Quotient.mk_surjective _ (x e)
    have hx' : x = fun e ↦ Submodule.Quotient.mk (H e) := funext fun e ↦ (hH e).symm
    rw [hx', gbar_mk, LinearMap.mem_ker]
    simp only [φ, Submodule.liftQ_apply, gmap, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, map_sum, psi0_pre, Finset.sum_const_zero]
  have h1 := LinearMap.finrank_range_add_finrank_ker (gbar (T := T) (k := k) i)
  have h2 := Submodule.finrank_mono (ker_gbar_le (T := T) (k := k) i)
  have h3 := LinearMap.finrank_range_le (fbar (T := T) (k := k) i)
  have h4 := Submodule.finrank_mono hrange
  rw [Module.finrank_pi_fintype] at h1
  have h5 : Module.finrank k ↥(gbar (T := T) (k := k) i).ker ≤ Module.finrank k (T.Pq k i) :=
    h2.trans h3
  calc (∑ e : T.OutArrow i, Module.finrank k (T.Pq k e.1)) + 1
      = Module.finrank k ↥(LinearMap.range (gbar (T := T) (k := k) i)) +
          Module.finrank k ↥(LinearMap.ker (gbar (T := T) (k := k) i)) + 1 := by rw [h1]
    _ ≤ Module.finrank k (LinearMap.ker φ) + Module.finrank k (T.Pq k i) + 1 := by
        gcongr
    _ = 2 * Module.finrank k (T.Pq k i) := by rw [← hφ]; ring

end OrientedTree

end MultiplicativeBasisDeformations
