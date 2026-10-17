import MultiplicativeBasisDeformations.Foundations.PathGrading
import Mathlib

/-!
# Lemma 12.3: flat mesh perturbations

`deformation-refinements.tex:165–211` (`lem:flat-mesh-perturbations`). Let `C = kQ/(r₁, …, r_t)`
be finite-dimensional and graded, with homogeneous relations of degree at least two, and assume
that the presentations of the simple modules obtained by splitting each relation according to its
arrows are projective resolutions of length at most two. Choose `N` with `C_d = 0` for `d ≥ N`
and perturbations `f_i` of strictly higher degree, and put
`B = kQ/(𝔪^{N+1}, r₁ − f₁, …, r_t − f_t)`. Then `B` has the dimensions of `C`, every homogeneous
path basis of `C` lifts to a basis of `B`, and the perturbed presentations are again resolutions.

The proof is the source's: exactness of the perturbed presentations at the arrow term (contextual
relations are sorted by their last factor), the dimension identities `ZH = I` and `ZH_B = I + K`,
and the spanning bound `H_B ≤ H`.

Conventions. The source uses right modules and splits relations by their first arrow; we use
the representables `C(−, x)` and split relations by their last arrow, the form in which the
mesh relations and their exact sequences appear in Section 2 (the lemma for one convention is the
lemma for the opposite quiver in the other). Relations are indexed by their target.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace FlatPert

universe u

variable {k : Type u} [CommRing k] {V : Type} [Quiver.{0} V]

variable (k) in
/-- The morphisms `x → y` of the linear path category `kQ`. -/
abbrev Hm (x y : V) := LinearPaths.obj (k := k) x ⟶ LinearPaths.obj (k := k) y

open LinearPaths

theorem path_comp_arrow {x y z : V} (p : Quiver.Path x y) (a : y ⟶ z) :
    path (k := k) p ≫ arrow a = path (p.cons a) := by
  rw [arrow, path_comp_path]; rfl

/-- Composition with an arrow is `mapDomain` along `· .cons a`. -/
theorem comp_arrow {x y z : V} (g : Hm k x y) (a : y ⟶ z) :
    g ≫ arrow a = ofFinsupp (Finsupp.mapDomain (fun p : Quiver.Path x y ↦ p.cons a) (toFinsupp g)) := by
  induction g using induction_on with
  | h0 => simp; rfl
  | hadd f g hf hg => rw [Preadditive.add_comp, hf, hg, toFinsupp_add, Finsupp.mapDomain_add]; rfl
  | hsingle p c =>
    rw [Linear.smul_comp, path_comp_arrow, toFinsupp_smul, toFinsupp_path, Finsupp.mapDomain_smul,
      Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    change c • Finsupp.single (p.cons a) (1 : k) = Finsupp.single (p.cons a) c
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem cons_injective {x y z : V} (a : y ⟶ z) :
    Function.Injective (fun p : Quiver.Path x y ↦ p.cons a) := by
  intro p q h
  simpa using h

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]

/-- **The last-arrow components** `f = f₀ + Σ_a f_a a`. -/
def lastComp {x z : V} (a : Σ y : V, y ⟶ z) : Hm k x z →ₗ[k] Hm k x a.1 :=
  (Finsupp.lcomapDomain (fun p : Quiver.Path x a.1 ↦ p.cons a.2) (cons_injective a.2))

theorem lastComp_apply {x z : V} (a : Σ y : V, y ⟶ z) (f : Hm k x z) (p : Quiver.Path x a.1) :
    toFinsupp (lastComp (k := k) a f) p = toFinsupp f (p.cons a.2) := rfl

/-- **The components of `g a`**: only the component of `a` survives. -/
theorem lastComp_comp_arrow {x y z : V} (g : Hm k x y) (b : y ⟶ z) :
    (fun a : Σ y : V, y ⟶ z ↦ lastComp (k := k) a (g ≫ arrow b)) = Pi.single ⟨y, b⟩ g := by
  funext a
  obtain ⟨y', b'⟩ := a
  by_cases h : (⟨y', b'⟩ : Σ y : V, y ⟶ z) = ⟨y, b⟩
  · obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.1 h
    obtain rfl := eq_of_heq hb
    rw [Pi.single_eq_same]
    apply (finsuppEquiv (k := k) x y').injective
    apply Finsupp.ext
    intro p
    change toFinsupp (g ≫ arrow b') (p.cons b') = toFinsupp g p
    rw [comp_arrow]
    exact Finsupp.mapDomain_apply (cons_injective _) _ _
  · rw [Pi.single_eq_of_ne h, comp_arrow]
    apply Finsupp.ext
    intro p
    change (Finsupp.mapDomain (fun p : Quiver.Path x y ↦ p.cons b) (toFinsupp g)) (p.cons b') = 0
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨q, hq⟩
    apply h
    have h1 := Quiver.Path.obj_eq_of_cons_eq_cons hq
    subst h1
    have h2 := Quiver.Path.hom_heq_of_cons_eq_cons hq
    rw [eq_of_heq h2]

/-- **The last-arrow decomposition** `f = f₀ + Σ_a f_a a`. -/
theorem decomp {x z : V} [Fintype (Σ y : V, y ⟶ z)] (f : Hm k x z) :
    f = proj (k := k) 0 x z f + ∑ a : Σ y : V, y ⟶ z, lastComp (k := k) a f ≫ arrow a.2 := by
  apply (finsuppEquiv (k := k) x z).injective
  apply Finsupp.ext
  intro q
  change toFinsupp f q = toFinsupp (proj 0 x z f + _) q
  rw [toFinsupp_add, Finsupp.add_apply]
  have hsum : ∀ q : Quiver.Path x z, toFinsupp (∑ a : Σ y : V, y ⟶ z,
      lastComp (k := k) a f ≫ arrow a.2) q =
      ∑ a : Σ y : V, y ⟶ z, Finsupp.mapDomain (fun p : Quiver.Path x a.1 ↦ p.cons a.2)
        (toFinsupp (lastComp (k := k) a f)) q := by
    intro q
    rw [show toFinsupp (∑ a : Σ y : V, y ⟶ z, lastComp (k := k) a f ≫ arrow a.2) =
      ∑ a : Σ y : V, y ⟶ z, toFinsupp (lastComp (k := k) a f ≫ arrow a.2) from
      map_sum (finsuppEquiv (k := k) x z) _ _, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [comp_arrow]; rfl
  rw [hsum]
  cases q with
  | nil =>
    rw [Finset.sum_eq_zero fun a _ ↦ Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨p, hp⟩; exact Quiver.Path.cons_ne_nil _ _ hp), add_zero]
    change _ = (Finsupp.filter _ (toFinsupp f)) _
    rw [Finsupp.filter_apply, if_pos (by rfl)]
  | cons p b =>
    rename_i y
    change _ = (Finsupp.filter _ (toFinsupp f)) _ + _
    rw [Finsupp.filter_apply, if_neg (by simp), zero_add]
    rw [Finset.sum_eq_single ⟨y, b⟩]
    · rw [Finsupp.mapDomain_apply (cons_injective b)]; rfl
    · intro a _ ha
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q, hq⟩
      apply ha
      have h1 := Quiver.Path.obj_eq_of_cons_eq_cons hq
      obtain ⟨y', b'⟩ := a
      simp only at h1 hq
      subst h1
      have h2 := Quiver.Path.hom_heq_of_cons_eq_cons hq
      rw [eq_of_heq h2]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- Components of a composite with a morphism without degree-zero part. -/
theorem lastComp_comp {x y z : V} [Fintype (Σ y : V, y ⟶ z)] (g : Hm k x y) (h : Hm k y z)
    (h0 : proj (k := k) 0 y z h = 0) (a : Σ y : V, y ⟶ z) :
    lastComp (k := k) a (g ≫ h) = g ≫ lastComp (k := k) a h := by
  conv_lhs => rw [decomp h, h0, zero_add, Preadditive.comp_sum, map_sum]
  have := fun b : Σ y : V, y ⟶ z ↦ congrFun (lastComp_comp_arrow (k := k) (g ≫ lastComp b h) b.2) a
  simp only [Category.assoc] at this
  rw [Finset.sum_congr rfl fun b _ ↦ this b, Finset.sum_eq_single a]
  · exact Pi.single_eq_same (M := fun a : Σ y : V, y ⟶ z ↦ Hm k x a.1) a _
  · intro b _ hb
    exact Pi.single_eq_of_ne (M := fun a : Σ y : V, y ⟶ z ↦ Hm k x a.1) (Ne.symm hb) _
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Right composition as a linear map. -/
def compR {x y z : V} (h : Hm k y z) : Hm k x y →ₗ[k] Hm k x z where
  toFun g := g ≫ h
  map_add' g g' := Preadditive.add_comp _ _ _ _ _ _
  map_smul' c g := Linear.smul_comp _ _ _ _ _ _

@[simp] theorem compR_apply {x y z : V} (h : Hm k y z) (g : Hm k x y) : compR h g = g ≫ h := rfl

theorem path_nil (x : V) : path (k := k) (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ := rfl

/-! ### Paths of large length -/

variable (k) in
/-- The span of the paths of length at least `d` (the power `𝔪^d` of the arrow ideal). -/
def geSpan (d : ℕ) (x y : V) : Submodule k (Hm k x y) :=
  Submodule.span k {g | ∃ p : Quiver.Path x y, d ≤ p.length ∧ g = path p}

theorem geSpan_anti {d d' : ℕ} (h : d ≤ d') (x y : V) : geSpan k d' x y ≤ geSpan k d x y :=
  Submodule.span_mono fun _ ⟨p, hp, hg⟩ ↦ ⟨p, le_trans h hp, hg⟩

theorem path_comp_geSpan {d : ℕ} {w x y z : V} (u : Quiver.Path w x) (v : Quiver.Path y z)
    {g : Hm k x y} (hg : g ∈ geSpan k d x y) :
    path (k := k) u ≫ g ≫ path v ∈ geSpan k (u.length + d + v.length) w z := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    rw [path_comp_path, path_comp_path]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    simp only [Quiver.Path.length_comp]
    omega
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp, Preadditive.comp_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ c ha

theorem degreePart_le_geSpan (d : ℕ) (x y : V) : degreePart (k := k) d x y ≤ geSpan k d x y :=
  Submodule.span_mono fun _ ⟨p, hp, hg⟩ ↦ ⟨p, hp.ge, hg⟩

theorem comp_geSpan {d e : ℕ} {x y z : V} {g : Hm k x y} {h : Hm k y z}
    (hg : g ∈ geSpan k d x y) (hh : h ∈ geSpan k e y z) : g ≫ h ∈ geSpan k (d + e) x z := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    have := path_comp_geSpan (k := k) p Quiver.Path.nil hh
    rw [path_nil, Category.comp_id] at this
    exact geSpan_anti (by simp; omega) _ _ this
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | smul c a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c ha

/-- The nil coefficient of an endomorphism. -/
def nilCoeff (x : V) : Hm k x x →ₗ[k] k :=
  (Finsupp.lapply (Quiver.Path.nil : Quiver.Path x x)) ∘ₗ (finsuppEquiv (k := k) x x).toLinearMap

theorem nilCoeff_geSpan {x : V} {g : Hm k x x} (hg : g ∈ geSpan k 1 x x) : nilCoeff x g = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    change (Finsupp.single p (1 : k)) Quiver.Path.nil = 0
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    simp at hp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

theorem nilCoeff_id (x : V) : nilCoeff (k := k) x (𝟙 _) = 1 := by
  change (Finsupp.single (Quiver.Path.nil : Quiver.Path x x) (1 : k)) Quiver.Path.nil = 1
  rw [Finsupp.single_eq_same]

theorem mem_geSpan_zero {x y : V} (g : Hm k x y) : g ∈ geSpan k 0 x y := by
  induction g using induction_on with
  | h0 => exact zero_mem _
  | hadd f g hf hg => exact add_mem hf hg
  | hsingle p c => exact Submodule.smul_mem _ c (Submodule.subset_span ⟨p, Nat.zero_le _, rfl⟩)

/-! ### Presentations and their ideals -/

variable (k V) in
/-- **A graded presentation `kQ/(r)`**: relations indexed by their target, homogeneous of degree
at least two. -/
structure Pres where
  T : V → Type
  [fin : ∀ x, Fintype (T x)]
  src : ∀ x, T x → V
  deg : ∀ x, T x → ℕ
  r : ∀ x (t : T x), Hm k (src x t) x
  hom : ∀ x t, r x t ∈ degreePart (k := k) (deg x t) (src x t) x
  two : ∀ x t, 2 ≤ deg x t

attribute [instance] Pres.fin

variable (P : Pres k V)

/-- The span of the contextual relations `u ρ_t v`. -/
def ctxSpan (ρ : ∀ x (t : P.T x), Hm k (P.src x t) x) (w y : V) : Submodule k (Hm k w y) :=
  Submodule.span k {g | ∃ (x : V) (t : P.T x) (u : Quiver.Path w (P.src x t))
    (v : Quiver.Path x y), g = path u ≫ ρ x t ≫ path v}

theorem ctx_mem (ρ : ∀ x (t : P.T x), Hm k (P.src x t) x) {w y x : V} (t : P.T x)
    (u : Hm k w (P.src x t)) (v : Hm k x y) : u ≫ ρ x t ≫ v ∈ ctxSpan P ρ w y := by
  induction u using induction_on with
  | h0 => simp
  | hadd a b ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | hsingle p c =>
    induction v using induction_on with
    | h0 => simp
    | hadd a b ha hb => rw [Preadditive.comp_add, Preadditive.comp_add]; exact add_mem ha hb
    | hsingle q c' =>
      rw [Linear.smul_comp, Linear.comp_smul, Linear.comp_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨x, t, p, q, rfl⟩))

theorem ctxSpan_comp {ρ : ∀ x (t : P.T x), Hm k (P.src x t) x} {w y z : V} {g : Hm k w y}
    (hg : g ∈ ctxSpan P ρ w y) (h : Hm k y z) : g ≫ h ∈ ctxSpan P ρ w z := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨x, t, u, v, rfl⟩ := hg
    simp only [Category.assoc]
    exact ctx_mem P ρ t _ _
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | smul c a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c ha

theorem comp_ctxSpan {ρ : ∀ x (t : P.T x), Hm k (P.src x t) x} {v w y : V} {g : Hm k w y}
    (hg : g ∈ ctxSpan P ρ w y) (h : Hm k v w) : h ≫ g ∈ ctxSpan P ρ v y := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨x, t, u, v', rfl⟩ := hg
    rw [← Category.assoc]
    exact ctx_mem P ρ t _ _
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

theorem ctxSpan_le_geSpan {ρ : ∀ x (t : P.T x), Hm k (P.src x t) x} {d : ℕ}
    (hρ : ∀ x t, ρ x t ∈ geSpan k d (P.src x t) x) (w y : V) :
    ctxSpan P ρ w y ≤ geSpan k d w y := by
  rw [ctxSpan, Submodule.span_le]
  rintro _ ⟨x, t, u, v, rfl⟩
  exact geSpan_anti (by omega) _ _ (path_comp_geSpan u v (hρ x t))

/-! ### Ideal families and the presentation complexes -/

variable (k V) in
/-- A two-sided ideal of `kQ` inside the arrow ideal. -/
structure IdealFam where
  I : ∀ w y : V, Submodule k (Hm k w y)
  comp_right : ∀ {w y z : V} {g : Hm k w y}, g ∈ I w y → ∀ h : Hm k y z, g ≫ h ∈ I w z
  comp_left : ∀ {v w y : V} {g : Hm k w y}, g ∈ I w y → ∀ h : Hm k v w, h ≫ g ∈ I v y
  le_ge1 : ∀ w y : V, I w y ≤ geSpan k 1 w y

variable (J : IdealFam k V)

/-- The quotient `kQ(w, y)/I`. -/
abbrev Q (w y : V) := Hm k w y ⧸ J.I w y

/-- Right composition with a morphism on the quotients. -/
def compQ {w y z : V} (h : Hm k y z) : Q J w y →ₗ[k] Q J w z :=
  Submodule.mapQ _ _ (compR h) fun _ hg ↦ J.comp_right hg h

theorem compQ_mk {w y z : V} (h : Hm k y z) (g : Hm k w y) :
    compQ J h (Submodule.Quotient.mk g) = Submodule.Quotient.mk (g ≫ h) := rfl

variable [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- **The arrow map** `⊕_a C(w, y_a) → C(w, x)`, `(z_a) ↦ Σ z_a a`. -/
def alpha (w x : V) : (∀ a : Σ y : V, y ⟶ x, Q J w a.1) →ₗ[k] Q J w x :=
  ∑ a : Σ y : V, y ⟶ x, compQ J (arrow a.2) ∘ₗ LinearMap.proj a

/-- **The relation map** `⊕_t C(w, s_t) → ⊕_a C(w, y_a)`, splitting each relation by its last
arrows. -/
def relMap (ρ : ∀ x (t : P.T x), Hm k (P.src x t) x) (w x : V) :
    (∀ t : P.T x, Q J w (P.src x t)) →ₗ[k] (∀ a : Σ y : V, y ⟶ x, Q J w a.1) :=
  LinearMap.pi fun a ↦ ∑ t : P.T x, compQ J (lastComp a (ρ x t)) ∘ₗ LinearMap.proj t

/-- The nil coefficient on the quotient. -/
def epsQ (x : V) : Q J x x →ₗ[k] k :=
  Submodule.liftQ _ (nilCoeff x) fun g hg ↦ by
    rw [LinearMap.mem_ker]; exact nilCoeff_geSpan (J.le_ge1 x x hg)

theorem proj_zero_of_ne {w x : V} (h : w ≠ x) (g : Hm k w x) : proj (k := k) 0 w x g = 0 := by
  induction g using induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, hf, hg, add_zero]
  | hsingle p c =>
    rw [map_smul, proj_path, if_neg, smul_zero]
    intro hp
    cases p with
    | nil => exact h rfl
    | cons p a => simp at hp

theorem mem_range_alpha {w x : V} (g : Hm k w x) (hg : proj (k := k) 0 w x g = 0) :
    Submodule.Quotient.mk g ∈ LinearMap.range (alpha J w x) := by
  refine ⟨fun a ↦ Submodule.Quotient.mk (lastComp a g), ?_⟩
  conv_rhs => rw [decomp g, hg, zero_add]
  simp only [alpha, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, compQ_mk]
  exact (map_sum (Submodule.mkQ (J.I w x)) _ _).symm

theorem proj_zero_endo (x : V) (g : Hm k x x) : proj (k := k) 0 x x g = nilCoeff x g • 𝟙 _ := by
  induction g using induction_on with
  | h0 => simp
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, add_smul]
  | hsingle p c =>
    rw [map_smul, map_smul, proj_path, smul_eq_mul, mul_smul]
    cases p with
    | nil =>
      rw [if_pos (by rfl), path_nil, nilCoeff_id, one_smul]
    | cons p a =>
      rw [if_neg (by simp)]
      have : nilCoeff (k := k) x (path (p.cons a)) = 0 := by
        change (Finsupp.single (p.cons a) (1 : k)) Quiver.Path.nil = 0
        rw [Finsupp.single_apply, if_neg (Quiver.Path.cons_ne_nil _ _)]
      rw [this, zero_smul, smul_zero]

theorem arrow_mem_ge1 {y x : V} (b : y ⟶ x) : arrow (k := k) b ∈ geSpan k 1 y x :=
  Submodule.subset_span ⟨b.toPath, by simp, rfl⟩

/-- **The presentation is a complex**: `α ∘ ρ = 0` for relations in the ideal. -/
theorem alpha_relMap (ρ : ∀ x (t : P.T x), Hm k (P.src x t) x)
    (hρI : ∀ x (t : P.T x) w (u : Hm k w (P.src x t)), u ≫ ρ x t ∈ J.I w x)
    (hρ0 : ∀ x (t : P.T x), proj (k := k) 0 (P.src x t) x (ρ x t) = 0) (w x : V)
    (z : ∀ t : P.T x, Q J w (P.src x t)) : alpha J w x (relMap P J ρ w x z) = 0 := by
  choose u hu using fun t ↦ Submodule.Quotient.mk_surjective _ (z t)
  have : relMap P J ρ w x z = fun a ↦ Submodule.Quotient.mk
      (∑ t : P.T x, u t ≫ lastComp a (ρ x t)) := by
    funext a
    simp only [relMap, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, ← hu, compQ_mk]
    exact (map_sum (Submodule.mkQ (J.I w a.1)) _ _).symm
  rw [this]
  simp only [alpha, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, compQ_mk]
  rw [show ∑ a : Σ y : V, y ⟶ x, (Submodule.Quotient.mk
      ((∑ t : P.T x, u t ≫ lastComp a (ρ x t)) ≫ arrow a.2) : Q J w x) =
      Submodule.Quotient.mk (∑ a : Σ y : V, y ⟶ x,
        (∑ t : P.T x, u t ≫ lastComp a (ρ x t)) ≫ arrow a.2) from
      (map_sum (Submodule.mkQ (J.I w x)) _ _).symm, Submodule.Quotient.mk_eq_zero]
  have h : ∑ a : Σ y : V, y ⟶ x, (∑ t : P.T x, u t ≫ lastComp a (ρ x t)) ≫ arrow a.2 =
      ∑ t : P.T x, u t ≫ ρ x t := by
    simp only [Preadditive.sum_comp, Category.assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← Preadditive.comp_sum]
    conv_rhs => rw [decomp (ρ x t), hρ0, zero_add]
  rw [h]
  exact Submodule.sum_mem _ fun t _ ↦ hρI x t w (u t)

/-! ### The ideals of `C` and of the perturbation `B` -/

theorem proj_eq_zero_of_geSpan {d e : ℕ} (he : e < d) {x y : V} {g : Hm k x y}
    (hg : g ∈ geSpan k d x y) : proj (k := k) e x y g = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    rw [proj_path, if_neg (by omega)]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

theorem r_mem_ge2 (x : V) (t : P.T x) : P.r x t ∈ geSpan k 2 (P.src x t) x :=
  geSpan_anti (P.two x t) _ _ (degreePart_le_geSpan _ _ _ (P.hom x t))

/-- **The ideal of `C`.** -/
def idealC : IdealFam k V where
  I := ctxSpan P P.r
  comp_right hg h := ctxSpan_comp P hg h
  comp_left hg h := comp_ctxSpan P hg h
  le_ge1 w y := le_trans (ctxSpan_le_geSpan P (r_mem_ge2 P) w y) (geSpan_anti (by norm_num) w y)

variable (f : ∀ x (t : P.T x), Hm k (P.src x t) x)
  (hf : ∀ x t, f x t ∈ geSpan k (P.deg x t + 1) (P.src x t) x) (N : ℕ)

include hf in
theorem rf_mem_ge2 (x : V) (t : P.T x) : P.r x t - f x t ∈ geSpan k 2 (P.src x t) x :=
  sub_mem (r_mem_ge2 P x t) (geSpan_anti (by have := P.two x t; omega) _ _ (hf x t))

/-- The perturbed relations `r_t − f_t`. -/
def rf (x : V) (t : P.T x) : Hm k (P.src x t) x := P.r x t - f x t

include hf in
/-- **The ideal of the perturbation** `B = kQ/(𝔪^{N+1}, r_t − f_t)`. -/
def idealB : IdealFam k V where
  I w y := ctxSpan P (rf P f) w y ⊔ geSpan k (N + 1) w y
  comp_right {w y z g} hg h := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hg
    rw [Preadditive.add_comp]
    exact add_mem (Submodule.mem_sup_left (ctxSpan_comp P ha h))
      (Submodule.mem_sup_right (by simpa using comp_geSpan hb (mem_geSpan_zero h)))
  comp_left {v w y g} hg h := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hg
    rw [Preadditive.comp_add]
    exact add_mem (Submodule.mem_sup_left (comp_ctxSpan P ha h))
      (Submodule.mem_sup_right (by simpa using comp_geSpan (mem_geSpan_zero h) hb))
  le_ge1 w y := sup_le
    (le_trans (ctxSpan_le_geSpan P (ρ := rf P f) (rf_mem_ge2 P f hf) w y)
      (geSpan_anti (by norm_num) w y))
    (geSpan_anti (by omega) w y)

/-! ### Finite dimensionality -/

variable [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]

theorem finite_paths_eq (w : V) : ∀ (n : ℕ) (y : V),
    Set.Finite {p : Quiver.Path w y | p.length = n}
  | 0, y => by
    refine Set.Subsingleton.finite fun p hp q hq ↦ ?_
    cases p with
    | nil => cases q with
      | nil => rfl
      | cons q b => simp at hq
    | cons p a => simp at hp
  | n + 1, y => by
    have hfin : Set.Finite (⋃ y' : V, ⋃ a : y' ⟶ y,
        (fun q : Quiver.Path w y' ↦ q.cons a) '' {q | q.length = n}) :=
      Set.finite_iUnion fun y' ↦ Set.finite_iUnion fun a ↦ (finite_paths_eq w n y').image _
    refine hfin.subset fun p hp ↦ ?_
    cases p with
    | nil => simp at hp
    | cons q a =>
      rename_i y'
      simp only [Set.mem_setOf_eq, Quiver.Path.length_cons, Nat.add_right_cancel_iff] at hp
      exact Set.mem_iUnion.2 ⟨y', Set.mem_iUnion.2 ⟨a, ⟨q, hp, rfl⟩⟩⟩

theorem finite_paths_lt (w y : V) (M : ℕ) : Set.Finite {p : Quiver.Path w y | p.length < M} := by
  have : {p : Quiver.Path w y | p.length < M} = ⋃ n ∈ Finset.range M, {p | p.length = n} := by
    ext p; simp
  rw [this]
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun n _ ↦ finite_paths_eq w n y

/-- **A quotient killing all long paths is finite-dimensional.** -/
theorem finiteDimensional_Q {M : ℕ} (hM : ∀ w y, geSpan k M w y ≤ J.I w y) (w y : V) :
    Module.Finite k (Q J w y) := by
  set S := (fun p : Quiver.Path w y ↦ path (k := k) p) '' {p | p.length < M}
  have hS : S.Finite := (finite_paths_lt w y M).image _
  have hfd : Module.Finite k (Submodule.span k S) := Module.Finite.span_of_finite k hS
  refine Module.Finite.of_surjective ((J.I w y).mkQ ∘ₗ (Submodule.span k S).subtype) ?_
  intro z
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have key : ∀ g : Hm k w y, ∃ s ∈ Submodule.span k S, g - s ∈ J.I w y := by
    intro g
    induction g using induction_on with
    | h0 => exact ⟨0, zero_mem _, by simp⟩
    | hadd a b ha hb =>
      obtain ⟨s, hs, hs'⟩ := ha
      obtain ⟨s', hs2, hs2'⟩ := hb
      exact ⟨s + s', add_mem hs hs2, by
        rw [show a + b - (s + s') = (a - s) + (b - s') by abel]; exact add_mem hs' hs2'⟩
    | hsingle p c =>
      by_cases hp : p.length < M
      · exact ⟨c • path p, Submodule.smul_mem _ c (Submodule.subset_span ⟨p, hp, rfl⟩), by simp⟩
      · exact ⟨0, zero_mem _, by
          rw [sub_zero]
          exact hM w y (Submodule.smul_mem _ c (Submodule.subset_span ⟨p, by omega, rfl⟩))⟩
  obtain ⟨s, hs, hgs⟩ := key g
  refine ⟨⟨s, hs⟩, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).2 (by rw [← neg_mem_iff, neg_sub]; exact hgs)

/-! ### Homogeneous contextual relations -/

/-- The span of the contextual relations of degree `d`. -/
def hctx (d : ℕ) (w y : V) : Submodule k (Hm k w y) :=
  Submodule.span k {g | ∃ (x : V) (t : P.T x) (u : Quiver.Path w (P.src x t))
    (v : Quiver.Path x y), u.length + P.deg x t + v.length = d ∧ g = path u ≫ P.r x t ≫ path v}

theorem proj_ctx (d : ℕ) {w y : V} {g : Hm k w y} (hg : g ∈ ctxSpan P P.r w y) :
    proj (k := k) d w y g ∈ hctx P d w y := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨x, t, u, v, rfl⟩ := hg
    have hdeg : path (k := k) u ≫ P.r x t ≫ path v ∈
        degreePart (k := k) (u.length + P.deg x t + v.length) w y := by
      have := comp_mem_degreePart (comp_mem_degreePart (path_mem_degreePart (k := k) u)
        (P.hom x t)) (path_mem_degreePart (k := k) v)
      simpa [Category.assoc] using this
    rw [proj_of_mem hdeg]
    split_ifs with h
    · exact Submodule.subset_span ⟨x, t, u, v, h, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

include hf in
theorem hctx_le_B {d : ℕ} (hd : N ≤ d) (w y : V) : hctx P d w y ≤ (idealB P f hf N).I w y := by
  rw [hctx, Submodule.span_le]
  rintro _ ⟨x, t, u, v, hdeg, rfl⟩
  have e : path (k := k) u ≫ P.r x t ≫ path v =
      path u ≫ rf P f x t ≫ path v + path u ≫ f x t ≫ path v := by
    simp [rf, Preadditive.sub_comp, Preadditive.comp_sub]
  rw [SetLike.mem_coe, e]
  refine add_mem (Submodule.mem_sup_left (ctx_mem P (rf P f) t _ _)) (Submodule.mem_sup_right ?_)
  exact geSpan_anti (by omega) _ _ (path_comp_geSpan u v (hf x t))

include hf in
/-- **`𝔪^N B = 0`** (`deformation-refinements.tex:186–188`). -/
theorem path_mem_B (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := k) p ∈ ctxSpan P P.r w y)
    {w y : V} (p : Quiver.Path w y) (hp : N ≤ p.length) : path (k := k) p ∈ (idealB P f hf N).I w y := by
  have := proj_ctx P p.length (hN w y p hp)
  rw [proj_path, if_pos rfl] at this
  exact hctx_le_B P f hf N hp w y this

/-! ### Exactness of the perturbed presentation at the arrow term -/

theorem rf_proj0 (x : V) (t : P.T x) (hf : ∀ x t, f x t ∈ geSpan k (P.deg x t + 1) (P.src x t) x) :
    proj (k := k) 0 (P.src x t) x (rf P f x t) = 0 :=
  proj_eq_zero_of_geSpan (by norm_num) (rf_mem_ge2 P f hf x t)

include hf in
/-- **Sorting contextual relations by their last factor** (`deformation-refinements.tex:197–203`):
the last-arrow components of an element of the ideal of `B` are, modulo the ideal, the
components of a combination of the perturbed relations ending at `x`. -/
theorem lastComp_B (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y)
    {w x : V} {g : Hm k w x} (hg : g ∈ (idealB P f hf N).I w x) :
    ∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
      lastComp a g - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ (idealB P f hf N).I w a.1 := by
  classical
  set IB := idealB P f hf N
  -- closure of the property under sums and scalars
  have hzero : ∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
      lastComp a (0 : Hm k w x) - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ IB.I w a.1 :=
    ⟨0, fun a ↦ by simp⟩
  have hadd : ∀ g g' : Hm k w x,
      (∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
        lastComp a g - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ IB.I w a.1) →
      (∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
        lastComp a g' - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ IB.I w a.1) →
      ∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
        lastComp a (g + g') - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ IB.I w a.1 := by
    rintro g g' ⟨u, hu⟩ ⟨u', hu'⟩
    refine ⟨u + u', fun a ↦ ?_⟩
    have := add_mem (hu a) (hu' a)
    convert this using 1
    simp only [map_add, Pi.add_apply, Preadditive.add_comp, Finset.sum_add_distrib]
    abel
  have hsmul : ∀ (c : k) (g : Hm k w x),
      (∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
        lastComp a g - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ IB.I w a.1) →
      ∃ u : ∀ t : P.T x, Hm k w (P.src x t), ∀ a : Σ y : V, y ⟶ x,
        lastComp a (c • g) - ∑ t : P.T x, u t ≫ lastComp a (rf P f x t) ∈ IB.I w a.1 := by
    rintro c g ⟨u, hu⟩
    refine ⟨c • u, fun a ↦ ?_⟩
    have := Submodule.smul_mem _ c (hu a)
    convert this using 1
    simp only [map_smul, Pi.smul_apply, Linear.smul_comp, smul_sub, Finset.smul_sum]
  obtain ⟨c, hc, e, he, rfl⟩ := Submodule.mem_sup.1 hg
  clear hg
  refine hadd _ _ ?_ ?_
  · induction hc using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x', t, u, v, rfl⟩ := hg
      cases v with
      | nil =>
        refine ⟨Pi.single t (path u), fun a ↦ ?_⟩
        rw [path_nil, Category.comp_id, lastComp_comp (h0 := rf_proj0 P f x t hf),
          Finset.sum_eq_single t]
        · rw [Pi.single_eq_same, sub_self]; exact zero_mem _
        · intro t' _ ht'; rw [Pi.single_eq_of_ne ht', Limits.zero_comp]
        · intro h; exact absurd (Finset.mem_univ t) h
      | cons v b =>
        rename_i y'
        refine ⟨0, fun a ↦ ?_⟩
        simp only [Pi.zero_apply, Limits.zero_comp, Finset.sum_const_zero, sub_zero]
        rw [← path_comp_arrow, ← Category.assoc, ← Category.assoc]
        have := congrFun (lastComp_comp_arrow (k := k) ((path u ≫ rf P f x' t) ≫ path v) b) a
        rw [this]
        by_cases ha : a = ⟨y', b⟩
        · subst ha
          rw [Pi.single_eq_same, Category.assoc]
          exact Submodule.mem_sup_left (ctx_mem P (rf P f) t _ _)
        · rw [Pi.single_eq_of_ne ha]; exact zero_mem _
    | zero => exact hzero
    | add a b _ _ ha hb => exact hadd a b ha hb
    | smul c a _ ha => exact hsmul c a ha
  · induction he using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨p, hp, rfl⟩ := hg
      refine ⟨0, fun a ↦ ?_⟩
      simp only [Pi.zero_apply, Limits.zero_comp, Finset.sum_const_zero, sub_zero]
      cases p with
      | nil => simp at hp
      | cons p b =>
        rename_i y'
        rw [← path_comp_arrow]
        have := congrFun (lastComp_comp_arrow (k := k) (path p) b) a
        rw [this]
        by_cases ha : a = ⟨y', b⟩
        · subst ha
          rw [Pi.single_eq_same]
          exact path_mem_B P f hf N hN p (by simp at hp; omega)
        · rw [Pi.single_eq_of_ne ha]; exact zero_mem _
    | zero => exact hzero
    | add a b _ _ ha hb => exact hadd a b ha hb
    | smul c a _ ha => exact hsmul c a ha

include hf in
/-- **Exactness of the perturbed presentation at the arrow term.** -/
theorem ker_alpha_B (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y) (w x : V) :
    LinearMap.ker (alpha (idealB P f hf N) w x) ≤
      LinearMap.range (relMap P (idealB P f hf N) (rf P f) w x) := by
  classical
  intro z hz
  rw [LinearMap.mem_ker] at hz
  choose zh hzh using fun a ↦ Submodule.Quotient.mk_surjective _ (z a)
  set g : Hm k w x := ∑ a : Σ y : V, y ⟶ x, zh a ≫ arrow a.2
  have hg : g ∈ (idealB P f hf N).I w x := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hz]
    simp only [g, alpha, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hzh,
      compQ_mk]
    exact map_sum (Submodule.mkQ ((idealB P f hf N).I w x)) _ _
  have hlast : ∀ a : Σ y : V, y ⟶ x, lastComp a g = zh a := by
    intro a
    simp only [g, map_sum]
    rw [Finset.sum_congr rfl fun b _ ↦ congrFun (lastComp_comp_arrow (k := k) (zh b) b.2) a,
      Finset.sum_eq_single a]
    · exact Pi.single_eq_same (M := fun a : Σ y : V, y ⟶ x ↦ Hm k w a.1) a _
    · intro b _ hb
      exact Pi.single_eq_of_ne (M := fun a : Σ y : V, y ⟶ x ↦ Hm k w a.1) (Ne.symm hb) _
    · intro h; exact absurd (Finset.mem_univ a) h
  obtain ⟨u, hu⟩ := lastComp_B P f hf N hN hg
  refine ⟨fun t ↦ Submodule.Quotient.mk (u t), ?_⟩
  funext a
  simp only [relMap, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, compQ_mk]
  rw [show ∑ t : P.T x, (Submodule.Quotient.mk (u t ≫ lastComp a (rf P f x t)) :
      Q (idealB P f hf N) w a.1) = Submodule.Quotient.mk
        (∑ t : P.T x, u t ≫ lastComp a (rf P f x t)) from
      (map_sum (Submodule.mkQ ((idealB P f hf N).I w a.1)) _ _).symm, ← hzh,
    Submodule.Quotient.eq]
  have := hu a
  rw [hlast] at this
  rw [← neg_mem_iff, neg_sub]
  exact this

include hf in
/-- **Classes of paths spanning `C` span `B`** (the leading-term bound `H_B ≤ H`). -/
theorem span_B (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y) {w y : V} (S : Set (Quiver.Path w y))
    (hS : Submodule.span k ((fun p ↦ Submodule.Quotient.mk (p := ctxSpan P P.r w y)
      (path (k := k) p)) '' S) = ⊤) :
    Submodule.span k ((fun p ↦ Submodule.Quotient.mk (p := (idealB P f hf N).I w y)
      (path (k := k) p)) '' S) = ⊤ := by
  set IB := idealB P f hf N
  set W := Submodule.span k ((fun p : Quiver.Path w y ↦ path (k := k) p) '' S) ⊔ IB.I w y
  have key : ∀ n (q : Quiver.Path w y), N + 1 ≤ q.length + n → path (k := k) q ∈ W := by
    intro n
    induction n with
    | zero =>
      intro q hq
      exact Submodule.mem_sup_right (Submodule.mem_sup_right
        (Submodule.subset_span ⟨q, by omega, rfl⟩))
    | succ n ih =>
      intro q hq
      by_cases hlen : N + 1 ≤ q.length
      · exact ih q (by omega)
      set d := q.length
      -- spanning in `C`
      have hq : Submodule.Quotient.mk (p := ctxSpan P P.r w y) (path (k := k) q) ∈
          Submodule.span k ((fun p ↦ Submodule.Quotient.mk (p := ctxSpan P P.r w y)
            (path (k := k) p)) '' S) := by rw [hS]; trivial
      rw [show (fun p ↦ Submodule.Quotient.mk (p := ctxSpan P P.r w y) (path (k := k) p)) '' S =
          (ctxSpan P P.r w y).mkQ '' ((fun p ↦ path (k := k) p) '' S) by
        rw [Set.image_image]; rfl, ← Submodule.map_span] at hq
      obtain ⟨s, hs, hseq⟩ := hq
      have hdiff : path (k := k) q - s ∈ ctxSpan P P.r w y := by
        rw [← neg_mem_iff, neg_sub]
        exact (Submodule.Quotient.eq _).1 hseq
      have hsplit : path (k := k) q = proj (k := k) d w y s + proj d w y (path q - s) := by
        rw [← map_add, add_sub_cancel, proj_path, if_pos rfl]
      have hps : ∀ s' ∈ Submodule.span k ((fun p : Quiver.Path w y ↦ path (k := k) p) '' S),
          proj (k := k) d w y s' ∈
            Submodule.span k ((fun p : Quiver.Path w y ↦ path (k := k) p) '' S) := by
        intro s' hs'
        induction hs' using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨p, hp, rfl⟩ := hg
          rw [proj_path]
          split_ifs
          · exact Submodule.subset_span ⟨p, hp, rfl⟩
          · exact zero_mem _
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
      rw [hsplit]
      refine add_mem (Submodule.mem_sup_left (hps s hs)) ?_
      · have hh := proj_ctx P d hdiff
        refine (show hctx P d w y ≤ W from ?_) hh
        rw [hctx, Submodule.span_le]
        rintro _ ⟨x, t, u, v, hdeg, rfl⟩
        have e : path (k := k) u ≫ P.r x t ≫ path v =
            path u ≫ rf P f x t ≫ path v + path u ≫ f x t ≫ path v := by
          simp [rf, Preadditive.sub_comp, Preadditive.comp_sub]
        rw [SetLike.mem_coe, e]
        refine add_mem (Submodule.mem_sup_right (Submodule.mem_sup_left
          (ctx_mem P (rf P f) t _ _))) ?_
        have hge := path_comp_geSpan u v (hf x t)
        refine (show geSpan k (u.length + (P.deg x t + 1) + v.length) w y ≤ W from ?_) hge
        rw [geSpan, Submodule.span_le]
        rintro _ ⟨p, hp, rfl⟩
        exact ih p (by omega)
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hg : g ∈ W := by
    clear * - key
    induction g using induction_on with
    | h0 => exact zero_mem _
    | hadd a b ha hb => exact add_mem ha hb
    | hsingle p c => exact Submodule.smul_mem _ c (key (N + 1) p (by omega))
  obtain ⟨s, hs, i, hi, rfl⟩ := Submodule.mem_sup.1 hg
  rw [show (fun p ↦ Submodule.Quotient.mk (p := IB.I w y) (path (k := k) p)) '' S =
      (IB.I w y).mkQ '' ((fun p ↦ path (k := k) p) '' S) by rw [Set.image_image]; rfl,
    ← Submodule.map_span]
  refine ⟨s, hs, ?_⟩
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hi, add_zero]

/-! ### Dimensions -/

theorem geSpan_le_C (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y) (w y : V) :
    geSpan k N w y ≤ (idealC P).I w y := by
  rw [geSpan, Submodule.span_le]
  rintro _ ⟨p, hp, rfl⟩
  exact hN w y p hp

include hf in
theorem geSpan_le_B (w y : V) : geSpan k (N + 1) w y ≤ (idealB P f hf N).I w y :=
  le_sup_right

theorem span_paths_eq_top (J : IdealFam k V) (w y : V) :
    Submodule.span k (Set.range fun p : Quiver.Path w y ↦
      (Submodule.Quotient.mk (p := J.I w y) (path (k := k) p))) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  induction g using induction_on with
  | h0 => exact zero_mem _
  | hadd a b ha hb => rw [Submodule.Quotient.mk_add]; exact add_mem (ha trivial) (hb trivial)
  | hsingle p c =>
    rw [Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨p, rfl⟩)

end FlatPert

end MultiplicativeBasisDeformations
