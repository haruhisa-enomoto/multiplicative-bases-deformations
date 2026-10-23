module

public import MultiplicativeBasisDeformations.Refinements.CocycleLift
public import MultiplicativeBasisDeformations.Foundations.PsiInjective
public import MultiplicativeBasisDeformations.Refinements.PolynomialFlatness
public import MultiplicativeBasisDeformations.Refinements.MeshNormalForm

/-!
# First-order mesh deformations (toward Proposition 12.5)

`deformation-refinements.tex`: "Given a correction tuple `z_v ∈ C_{q+2}(τv, v)`, impose
`r_v − εz_v` over `k[ε]/(ε²)`. Corollary 12.4 makes this a free deformation of `C`."

Here `C = kQ/(r)` is the scalar mesh category, assumed to satisfy the hypothesis of Lemma 12.3
(its mesh presentations are resolutions). The deformation `B = kQ[ε]/(𝔪^{N+1}, r − εz)` is free
over `k[ε]` with every path basis of `C` (Corollary 12.4, by base change from `k[t]`). Writing
morphisms of `B` as `ŝ(f) + ε ŝ(g)` for a path section `ŝ`, the `ε`-part of `ŝ(f) ŝ(g)` is a
Hochschild two-cocycle `φ` of `C`, whose mesh value `Σ_a c_{x,a} φ(σa, a)` is `z_x`
(`exists_cocycle`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshFirstOrder

open ScalarMeshCategory FlatPert LinearPaths

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} (c : MeshCoefficients k Q)

/-! ### The quotient map `kQ → C` -/

/-- The quotient map on Hom spaces. -/
def qL (x y : V) : Hm k x y →ₗ[k] (obj c x ⟶ obj c y) :=
  (RelationCategory.functor k (meshRelations c)).mapLinearMap k
    (X := LinearPaths.obj x) (Y := LinearPaths.obj y)

theorem qL_apply {x y : V} (g : Hm k x y) :
    qL c x y g = (RelationCategory.functor k (meshRelations c)).map g := rfl

theorem qL_comp {x y z : V} (g : Hm k x y) (h : Hm k y z) :
    qL c x z (g ≫ h) = qL c x y g ≫ qL c y z h :=
  (RelationCategory.functor k (meshRelations c)).map_comp g h

theorem qL_eq_zero_iff {x y : V} (g : Hm k x y) :
    qL c x y g = 0 ↔ g ∈ ctxSpan (meshPres c) (meshPres c).r x y := by
  rw [ctxSpan_meshPres, qL_apply, RelationCategory.functor_map_eq_zero_iff]
  rfl

theorem qL_surjective (x y : V) : Function.Surjective (qL c x y) := fun g ↦
  RelationCategory.functor_map_surjective (k := k) (meshRelations c) g

theorem qL_arrow {x y : V} (α : x ⟶ y) : qL c x y (arrow α) = arrowMor c α := rfl

/-- `C(x, y) = kQ(x, y)/I` as a linear equivalence. -/
def eqv (x y : V) : FlatPert.Q (idealC (meshPres c)) x y ≃ₗ[k] (obj c x ⟶ obj c y) :=
  (Submodule.quotEquivOfEq _ _ (by ext g; exact (qL_eq_zero_iff c g).symm)).trans
    ((qL c x y).quotKerEquivOfSurjective (qL_surjective c x y))

theorem eqv_mk {x y : V} (g : Hm k x y) :
    eqv c x y (Submodule.Quotient.mk g) = qL c x y g := by
  simp [eqv]

variable [hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)]

include hfin in
/-- `C_d = 0` for `d ≥ N`, as paths in the mesh ideal. -/
theorem exists_hN : ∃ N : ℕ, ∀ w y (p : Quiver.Path w y), N ≤ p.length →
    path (k := k) p ∈ ctxSpan (meshPres c) (meshPres c).r w y := by
  obtain ⟨N, hN⟩ := ScalarMeshCategory.exists_degreePart_eq_bot c hfin
  refine ⟨N, fun w y p hp ↦ (qL_eq_zero_iff c _).1 ?_⟩
  have hmem : qL c w y (path p) ∈ ScalarMeshCategory.degreePart c p.length w y :=
    ⟨path p, path_mem_degreePart p, rfl⟩
  rwa [hN _ _ _ hp, Submodule.mem_bot] at hmem

/-! ### Exactness of the mesh presentations -/

omit hfin in
theorem eqv_compQ {w y z : V} (h : Hm k y z) (x : FlatPert.Q (idealC (meshPres c)) w y) :
    eqv c w z (compQ (idealC (meshPres c)) h x) = eqv c w y x ≫ qL c y z h := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [compQ_mk, eqv_mk, eqv_mk, qL_comp]

omit hfin in
theorem lastComp_mesh (x : V) (t : (meshPres c).T x) (a : Σ y : V, y ⟶ x) :
    lastComp (k := k) a ((meshPres c).r x t) =
      ((c ⟨x, t.2⟩ a.1 a.2 : kˣ) : k) • arrow (Q.mate ⟨x, t.2⟩ a.1 a.2) := by
  classical
  change lastComp a (meshRelation c ⟨x, t.2⟩) = _
  simp only [meshRelation, map_sum, map_smul]
  rw [Finset.sum_eq_single a]
  · congr 1
    rw [← path_comp_path]
    exact (congrFun (lastComp_comp_arrow (k := k) (arrow (Q.mate ⟨x, t.2⟩ a.1 a.2)) a.2) a).trans
      (Pi.single_eq_same (M := fun a : Σ y : V, y ⟶ x ↦ Hm k (Q.tau ⟨x, t.2⟩).1 a.1) a _)
  · intro b _ hb
    rw [← path_comp_path]
    have h0 : lastComp a (arrow (k := k) (Q.mate ⟨x, t.2⟩ b.1 b.2) ≫ arrow b.2) = 0 :=
      (congrFun (lastComp_comp_arrow (k := k) (arrow (Q.mate ⟨x, t.2⟩ b.1 b.2)) b.2) a).trans
        (Pi.single_eq_of_ne (M := fun a : Σ y : V, y ⟶ x ↦ Hm k (Q.tau ⟨x, t.2⟩).1 a.1)
          (Ne.symm hb) _)
    exact (congrArg (fun Y ↦ ((c ⟨x, t.2⟩ b.1 b.2 : kˣ) : k) • Y) h0).trans (smul_zero _)
  · intro h; exact absurd (Finset.mem_univ a) h

omit hfin in
theorem lastComp_meshRelation (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1) :
    lastComp (k := k) a (meshRelation c x) =
      ((c x a.1 a.2 : kˣ) : k) • arrow (Q.mate x a.1 a.2) :=
  lastComp_mesh c x.1 ⟨(), x.2⟩ a

omit hfin in
/-- **The mesh presentations are resolutions** (the hypothesis of Lemma 12.3) when the mesh
sequences of `C` are exact: the paragraph after Lemma 12.3. -/
theorem hres_of_exact
    (hmono : ∀ (x : Q.nonprojective) (w : V) (z : obj c w ⟶ obj c (Q.tau x).1),
      (∀ a : Σ y : V, y ⟶ x.1,
        z ≫ (((c x a.1 a.2 : kˣ) : k) • arrowMor c (Q.mate x a.1 a.2)) = 0) → z = 0)
    (hexact : ∀ (x : Q.nonprojective) (w : V) (g : ∀ a : Σ y : V, y ⟶ x.1, obj c w ⟶ obj c a.1),
      ∑ a, g a ≫ arrowMor c a.2 = 0 → ∃ z : obj c w ⟶ obj c (Q.tau x).1,
        ∀ a, g a = z ≫ (((c x a.1 a.2 : kˣ) : k) • arrowMor c (Q.mate x a.1 a.2)))
    (hproj : ∀ x : V, x ∉ Q.nonprojective → ∀ (w : V)
      (g : ∀ a : Σ y : V, y ⟶ x, obj c w ⟶ obj c a.1), ∑ a, g a ≫ arrowMor c a.2 = 0 →
        ∀ a, g a = 0) (w x : V) :
    Function.Injective (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x) ∧
      LinearMap.ker (alpha (idealC (meshPres c)) w x) ≤
        LinearMap.range (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x) := by
  classical
  have halpha : ∀ z, eqv c w x (alpha (idealC (meshPres c)) w x z) =
      ∑ a : Σ y : V, y ⟶ x, eqv c w a.1 (z a) ≫ arrowMor c a.2 := by
    intro z
    simp only [alpha, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
      eqv_compQ, qL_arrow]
  by_cases hx : x ∈ Q.nonprojective
  · set t0 : (meshPres c).T x := ⟨(), hx⟩
    have hT : ∀ t : (meshPres c).T x, t = t0 := fun t ↦ Subtype.ext rfl
    have hrel : ∀ u a, eqv c w a.1 (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x
        u a) = eqv c w _ (u t0) ≫ (((c ⟨x, hx⟩ a.1 a.2 : kˣ) : k) •
          arrowMor c (Q.mate ⟨x, hx⟩ a.1 a.2)) := by
      intro u a
      have e1 : relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x u a =
          compQ (idealC (meshPres c)) (lastComp a ((meshPres c).r x t0)) (u t0) := by
        simp only [relMap, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
          LinearMap.proj_apply]
        exact Finset.sum_eq_single_of_mem t0 (@Finset.mem_univ _ ((meshPres c).fin x) t0)
          (fun t _ ht ↦ absurd (hT t) ht)
      refine (congrArg (eqv c w a.1) e1).trans ((eqv_compQ c _ _).trans ?_)
      exact congrArg (fun Y ↦ eqv c w _ (u t0) ≫ Y)
        ((congrArg (qL c _ _) (lastComp_meshRelation c ⟨x, hx⟩ a)).trans
          ((map_smul (qL c _ _) _ _).trans (congrArg _ (qL_arrow c _))))
    refine ⟨fun u u' huu ↦ ?_, fun z hz ↦ ?_⟩
    · have h0 : eqv c w _ (u t0 - u' t0) = 0 := by
        refine hmono ⟨x, hx⟩ w _ fun a ↦ ?_
        rw [map_sub, Preadditive.sub_comp, ← hrel, ← hrel, huu, sub_self]
      funext t
      rw [hT t]
      exact sub_eq_zero.1 ((eqv c w _).map_eq_zero_iff.1 h0)
    · rw [LinearMap.mem_ker] at hz
      have hsum := halpha z
      rw [hz, map_zero] at hsum
      obtain ⟨Z, hZ⟩ := hexact ⟨x, hx⟩ w (fun a ↦ eqv c w a.1 (z a)) hsum.symm
      refine ⟨fun _ ↦ (eqv c w _).symm Z, funext fun a ↦ (eqv c w a.1).injective ?_⟩
      rw [hrel, LinearEquiv.apply_symm_apply]
      exact (hZ a).symm
  · have hT : IsEmpty ((meshPres c).T x) := ⟨fun t ↦ hx t.2⟩
    refine ⟨fun u u' _ ↦ funext fun t ↦ isEmptyElim t, fun z hz ↦ ?_⟩
    rw [LinearMap.mem_ker] at hz
    have hsum := halpha z
    rw [hz, map_zero] at hsum
    have h0 := hproj x hx w (fun a ↦ eqv c w a.1 (z a)) hsum.symm
    have : z = 0 := funext fun a ↦ (eqv c w a.1).map_eq_zero_iff.1 (h0 a)
    rw [this]
    exact zero_mem _

/-! ### Path bases -/

/-- **Path bases** of all Hom spaces of `C`. -/
structure PathBases where
  ι : V → V → Type u
  fin : ∀ w y, Fintype (ι w y)
  p : ∀ w y, ι w y → Quiver.Path w y
  li : ∀ w y, LinearIndependent k fun i ↦
    Submodule.Quotient.mk (p := (idealC (meshPres c)).I w y) (path (k := k) (p w y i))
  sp : ∀ w y, Submodule.span k (Set.range fun i ↦
    Submodule.Quotient.mk (p := (idealC (meshPres c)).I w y) (path (k := k) (p w y i))) = ⊤

attribute [instance] PathBases.fin

include hfin in
theorem nonempty_pathBases : Nonempty (PathBases c) := by
  classical
  have hex : ∀ w y : V, ∃ (ι : Type u) (_ : Fintype ι) (p : ι → Quiver.Path w y),
      (LinearIndependent k fun i ↦
        Submodule.Quotient.mk (p := (idealC (meshPres c)).I w y) (path (k := k) (p i))) ∧
      Submodule.span k (Set.range fun i ↦
        Submodule.Quotient.mk (p := (idealC (meshPres c)).I w y) (path (k := k) (p i))) = ⊤ := by
    intro w y
    haveI : FiniteDimensional k (FlatPert.Q (idealC (meshPres c)) w y) :=
      LinearEquiv.finiteDimensional (eqv c w y).symm
    obtain ⟨t, hts, hspan', hli⟩ := exists_linearIndependent k (Set.range fun q : Quiver.Path w y ↦
      Submodule.Quotient.mk (p := (idealC (meshPres c)).I w y) (path (k := k) q))
    have htop : Submodule.span k t = ⊤ := by
      rw [hspan']; exact span_paths_eq_top (idealC (meshPres c)) w y
    have htfin : t.Finite := hli.finite
    choose pth hpth using fun τ : t ↦ hts τ.2
    have hfam : (fun τ : t ↦ Submodule.Quotient.mk (p := (idealC (meshPres c)).I w y)
        (path (k := k) (pth τ))) = Subtype.val := funext hpth
    refine ⟨t, htfin.fintype, pth, ?_, ?_⟩
    · rw [hfam]; exact hli
    · rw [hfam, Subtype.range_coe]; exact htop
  choose ι hι p hli hsp using hex
  exact ⟨⟨ι, hι, p, hli, hsp⟩⟩

variable {c} (B : PathBases c)

/-- The basis of `C(w, y)` given by the path classes. -/
def bC (w y : V) : Module.Basis (B.ι w y) k (obj c w ⟶ obj c y) :=
  (Module.Basis.mk (B.li w y) (by rw [B.sp w y])).map (eqv c w y)

theorem bC_apply {w y : V} (i : B.ι w y) : bC B w y i = qL c w y (path (B.p w y i)) := by
  simp [bC, eqv_mk]

/-- **Every path basis contains the arrows.** -/
theorem exists_arrow_mem {w y : V} (α : w ⟶ y) : ∃ i, B.p w y i = α.toPath := by
  classical
  by_contra hne
  push_neg at hne
  -- `qL(α) = Σ_i a_i qL(p_i)` in `C`
  have hrepr := (bC B w y).sum_repr (qL c w y (arrow α))
  set a := (bC B w y).repr (qL c w y (arrow α))
  have hmem : arrow (k := k) α - ∑ i, a i • path (B.p w y i) ∈
      ctxSpan (meshPres c) (meshPres c).r w y := by
    rw [← qL_eq_zero_iff, map_sub, map_sum]
    simp only [map_smul, ← bC_apply]
    rw [hrepr, sub_self]
  -- the degree-one part of the difference vanishes
  have h2 := ctxSpan_le_geSpan (meshPres c) (r_mem_ge2 (meshPres c)) w y hmem
  have h1 := proj_eq_zero_of_geSpan (k := k) (show 1 < 2 by norm_num) h2
  simp only [map_sub, map_sum, map_smul, arrow, proj_path] at h1
  rw [if_pos (by simp)] at h1
  let lc : Hm k w y →ₗ[k] k :=
    (Finsupp.lapply α.toPath) ∘ₗ (finsuppEquiv (k := k) w y).toLinearMap
  have hlc : ∀ p : Quiver.Path w y, lc (path p) = if p = α.toPath then 1 else 0 := by
    intro p
    change (Finsupp.single p (1 : k)) α.toPath = _
    rw [Finsupp.single_apply]
  have h1' := congrArg lc (sub_eq_zero.1 h1)
  rw [hlc, if_pos rfl, map_sum, Finset.sum_eq_zero] at h1'
  · exact one_ne_zero h1'
  · intro i _
    rw [map_smul]
    split_ifs
    · rw [hlc, if_neg (hne i), smul_zero]
    · rw [map_zero, smul_zero]

/-! ### Changing coefficients twice -/

theorem cmap_cmap {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) {x y : V} (g : Hm A x y) : cmap ψ (cmap φ g) = cmap (ψ.comp φ) g := by
  change Finsupp.mapRange ψ ψ.map_zero (Finsupp.mapRange φ φ.map_zero (toFinsupp g)) =
    Finsupp.mapRange (ψ.comp φ) (ψ.comp φ).map_zero (toFinsupp g)
  ext p
  simp

theorem cmap_id {A : Type*} [CommRing A] {x y : V} (g : Hm A x y) :
    cmap (RingHom.id A) g = g := by
  change Finsupp.mapRange (RingHom.id A) (RingHom.id A).map_zero (toFinsupp g) = g
  ext p
  simp; rfl

/-! ### The deformation over the dual numbers -/

/-- The polynomial ring `k[t]`. -/
abbrev Kp (k : Type u) [Field k] := MvPolynomial Unit k

/-- `t ↦ ε`. -/
def φε : Kp k →+* DualNumber k :=
  MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom k k) (fun _ ↦ DualNumber.eps)

/-- Reduction modulo `ε`. -/
def ρ : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

theorem ρ_comp : ((ρ (k := k)).comp (φε (k := k))).comp MvPolynomial.C = RingHom.id k := by
  ext t; simp [φε, ρ]

theorem ρ_X : ρ (φε (k := k) (MvPolynomial.X ())) = 0 := by simp [φε, ρ]

theorem φε_C (t : k) : φε (k := k) (MvPolynomial.C t) = TrivSqZeroExt.inl t := by simp [φε]

theorem φε_X : φε (k := k) (MvPolynomial.X ()) = DualNumber.eps := by simp [φε]

variable (c) in
/-- **Reduction modulo `ε`** `B → C`. -/
def red {w y : V} (g : Hm (DualNumber k) w y) : obj c w ⟶ obj c y := qL c w y (cmap ρ g)

variable (c) in
theorem red_add {w y : V} (g h : Hm (DualNumber k) w y) : red c (g + h) = red c g + red c h := by
  simp [red, cmap_add]

variable (c) in
theorem red_smul {w y : V} (a : DualNumber k) (g : Hm (DualNumber k) w y) :
    red c (a • g) = ρ a • red c g := by
  simp [red, cmap_smul]

variable (c) in
theorem red_comp {w x y : V} (g : Hm (DualNumber k) w x) (h : Hm (DualNumber k) x y) :
    red c (g ≫ h) = red c g ≫ red c h := by
  simp [red, cmap_comp, qL_comp]

variable (c) in
theorem red_path {w y : V} (p : Quiver.Path w y) :
    red c (path (k := DualNumber k) p) = qL c w y (path p) := by
  simp [red, cmap_path]

variable (c) in
theorem red_sum {w y : V} {ι : Type*} (s : Finset ι) (g : ι → Hm (DualNumber k) w y) :
    red c (∑ i ∈ s, g i) = ∑ i ∈ s, red c (g i) := by
  simp [red, cmap_sum]

variable (c) in
theorem red_zero {w y : V} : red c (0 : Hm (DualNumber k) w y) = 0 := by
  simp [red, cmap_zero]

/-! ### The path section -/

/-- **The path section** `ŝ : C(w, y) → kQ[ε](w, y)`, `ŝ(f) = Σ_i f_i p_i`. -/
def sh {w y : V} (f : obj c w ⟶ obj c y) : Hm (DualNumber k) w y :=
  ∑ i, (TrivSqZeroExt.inl ((bC B w y).repr f i) : DualNumber k) • path (B.p w y i)

theorem sh_add {w y : V} (f f' : obj c w ⟶ obj c y) : sh B (f + f') = sh B f + sh B f' := by
  simp [sh, add_smul, Finset.sum_add_distrib, TrivSqZeroExt.inl_add]

theorem sh_smul {w y : V} (t : k) (f : obj c w ⟶ obj c y) :
    sh B (t • f) = (TrivSqZeroExt.inl t : DualNumber k) • sh B f := by
  simp only [sh, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [TrivSqZeroExt.inl_mul]

theorem sh_zero {w y : V} : sh B (0 : obj c w ⟶ obj c y) = 0 := by
  have := sh_add B (0 : obj c w ⟶ obj c y) 0
  rw [add_zero] at this
  simpa using this

theorem sh_sub {w y : V} (f f' : obj c w ⟶ obj c y) : sh B (f - f') = sh B f - sh B f' := by
  have := sh_add B (f - f') f'
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem sh_sum {w y : V} {ι : Type*} (s : Finset ι) (f : ι → (obj c w ⟶ obj c y)) :
    sh B (∑ i ∈ s, f i) = ∑ i ∈ s, sh B (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sh_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sh_add, ih]

theorem red_sh {w y : V} (f : obj c w ⟶ obj c y) : red c (sh B f) = f := by
  rw [sh, red_sum]
  simp only [red_smul, red_path, ← bC_apply]
  conv_rhs => rw [← (bC B w y).sum_repr f]
  rfl

theorem sh_arrow {w y : V} (α : w ⟶ y) : sh B (arrowMor c α) = arrow α := by
  classical
  obtain ⟨i, hi⟩ := exists_arrow_mem B α
  have hb : bC B w y i = arrowMor c α := by rw [bC_apply, hi]; rfl
  rw [sh, ← hb, Module.Basis.repr_self, Finset.sum_eq_single i]
  · rw [Finsupp.single_eq_same, hi]; simp [arrow]
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg (Ne.symm hj), TrivSqZeroExt.inl_zero,
      ← sub_self (1 : TrivSqZeroExt k k), sub_smul, sub_self]
  · simp

variable (c) in
/-- The presentation over `k[t]`. -/
abbrev PK : Pres (Kp k) V := (meshPres c).map MvPolynomial.C

variable (c) in
/-- The presentation over `k[ε]`. -/
abbrev PR : Pres (DualNumber k) V := (PK c).map φε

variable (c) in
/-- **The data of a first-order mesh deformation**: a cutoff `N`, the resolution hypothesis of
Lemma 12.3, and a correction tuple `z_x ∈ C_{q+2}(τx, x)` with `q ≥ 1`. -/
structure Setup where
  N : ℕ
  hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
    path (k := k) p ∈ ctxSpan (meshPres c) (meshPres c).r w y
  hres : ∀ w x, Function.Injective (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x) ∧
    LinearMap.ker (alpha (idealC (meshPres c)) w x) ≤
      LinearMap.range (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x)
  q : ℕ
  hq : 1 ≤ q
  z : MeshFamily c
  hz : ∀ x, z x ∈ ScalarMeshCategory.degreePart c (q + 2) (Q.tau x).1 x.1

namespace Setup

variable (S : Setup c)

/-- Lifts of the corrections to `kQ`. -/
def zh (x : Q.nonprojective) : Hm k (Q.tau x).1 x.1 := (S.hz x).choose

theorem zh_mem (x : Q.nonprojective) : S.zh x ∈ LinearPaths.degreePart (k := k) (S.q + 2) _ _ :=
  (S.hz x).choose_spec.1

theorem qL_zh (x : Q.nonprojective) : qL c _ _ (S.zh x) = S.z x := (S.hz x).choose_spec.2

/-- The perturbation `t · z` over `k[t]`. -/
def fK : ∀ x (t : (PK c).T x), Hm (Kp k) ((PK c).src x t) x :=
  fun x t ↦ (MvPolynomial.X () : Kp k) • cmap MvPolynomial.C (S.zh ⟨x, t.2⟩)

theorem hfK : ∀ x t, S.fK x t ∈ geSpan (Kp k) ((PK c).deg x t + 1) ((PK c).src x t) x := fun x t ↦
  Submodule.smul_mem _ _ (cmap_geSpan _ (geSpan_anti (by have := S.hq; change 3 ≤ S.q + 2; omega)
    _ _ (degreePart_le_geSpan _ _ _ (S.zh_mem ⟨x, t.2⟩))))

/-- **The ideal of the deformation** `B = kQ[ε]/(𝔪^{N+1}, r − εz)`. -/
abbrev IB : IdealFam (DualNumber k) V :=
  idealB (PR c) (fmap (φε (k := k)) (PK c) S.fK) (hf_map (φε (k := k)) (PK c) S.fK S.hfK) S.N

theorem basisR (w y : V) :
    (LinearIndependent (DualNumber k) fun i ↦
      Submodule.Quotient.mk (p := S.IB.I w y) (path (k := DualNumber k) (B.p w y i))) ∧
    Submodule.span (DualNumber k) (Set.range fun i ↦
      Submodule.Quotient.mk (p := S.IB.I w y) (path (k := DualNumber k) (B.p w y i))) = ⊤ :=
  (polynomial_flatness (meshPres c) S.N S.hN S.hres S.fK S.hfK (B.p w y) (B.li w y)
    (B.sp w y)).2 φε

/-- **The basis of `B(w, y)` over `k[ε]`** given by the path basis of `C`. -/
def bR (w y : V) : Module.Basis (B.ι w y) (DualNumber k) (FlatPert.Q S.IB w y) :=
  Module.Basis.mk (S.basisR B w y).1 (by rw [(S.basisR B w y).2])

theorem bR_apply {w y : V} (i : B.ι w y) :
    S.bR B w y i = Submodule.Quotient.mk (path (k := DualNumber k) (B.p w y i)) := by
  simp [bR]

/-- The quotient map onto `B`. -/
abbrev mkB {w y : V} (g : Hm (DualNumber k) w y) : FlatPert.Q S.IB w y :=
  Submodule.Quotient.mk (p := S.IB.I w y) g

theorem mk_comp_congr {w x y : V} {g g' : Hm (DualNumber k) w x} {h h' : Hm (DualNumber k) x y}
    (hg : S.mkB g = S.mkB g') (hh : S.mkB h = S.mkB h') : S.mkB (g ≫ h) = S.mkB (g' ≫ h') := by
  rw [Submodule.Quotient.eq] at hg hh ⊢
  have e : g ≫ h - g' ≫ h' = (g - g') ≫ h + g' ≫ (h - h') := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub]; abel
  rw [e]
  exact add_mem (S.IB.comp_right hg h) (S.IB.comp_left hh g')

/-- The relations of `B` reduce to those of `C`. -/
theorem cmap_rR (x : V) (t : (PR c).T x) :
    cmap ρ ((PR c).r x t) = (meshPres c).r x t := by
  change cmap ρ (cmap φε (cmap MvPolynomial.C ((meshPres c).r x t))) = _
  rw [cmap_cmap, cmap_cmap, ρ_comp, cmap_id]

theorem cmap_fR (x : V) (t : (PR c).T x) : cmap ρ (fmap (φε (k := k)) (PK c) S.fK x t) = 0 := by
  simp only [fmap, Setup.fK, cmap_smul, ρ_X, zero_smul]

/-- **Reduction kills the ideal of `B`.** -/
theorem red_eq_zero {w y : V} {g : Hm (DualNumber k) w y} (hg : g ∈ S.IB.I w y) : red c g = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hg
  clear hg
  have h1 : red c a = 0 := by
    clear hb
    induction ha using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x, t, u, v, rfl⟩ := hg
      have e : red c (rf (PR c) (fmap (φε (k := k)) (PK c) S.fK) x t) =
          qL c _ _ ((meshPres c).r x t) := by
        change qL c _ _ (cmap ρ (rf (PR c) (fmap (φε (k := k)) (PK c) S.fK) x t)) = _
        rw [rf, cmap_sub, cmap_rR, S.cmap_fR, sub_zero]
      rw [red_comp, red_comp, red_path, red_path, e, ← qL_comp, ← qL_comp, qL_eq_zero_iff]
      exact ctx_mem (meshPres c) (meshPres c).r t _ _
    | zero => exact red_zero c
    | add a b _ _ ha hb => rw [red_add, ha, hb, add_zero]
    | smul t a _ ha => rw [red_smul, ha, smul_zero]
  have h2 : red c b = 0 := by
    clear ha h1
    induction hb using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨p, hp, rfl⟩ := hg
      rw [red_path, qL_eq_zero_iff]
      exact S.hN w y p (by omega)
    | zero => exact red_zero c
    | add a b _ _ ha hb => rw [red_add, ha, hb, add_zero]
    | smul t a _ ha => rw [red_smul, ha, smul_zero]
  rw [red_add, h1, h2, add_zero]

/-! ### Coordinates in `B` -/

theorem repr_mkB_sh {w y : V} (f : obj c w ⟶ obj c y) (i : B.ι w y) :
    (S.bR B w y).repr (S.mkB (sh B f)) i = TrivSqZeroExt.inl ((bC B w y).repr f i) := by
  have : S.mkB (sh B f) = ∑ j, (TrivSqZeroExt.inl ((bC B w y).repr f j) : DualNumber k) •
      S.bR B w y j := by
    change (S.IB.I w y).mkQ (sh B f) = _
    rw [sh, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, Submodule.mkQ_apply, S.bR_apply]
  rw [this, (S.bR B w y).repr_sum_self]

/-- The reduction of a morphism of `B`, by coordinates. -/
def redQ {w y : V} (x : FlatPert.Q S.IB w y) : obj c w ⟶ obj c y :=
  ∑ i, ((S.bR B w y).repr x i).fst • bC B w y i

/-- **The `ε`-part** of a morphism of `B`. -/
def π1 {w y : V} (x : FlatPert.Q S.IB w y) : obj c w ⟶ obj c y :=
  ∑ i, ((S.bR B w y).repr x i).snd • bC B w y i

theorem red_eq_redQ {w y : V} (g : Hm (DualNumber k) w y) : red c g = S.redQ B (S.mkB g) := by
  set a := (S.bR B w y).repr (S.mkB g)
  have hsum : S.mkB g = ∑ i, a i • S.mkB (path (k := DualNumber k) (B.p w y i)) := by
    conv_lhs => rw [← (S.bR B w y).sum_repr (S.mkB g)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S.bR_apply]
  have hmem : g - ∑ i, a i • path (k := DualNumber k) (B.p w y i) ∈ S.IB.I w y := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
      ← Submodule.mkQ_apply (p := S.IB.I w y) (∑ _, _), map_sum]
    simp only [map_smul, Submodule.mkQ_apply]
    rw [← hsum, sub_self]
  have h0 := S.red_eq_zero hmem
  have e : red c (g - ∑ i, a i • path (k := DualNumber k) (B.p w y i)) =
      red c g - ∑ i, ρ (a i) • qL c w y (path (B.p w y i)) := by
    simp only [red, cmap_sub, cmap_sum, cmap_smul, cmap_path, map_sub, map_sum, map_smul]
  rw [e, sub_eq_zero] at h0
  rw [h0, redQ]
  simp only [← bC_apply]
  rfl

theorem π1_add {w y : V} (x x' : FlatPert.Q S.IB w y) : S.π1 B (x + x') = S.π1 B x + S.π1 B x' := by
  unfold π1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_add, Finsupp.add_apply, TrivSqZeroExt.snd_add, add_smul]

theorem π1_mkB_sh {w y : V} (f : obj c w ⟶ obj c y) : S.π1 B (S.mkB (sh B f)) = 0 := by
  unfold π1
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [repr_mkB_sh, TrivSqZeroExt.snd_inl, zero_smul]

theorem snd_eps_inl (r : k) :
    ((DualNumber.eps : DualNumber k) * TrivSqZeroExt.inl r).snd = r := by
  rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, DualNumber.fst_eps, DualNumber.snd_eps,
    TrivSqZeroExt.fst_inl, smul_zero, zero_add, op_smul_eq_mul, one_mul]

theorem fst_eps_inl (r : k) :
    ((DualNumber.eps : DualNumber k) * TrivSqZeroExt.inl r).fst = 0 := by
  rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul]

theorem π1_eps {w y : V} (f : obj c w ⟶ obj c y) :
    S.π1 B ((DualNumber.eps : DualNumber k) • S.mkB (sh B f)) = f := by
  unfold π1
  conv_rhs => rw [← (bC B w y).sum_repr f]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, Finsupp.smul_apply, repr_mkB_sh, smul_eq_mul, snd_eps_inl]

theorem redQ_mkB_sh {w y : V} (f : obj c w ⟶ obj c y) : S.redQ B (S.mkB (sh B f)) = f := by
  rw [← red_eq_redQ, red_sh]

/-- **Decomposition** `x = ŝ(x̄) + ε ŝ(π₁ x)`. -/
theorem decomp {w y : V} (x : FlatPert.Q S.IB w y) :
    x = S.mkB (sh B (S.redQ B x)) + (DualNumber.eps : DualNumber k) • S.mkB (sh B (S.π1 B x)) := by
  apply (S.bR B w y).repr.injective
  refine Finsupp.ext fun i ↦ ?_
  rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, repr_mkB_sh, repr_mkB_sh,
    redQ, π1, (bC B w y).repr_sum_self, (bC B w y).repr_sum_self, smul_eq_mul]
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_add, fst_eps_inl, TrivSqZeroExt.fst_inl, add_zero]
  · rw [TrivSqZeroExt.snd_add, snd_eps_inl, TrivSqZeroExt.snd_inl, zero_add]

theorem eps_eps {w y : V} (x : FlatPert.Q S.IB w y) :
    (DualNumber.eps : DualNumber k) • (DualNumber.eps : DualNumber k) • x = (0 : FlatPert.Q S.IB w y) := by
  exact (smul_smul _ _ x).trans ((congrArg (· • x) DualNumber.eps_mul_eps).trans (zero_smul (DualNumber k) x))

theorem π1_pair {w y : V} (f g : obj c w ⟶ obj c y) :
    S.π1 B (S.mkB (sh B f) + (DualNumber.eps : DualNumber k) • S.mkB (sh B g)) = g := by
  rw [π1_add, π1_mkB_sh, π1_eps, zero_add]

theorem π1_inl_smul {w y : V} (t : k) (x : FlatPert.Q S.IB w y) :
    S.π1 B ((TrivSqZeroExt.inl t : DualNumber k) • x) = t • S.π1 B x := by
  unfold π1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero,
    smul_eq_mul]

theorem mkB_add {w y : V} (g h : Hm (DualNumber k) w y) : S.mkB (g + h) = S.mkB g + S.mkB h :=
  Submodule.Quotient.mk_add _

theorem mkB_smul {w y : V} (a : DualNumber k) (g : Hm (DualNumber k) w y) :
    S.mkB (a • g) = a • S.mkB g := Submodule.Quotient.mk_smul _ _ _

/-! ### The cocycle -/

/-- **The `ε`-part of a product of sections** `φ(f, g) = π₁(ŝ f · ŝ g)`. -/
def phi {X Y Z : V} (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) : obj c X ⟶ obj c Z :=
  S.π1 B (S.mkB (sh B f ≫ sh B g))

/-- `ŝ f · ŝ g = ŝ(f g) + ε ŝ(φ(f, g))` in `B`. -/
theorem mkB_comp {X Y Z : V} (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    S.mkB (sh B f ≫ sh B g) =
      S.mkB (sh B (f ≫ g)) + (DualNumber.eps : DualNumber k) • S.mkB (sh B (S.phi B f g)) := by
  conv_lhs => rw [S.decomp B (S.mkB (sh B f ≫ sh B g))]
  rw [← red_eq_redQ, red_comp, red_sh, red_sh]
  rfl

theorem eps_mkB_comp {X Y Z : V} (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    (DualNumber.eps : DualNumber k) • S.mkB (sh B f ≫ sh B g) =
      (DualNumber.eps : DualNumber k) • S.mkB (sh B (f ≫ g)) := by
  rw [mkB_comp, smul_add, eps_eps, add_zero]

theorem phi_add_left {X Y Z : V} (f f' : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    S.phi B (f + f') g = S.phi B f g + S.phi B f' g := by
  simp only [phi, sh_add, Preadditive.add_comp, mkB_add, π1_add]

theorem phi_add_right {X Y Z : V} (f : obj c X ⟶ obj c Y) (g g' : obj c Y ⟶ obj c Z) :
    S.phi B f (g + g') = S.phi B f g + S.phi B f g' := by
  simp only [phi, sh_add, Preadditive.comp_add, mkB_add, π1_add]

theorem phi_smul_left {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    S.phi B (t • f) g = t • S.phi B f g := by
  simp only [phi, sh_smul, Linear.smul_comp, mkB_smul, π1_inl_smul]

theorem phi_smul_right {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    S.phi B f (t • g) = t • S.phi B f g := by
  simp only [phi, sh_smul, Linear.comp_smul, mkB_smul, π1_inl_smul]

theorem π1_assoc_left {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) :
    S.π1 B (S.mkB ((sh B f ≫ sh B g) ≫ sh B h)) = S.phi B (f ≫ g) h + S.phi B f g ≫ h := by
  have e1 : S.mkB (sh B f ≫ sh B g) =
      S.mkB (sh B (f ≫ g) + (DualNumber.eps : DualNumber k) • sh B (S.phi B f g)) := by
    rw [mkB_add, mkB_smul, mkB_comp]
  rw [S.mk_comp_congr e1 rfl, Preadditive.add_comp, Linear.smul_comp, mkB_add, mkB_smul,
    mkB_comp, eps_mkB_comp, add_assoc, ← smul_add, ← mkB_add, ← sh_add, π1_pair]

theorem π1_assoc_right {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) :
    S.π1 B (S.mkB (sh B f ≫ (sh B g ≫ sh B h))) = S.phi B f (g ≫ h) + f ≫ S.phi B g h := by
  have e1 : S.mkB (sh B g ≫ sh B h) =
      S.mkB (sh B (g ≫ h) + (DualNumber.eps : DualNumber k) • sh B (S.phi B g h)) := by
    rw [mkB_add, mkB_smul, mkB_comp]
  rw [S.mk_comp_congr rfl e1, Preadditive.comp_add, Linear.comp_smul, mkB_add, mkB_smul,
    mkB_comp, eps_mkB_comp, add_assoc, ← smul_add, ← mkB_add, ← sh_add, π1_pair]

/-- **The cocycle identity.** -/
theorem phi_cocycle {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) :
    f ≫ S.phi B g h - S.phi B (f ≫ g) h + S.phi B f (g ≫ h) - S.phi B f g ≫ h = 0 := by
  have e := S.π1_assoc_left B f g h
  rw [Category.assoc, π1_assoc_right] at e
  rw [← sub_eq_zero.2 e]; abel

/-! ### The mesh value -/

theorem eps_mkB_red {w y : V} (u : Hm (DualNumber k) w y) :
    (DualNumber.eps : DualNumber k) • S.mkB u =
      (DualNumber.eps : DualNumber k) • S.mkB (sh B (red c u)) := by
  conv_lhs => rw [S.decomp B (S.mkB u)]
  rw [smul_add, eps_eps, add_zero, ← red_eq_redQ]

theorem rR_eq (x : Q.nonprojective) (t : (PR c).T x.1) :
    (PR c).r x.1 t = ∑ a : Σ y : V, y ⟶ x.1, (TrivSqZeroExt.inl ((c x a.1 a.2 : kˣ) : k) :
      DualNumber k) • (arrow (Q.mate x a.1 a.2) ≫ arrow a.2) := by
  change cmap φε (cmap MvPolynomial.C (meshRelation c ⟨x.1, t.2⟩)) = _
  simp only [meshRelation, cmap_sum, cmap_smul, cmap_path, φε_C, arrow, path_comp_path]

theorem fR_eq (x : V) (t : (PR c).T x) :
    fmap (φε (k := k)) (PK c) S.fK x t =
      (DualNumber.eps : DualNumber k) • cmap ((φε (k := k)).comp MvPolynomial.C) (S.zh ⟨x, t.2⟩) := by
  simp only [fmap, Setup.fK, cmap_smul, φε_X, cmap_cmap]

theorem red_fR_part (x : V) (t : (PR c).T x) :
    red c (cmap ((φε (k := k)).comp MvPolynomial.C) (S.zh ⟨x, t.2⟩)) = S.z ⟨x, t.2⟩ := by
  change qL c _ _ (cmap ρ (cmap ((φε (k := k)).comp MvPolynomial.C) (S.zh ⟨x, t.2⟩))) = _
  rw [cmap_cmap, ← RingHom.comp_assoc, ρ_comp, cmap_id, qL_zh]

theorem mkB_rR (x : V) (t : (PR c).T x) :
    S.mkB ((PR c).r x t) = S.mkB (fmap (φε (k := k)) (PK c) S.fK x t) := by
  rw [Submodule.Quotient.eq]
  have := ctx_mem (PR c) (rf (PR c) (fmap (φε (k := k)) (PK c) S.fK)) t (𝟙 _) (𝟙 _)
  rw [Category.id_comp, Category.comp_id] at this
  exact Submodule.mem_sup_left this

theorem mkB_sum {w y : V} {ι : Type*} (s : Finset ι) (g : ι → Hm (DualNumber k) w y) :
    S.mkB (∑ i ∈ s, g i) = ∑ i ∈ s, S.mkB (g i) :=
  map_sum (S.IB.I w y).mkQ g s

theorem mkB_zero {w y : V} : S.mkB (0 : Hm (DualNumber k) w y) = 0 :=
  Submodule.Quotient.mk_zero _

/-- **The mesh value of `φ` is the correction tuple** `z`. -/
theorem meshVal_phi (x : Q.nonprojective) :
    ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
      S.phi B (arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2) = S.z x := by
  obtain ⟨cc, hcc⟩ : ∃ cc : (Σ y : V, y ⟶ x.1) → k,
      ∀ a, ((c x a.1 a.2 : kˣ) : k) = cc a := ⟨_, fun _ ↦ rfl⟩
  simp only [hcc]
  have hr0 := rR_eq (c := c) x ⟨(), x.2⟩
  simp only [hcc] at hr0
  have hr : (PR c).r x.1 ⟨(), x.2⟩ = ∑ a : Σ y : V, y ⟶ x.1,
      (TrivSqZeroExt.inl (cc a) : DualNumber k) • (arrow (Q.mate x a.1 a.2) ≫ arrow a.2) := hr0
  have hm := MeshWalk.mesh_zero (c := c) x
  simp only [hcc] at hm
  have hL : S.mkB ((PR c).r x.1 ⟨(), x.2⟩) = (DualNumber.eps : DualNumber k) • S.mkB (sh B
      (∑ a : Σ y : V, y ⟶ x.1, cc a •
        S.phi B (arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2))) := by
    rw [hr]
    simp only [← sh_arrow B]
    rw [mkB_sum]
    simp only [mkB_smul, mkB_comp, smul_add, Finset.sum_add_distrib]
    have h0 : ∑ a : Σ y : V, y ⟶ x.1, (TrivSqZeroExt.inl (cc a) : DualNumber k) •
        S.mkB (sh B (arrowMor c (Q.mate x a.1 a.2) ≫ arrowMor c a.2)) = 0 := by
      simp only [← mkB_smul, ← mkB_sum, ← sh_smul, ← sh_sum, hm, sh_zero, mkB_zero]
    rw [h0, zero_add]
    simp only [sh_sum, sh_smul, mkB_sum, mkB_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [smul_comm]
  have hR : S.mkB ((PR c).r x.1 ⟨(), x.2⟩) =
      (DualNumber.eps : DualNumber k) • S.mkB (sh B (S.z x)) := by
    rw [S.mkB_rR x.1 ⟨(), x.2⟩, S.fR_eq x.1 ⟨(), x.2⟩, mkB_smul, eps_mkB_red,
      S.red_fR_part x.1 ⟨(), x.2⟩]
  have := congrArg (S.π1 B) (hL.symm.trans hR)
  rwa [π1_eps, π1_eps] at this

end Setup

/-! ### Homogeneous components of a cocycle -/

variable (c) in
/-- A bilinear Hochschild two-cocycle of `C`, not necessarily homogeneous. -/
structure RawCocycle where
  φ : ∀ {X Y Z : V}, (obj c X ⟶ obj c Y) → (obj c Y ⟶ obj c Z) → (obj c X ⟶ obj c Z)
  add_left : ∀ {X Y Z : V} (f f' : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z),
    φ (f + f') g = φ f g + φ f' g
  add_right : ∀ {X Y Z : V} (f : obj c X ⟶ obj c Y) (g g' : obj c Y ⟶ obj c Z),
    φ f (g + g') = φ f g + φ f g'
  smul_left : ∀ {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z),
    φ (t • f) g = t • φ f g
  smul_right : ∀ {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z),
    φ f (t • g) = t • φ f g
  cocycle : ∀ {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z), f ≫ φ g h - φ (f ≫ g) h + φ f (g ≫ h) - φ f g ≫ h = 0

namespace RawCocycle

variable (Φ : RawCocycle c)

theorem zero_left {X Y Z : V} (g : obj c Y ⟶ obj c Z) : Φ.φ (0 : obj c X ⟶ obj c Y) g = 0 := by
  have := Φ.add_left (0 : obj c X ⟶ obj c Y) 0 g
  rw [add_zero] at this
  simpa using this

theorem zero_right {X Y Z : V} (f : obj c X ⟶ obj c Y) : Φ.φ f (0 : obj c Y ⟶ obj c Z) = 0 := by
  have := Φ.add_right f (0 : obj c Y ⟶ obj c Z) 0
  rw [add_zero] at this
  simpa using this

include hfin in
theorem degProj_comp_right {p r : ℕ} {x y z : V} (f : obj c x ⟶ obj c y) {h : obj c y ⟶ obj c z}
    (hh : h ∈ degreePart c p y z) : degProj c (r + p) x z (f ≫ h) = degProj c r x y f ≫ h := by
  classical
  conv_lhs => rw [eq_sum_degProj c (MeshWalk.Nb_spec hfin) f, Preadditive.sum_comp, map_sum]
  rw [Finset.sum_eq_single r]
  · rw [degProj_of_mem c (comp_mem_degreePart' c (degProj_mem c r f) hh), if_pos rfl]
  · intro e _ he
    rw [degProj_of_mem c (comp_mem_degreePart' c (degProj_mem c e f) hh), if_neg (by omega)]
  · intro hr
    have := degProj_mem c r f
    rw [MeshWalk.Nb_spec hfin r x y (by simpa using hr), Submodule.mem_bot] at this
    rw [this, Limits.zero_comp, map_zero]

/-- **The degree-`q` component** of a cocycle. -/
def φq (q : ℕ) {X Y Z : V} (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) : obj c X ⟶ obj c Z :=
  ∑ d ∈ Finset.range (MeshWalk.Nb hfin), ∑ e ∈ Finset.range (MeshWalk.Nb hfin),
    degProj c (d + e + q) X Z (Φ.φ (degProj c d X Y f) (degProj c e Y Z g))

theorem φq_hom (q : ℕ) {X Y Z : V} {a b : ℕ} {f : obj c X ⟶ obj c Y} {g : obj c Y ⟶ obj c Z}
    (hf : f ∈ degreePart c a X Y) (hg : g ∈ degreePart c b Y Z) :
    Φ.φq q f g = degProj c (a + b + q) X Z (Φ.φ f g) := by
  classical
  by_cases ha : a < MeshWalk.Nb hfin
  · by_cases hb : b < MeshWalk.Nb hfin
    · rw [φq, Finset.sum_eq_single a, Finset.sum_eq_single b]
      · rw [degProj_of_mem c hf, if_pos rfl, degProj_of_mem c hg, if_pos rfl]
      · intro e _ he
        rw [degProj_of_mem c hg, if_neg (Ne.symm he), Φ.zero_right, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 hb) h
      · intro d _ hd
        refine Finset.sum_eq_zero fun e _ ↦ ?_
        rw [degProj_of_mem c hf, if_neg (Ne.symm hd), Φ.zero_left, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 ha) h
    · have : g = 0 := by
        have := MeshWalk.Nb_spec hfin b Y Z (by omega)
        rw [this, Submodule.mem_bot] at hg; exact hg
      subst this
      simp [φq, Φ.zero_right]
  · have : f = 0 := by
      have := MeshWalk.Nb_spec hfin a X Y (by omega)
      rw [this, Submodule.mem_bot] at hf; exact hf
    subst this
    simp [φq, Φ.zero_left]

theorem φq_add_left (q : ℕ) {X Y Z : V} (f f' : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    Φ.φq q (f + f') g = Φ.φq q f g + Φ.φq q f' g := by
  simp only [φq, map_add, Φ.add_left, ← Finset.sum_add_distrib]

theorem φq_add_right (q : ℕ) {X Y Z : V} (f : obj c X ⟶ obj c Y) (g g' : obj c Y ⟶ obj c Z) :
    Φ.φq q f (g + g') = Φ.φq q f g + Φ.φq q f g' := by
  simp only [φq, map_add, Φ.add_right, ← Finset.sum_add_distrib]

theorem φq_smul_left (q : ℕ) {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    Φ.φq q (t • f) g = t • Φ.φq q f g := by
  simp only [φq, map_smul, Φ.smul_left, Finset.smul_sum]

theorem φq_smul_right (q : ℕ) {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y)
    (g : obj c Y ⟶ obj c Z) : Φ.φq q f (t • g) = t • Φ.φq q f g := by
  simp only [φq, map_smul, Φ.smul_right, Finset.smul_sum]

include hfin in
/-- An additive function vanishing on homogeneous morphisms vanishes. -/
theorem eq_zero_of_hom {X Y : V} {M : Type*} [AddCommGroup M] (F : (obj c X ⟶ obj c Y) →+ M)
    (h : ∀ d (f : obj c X ⟶ obj c Y), f ∈ degreePart c d X Y → F f = 0)
    (f : obj c X ⟶ obj c Y) : F f = 0 := by
  rw [eq_sum_degProj c (MeshWalk.Nb_spec hfin) f, map_sum]
  exact Finset.sum_eq_zero fun d _ ↦ h d _ (degProj_mem c d f)

/-- The cocycle expression of `φ_q`. -/
def cocExpr (q : ℕ) {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) : obj c W ⟶ obj c Z :=
  f ≫ Φ.φq q g h - Φ.φq q (f ≫ g) h + Φ.φq q f (g ≫ h) - Φ.φq q f g ≫ h

theorem cocExpr_hom (q : ℕ) {W X Y Z : V} {a b d : ℕ} {f : obj c W ⟶ obj c X}
    {g : obj c X ⟶ obj c Y} {h : obj c Y ⟶ obj c Z} (hf : f ∈ degreePart c a W X)
    (hg : g ∈ degreePart c b X Y) (hh : h ∈ degreePart c d Y Z) : Φ.cocExpr q f g h = 0 := by
  rw [cocExpr, Φ.φq_hom q hg hh, Φ.φq_hom q (comp_mem_degreePart' c hf hg) hh,
    Φ.φq_hom q hf (comp_mem_degreePart' c hg hh), Φ.φq_hom q hf hg,
    ← MeshWalk.degProj_comp_left hfin hf, ← degProj_comp_right (Φ.φ f g) hh]
  rw [show a + (b + d + q) = a + b + d + q by omega, show a + (b + d) + q = a + b + d + q by omega,
    show a + b + q + d = a + b + d + q by omega, ← map_sub, ← map_add, ← map_sub, Φ.cocycle,
    map_zero]

theorem cocExpr_eq_zero (q : ℕ) {W X Y Z : V} (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) : Φ.cocExpr q f g h = 0 := by
  -- additivity in each variable
  have h1 : ∀ (g : obj c X ⟶ obj c Y) (h : obj c Y ⟶ obj c Z) {b d : ℕ},
      g ∈ degreePart c b X Y → h ∈ degreePart c d Y Z →
        ∀ f : obj c W ⟶ obj c X, Φ.cocExpr q f g h = 0 := by
    intro g h b d hg hh
    refine eq_zero_of_hom (AddMonoidHom.mk' (fun f ↦ Φ.cocExpr q f g h) fun f f' ↦ ?_)
      (fun a f hf ↦ Φ.cocExpr_hom q hf hg hh)
    simp only [cocExpr, Preadditive.add_comp, Φ.φq_add_left, Preadditive.comp_add]; abel
  have h2 : ∀ (h : obj c Y ⟶ obj c Z) {d : ℕ}, h ∈ degreePart c d Y Z →
      ∀ (f : obj c W ⟶ obj c X) (g : obj c X ⟶ obj c Y), Φ.cocExpr q f g h = 0 := by
    intro h d hh f
    refine eq_zero_of_hom (AddMonoidHom.mk' (fun g ↦ Φ.cocExpr q f g h) fun g g' ↦ ?_)
      (fun b g hg ↦ h1 g h hg hh f)
    simp only [cocExpr, Preadditive.add_comp, Preadditive.comp_add, Φ.φq_add_left,
      Φ.φq_add_right]; abel
  refine eq_zero_of_hom (AddMonoidHom.mk' (fun h ↦ Φ.cocExpr q f g h) fun h h' ↦ ?_)
    (fun d h hh ↦ h2 h hh f g) h
  simp only [cocExpr, Preadditive.comp_add, Φ.φq_add_right]; abel

/-- **The homogeneous cocycle** of internal degree `q`. -/
def toCat (q : ℕ) : MeshWalk.CatCocycle c q where
  φ := Φ.φq q
  add_left := Φ.φq_add_left q
  add_right := Φ.φq_add_right q
  smul_left := Φ.φq_smul_left q
  smul_right := Φ.φq_smul_right q
  cocycle := Φ.cocExpr_eq_zero q
  deg hf hg := by rw [Φ.φq_hom q hf hg]; exact degProj_mem c _ _

end RawCocycle

namespace Setup

variable (S : Setup c)

/-- The cocycle of the deformation. -/
def raw : RawCocycle c where
  φ := S.phi B
  add_left := S.phi_add_left B
  add_right := S.phi_add_right B
  smul_left := S.phi_smul_left B
  smul_right := S.phi_smul_right B
  cocycle := S.phi_cocycle B

/-- **The deformation gives a homogeneous cocycle with mesh value `z`.** -/
theorem meshVal_toCat : ((S.raw B).toCat S.q).meshVal = S.z := by
  funext x
  rw [MeshWalk.CatCocycle.meshVal]
  change ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
    (S.raw B).φq S.q (arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2) = _
  simp only [(S.raw B).φq_hom S.q (MeshWalk.arrowMor_mem_degreePart (c := c) _)
    (MeshWalk.arrowMor_mem_degreePart (c := c) _)]
  rw [show 1 + 1 + S.q = S.q + 2 by omega]
  simp only [← map_smul, ← map_sum]
  change degProj c (S.q + 2) _ _ (∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
    S.phi B (arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2)) = _
  rw [S.meshVal_phi B x, degProj_of_mem c (S.hz x), if_pos rfl]

end Setup

include hfin in
/-- **Every correction tuple is the mesh value of a homogeneous cocycle** (the first-order
deformation `r − εz` of `C`, Corollary 12.4). -/
theorem exists_catCocycle (S : Setup c) : ∃ Φ : MeshWalk.CatCocycle c S.q, Φ.meshVal = S.z := by
  obtain ⟨B⟩ := nonempty_pathBases c
  exact ⟨(S.raw B).toCat S.q, S.meshVal_toCat B⟩

end MeshFirstOrder

end MultiplicativeBasisDeformations

/-! ## Proposition 12.5: the full Hochschild comparison -/

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt FlatPert

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

include hfin hfd in
/-- **Proposition 12.5, surjectivity** (`prop:full-hochschild-comparison`): if the mesh
presentations of `C` are resolutions (the hypothesis of Lemma 12.3), every class of
`coker D_{q+1}` in degree `q + 2 ≥ 3` is `Ψ[μ]` for a Hochschild two-cocycle `μ` of `A₀` of
internal degree `q`: the corner of the first-order deformation `r − εz` of `C`. -/
theorem Ψc_surjective
    (hres : ∀ w x, Function.Injective (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x) ∧
      LinearMap.ker (alpha (idealC (meshPres c)) w x) ≤
        LinearMap.range (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x))
    {q : ℕ} (hq : 1 ≤ q) (z : MeshFamily c)
    (hz : ∀ x, z x ∈ ScalarMeshCategory.degreePart c (q + 2) (Q.tau x).1 x.1) :
    ∃ (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) (_ : IsHCocycle μ)
      (_ : HDeg (galgA0 D hfin) μ (q : ℤ)) (Ld : LiftData D hfin q μ),
      Ψc Ld = Submodule.Quotient.mk z := by
  haveI := hfin
  obtain ⟨N, hN⟩ := MeshFirstOrder.exists_hN c
  obtain ⟨Φ, hΦ⟩ := MeshFirstOrder.exists_catCocycle (c := c) ⟨N, hN, hres, q, hq, z, hz⟩
  exact ⟨catMu D Φ, catMu_isHCocycle D Φ, catMu_hDeg D hfin Φ, catLift D hfin Φ,
    (Ψc_catLift D hfin Φ).trans (congrArg _ hΦ)⟩

include hfin hfd in
/-- **Proposition 12.5** (`prop:full-hochschild-comparison`): in every internal degree `q ≥ 1`,
`Ψ : HH²(A₀)_q → coker D_{q+1}` is an isomorphism — onto the degree-`(q+2)` mesh families, and
injective by Proposition 7.7. -/
theorem fullHochschildComparison (J : D.InjData) (h1 : DegOne D)
    (hres : ∀ w x, Function.Injective (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x) ∧
      LinearMap.ker (alpha (idealC (meshPres c)) w x) ≤
        LinearMap.range (relMap (meshPres c) (idealC (meshPres c)) (meshPres c).r w x))
    {q : ℕ} (hq : 1 ≤ q) :
    (∀ (z : MeshFamily c), (∀ x, z x ∈ ScalarMeshCategory.degreePart c (q + 2) (Q.tau x).1 x.1) →
      ∃ (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) (_ : IsHCocycle μ)
        (_ : HDeg (galgA0 D hfin) μ (q : ℤ)) (Ld : LiftData D hfin q μ),
        Ψc Ld = Submodule.Quotient.mk z) ∧
    ∀ (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) (_ : IsHCocycle μ)
      (_ : HDeg (galgA0 D hfin) μ (q : ℤ)) (Ld : LiftData D hfin q μ), Ψc Ld = 0 →
      ∃ H : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
        (∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + q) (H a)) ∧
        μ = hcobdry H :=
  ⟨fun z hz ↦ Ψc_surjective D hfin hres hq z hz,
    fun _ hμ hμdeg Ld h ↦ eq_hcobdry_of_Ψc_eq_zero J h1 hμ hμdeg Ld h⟩

end MeshWalk

end MultiplicativeBasisDeformations
