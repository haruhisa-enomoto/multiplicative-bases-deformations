import MultiplicativeBasisDeformations.Refinements.FlatPerturbation

/-!
# Lemma 12.3: the dimension count

The dimension part of `lem:flat-mesh-perturbations` over a field: the identities `ZH = I`,
`ZH_B ≥ I`, the bound `H_B ≤ H` and the matrix argument (see `FlatPerturbation.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace FlatPert

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [DecidableEq V]
  [∀ x y : V, DecidableEq (x ⟶ y)]

open LinearPaths

section Alpha

variable (J : IdealFam k V) [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- **The arrow map hits everything but the top**: `dim C(w, x) = rank α + δ_{wx}`. -/
theorem finrank_alpha [∀ w y, FiniteDimensional k (Q J w y)] (w x : V) :
    Module.finrank k (Q J w x) =
      Module.finrank k (LinearMap.range (alpha J w x)) + if w = x then 1 else 0 := by
  by_cases hwx : w = x
  · subst hwx
    rw [if_pos rfl]
    have hrange : LinearMap.range (alpha J w w) = LinearMap.ker (epsQ J w) := by
      apply le_antisymm
      · rintro _ ⟨z, rfl⟩
        rw [LinearMap.mem_ker]
        simp only [alpha, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (z a)
        rw [← hg, compQ_mk]
        exact nilCoeff_geSpan (by simpa using comp_geSpan (mem_geSpan_zero g) (arrow_mem_ge1 a.2))
      · intro y hy
        obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        refine mem_range_alpha J g ?_
        rw [proj_zero_endo]
        have : nilCoeff (k := k) w g = 0 := hy
        rw [this, zero_smul]
    have hsurj : Function.Surjective (epsQ J w) := fun c ↦
      ⟨Submodule.Quotient.mk (c • 𝟙 _), by
        change nilCoeff w (c • 𝟙 _) = c
        rw [map_smul, nilCoeff_id, smul_eq_mul, mul_one]⟩
    rw [hrange, ← LinearMap.finrank_range_add_finrank_ker (epsQ J w),
      LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, add_comm]
  · rw [if_neg hwx, add_zero]
    have : LinearMap.range (alpha J w x) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact mem_range_alpha J g (proj_zero_of_ne hwx g)
    rw [this, finrank_top]

end Alpha

variable (P : Pres k V) [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (f : ∀ x (t : P.T x), Hm k (P.src x t) x)
  (hf : ∀ x t, f x t ∈ geSpan k (P.deg x t + 1) (P.src x t) x) (N : ℕ)
  [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]

include hf in
/-- **`H_B ≤ H`.** -/
theorem finrank_B_le (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y) (w y : V) :
    Module.finrank k (Q (idealB P f hf N) w y) ≤ Module.finrank k (Q (idealC P) w y) := by
  classical
  haveI := finiteDimensional_Q (idealC P) (geSpan_le_C P N hN)
  haveI := finiteDimensional_Q (idealB P f hf N) (geSpan_le_B P f hf N)
  set s : Set (Q (idealC P) w y) := Set.range fun p : Quiver.Path w y ↦
    Submodule.Quotient.mk (path (k := k) p)
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent k s
  have htop : Submodule.span k t = ⊤ := by rw [hspan]; exact span_paths_eq_top (idealC P) w y
  have htfin : t.Finite := hli.finite
  haveI : Fintype t := htfin.fintype
  have hcard : Module.finrank k (Q (idealC P) w y) = Fintype.card t := by
    have := finrank_span_eq_card hli
    rw [Subtype.range_coe] at this
    rw [← finrank_top, ← htop, this]
  choose pth hpth using fun τ : t ↦ hts τ.2
  set S := Set.range pth
  have himg : (fun p ↦ Submodule.Quotient.mk (p := ctxSpan P P.r w y) (path (k := k) p)) '' S =
      t := by
    ext z
    constructor
    · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
      exact (hpth τ).symm ▸ τ.2
    · intro hz
      exact ⟨pth ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, hpth ⟨z, hz⟩⟩
  have hB := span_B P f hf N hN S (by rw [himg]; exact htop)
  set T := Set.range fun τ : t ↦
    Submodule.Quotient.mk (p := (idealB P f hf N).I w y) (path (k := k) (pth τ))
  have hT : (fun p ↦ Submodule.Quotient.mk (p := (idealB P f hf N).I w y) (path (k := k) p)) '' S =
      T := by
    rw [← Set.range_comp]; rfl
  rw [hT] at hB
  haveI : Fintype T := Set.fintypeRange _
  calc Module.finrank k (Q (idealB P f hf N) w y)
      = Module.finrank k (Submodule.span k T) := by rw [hB, finrank_top]
    _ ≤ T.toFinset.card := finrank_span_le_card T
    _ = Fintype.card T := Set.toFinset_card T
    _ ≤ Fintype.card t := Fintype.card_range_le _
    _ = _ := hcard.symm

/-! ### The dimension matrices -/

/-- **The matrix argument** (`deformation-refinements.tex`): `ZH = I`, `ZH_B ≥ I` and
`H_B ≤ H` force `H_B = H` and `ZH_B = I`. -/
theorem matrix_arg {W : Type} [Fintype W] [DecidableEq W] (A R H HB : W → W → ℕ)
    (hC : ∀ w x, ∑ y, R y x * H w y + H w x = ∑ y, A y x * H w y + if w = x then 1 else 0)
    (hB : ∀ w x, ∑ y, A y x * HB w y + (if w = x then 1 else 0) ≤ ∑ y, R y x * HB w y + HB w x)
    (hle : ∀ w y, HB w y ≤ H w y) :
    HB = H ∧ ∀ w x, ∑ y, A y x * HB w y + (if w = x then 1 else 0) =
      ∑ y, R y x * HB w y + HB w x := by
  classical
  let Z : Matrix W W ℚ := Matrix.of fun y x ↦ (if y = x then 1 else 0) - (A y x : ℚ) + R y x
  let Hq : Matrix W W ℚ := Matrix.of fun w y ↦ (H w y : ℚ)
  let HBq : Matrix W W ℚ := Matrix.of fun w y ↦ (HB w y : ℚ)
  have hZ : ∀ (G : W → W → ℕ) w x, (Matrix.of (fun w y ↦ (G w y : ℚ)) * Z) w x =
      (G w x : ℚ) - ∑ y, (A y x : ℚ) * G w y + ∑ y, (R y x : ℚ) * G w y := by
    intro G w x
    simp only [Matrix.mul_apply, Matrix.of_apply, Z, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    simp only [mul_comm]
  have h1 : Hq * Z = 1 := by
    ext w x
    have := hZ H w x
    rw [this, Matrix.one_apply]
    have hc := hC w x
    have hc' : ((∑ y, R y x * H w y + H w x : ℕ) : ℚ) =
        ((∑ y, A y x * H w y + if w = x then 1 else 0 : ℕ) : ℚ) := by rw [hc]
    push_cast at hc'
    split_ifs at hc' ⊢ <;> linarith
  have h2 : Z * Hq = 1 := mul_eq_one_comm.1 h1
  set E : Matrix W W ℚ := HBq * Z - 1
  have hE : ∀ w x, 0 ≤ E w x := by
    intro w x
    simp only [E, Matrix.sub_apply, Matrix.one_apply]
    have := hZ HB w x
    rw [this]
    have hb := hB w x
    have hb' : ((∑ y, A y x * HB w y + if w = x then 1 else 0 : ℕ) : ℚ) ≤
        ((∑ y, R y x * HB w y + HB w x : ℕ) : ℚ) := by exact_mod_cast hb
    push_cast at hb'
    split_ifs at hb' ⊢ <;> linarith
  have h3 : HBq = Hq + E * Hq := by
    calc HBq = HBq * (Z * Hq) := by rw [h2, Matrix.mul_one]
      _ = (HBq * Z) * Hq := by rw [Matrix.mul_assoc]
      _ = (1 + E) * Hq := by simp only [E, add_sub_cancel]
      _ = Hq + E * Hq := by rw [Matrix.add_mul, Matrix.one_mul]
  have hEH : ∀ w y, 0 ≤ (E * Hq) w y := fun w y ↦
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (hE w x) (by simp [Hq, Matrix.of_apply])
  have hEH0 : E * Hq = 0 := by
    ext w y
    have h := congrFun (congrFun h3 w) y
    simp only [Matrix.add_apply] at h
    have hl : (HB w y : ℚ) ≤ H w y := by exact_mod_cast hle w y
    have : HBq w y = (HB w y : ℚ) := rfl
    have : Hq w y = (H w y : ℚ) := rfl
    have := hEH w y
    rw [Matrix.zero_apply]
    linarith
  have hEz : E = 0 := by
    calc E = E * (Hq * Z) := by rw [h1, Matrix.mul_one]
      _ = (E * Hq) * Z := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hEH0, Matrix.zero_mul]
  have hHB : HBq = Hq := by rw [h3, hEH0, add_zero]
  refine ⟨funext fun w ↦ funext fun y ↦ ?_, fun w x ↦ ?_⟩
  · have := congrFun (congrFun hHB w) y
    have h' : (HB w y : ℚ) = H w y := this
    exact_mod_cast h'
  · have hEwx := congrFun (congrFun hEz w) x
    simp only [E, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply] at hEwx
    have := hZ HB w x
    rw [this] at hEwx
    have key : ((∑ y, A y x * HB w y + if w = x then 1 else 0 : ℕ) : ℚ) =
        ((∑ y, R y x * HB w y + HB w x : ℕ) : ℚ) := by
      push_cast
      split_ifs at hEwx ⊢ <;> linarith
    exact_mod_cast key

/-! ### The dimension identities -/

theorem sum_arrows (x : V) (h : V → ℕ) :
    ∑ a : Σ y : V, y ⟶ x, h a.1 = ∑ y, Fintype.card (y ⟶ x) * h y := by
  rw [show (Finset.univ : Finset (Σ y : V, y ⟶ x)) =
    Finset.univ.sigma (fun _ ↦ Finset.univ) from by ext; simp, Finset.sum_sigma]
  exact Finset.sum_congr rfl fun y _ ↦ by simp

theorem sum_rels (x : V) (h : V → ℕ) :
    ∑ t : P.T x, h (P.src x t) = ∑ y, Fintype.card {t : P.T x // P.src x t = y} * h y := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := P.src x)]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.1 ht).2], Finset.sum_const,
    smul_eq_mul, Fintype.card_subtype]

theorem r_comp_mem_C (x : V) (t : P.T x) (w : V) (u : Hm k w (P.src x t)) :
    u ≫ P.r x t ∈ (idealC P).I w x := by
  have := ctx_mem P P.r t u (𝟙 _)
  rwa [Category.comp_id] at this

include hf in
theorem rf_comp_mem_B (x : V) (t : P.T x) (w : V) (u : Hm k w (P.src x t)) :
    u ≫ rf P f x t ∈ (idealB P f hf N).I w x := by
  have := ctx_mem P (rf P f) t u (𝟙 _)
  rw [Category.comp_id] at this
  exact Submodule.mem_sup_left this

theorem r_proj0 (x : V) (t : P.T x) : proj (k := k) 0 (P.src x t) x (P.r x t) = 0 :=
  proj_eq_zero_of_geSpan (by norm_num) (r_mem_ge2 P x t)

/-- **`ZH = I`** from the assumed resolutions of `C`. -/
theorem dim_C (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y)
    (hC : ∀ w x, Function.Injective (relMap P (idealC P) P.r w x) ∧
      LinearMap.ker (alpha (idealC P) w x) ≤ LinearMap.range (relMap P (idealC P) P.r w x))
    (w x : V) :
    ∑ t : P.T x, Module.finrank k (Q (idealC P) w (P.src x t)) + Module.finrank k (Q (idealC P) w x) =
      ∑ a : Σ y : V, y ⟶ x, Module.finrank k (Q (idealC P) w a.1) + if w = x then 1 else 0 := by
  have := finiteDimensional_Q (idealC P) (geSpan_le_C P N hN)
  have hrange : LinearMap.range (relMap P (idealC P) P.r w x) =
      LinearMap.ker (alpha (idealC P) w x) := by
    refine le_antisymm ?_ (hC w x).2
    rintro _ ⟨z, rfl⟩
    exact alpha_relMap P (idealC P) P.r (r_comp_mem_C P) (r_proj0 P) w x z
  have h1 := LinearMap.finrank_range_of_inj (hC w x).1
  rw [Module.finrank_pi_fintype] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (alpha (idealC P) w x)
  rw [Module.finrank_pi_fintype] at h2
  have h3 := finrank_alpha (idealC P) w x
  rw [hrange] at h1
  omega

include hf in
/-- **`ZH_B ≥ I`** from the exactness of the perturbed presentation at the arrow term. -/
theorem dim_B (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y) (w x : V) :
    ∑ a : Σ y : V, y ⟶ x, Module.finrank k (Q (idealB P f hf N) w a.1) + (if w = x then 1 else 0) ≤
      ∑ t : P.T x, Module.finrank k (Q (idealB P f hf N) w (P.src x t)) +
        Module.finrank k (Q (idealB P f hf N) w x) := by
  have := finiteDimensional_Q (idealB P f hf N) (geSpan_le_B P f hf N)
  have h1 := Submodule.finrank_mono (ker_alpha_B P f hf N hN w x)
  have h2 := LinearMap.finrank_range_le (relMap P (idealB P f hf N) (rf P f) w x)
  rw [Module.finrank_pi_fintype] at h2
  have h3 := LinearMap.finrank_range_add_finrank_ker (alpha (idealB P f hf N) w x)
  rw [Module.finrank_pi_fintype] at h3
  have h4 := finrank_alpha (idealB P f hf N) w x
  omega

/-! ### Lemma 12.3 -/

include hf in
/-- A path basis of `C` lifts to a basis of `B` when `B` and `C` have the same dimensions. -/
theorem lift_basis_of_finrank (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y)
    (hdim : ∀ w y, Module.finrank k (Q (idealB P f hf N) w y) =
      Module.finrank k (Q (idealC P) w y))
    (w y : V) {ι : Type} [Fintype ι] (p : ι → Quiver.Path w y)
    (hli : LinearIndependent k (fun i ↦ Submodule.Quotient.mk (p := (idealC P).I w y)
        (path (k := k) (p i))))
    (hsp : Submodule.span k (Set.range fun i ↦ Submodule.Quotient.mk (p := (idealC P).I w y)
        (path (k := k) (p i))) = ⊤) :
    LinearIndependent k (fun i ↦ Submodule.Quotient.mk (p := (idealB P f hf N).I w y)
        (path (k := k) (p i))) ∧
      Submodule.span k (Set.range fun i ↦ Submodule.Quotient.mk (p := (idealB P f hf N).I w y)
        (path (k := k) (p i))) = ⊤ := by
  classical
  have hfdC := finiteDimensional_Q (idealC P) (geSpan_le_C P N hN)
  have hfdB := finiteDimensional_Q (idealB P f hf N) (geSpan_le_B P f hf N)
  have hspB := span_B P f hf N hN (Set.range p) (by
    rw [← Set.range_comp]; exact hsp)
  rw [← Set.range_comp] at hspB
  refine ⟨?_, hspB⟩
  have hcard : Fintype.card ι = Module.finrank k (Q (idealC P) w y) := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp]))]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank (le_of_eq hspB.symm)
    (by rw [hdim, hcard])

include hf in
/-- **Lemma 12.3** (`lem:flat-mesh-perturbations`): if the presentations of the simple modules of
`C = kQ/(r)` are resolutions and `C_d = 0` for `d ≥ N`, then `B = kQ/(𝔪^{N+1}, r − f)` has the
dimensions of `C`, its presentations are again resolutions, and every path basis of `C` lifts to
a basis of `B`. -/
theorem flat_perturbation (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length →
      path (k := k) p ∈ ctxSpan P P.r w y)
    (hC : ∀ w x, Function.Injective (relMap P (idealC P) P.r w x) ∧
      LinearMap.ker (alpha (idealC P) w x) ≤ LinearMap.range (relMap P (idealC P) P.r w x)) :
    (∀ w y, Module.finrank k (Q (idealB P f hf N) w y) = Module.finrank k (Q (idealC P) w y)) ∧
    (∀ w x, Function.Injective (relMap P (idealB P f hf N) (rf P f) w x) ∧
      LinearMap.ker (alpha (idealB P f hf N) w x) ≤
        LinearMap.range (relMap P (idealB P f hf N) (rf P f) w x)) ∧
    ∀ (w y : V) {ι : Type} [Fintype ι] (p : ι → Quiver.Path w y),
      LinearIndependent k (fun i ↦ Submodule.Quotient.mk (p := (idealC P).I w y)
        (path (k := k) (p i))) →
      Submodule.span k (Set.range fun i ↦ Submodule.Quotient.mk (p := (idealC P).I w y)
        (path (k := k) (p i))) = ⊤ →
      LinearIndependent k (fun i ↦ Submodule.Quotient.mk (p := (idealB P f hf N).I w y)
        (path (k := k) (p i))) ∧
      Submodule.span k (Set.range fun i ↦ Submodule.Quotient.mk (p := (idealB P f hf N).I w y)
        (path (k := k) (p i))) = ⊤ := by
  classical
  have hfdC := finiteDimensional_Q (idealC P) (geSpan_le_C P N hN)
  have hfdB := finiteDimensional_Q (idealB P f hf N) (geSpan_le_B P f hf N)
  set H : V → V → ℕ := fun w y ↦ Module.finrank k (Q (idealC P) w y)
  set HB : V → V → ℕ := fun w y ↦ Module.finrank k (Q (idealB P f hf N) w y)
  set A : V → V → ℕ := fun y x ↦ Fintype.card (y ⟶ x)
  set R : V → V → ℕ := fun y x ↦ Fintype.card {t : P.T x // P.src x t = y}
  have hC' : ∀ w x, ∑ y, R y x * H w y + H w x = ∑ y, A y x * H w y + if w = x then 1 else 0 := by
    intro w x
    have := dim_C P N hN hC w x
    rwa [sum_rels P x (fun y ↦ H w y), sum_arrows x (fun y ↦ H w y)] at this
  have hB' : ∀ w x, ∑ y, A y x * HB w y + (if w = x then 1 else 0) ≤
      ∑ y, R y x * HB w y + HB w x := by
    intro w x
    have := dim_B P f hf N hN w x
    rwa [sum_rels P x (fun y ↦ HB w y), sum_arrows x (fun y ↦ HB w y)] at this
  obtain ⟨hEq, hEqB⟩ := matrix_arg A R H HB hC' hB' (finrank_B_le P f hf N hN)
  have hdim : ∀ w y, Module.finrank k (Q (idealB P f hf N) w y) =
      Module.finrank k (Q (idealC P) w y) := fun w y ↦ congrFun (congrFun hEq w) y
  refine ⟨hdim, fun w x ↦ ⟨?_, ker_alpha_B P f hf N hN w x⟩, fun w y ι _ p hli hsp ↦ ?_⟩
  · -- injectivity from the equality `ZH_B = I`
    have heq := hEqB w x
    rw [← sum_rels P x (fun y ↦ HB w y), ← sum_arrows x (fun y ↦ HB w y)] at heq
    have h1 := Submodule.finrank_mono (ker_alpha_B P f hf N hN w x)
    have h3 := LinearMap.finrank_range_add_finrank_ker (alpha (idealB P f hf N) w x)
    rw [Module.finrank_pi_fintype] at h3
    have h4 := finrank_alpha (idealB P f hf N) w x
    have h5 := LinearMap.finrank_range_add_finrank_ker (relMap P (idealB P f hf N) (rf P f) w x)
    rw [Module.finrank_pi_fintype] at h5
    have hker : Module.finrank k (LinearMap.ker (relMap P (idealB P f hf N) (rf P f) w x)) = 0 := by
      simp only [HB] at heq
      omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.1 hker
  · -- a path basis of `C` lifts
    have hspB := span_B P f hf N hN (Set.range p) (by
      rw [← Set.range_comp]; exact hsp)
    rw [← Set.range_comp] at hspB
    refine ⟨?_, hspB⟩
    have hcard : Fintype.card ι = Module.finrank k (Q (idealC P) w y) := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp]))]
    exact linearIndependent_of_top_le_span_of_card_eq_finrank (le_of_eq hspB.symm)
      (by rw [hdim, hcard])

end FlatPert

end MultiplicativeBasisDeformations
