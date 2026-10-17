import MultiplicativeBasisDeformations.Refinements.FlatPerturbationDim

/-!
# Lemma 12.3: `gr_𝔪 B ≅ C`

`lem:flat-mesh-perturbations` (`deformation-refinements.tex`): "Then `gr_𝔪 B ≅ C`."
In each degree `d`, paths induce a linear isomorphism from `C_d(w, y)` (the image of the degree-`d`
paths in `C`) onto `𝔪^d B(w, y)/𝔪^{d+1} B(w, y)` (`grIso`); composition is induced by composition of
paths on both sides. The map is well defined since a homogeneous relation `u r v` of degree `d`
is `u (r − f) v + u f v` with `u f v ∈ 𝔪^{d+1}` (`hctx_le_B_succ`), onto since paths of length
`> d` lie in `𝔪^{d+1}` (`sub_proj_mem_geSpan_succ`), and bijective by counting: the degree
projections make `C` graded (`πC`), so `Σ_d dim C_d ≤ dim C`, while
`Σ_d dim gr^d B = dim B = dim C` (Lemma 12.3's dimension equality).
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

variable (P : Pres k V) [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (f : ∀ x (t : P.T x), Hm k (P.src x t) x)
  (hf : ∀ x t, f x t ∈ geSpan k (P.deg x t + 1) (P.src x t) x) (N : ℕ)
  [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]

/-! ### The degree projections of `C` -/

theorem hctx_le_ctx (d : ℕ) (w y : V) : hctx P d w y ≤ ctxSpan P P.r w y := by
  rw [hctx, Submodule.span_le]
  rintro _ ⟨x, t, u, v, -, rfl⟩
  exact Submodule.subset_span ⟨x, t, u, v, rfl⟩

theorem proj_ctx_mem (d : ℕ) {w y : V} {g : Hm k w y} (hg : g ∈ ctxSpan P P.r w y) :
    proj (k := k) d w y g ∈ ctxSpan P P.r w y :=
  hctx_le_ctx P d w y (proj_ctx P d hg)

/-- The degree-`d` projection of `C`. -/
def πC (d : ℕ) (w y : V) : Q (idealC P) w y →ₗ[k] Q (idealC P) w y :=
  ((idealC P).I w y).mapQ ((idealC P).I w y) (proj (k := k) d w y)
    (fun _ hg ↦ proj_ctx_mem P d hg)

theorem πC_mk (d : ℕ) {w y : V} (g : Hm k w y) :
    πC P d w y (Submodule.Quotient.mk g) = Submodule.Quotient.mk (proj (k := k) d w y g) := rfl

/-- `C_d(w, y)`: the image of the degree-`d` paths. -/
def CD (d : ℕ) (w y : V) : Submodule k (Q (idealC P) w y) :=
  (degreePart (k := k) d w y).map ((idealC P).I w y).mkQ

theorem πC_mem (d : ℕ) {w y : V} (x : Q (idealC P) w y) : πC P d w y x ∈ CD P d w y := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [πC_mk]
  exact ⟨_, proj_mem g, rfl⟩

theorem πC_of_mem {d e : ℕ} {w y : V} {x : Q (idealC P) w y} (hx : x ∈ CD P e w y) :
    πC P d w y x = if e = d then x else 0 := by
  obtain ⟨g, hg, rfl⟩ := hx
  show πC P d w y (Submodule.Quotient.mk g) = if e = d then Submodule.Quotient.mk g else 0
  rw [πC_mk, proj_of_mem hg]
  split_ifs <;> simp

/-! ### The filtration of `B` -/

/-- `𝔪^d B(w, y)`. -/
def FB (d : ℕ) (w y : V) : Submodule k (Q (idealB P f hf N) w y) :=
  (geSpan k d w y).map ((idealB P f hf N).I w y).mkQ

theorem FB_anti {d d' : ℕ} (h : d ≤ d') (w y : V) : FB P f hf N d' w y ≤ FB P f hf N d w y :=
  Submodule.map_mono (geSpan_anti h w y)

/-- `gr^d B(w, y) = 𝔪^d B/𝔪^{d+1} B`. -/
abbrev grB (d : ℕ) (w y : V) :=
  FB P f hf N d w y ⧸ (FB P f hf N (d + 1) w y).comap (FB P f hf N d w y).subtype

include hf in
theorem hctx_le_B_succ (d : ℕ) (w y : V) :
    hctx P d w y ≤ (idealB P f hf N).I w y ⊔ geSpan k (d + 1) w y := by
  rw [hctx, Submodule.span_le]
  rintro _ ⟨x, t, u, v, hdeg, rfl⟩
  have e : path (k := k) u ≫ P.r x t ≫ path v =
      path u ≫ rf P f x t ≫ path v + path u ≫ f x t ≫ path v := by
    simp [rf, Preadditive.sub_comp, Preadditive.comp_sub]
  rw [SetLike.mem_coe, e]
  refine add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left (ctx_mem P (rf P f) t _ _)))
    (Submodule.mem_sup_right ?_)
  exact geSpan_anti (by omega) _ _ (path_comp_geSpan u v (hf x t))

theorem sub_proj_mem_geSpan_succ {d : ℕ} {w y : V} {g : Hm k w y} (hg : g ∈ geSpan k d w y) :
    g - proj (k := k) d w y g ∈ geSpan k (d + 1) w y := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    rw [proj_path]
    split_ifs with h
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact Submodule.subset_span ⟨p, by omega, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, add_sub_add_comm]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c ha

/-! ### The map induced by paths -/

/-- Degree-`d` elements of `kQ` in `C`. -/
def ψC (d : ℕ) (w y : V) : degreePart (k := k) d w y →ₗ[k] Q (idealC P) w y :=
  ((idealC P).I w y).mkQ ∘ₗ (degreePart (k := k) d w y).subtype

theorem range_ψC (d : ℕ) (w y : V) : LinearMap.range (ψC P d w y) = CD P d w y := by
  rw [ψC, LinearMap.range_comp, Submodule.range_subtype]; rfl

/-- Degree-`d` elements of `kQ` in `gr^d B`. -/
def θ₀ (d : ℕ) (w y : V) : degreePart (k := k) d w y →ₗ[k] grB P f hf N d w y :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (FB P f hf N d w y)
    (((idealB P f hf N).I w y).mkQ ∘ₗ (degreePart (k := k) d w y).subtype)
    (fun g ↦ ⟨g.1, degreePart_le_geSpan d w y g.2, rfl⟩)

theorem θ₀_apply (d : ℕ) {w y : V} (g : degreePart (k := k) d w y) :
    θ₀ P f hf N d w y g = Submodule.Quotient.mk ⟨Submodule.Quotient.mk g.1,
      ⟨g.1, degreePart_le_geSpan d w y g.2, rfl⟩⟩ := rfl

theorem θ₀_surjective (d : ℕ) (w y : V) : Function.Surjective (θ₀ P f hf N d w y) := by
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨⟨proj (k := k) d w y g, proj_mem g⟩, ?_⟩
  rw [θ₀_apply, Submodule.Quotient.eq]
  rw [Submodule.mem_comap]
  change (Submodule.Quotient.mk (proj (k := k) d w y g) - Submodule.Quotient.mk g :
    Q (idealB P f hf N) w y) ∈ _
  rw [← Submodule.Quotient.mk_sub]
  refine ⟨proj (k := k) d w y g - g, ?_, rfl⟩
  rw [← neg_sub]
  exact neg_mem (sub_proj_mem_geSpan_succ hg)

theorem ker_ψC_le (d : ℕ) (w y : V) :
    LinearMap.ker (ψC P d w y) ≤ LinearMap.ker (θ₀ P f hf N d w y) := by
  intro g hg
  rw [LinearMap.mem_ker, ψC, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hg
  rw [LinearMap.mem_ker, θ₀_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  have h1 : g.1 ∈ hctx P d w y := by
    have := proj_ctx P d hg
    change proj (k := k) d w y g.1 ∈ hctx P d w y at this
    rwa [proj_of_mem g.2, if_pos rfl] at this
  obtain ⟨i, hi, h, hh, e⟩ := Submodule.mem_sup.1 (hctx_le_B_succ P f hf N d w y h1)
  refine ⟨h, hh, ?_⟩
  change Submodule.Quotient.mk h = Submodule.Quotient.mk g.1
  rw [← e, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hi, zero_add]

/-- **The map `C_d → gr^d B` induced by paths.** -/
def θ (d : ℕ) (w y : V) : CD P d w y →ₗ[k] grB P f hf N d w y :=
  (LinearMap.ker (ψC P d w y)).liftQ (θ₀ P f hf N d w y) (ker_ψC_le P f hf N d w y) ∘ₗ
    ((LinearMap.quotKerEquivRange (ψC P d w y)).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (range_ψC P d w y)).symm.toLinearMap)

theorem θ_ψC (d : ℕ) {w y : V} (g : degreePart (k := k) d w y) :
    θ P f hf N d w y ⟨ψC P d w y g, range_ψC P d w y ▸ LinearMap.mem_range_self _ g⟩ =
      θ₀ P f hf N d w y g := by
  simp only [θ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  have : (LinearEquiv.ofEq _ _ (range_ψC P d w y)).symm
      ⟨ψC P d w y g, range_ψC P d w y ▸ LinearMap.mem_range_self _ g⟩ =
      ⟨ψC P d w y g, LinearMap.mem_range_self _ g⟩ := rfl
  rw [this, LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem θ_surjective (d : ℕ) (w y : V) : Function.Surjective (θ P f hf N d w y) := by
  intro z
  obtain ⟨g, rfl⟩ := θ₀_surjective P f hf N d w y z
  exact ⟨_, θ_ψC P f hf N d g⟩

/-! ### Counting dimensions -/

section Count

variable (hN : ∀ w y (p : Quiver.Path w y), N ≤ p.length → path (k := k) p ∈ ctxSpan P P.r w y)

theorem FB_zero (w y : V) : FB P f hf N 0 w y = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨g, mem_geSpan_zero g, rfl⟩

theorem FB_eq_bot {d : ℕ} (hd : N + 1 ≤ d) (w y : V) : FB P f hf N d w y = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact geSpan_le_B P f hf N w y (geSpan_anti hd w y hg)

theorem finrank_grB_add (d : ℕ) (w y : V) [Module.Finite k (Q (idealB P f hf N) w y)] :
    Module.finrank k (grB P f hf N d w y) + Module.finrank k (FB P f hf N (d + 1) w y) =
      Module.finrank k (FB P f hf N d w y) := by
  have := Submodule.finrank_quotient_add_finrank
    ((FB P f hf N (d + 1) w y).comap (FB P f hf N d w y).subtype)
  rwa [(Submodule.comapSubtypeEquivOfLe (FB_anti P f hf N (Nat.le_succ d) w y)).finrank_eq] at this

theorem sum_grB (w y : V) [Module.Finite k (Q (idealB P f hf N) w y)] (M : ℕ) :
    ∑ d ∈ Finset.range M, Module.finrank k (grB P f hf N d w y) +
      Module.finrank k (FB P f hf N M w y) = Module.finrank k (FB P f hf N 0 w y) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, add_assoc, finrank_grB_add, ih]

theorem sum_CD_le (w y : V) [Module.Finite k (Q (idealC P) w y)] (M : ℕ) :
    ∑ d ∈ Finset.range M, Module.finrank k (CD P d w y) ≤
      Module.finrank k (Q (idealC P) w y) := by
  let Φ : Q (idealC P) w y →ₗ[k] (∀ d : Fin M, CD P d w y) :=
    LinearMap.pi fun d ↦ (πC P d w y).codRestrict (CD P d w y) (πC_mem P d)
  have hΦ : Function.Surjective Φ := by
    intro c
    refine ⟨∑ e, (c e).1, funext fun d ↦ Subtype.ext ?_⟩
    change πC P d w y (∑ e, (c e).1) = (c d).1
    rw [map_sum]
    simp_rw [πC_of_mem P (c _).2]
    rw [Finset.sum_eq_single d]
    · rw [if_pos rfl]
    · intro e _ he
      rw [if_neg (fun h ↦ he (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ d) h
  have h1 := LinearMap.finrank_range_le Φ
  rw [LinearMap.range_eq_top.2 hΦ, finrank_top, Module.finrank_pi_fintype] at h1
  rwa [← Fin.sum_univ_eq_sum_range (fun d ↦ Module.finrank k (CD P d w y))]

include hN in
/-- `gr_𝔪 B ≅ C` from the equality of the dimensions of `B` and `C`. -/
theorem grIso_of_finrank (hdim : ∀ w y, Module.finrank k (Q (idealB P f hf N) w y) =
      Module.finrank k (Q (idealC P) w y)) (d : ℕ) (w y : V) :
    ∃ e : CD P d w y ≃ₗ[k] grB P f hf N d w y, ∀ g : degreePart (k := k) d w y,
      e ⟨ψC P d w y g, range_ψC P d w y ▸ LinearMap.mem_range_self _ g⟩ = θ₀ P f hf N d w y g := by
  haveI := finiteDimensional_Q (idealC P) (geSpan_le_C P N hN) w y
  haveI := finiteDimensional_Q (idealB P f hf N) (geSpan_le_B P f hf N) w y
  set M := max (N + 1) (d + 1)
  have hle : ∀ e, Module.finrank k (grB P f hf N e w y) ≤ Module.finrank k (CD P e w y) := by
    intro e
    have h1 := LinearMap.finrank_range_le (θ P f hf N e w y)
    rwa [LinearMap.range_eq_top.2 (θ_surjective P f hf N e w y), finrank_top] at h1
  have hsumB : ∑ e ∈ Finset.range M, Module.finrank k (grB P f hf N e w y) =
      Module.finrank k (Q (idealC P) w y) := by
    have := sum_grB P f hf N w y M
    rw [FB_eq_bot P f hf N (le_max_left _ _) w y, finrank_bot, add_zero, FB_zero, finrank_top,
      hdim w y] at this
    exact this
  have hsum := sum_CD_le P w y M
  have heq : ∀ e ∈ Finset.range M,
      Module.finrank k (grB P f hf N e w y) = Module.finrank k (CD P e w y) :=
    (Finset.sum_eq_sum_iff_of_le fun e _ ↦ hle e).1 (le_antisymm
      (Finset.sum_le_sum fun e _ ↦ hle e) (hsum.trans hsumB.ge))
  have hd := heq d (Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_right _ _)))
  have hbij : Function.Bijective (θ P f hf N d w y) :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd.symm).2
      (θ_surjective P f hf N d w y), θ_surjective P f hf N d w y⟩
  exact ⟨LinearEquiv.ofBijective _ hbij, fun g ↦ θ_ψC P f hf N d g⟩


variable (hC : ∀ w x, Function.Injective (relMap P (idealC P) P.r w x) ∧
  LinearMap.ker (alpha (idealC P) w x) ≤ LinearMap.range (relMap P (idealC P) P.r w x))

include hN hC in
/-- **Lemma 12.3, `gr_𝔪 B ≅ C`**: in every degree `d`, paths induce a linear isomorphism
`C_d(w, y) ≅ 𝔪^d B(w, y)/𝔪^{d+1} B(w, y)`. -/
theorem grIso (d : ℕ) (w y : V) :
    ∃ e : CD P d w y ≃ₗ[k] grB P f hf N d w y, ∀ g : degreePart (k := k) d w y,
      e ⟨ψC P d w y g, range_ψC P d w y ▸ LinearMap.mem_range_self _ g⟩ = θ₀ P f hf N d w y g :=
  grIso_of_finrank P f hf N hN (flat_perturbation P f hf N hN hC).1 d w y

end Count

end FlatPert

end MultiplicativeBasisDeformations
