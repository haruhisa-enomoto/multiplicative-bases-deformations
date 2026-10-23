module

public import MultiplicativeBasisDeformations.Foundations.MGrading

/-!
# Weights in a cone (toward Proposition 12.8)

`deformation-refinements.tex`: "For each bar differential choose a `k`-linear right
inverse on its image; […] Make these choices separately in each degree and weight". In the family
`m + Σ_i t_i μ_i` the parameter `t_i` carries the weight `χ_i` of `μ_i`, so the lifts are
homogeneous when every component has relative weight in the monoid `C` spanned by the `χ_i`.

For a weight grading `G` and `σ`, `ConeAt C σ n` says that the components of `n` have weights in
`σ + C`, and `cpart C σ` projects onto them. Maps shifting weights by `γ` move `σ + C` to
`σ + γ + C` (`ConeAt.shift`); maps and bilinear maps whose components have relative weights in `C`
(`ConeLin`, `ConeBil`) preserve the cone condition, and their cone parts are `clin`, `cbil`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace MGr

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [DecidableEq M] (C : AddSubmonoid M)
  {N N' N'' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
  [AddCommGroup N''] [Module R N''] (G : MGr R M N) (G' : MGr R M N') (G'' : MGr R M N'')

/-- The components of `n` have weights in `σ + C`. -/
def ConeAt (σ : M) (n : N) : Prop := ∀ δ, δ - σ ∉ C → G.proj δ n = 0

open Classical in
/-- The part of weights in `σ + C`. -/
def cpart (σ : M) : N →ₗ[R] N := ∑ δ ∈ G.supp.filter (fun δ ↦ δ - σ ∈ C), G.proj δ

variable {C G G' G''}

open Classical in
theorem proj_cpart (σ δ : M) (n : N) :
    G.proj δ (cpart C G σ n) = if δ - σ ∈ C then G.proj δ n else 0 := by
  simp only [cpart, LinearMap.coe_sum, Finset.sum_apply, map_sum, G.proj_proj]
  by_cases hδ : δ ∈ G.supp
  · split_ifs with h
    · rw [Finset.sum_eq_single δ]
      · rw [if_pos rfl]
      · intro e _ he; rw [if_neg he]
      · intro h'; exact absurd (Finset.mem_filter.2 ⟨hδ, h⟩) h'
    · refine Finset.sum_eq_zero fun e he ↦ ?_
      rw [if_neg]
      rintro rfl; exact h (Finset.mem_filter.1 he).2
  · rw [G.proj_out δ hδ, LinearMap.zero_apply]
    split_ifs
    · refine Finset.sum_eq_zero fun e he ↦ ?_
      rw [if_neg]
      rintro rfl; exact hδ (Finset.mem_filter.1 he).1
    · refine Finset.sum_eq_zero fun e he ↦ ?_
      rw [if_neg]
      rintro rfl; exact hδ (Finset.mem_filter.1 he).1

theorem coneAt_cpart (σ : M) (n : N) : ConeAt C G σ (cpart C G σ n) := fun δ hδ ↦ by
  rw [proj_cpart, if_neg hδ]

theorem cpart_of_coneAt {σ : M} {n : N} (h : ConeAt C G σ n) : cpart C G σ n = n :=
  G.eq_of_proj fun δ ↦ by
    rw [proj_cpart]
    split_ifs with h'
    · rfl
    · rw [h δ h']

theorem ConeAt.zero (σ : M) : ConeAt C G σ (0 : N) := fun δ _ ↦ map_zero _

theorem ConeAt.add {σ : M} {n n' : N} (h : ConeAt C G σ n) (h' : ConeAt C G σ n') :
    ConeAt C G σ (n + n') := fun δ hδ ↦ by rw [map_add, h δ hδ, h' δ hδ, add_zero]

theorem ConeAt.smul {σ : M} (c : R) {n : N} (h : ConeAt C G σ n) : ConeAt C G σ (c • n) :=
  fun δ hδ ↦ by rw [map_smul, h δ hδ, smul_zero]

theorem ConeAt.neg {σ : M} {n : N} (h : ConeAt C G σ n) : ConeAt C G σ (-n) :=
  fun δ hδ ↦ by rw [map_neg, h δ hδ, neg_zero]

theorem ConeAt.sub {σ : M} {n n' : N} (h : ConeAt C G σ n) (h' : ConeAt C G σ n') :
    ConeAt C G σ (n - n') := fun δ hδ ↦ by rw [map_sub, h δ hδ, h' δ hδ, sub_zero]

theorem ConeAt.sum {σ : M} {ι : Type*} (s : Finset ι) {n : ι → N} (h : ∀ i ∈ s, ConeAt C G σ (n i)) :
    ConeAt C G σ (∑ i ∈ s, n i) := fun δ hδ ↦ by
  rw [map_sum]; exact Finset.sum_eq_zero fun i hi ↦ h i hi δ hδ

theorem ConeAt.mono {σ σ' : M} {n : N} (h : ConeAt C G σ' n) (hσ : σ' - σ ∈ C) :
    ConeAt C G σ n := fun δ hδ ↦ h δ fun h' ↦ hδ (by
  have := C.add_mem h' hσ
  rwa [show δ - σ' + (σ' - σ) = δ - σ by abel] at this)

theorem coneAt_of_isHom {σ : M} {n : N} (h : G.IsHom σ n) : ConeAt C G σ n := fun δ hδ ↦ by
  rw [G.proj_of_isHom h, if_neg]
  rintro rfl; exact hδ (by rw [sub_self]; exact C.zero_mem)

theorem coneAt_proj {σ δ : M} {n : N} (h : ConeAt C G σ n) : ConeAt C G σ (G.proj δ n) := by
  by_cases hδ : δ - σ ∈ C
  · exact (coneAt_of_isHom (G.isHom_proj δ n)).mono hδ
  · rw [h δ hδ]; exact ConeAt.zero σ

/-- Shifting maps move the cone. -/
theorem ConeAt.shift {σ γ : M} {φ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) {n : N}
    (h : ConeAt C G σ n) : ConeAt C G' (σ + γ) (φ n) := fun δ hδ ↦ by
  have := hφ.proj (δ - γ) n
  rw [sub_add_cancel] at this
  rw [this, h (δ - γ) (by rwa [show δ - γ - σ = δ - (σ + γ) by abel]), map_zero]

/-- Shifting maps commute with the cone parts. -/
theorem cpart_shift {σ γ : M} {φ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) (n : N) :
    φ (cpart C G σ n) = cpart C G' (σ + γ) (φ n) := by
  refine G'.eq_of_proj fun δ ↦ ?_
  have h1 := hφ.proj (δ - γ) (cpart C G σ n)
  have h2 := hφ.proj (δ - γ) n
  rw [sub_add_cancel] at h1 h2
  rw [h1, proj_cpart, proj_cpart, h2, show δ - γ - σ = δ - (σ + γ) by abel]
  split_ifs <;> simp

/-! ### Maps with relative weights in the cone -/

/-- The components of `f` have relative weights in `ρ + C`. -/
def ConeLin (ρ : M) (f : N →ₗ[R] N') : Prop :=
  ∀ β n, G.IsHom β n → ConeAt C G' (β + ρ) (f n)

/-- The components of `φ` have relative weights in `ρ + C`. -/
def ConeBil (ρ : M) (φ : N →ₗ[R] N' →ₗ[R] N'') : Prop :=
  ∀ β α n n', G.IsHom β n → G'.IsHom α n' → ConeAt C G'' (β + α + ρ) (φ n n')

/-- A cone condition on the input propagates. -/
theorem ConeLin.apply {ρ σ : M} {f : N →ₗ[R] N'} (hf : ConeLin (C := C) (G := G) (G' := G') ρ f)
    {n : N} (hn : ConeAt C G σ n) : ConeAt C G' (σ + ρ) (f n) := by
  rw [G.sum n, map_sum]
  refine ConeAt.sum _ fun β _ ↦ ?_
  by_cases hβ : β - σ ∈ C
  · exact (hf β _ (G.isHom_proj β n)).mono (by rwa [show β + ρ - (σ + ρ) = β - σ by abel])
  · rw [hn β hβ, map_zero]; exact ConeAt.zero _

theorem ConeBil.apply {ρ σ σ' : M} {φ : N →ₗ[R] N' →ₗ[R] N''}
    (hφ : ConeBil (C := C) (G := G) (G' := G') (G'' := G'') ρ φ) {n : N} {n' : N'}
    (hn : ConeAt C G σ n) (hn' : ConeAt C G' σ' n') : ConeAt C G'' (σ + σ' + ρ) (φ n n') := by
  have e : φ n n' = ∑ β ∈ G.supp, ∑ α ∈ G'.supp, φ (G.proj β n) (G'.proj α n') := by
    conv_lhs => rw [G.sum n, G'.sum n']
    simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_comm
  rw [e]
  refine ConeAt.sum _ fun β _ ↦ ConeAt.sum _ fun α _ ↦ ?_
  by_cases hβ : β - σ ∈ C
  · by_cases hα : α - σ' ∈ C
    · refine (hφ β α _ _ (G.isHom_proj β n) (G'.isHom_proj α n')).mono ?_
      have := C.add_mem hβ hα
      rwa [show β - σ + (α - σ') = β + α + ρ - (σ + σ' + ρ) by abel] at this
    · rw [hn' α hα, map_zero]; exact ConeAt.zero _
  · rw [hn β hβ, LinearMap.map_zero₂]; exact ConeAt.zero _

variable (C G G')

/-- The cone part of a linear map relative to `ρ`. -/
def clin (ρ : M) (f : N →ₗ[R] N') : N →ₗ[R] N' :=
  ∑ β ∈ G.supp, cpart C G' (β + ρ) ∘ₗ f ∘ₗ G.proj β

variable {C G G'}

theorem clin_apply_hom (ρ : M) (f : N →ₗ[R] N') {β : M} {n : N} (hn : G.IsHom β n) :
    clin C G G' ρ f n = cpart C G' (β + ρ) (f n) := by
  simp only [clin, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  by_cases hβ : β ∈ G.supp
  · rw [Finset.sum_eq_single β]
    · rw [hn]
    · intro e _ he; rw [G.proj_of_isHom hn, if_neg (Ne.symm he), map_zero, map_zero]
    · intro h; exact absurd hβ h
  · rw [G.eq_zero_of_isHom_out hn hβ]; simp

theorem coneLin_clin (ρ : M) (f : N →ₗ[R] N') : ConeLin (C := C) (G := G) (G' := G') ρ (clin C G G' ρ f) :=
  fun β n hn ↦ by rw [clin_apply_hom ρ f hn]; exact coneAt_cpart _ _

theorem clin_of_coneLin {ρ : M} {f : N →ₗ[R] N'} (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) :
    clin C G G' ρ f = f :=
  G.ext_of_hom fun β n hn ↦ by rw [clin_apply_hom ρ f hn, cpart_of_coneAt (hf β n hn)]

variable (C G G' G'')

/-- The cone part of a bilinear map relative to `ρ`. -/
def cbil (ρ : M) (φ : N →ₗ[R] N' →ₗ[R] N'') : N →ₗ[R] N' →ₗ[R] N'' :=
  ∑ β ∈ G.supp, ∑ α ∈ G'.supp,
    ((φ.compl₁₂ (G.proj β) (G'.proj α)).compr₂ (cpart C G'' (β + α + ρ)))

variable {C G G' G''}

theorem cbil_apply_hom (ρ : M) (φ : N →ₗ[R] N' →ₗ[R] N'') {β α : M} {n : N} {n' : N'}
    (hn : G.IsHom β n) (hn' : G'.IsHom α n') :
    cbil C G G' G'' ρ φ n n' = cpart C G'' (β + α + ρ) (φ n n') := by
  simp only [cbil, LinearMap.coe_sum, Finset.sum_apply, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply]
  by_cases hβ : β ∈ G.supp
  · rw [Finset.sum_eq_single β]
    · by_cases hα : α ∈ G'.supp
      · rw [Finset.sum_eq_single α]
        · rw [hn, hn']
        · intro e _ he
          rw [G'.proj_of_isHom hn', if_neg (Ne.symm he), map_zero, map_zero]
        · intro h; exact absurd hα h
      · rw [G'.eq_zero_of_isHom_out hn' hα]; simp
    · intro e _ he
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      rw [G.proj_of_isHom hn, if_neg (Ne.symm he), LinearMap.map_zero₂, map_zero]
    · intro h; exact absurd hβ h
  · rw [G.eq_zero_of_isHom_out hn hβ]; simp

theorem coneBil_cbil (ρ : M) (φ : N →ₗ[R] N' →ₗ[R] N'') :
    ConeBil (C := C) (G := G) (G' := G') (G'' := G'') ρ (cbil C G G' G'' ρ φ) :=
  fun β α n n' hn hn' ↦ by rw [cbil_apply_hom ρ φ hn hn']; exact coneAt_cpart _ _

/-- Bilinear maps agreeing on homogeneous elements agree. -/
theorem bil_ext_of_hom {φ ψ : N →ₗ[R] N' →ₗ[R] N''}
    (h : ∀ β α n n', G.IsHom β n → G'.IsHom α n' → φ n n' = ψ n n') : φ = ψ :=
  G.ext_of_hom fun β n hn ↦ G'.ext_of_hom fun α n' hn' ↦ h β α n n' hn hn'

theorem cbil_of_coneBil {ρ : M} {φ : N →ₗ[R] N' →ₗ[R] N''}
    (hφ : ConeBil (C := C) (G := G) (G' := G') (G'' := G'') ρ φ) : cbil C G G' G'' ρ φ = φ :=
  bil_ext_of_hom fun β α n n' hn hn' ↦ by
    rw [cbil_apply_hom ρ φ hn hn', cpart_of_coneAt (hφ β α n n' hn hn')]

/-! ### Bottom components in a pointed cone -/

theorem cpart_bot (σ : M) (n : N) : cpart ⊥ G σ n = G.proj σ n :=
  G.eq_of_proj fun δ ↦ by
    rw [proj_cpart, AddSubmonoid.mem_bot, sub_eq_zero, G.proj_proj]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl

variable (hCp : ∀ γ ∈ C, ∀ δ ∈ C, γ + δ = 0 → γ = 0)
include hCp

theorem proj_eq_zero_of_coneAt {σ σ' : M} {n : N} (h : ConeAt C G σ' n) (hσ : σ' - σ ∈ C)
    (hne : σ' ≠ σ) : G.proj σ n = 0 := by
  refine h σ fun h' ↦ hne ?_
  have := hCp _ hσ _ h' (by abel)
  exact sub_eq_zero.1 this

/-- Only the bottom component of the input reaches the bottom component of the output. -/
theorem ConeLin.proj_bottom {ρ σ : M} {f : N →ₗ[R] N'}
    (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) {n : N} (hn : ConeAt C G σ n) :
    G'.proj (σ + ρ) (f n) = G'.proj (σ + ρ) (f (G.proj σ n)) := by
  conv_lhs => rw [G.sum n, map_sum, map_sum]
  by_cases hσ : σ ∈ G.supp
  · rw [Finset.sum_eq_single σ]
    intro β _ hβ
    by_cases hβσ : β - σ ∈ C
    · refine proj_eq_zero_of_coneAt hCp (hf β _ (G.isHom_proj β n)) ?_ ?_
      · rwa [show β + ρ - (σ + ρ) = β - σ by abel]
      · intro h; exact hβ (by simpa using h)
    · rw [hn β hβσ, map_zero, map_zero]
    · intro h; exact absurd hσ h
  · rw [G.proj_out σ hσ, LinearMap.zero_apply, map_zero, map_zero]
    refine Finset.sum_eq_zero fun β hβ ↦ ?_
    by_cases hβσ : β - σ ∈ C
    · refine proj_eq_zero_of_coneAt hCp (hf β _ (G.isHom_proj β n)) ?_ ?_
      · rwa [show β + ρ - (σ + ρ) = β - σ by abel]
      · intro h; exact hσ (by rw [← show β = σ by simpa using h]; exact hβ)
    · rw [hn β hβσ, map_zero, map_zero]

theorem ConeBil.proj_bottom {ρ σ σ' : M} {φ : N →ₗ[R] N' →ₗ[R] N''}
    (hφ : ConeBil (C := C) (G := G) (G' := G') (G'' := G'') ρ φ) {n : N} {n' : N'}
    (hn : ConeAt C G σ n) (hn' : ConeAt C G' σ' n') :
    G''.proj (σ + σ' + ρ) (φ n n') = G''.proj (σ + σ' + ρ) (φ (G.proj σ n) (G'.proj σ' n')) := by
  have h1 : ConeLin (C := C) (G := G) (G' := G'') (σ' + ρ) (φ.flip n') := by
    intro β x hx
    exact ConeAt.congr'' ((hφ.apply (coneAt_of_isHom hx) hn')) (by abel)
  have h2 : ConeLin (C := C) (G := G') (G' := G'') (σ + ρ) (φ (G.proj σ n)) := by
    intro α x hx
    exact ConeAt.congr'' ((hφ.apply (coneAt_of_isHom (G.isHom_proj σ n)) (coneAt_of_isHom hx)))
      (by abel)
  have e1 := h1.proj_bottom hCp hn
  simp only [LinearMap.flip_apply] at e1
  rw [show σ + (σ' + ρ) = σ + σ' + ρ by abel] at e1
  have e2 := h2.proj_bottom hCp hn'
  rw [show σ' + (σ + ρ) = σ + σ' + ρ by abel] at e2
  rw [e1, e2]
where
  ConeAt.congr'' {σ₁ σ₂ : M} {x : N''} (h : ConeAt C G'' σ₁ x) (e : σ₁ = σ₂) :
      ConeAt C G'' σ₂ x := e ▸ h

/-! ### Cone conditions on maps: closure properties and bottom parts -/

section MapsCone

omit hCp

theorem ConeLin.zero (ρ : M) : ConeLin (C := C) (G := G) (G' := G') ρ (0 : N →ₗ[R] N') :=
  fun _ _ _ ↦ ConeAt.zero _

theorem ConeLin.add {ρ : M} {f g : N →ₗ[R] N'} (hf : ConeLin (C := C) (G := G) (G' := G') ρ f)
    (hg : ConeLin (C := C) (G := G) (G' := G') ρ g) :
    ConeLin (C := C) (G := G) (G' := G') ρ (f + g) := fun β n hn ↦ (hf β n hn).add (hg β n hn)

theorem ConeLin.sub {ρ : M} {f g : N →ₗ[R] N'} (hf : ConeLin (C := C) (G := G) (G' := G') ρ f)
    (hg : ConeLin (C := C) (G := G) (G' := G') ρ g) :
    ConeLin (C := C) (G := G) (G' := G') ρ (f - g) := fun β n hn ↦ (hf β n hn).sub (hg β n hn)

theorem ConeLin.smul {ρ : M} (c : R) {f : N →ₗ[R] N'}
    (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) :
    ConeLin (C := C) (G := G) (G' := G') ρ (c • f) := fun β n hn ↦ (hf β n hn).smul c

theorem ConeLin.sum {ρ : M} {ι : Type*} (s : Finset ι) {f : ι → N →ₗ[R] N'}
    (hf : ∀ i ∈ s, ConeLin (C := C) (G := G) (G' := G') ρ (f i)) :
    ConeLin (C := C) (G := G) (G' := G') ρ (∑ i ∈ s, f i) := fun β n hn ↦ by
  rw [LinearMap.coe_sum, Finset.sum_apply]; exact ConeAt.sum _ fun i hi ↦ hf i hi β n hn

theorem ConeLin.mono {ρ γ : M} {f : N →ₗ[R] N'} (hf : ConeLin (C := C) (G := G) (G' := G') (ρ + γ) f)
    (hγ : γ ∈ C) : ConeLin (C := C) (G := G) (G' := G') ρ f := fun β n hn ↦
  (hf β n hn).mono (by rwa [show β + (ρ + γ) - (β + ρ) = γ by abel])

theorem ConeLin.of_shift {ρ : M} {f : N →ₗ[R] N'} (hf : Shift G G' ρ f) :
    ConeLin (C := C) (G := G) (G' := G') ρ f := fun β n hn ↦ coneAt_of_isHom (hf β n hn)

theorem ConeLin.comp {ρ ρ' : M} {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''}
    (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) (hg : ConeLin (C := C) (G := G') (G' := G'') ρ' g) :
    ConeLin (C := C) (G := G) (G' := G'') (ρ + ρ') (g ∘ₗ f) := fun β n hn ↦ by
  rw [LinearMap.comp_apply, ← add_assoc]; exact hg.apply (hf β n hn)

theorem clin_bot_apply (ρ : M) (f : N →ₗ[R] N') {β : M} {n : N} (hn : G.IsHom β n) :
    clin ⊥ G G' ρ f n = G'.proj (β + ρ) (f n) := by
  rw [clin_apply_hom ρ f hn, cpart_bot]

theorem clin_bot_add (ρ : M) (f g : N →ₗ[R] N') :
    clin ⊥ G G' ρ (f + g) = clin ⊥ G G' ρ f + clin ⊥ G G' ρ g :=
  G.ext_of_hom fun β n hn ↦ by
    rw [LinearMap.add_apply, clin_bot_apply ρ _ hn, clin_bot_apply ρ _ hn, clin_bot_apply ρ _ hn,
      LinearMap.add_apply, map_add]

theorem clin_bot_smul (ρ : M) (c : R) (f : N →ₗ[R] N') :
    clin ⊥ G G' ρ (c • f) = c • clin ⊥ G G' ρ f :=
  G.ext_of_hom fun β n hn ↦ by
    rw [LinearMap.smul_apply, clin_bot_apply ρ _ hn, clin_bot_apply ρ _ hn, LinearMap.smul_apply,
      map_smul]

theorem clin_bot_sub (ρ : M) (f g : N →ₗ[R] N') :
    clin ⊥ G G' ρ (f - g) = clin ⊥ G G' ρ f - clin ⊥ G G' ρ g :=
  G.ext_of_hom fun β n hn ↦ by
    rw [LinearMap.sub_apply, clin_bot_apply ρ _ hn, clin_bot_apply ρ _ hn, clin_bot_apply ρ _ hn,
      LinearMap.sub_apply, map_sub]

theorem clin_bot_sum (ρ : M) {ι : Type*} (s : Finset ι) (f : ι → N →ₗ[R] N') :
    clin ⊥ G G' ρ (∑ i ∈ s, f i) = ∑ i ∈ s, clin ⊥ G G' ρ (f i) :=
  G.ext_of_hom fun β n hn ↦ by
    rw [clin_bot_apply ρ _ hn, LinearMap.coe_sum, Finset.sum_apply, map_sum, LinearMap.coe_sum,
      Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ (clin_bot_apply ρ _ hn).symm

theorem clin_bot_of_shift {ρ : M} {f : N →ₗ[R] N'} (hf : Shift G G' ρ f) : clin ⊥ G G' ρ f = f :=
  G.ext_of_hom fun β n hn ↦ by rw [clin_bot_apply ρ _ hn, hf β n hn]

include hCp in
/-- A map whose relative weights lie in `γ + C` with `γ ≠ 0` has no bottom part. -/
theorem clin_bot_of_pos {ρ γ : M} {f : N →ₗ[R] N'} (hf : ConeLin (C := C) (G := G) (G' := G') (ρ + γ) f)
    (hγ : γ ∈ C) (hγ0 : γ ≠ 0) : clin ⊥ G G' ρ f = 0 :=
  G.ext_of_hom fun β n hn ↦ by
    rw [clin_bot_apply ρ _ hn, LinearMap.zero_apply]
    refine proj_eq_zero_of_coneAt hCp (hf β n hn) ?_ ?_
    · rwa [show β + (ρ + γ) - (β + ρ) = γ by abel]
    · intro h; apply hγ0; rw [← add_assoc] at h; simpa using h

include hCp in
/-- **The bottom part of a composite is the composite of the bottom parts.** -/
theorem clin_bot_comp {ρ ρ' : M} {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''}
    (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) (hg : ConeLin (C := C) (G := G') (G' := G'') ρ' g) :
    clin ⊥ G G'' (ρ + ρ') (g ∘ₗ f) = clin ⊥ G' G'' ρ' g ∘ₗ clin ⊥ G G' ρ f :=
  G.ext_of_hom fun β n hn ↦ by
    rw [clin_bot_apply _ _ hn, LinearMap.comp_apply, LinearMap.comp_apply, clin_bot_apply _ _ hn,
      clin_bot_apply _ _ (G'.isHom_proj _ _), ← add_assoc]
    exact hg.proj_bottom hCp (hf β n hn)

end MapsCone

/-! ### Components at an atom of the cone -/

section Atom

variable {γ : M} (hγ : γ ∈ C) (hγ0 : γ ≠ 0) (hat : ∀ u ∈ C, ∀ v ∈ C, u + v = γ → u = 0 ∨ v = 0)
include hγ hγ0 hat

/-- **Atom components of a linear image**: only the bottom and the atom component of the input
contribute to the atom component of the output. -/
theorem ConeLin.proj_atom {ρ σ : M} {f : N →ₗ[R] N'}
    (hf : ConeLin (C := C) (G := G) (G' := G') ρ f) {n : N} (hn : ConeAt C G σ n) :
    G'.proj (σ + ρ + γ) (f n) =
      G'.proj (σ + ρ + γ) (f (G.proj σ n)) + G'.proj (σ + ρ + γ) (f (G.proj (σ + γ) n)) := by
  classical
  have key : ∀ δ, δ ≠ σ → δ ≠ σ + γ → G'.proj (σ + ρ + γ) (f (G.proj δ n)) = 0 := by
    intro δ h1 h2
    by_cases hδ : δ - σ ∈ C
    · by_cases hδ' : γ - (δ - σ) ∈ C
      · rcases hat _ hδ _ hδ' (by abel) with h | h
        · exact absurd (sub_eq_zero.1 h) h1
        · exact absurd (by rw [sub_eq_zero] at h; rw [h]; abel) h2
      · refine hf δ _ (G.isHom_proj δ n) _ ?_
        rwa [show σ + ρ + γ - (δ + ρ) = γ - (δ - σ) by abel]
    · rw [hn δ hδ, map_zero, map_zero]
  conv_lhs => rw [G.sum n, map_sum, map_sum]
  have hne : σ ≠ σ + γ := fun h ↦ hγ0 (by simpa using h.symm)
  rw [← Finset.sum_filter_add_sum_filter_not G.supp (fun δ ↦ δ = σ ∨ δ = σ + γ),
    Finset.sum_eq_zero (s := G.supp.filter fun δ ↦ ¬(δ = σ ∨ δ = σ + γ))
      (fun δ hδ ↦ key δ (fun h ↦ (Finset.mem_filter.1 hδ).2 (Or.inl h))
        (fun h ↦ (Finset.mem_filter.1 hδ).2 (Or.inr h))), add_zero]
  have hsub : G.supp.filter (fun δ ↦ δ = σ ∨ δ = σ + γ) ⊆ {σ, σ + γ} := fun δ hδ ↦ by
    rcases (Finset.mem_filter.1 hδ).2 with h | h <;> simp [h]
  rw [Finset.sum_subset hsub (fun δ hδ hδ' ↦ by
    have : δ ∉ G.supp := fun h ↦ hδ' (Finset.mem_filter.2 ⟨h, by
      rcases Finset.mem_insert.1 hδ with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Finset.mem_singleton.1 h')⟩)
    rw [G.proj_out δ this, LinearMap.zero_apply, map_zero, map_zero]),
    Finset.sum_pair hne]

include hCp in
/-- **Atom components of a bilinear image.** -/
theorem ConeBil.proj_atom {ρ σ σ' : M} {φ : N →ₗ[R] N' →ₗ[R] N''}
    (hφ : ConeBil (C := C) (G := G) (G' := G') (G'' := G'') ρ φ) {n : N} {n' : N'}
    (hn : ConeAt C G σ n) (hn' : ConeAt C G' σ' n') :
    G''.proj (σ + σ' + ρ + γ) (φ n n') =
      G''.proj (σ + σ' + ρ + γ) (φ (G.proj σ n) (G'.proj σ' n')) +
      G''.proj (σ + σ' + ρ + γ) (φ (G.proj (σ + γ) n) (G'.proj σ' n')) +
      G''.proj (σ + σ' + ρ + γ) (φ (G.proj σ n) (G'.proj (σ' + γ) n')) := by
  have h1 : ConeLin (C := C) (G := G) (G' := G'') (σ' + ρ) (φ.flip n') := fun β x hx ↦ by
    have := hφ.apply (coneAt_of_isHom hx) hn'
    rwa [show β + σ' + ρ = β + (σ' + ρ) by abel] at this
  have e1 := h1.proj_atom hCp hγ hγ0 hat hn
  simp only [LinearMap.flip_apply] at e1
  rw [show σ + (σ' + ρ) + γ = σ + σ' + ρ + γ by abel] at e1
  have h2 : ConeLin (C := C) (G := G') (G' := G'') (σ + ρ) (φ (G.proj σ n)) := fun α y hy ↦ by
    have := hφ.apply (coneAt_of_isHom (G.isHom_proj σ n)) (coneAt_of_isHom hy)
    rwa [show σ + α + ρ = α + (σ + ρ) by abel] at this
  have e2 := h2.proj_atom hCp hγ hγ0 hat hn'
  rw [show σ' + (σ + ρ) + γ = σ + σ' + ρ + γ by abel] at e2
  have h3 : ConeLin (C := C) (G := G') (G' := G'') (σ + γ + ρ) (φ (G.proj (σ + γ) n)) :=
    fun α y hy ↦ by
      have := hφ.apply (coneAt_of_isHom (G.isHom_proj (σ + γ) n)) (coneAt_of_isHom hy)
      rwa [show σ + γ + α + ρ = α + (σ + γ + ρ) by abel] at this
  have e3 := h3.proj_bottom hCp hn'
  rw [show σ' + (σ + γ + ρ) = σ + σ' + ρ + γ by abel] at e3
  rw [e1, e2, e3]
  abel

end Atom

end MGr

end MultiplicativeBasisDeformations
