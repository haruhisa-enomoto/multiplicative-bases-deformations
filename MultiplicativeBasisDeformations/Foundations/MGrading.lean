import Mathlib

/-!
# Gradings of modules by an abelian group

Used for the integer weights of Section 7 (`weights-and-parameters.tex`): "a mesh weight `w` grades `V_{m+1}(C)` … and grades `U_m(C)` …; the map `D_m`
preserves these gradings", and "Lift a basis of the integer ray weights to mesh weights
… These give simultaneous gradings on the lifted modules. If `μ` has character `χ`, give
`ε` weight `−χ` and choose the homogeneous solutions in the lemma."

A grading `MGr` of an `R`-module by an abelian group `M` is a family of finitely
supported orthogonal projections. A linear map *shifts by* `γ` if it sends weight `g` to
weight `g + γ`; the weight-`γ` part of an arbitrary linear map is `pr γ φ`. Homogeneous
solutions of linear equations are obtained by applying `pr` to arbitrary solutions,
since `pr` commutes with composition by shifting maps (`pr_comp_left`, `pr_comp_right`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [DecidableEq M]

variable (R M) in
/-- A grading by `M`, by finitely supported orthogonal projections. -/
structure MGr (N : Type*) [AddCommGroup N] [Module R N] where
  proj : M → N →ₗ[R] N
  supp : Finset M
  proj_proj : ∀ g h n, proj g (proj h n) = if h = g then proj h n else 0
  proj_out : ∀ g, g ∉ supp → proj g = 0
  sum : ∀ n, n = ∑ g ∈ supp, proj g n

namespace MGr

variable {N N' N'' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
  [AddCommGroup N''] [Module R N'']

variable (G : MGr R M N) (G' : MGr R M N') (G'' : MGr R M N'')

/-- A homogeneous element of weight `g`. -/
def IsHom (g : M) (n : N) : Prop := G.proj g n = n

theorem isHom_proj (g : M) (n : N) : G.IsHom g (G.proj g n) := by
  unfold IsHom; rw [G.proj_proj, if_pos rfl]

theorem proj_of_isHom {g h : M} {n : N} (hn : G.IsHom g n) : G.proj h n = if g = h then n else 0 := by
  rw [← hn, G.proj_proj, hn]

theorem isHom_zero (g : M) : G.IsHom g (0 : N) := by unfold IsHom; rw [map_zero]

theorem isHom_add {g : M} {n n' : N} (h : G.IsHom g n) (h' : G.IsHom g n') : G.IsHom g (n + n') := by
  unfold IsHom; rw [map_add, h, h']

theorem isHom_smul {g : M} (c : R) {n : N} (h : G.IsHom g n) : G.IsHom g (c • n) := by
  unfold IsHom; rw [map_smul, h]

theorem isHom_neg {g : M} {n : N} (h : G.IsHom g n) : G.IsHom g (-n) := by
  unfold IsHom; rw [map_neg, h]

theorem isHom_sub {g : M} {n n' : N} (h : G.IsHom g n) (h' : G.IsHom g n') : G.IsHom g (n - n') := by
  unfold IsHom; rw [map_sub, h, h']

theorem isHom_sum {g : M} {ι : Type*} (s : Finset ι) (f : ι → N) (h : ∀ i ∈ s, G.IsHom g (f i)) :
    G.IsHom g (∑ i ∈ s, f i) := by
  unfold IsHom; rw [map_sum]; exact Finset.sum_congr rfl h

theorem eq_zero_of_isHom_out {g : M} {n : N} (h : G.IsHom g n) (hg : g ∉ G.supp) : n = 0 := by
  rw [← h, G.proj_out g hg, LinearMap.zero_apply]

theorem eq_zero_of_isHom_ne {g h : M} {n : N} (hg : G.IsHom g n) (hh : G.IsHom h n) (hne : g ≠ h) :
    n = 0 := by
  rw [← hh, G.proj_of_isHom hg, if_neg hne]

/-- Linear maps agreeing on homogeneous elements agree. -/
theorem ext_of_hom {P : Type*} [AddCommGroup P] [Module R P] {f f' : N →ₗ[R] P}
    (h : ∀ g n, G.IsHom g n → f n = f' n) : f = f' := by
  ext n
  rw [G.sum n, map_sum, map_sum]
  exact Finset.sum_congr rfl fun g _ ↦ h g _ (G.isHom_proj g n)

/-- Elements with the same components are equal. -/
theorem eq_of_proj {n n' : N} (h : ∀ g, G.proj g n = G.proj g n') : n = n' := by
  rw [G.sum n, G.sum n']
  exact Finset.sum_congr rfl fun g _ ↦ h g

/-- The projection of a homogeneous sum. -/
theorem proj_sum_hom {ι : Type*} (s : Finset ι) (f : ι → N) (w : ι → M)
    (hf : ∀ i ∈ s, G.IsHom (w i) (f i)) (g : M) :
    G.proj g (∑ i ∈ s, f i) = ∑ i ∈ s.filter (fun i ↦ w i = g), f i := by
  rw [map_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i hi ↦ G.proj_of_isHom (hf i hi)

/-! ### Shifting maps -/

/-- `φ` shifts weights by `γ`. -/
def Shift (γ : M) (φ : N →ₗ[R] N') : Prop := ∀ g n, G.IsHom g n → G'.IsHom (g + γ) (φ n)

variable {G G' G''}

theorem Shift.zero (γ : M) : Shift G G' γ 0 := fun _ _ _ ↦ G'.isHom_zero _

theorem Shift.add {γ : M} {φ ψ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) (hψ : Shift G G' γ ψ) :
    Shift G G' γ (φ + ψ) := fun g n hn ↦ G'.isHom_add (hφ g n hn) (hψ g n hn)

theorem Shift.sub {γ : M} {φ ψ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) (hψ : Shift G G' γ ψ) :
    Shift G G' γ (φ - ψ) := fun g n hn ↦ G'.isHom_sub (hφ g n hn) (hψ g n hn)

theorem Shift.smul {γ : M} {φ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) (c : R) :
    Shift G G' γ (c • φ) := fun g n hn ↦ G'.isHom_smul c (hφ g n hn)

theorem Shift.sum {γ : M} {ι : Type*} (s : Finset ι) {φ : ι → N →ₗ[R] N'}
    (h : ∀ i ∈ s, Shift G G' γ (φ i)) : Shift G G' γ (∑ i ∈ s, φ i) := fun g n hn ↦ by
  rw [LinearMap.coe_sum, Finset.sum_apply]
  exact G'.isHom_sum _ _ fun i hi ↦ h i hi g n hn

theorem Shift.comp {γ δ : M} {φ : N →ₗ[R] N'} {ψ : N' →ₗ[R] N''} (hψ : Shift G' G'' δ ψ)
    (hφ : Shift G G' γ φ) : Shift G G'' (γ + δ) (ψ ∘ₗ φ) := fun g n hn ↦ by
  rw [← add_assoc]; exact hψ _ _ (hφ g n hn)

theorem Shift.congr {γ γ' : M} {φ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) (h : γ = γ') :
    Shift G G' γ' φ := h ▸ hφ

/-- A shifting map commutes with the projections. -/
theorem Shift.proj {γ : M} {φ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) (g : M) (n : N) :
    G'.proj (g + γ) (φ n) = φ (G.proj g n) := by
  conv_lhs => rw [G.sum n, map_sum]
  rw [G'.proj_sum_hom _ _ (fun h ↦ h + γ) (fun h _ ↦ hφ h _ (G.isHom_proj h n))]
  simp only [add_left_inj]
  by_cases hg : g ∈ G.supp
  · rw [Finset.sum_eq_single g]
    · intro h hh hne
      exact absurd (Finset.mem_filter.1 hh).2 hne
    · intro hg'; exact (hg' (Finset.mem_filter.2 ⟨hg, rfl⟩)).elim
  · rw [G.proj_out g hg, LinearMap.zero_apply, map_zero]
    refine Finset.sum_eq_zero fun h hh ↦ ?_
    obtain ⟨hh, he⟩ := Finset.mem_filter.1 hh
    exact absurd (he ▸ hh) hg

variable (G G') in
/-- The weight-`γ` part of a linear map. -/
def pr (γ : M) (φ : N →ₗ[R] N') : N →ₗ[R] N' :=
  ∑ g ∈ G.supp, G'.proj (g + γ) ∘ₗ φ ∘ₗ G.proj g

theorem pr_apply_hom (γ : M) (φ : N →ₗ[R] N') {g : M} {n : N} (hn : G.IsHom g n) :
    pr G G' γ φ n = G'.proj (g + γ) (φ n) := by
  simp only [pr, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  by_cases hg : g ∈ G.supp
  · rw [Finset.sum_eq_single g]
    · rw [hn]
    · intro h _ hne; rw [G.proj_of_isHom hn, if_neg (Ne.symm hne), map_zero, map_zero]
    · intro h; exact absurd hg h
  · rw [G.eq_zero_of_isHom_out hn hg]; simp

theorem shift_pr (γ : M) (φ : N →ₗ[R] N') : Shift G G' γ (pr G G' γ φ) := fun g n hn ↦ by
  rw [pr_apply_hom γ φ hn]; exact G'.isHom_proj _ _

theorem pr_of_shift {γ : M} {φ : N →ₗ[R] N'} (hφ : Shift G G' γ φ) : pr G G' γ φ = φ :=
  G.ext_of_hom fun g n hn ↦ by rw [pr_apply_hom γ φ hn, hφ g n hn]

theorem pr_add (γ : M) (φ ψ : N →ₗ[R] N') : pr G G' γ (φ + ψ) = pr G G' γ φ + pr G G' γ ψ :=
  G.ext_of_hom fun g n hn ↦ by
    rw [LinearMap.add_apply, pr_apply_hom γ _ hn, pr_apply_hom γ _ hn, pr_apply_hom γ _ hn,
      LinearMap.add_apply, map_add]

theorem pr_sub (γ : M) (φ ψ : N →ₗ[R] N') : pr G G' γ (φ - ψ) = pr G G' γ φ - pr G G' γ ψ :=
  G.ext_of_hom fun g n hn ↦ by
    rw [LinearMap.sub_apply, pr_apply_hom γ _ hn, pr_apply_hom γ _ hn, pr_apply_hom γ _ hn,
      LinearMap.sub_apply, map_sub]

theorem pr_smul (γ : M) (c : R) (φ : N →ₗ[R] N') : pr G G' γ (c • φ) = c • pr G G' γ φ :=
  G.ext_of_hom fun g n hn ↦ by
    rw [LinearMap.smul_apply, pr_apply_hom γ _ hn, pr_apply_hom γ _ hn, LinearMap.smul_apply,
      map_smul]

theorem pr_zero (γ : M) : pr G G' γ (0 : N →ₗ[R] N') = 0 := pr_of_shift (Shift.zero γ)

theorem pr_sum (γ : M) {ι : Type*} (s : Finset ι) (φ : ι → N →ₗ[R] N') :
    pr G G' γ (∑ i ∈ s, φ i) = ∑ i ∈ s, pr G G' γ (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact pr_zero γ
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add, ih]

/-- Composition on the left with a shifting map. -/
theorem pr_comp_left {γ δ : M} (φ : N →ₗ[R] N') {ψ : N' →ₗ[R] N''} (hψ : Shift G' G'' δ ψ) :
    pr G G'' (γ + δ) (ψ ∘ₗ φ) = ψ ∘ₗ pr G G' γ φ :=
  G.ext_of_hom fun g n hn ↦ by
    rw [pr_apply_hom _ _ hn, LinearMap.comp_apply, LinearMap.comp_apply, pr_apply_hom _ _ hn,
      ← add_assoc, hψ.proj]

/-- Composition on the right with a shifting map. -/
theorem pr_comp_right {γ δ : M} (φ : N →ₗ[R] N') {ψ : N'' →ₗ[R] N} (hψ : Shift G'' G δ ψ) :
    pr G'' G' (δ + γ) (φ ∘ₗ ψ) = pr G G' γ φ ∘ₗ ψ :=
  G''.ext_of_hom fun g n hn ↦ by
    rw [pr_apply_hom _ _ hn, LinearMap.comp_apply, LinearMap.comp_apply,
      pr_apply_hom _ _ (hψ g n hn), add_assoc]

/-- The projections themselves do not shift. -/
theorem shift_proj (g : M) : Shift G G 0 (G.proj g) := fun h n hn ↦ by
  rw [add_zero, G.proj_of_isHom hn]
  split_ifs
  · exact hn
  · exact G.isHom_zero _

end MGr

end MultiplicativeBasisDeformations
