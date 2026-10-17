import MultiplicativeBasisDeformations.Refinements.SplitRelative

/-!
# Lemma 6.4 for a split semisimple `S = Λ₀`

`lem:split-positive-deformation` (`positive-deformations.tex:180–193`): "Let `k` be any field, let
`Λ` be a finite-dimensional nonnegatively graded algebra with split semisimple `S = Λ₀`, and let
`B` be a positive filtered deformation of `Λ`. Then `S` lifts to a unital subalgebra of `B`, and
the filtration of `B` splits as `S`-bimodules. […] each `μ_q` raises internal degree by `q`, is
`S`-relative, and vanishes when an input belongs to `S`."

A split semisimple `S ≅ ∏_a M_{n_a}(k)` is recorded by a complete system of matrix units
spanning `Λ₀` (`MatUnits`: `E_{ij}` for `i, j` in one block, the block of `i` named by a root
`rt i`). The diagonal units lift to orthogonal idempotents `f_i` (through the nilpotent ideal
`F¹`), the units `E_{i,rt i}`, `E_{rt i,i}` lift to `x_i`, `y_i` with `x_i y_i = f_i` after
inverting `x_i y_i` in the corner `f_iBf_i` (geometric series), and then `y_i x_i = f_{rt i}`
(an idempotent congruent to `f_{rt i}` modulo `F¹`); `L_{ij} = x_i y_j` are lifted matrix units
(`L_mul`, `σ_L`). The splitting of the corners (`φ0`, from the diagonal idempotents) is
transported from the root corners: `Φ(a) = Σ_{i,j} L_{i,rt i} φ0(E_{rt i,i} a E_{j,rt j}) L_{rt j,j}`,
which is `S`-bilinear (`Φ_left`, `Φ_right`), unital and has leading term the identity
(`Φ_lead`). The statement is `splitPositiveDeformation_ss`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

namespace LenGrading

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ] (G : LenGrading k Λ)

/-- **A split semisimple degree-zero part** `Λ₀ ≅ ∏_a M_{n_a}(k)`: a complete system of matrix
units of degree `0` spanning `Λ₀`. Indices in one block have the same root `rt i`; `E_{ij}` is
defined for `i, j` in one block and zero otherwise. -/
structure MatUnits where
  n : ℕ
  rt : Fin n → Fin n
  rt_rt : ∀ i, rt (rt i) = rt i
  E : Fin n → Fin n → Λ
  E_mul : ∀ i j l m, rt i = rt j → rt l = rt m → E i j * E l m = if j = l then E i m else 0
  E_off : ∀ i j, rt i ≠ rt j → E i j = 0
  sum_E : ∑ i, E i i = 1
  deg0 : ∀ i j, G.IsHom 0 (E i j)
  span0 : ∀ a, G.IsHom 0 a → ∃ c : Fin n → Fin n → k, a = ∑ i, ∑ j, c i j • E i j

variable {G} (M : MatUnits G)

namespace MatUnits

theorem diag_complete : CompleteOrthogonalIdempotents fun i ↦ M.E i i :=
  ⟨⟨fun i ↦ by change _ * _ = _; rw [M.E_mul i i i i rfl rfl, if_pos rfl],
    fun i j hij ↦ by change _ * _ = _; rw [M.E_mul i i j j rfl rfl, if_neg hij]⟩, M.sum_E⟩

theorem diag_mul_mul_diag (i l m : Fin M.n) :
    M.E i i * M.E l m * M.E i i = if l = i ∧ m = i then M.E i i else 0 := by
  by_cases h : M.rt l = M.rt m
  · rw [M.E_mul i i l m rfl h]
    by_cases hl : i = l
    · subst hl
      rw [if_pos rfl, M.E_mul i m i i h rfl]
      by_cases hm : m = i
      · rw [if_pos hm, if_pos ⟨rfl, hm⟩]
      · rw [if_neg hm, if_neg (fun h' ↦ hm h'.2)]
    · rw [if_neg hl, zero_mul, if_neg (fun h' ↦ hl h'.1.symm)]
  · rw [M.E_off l m h, mul_zero, zero_mul]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'; exact absurd rfl h
    · rfl

/-- The diagonal matrix units as diagonal idempotents (`e_i Λ₀ e_i = k e_i`). -/
abbrev diag : Diag G where
  n := M.n
  e i := M.E i i
  complete := M.diag_complete
  deg0 i := M.deg0 i i
  corner0 i a ha := by
    obtain ⟨c, rfl⟩ := M.span0 a ha
    refine ⟨c i i, ?_⟩
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    simp_rw [diag_mul_mul_diag]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i, if_pos ⟨rfl, rfl⟩]
    · intro m _ hm; rw [if_neg (fun h ↦ hm h.2), smul_zero]
    · intro h; exact absurd (mem_univ i) h
    · intro l _ hl
      exact Finset.sum_eq_zero fun m _ ↦ by rw [if_neg (fun h ↦ hl h.1), smul_zero]
    · intro h; exact absurd (mem_univ i) h

theorem diag_e (i : Fin M.n) : M.diag.e i = M.E i i := rfl

theorem rt_eq (i : Fin M.n) : M.rt (M.rt i) = M.rt i := M.rt_rt i

/-- `E_{i,rt i} E_{rt i,i} = E_{ii}`. -/
theorem E_rt_mul (i : Fin M.n) : M.E i (M.rt i) * M.E (M.rt i) i = M.E i i := by
  rw [M.E_mul _ _ _ _ (M.rt_rt i).symm (M.rt_rt i), if_pos rfl]

end MatUnits

end LenGrading

namespace PosFiltration

open LenGrading

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type*} [Ring B] [Algebra k B] {P : PosFiltration G B}

/-! ### Linear maps with leading term the identity -/

section Lead

variable (Ψ : Λ →ₗ[k] B) (hΨ : ∀ d a, G.IsHom d a → Ψ a ∈ P.F d ∧ P.σ d (Ψ a) = a)

include hΨ in
theorem lead_ge {d : ℕ} {a : Λ} (ha : G.Ge d a) : Ψ a ∈ P.F d := by
  rw [G.eq_sum_proj_of_ge ha, map_sum]
  exact Submodule.sum_mem _ fun e he ↦
    P.F_anti (Finset.mem_Ico.1 he).1 (hΨ e _ (G.isHom_proj e a)).1

include hΨ in
theorem lead_surj_aux : ∀ n d, P.M ≤ d + n → ∀ x ∈ P.F d, ∃ a, G.Ge d a ∧ Ψ a = x := by
  intro n
  induction n with
  | zero =>
      intro d hd x hx
      rw [P.eq_bot_of_le (by omega)] at hx
      rw [(Submodule.mem_bot k).1 hx]
      exact ⟨0, fun _ _ ↦ map_zero _, map_zero _⟩
  | succ n ih =>
      intro d hd x hx
      set y := x - Ψ (P.σ d x)
      have hlead := hΨ d _ (P.σ_hom d x)
      have hy : y ∈ P.F (d + 1) := by
        refine (P.σ_ker d y (Submodule.sub_mem _ hx hlead.1)).1 ?_
        rw [map_sub, hlead.2, sub_self]
      obtain ⟨a', ha', hay⟩ := ih (d + 1) (by omega) y hy
      refine ⟨P.σ d x + a', G.ge_add (G.ge_of_isHom (P.σ_hom d x)) (G.ge_mono (by omega) ha'), ?_⟩
      rw [map_add, hay]
      show _ + (x - _) = x
      abel

include hΨ in
theorem lead_injective : Function.Injective Ψ := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [LinearMap.mem_ker] at ha
  rw [Submodule.mem_bot]
  by_contra ha0
  have hex : ∃ d, G.proj d a ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (by rw [G.sum a]; exact Finset.sum_eq_zero fun d _ ↦ h d)
  set d := Nat.find hex
  have hge : G.Ge d a := fun e he ↦ by
    by_contra h
    exact Nat.find_min hex he h
  have h1 := lead_ge Ψ hΨ (G.ge_sub_proj hge)
  rw [map_sub, ha, zero_sub] at h1
  have h2 : Ψ (G.proj d a) ∈ P.F (d + 1) := by
    have := Submodule.neg_mem _ h1
    rwa [neg_neg] at this
  have h3 := hΨ d _ (G.isHom_proj d a)
  have h4 := (P.σ_ker d _ h3.1).2 h2
  rw [h3.2] at h4
  exact Nat.find_spec hex h4

/-- A unital linear map with leading term the identity is a splitting. -/
def splitOfLead (h1 : Ψ 1 = 1) : Split P where
  φ := LinearEquiv.ofBijective Ψ ⟨lead_injective Ψ hΨ, fun x ↦ by
    obtain ⟨a, -, ha⟩ := lead_surj_aux Ψ hΨ P.M 0 (by omega) x (P.mem_zero x)
    exact ⟨a, ha⟩⟩
  one := h1
  σφ d a ha := (hΨ d a ha).2
  F_eq d := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact lead_ge Ψ hΨ ha
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := lead_surj_aux Ψ hΨ P.M d (by omega) x hx
      exact ⟨a, ha, rfl⟩

theorem splitOfLead_φ (h1 : Ψ 1 = 1) (a : Λ) : (splitOfLead Ψ hΨ h1).φ a = Ψ a := rfl

end Lead

/-! ### Lifting the matrix units -/

section Lift

variable (M : MatUnits G) {f : Fin M.n → B} (hf : CompleteOrthogonalIdempotents f)
  (hσf : ∀ i, P.σ 0 (f i) = M.diag.e i)

local notation "σ'" => P.σ0 M.diag

variable (P) in
/-- A lift of `E_{i,rt i}`. -/
def aL (i : Fin M.n) : B := Classical.choose (P.σ_surj 0 (M.E i (M.rt i)) (M.deg0 _ _))

variable (P) in
/-- A lift of `E_{rt i,i}`. -/
def aR (i : Fin M.n) : B := Classical.choose (P.σ_surj 0 (M.E (M.rt i) i) (M.deg0 _ _))

theorem σ_aL (i : Fin M.n) : P.σ 0 (aL P M i) = M.E i (M.rt i) :=
  (Classical.choose_spec (P.σ_surj 0 (M.E i (M.rt i)) (M.deg0 _ _))).2

theorem σ_aR (i : Fin M.n) : P.σ 0 (aR P M i) = M.E (M.rt i) i :=
  (Classical.choose_spec (P.σ_surj 0 (M.E (M.rt i) i) (M.deg0 _ _))).2

variable (P f) in
def xL (i : Fin M.n) : B := f i * aL P M i * f (M.rt i)

variable (P f) in
def yL (i : Fin M.n) : B := f (M.rt i) * aR P M i * f i

include hf in
theorem f_xL (i : Fin M.n) : f i * xL P M f i = xL P M f i := by
  simp only [xL, ← mul_assoc, (hf.idem i).eq]

include hf in
theorem xL_f (i : Fin M.n) : xL P M f i * f (M.rt i) = xL P M f i := by
  simp only [xL, mul_assoc, (hf.idem (M.rt i)).eq]

include hf in
theorem f_yL (i : Fin M.n) : f (M.rt i) * yL P M f i = yL P M f i := by
  simp only [yL, ← mul_assoc, (hf.idem (M.rt i)).eq]

include hf in
theorem yL_f (i : Fin M.n) : yL P M f i * f i = yL P M f i := by
  simp only [yL, mul_assoc, (hf.idem i).eq]

include hσf in
theorem σ_xL (i : Fin M.n) : σ' (xL P M f i) = M.E i (M.rt i) := by
  rw [xL, map_mul, map_mul]
  simp only [σ0_apply]
  rw [hσf, hσf, σ_aL, M.diag_e, M.diag_e,
    M.E_mul _ _ _ _ rfl (M.rt_rt i).symm, if_pos rfl, M.E_mul _ _ _ _ (M.rt_rt i).symm rfl,
    if_pos rfl]

include hσf in
theorem σ_yL (i : Fin M.n) : σ' (yL P M f i) = M.E (M.rt i) i := by
  rw [yL, map_mul, map_mul]
  simp only [σ0_apply]
  rw [hσf, hσf, σ_aR, M.diag_e, M.diag_e,
    M.E_mul _ _ _ _ rfl (M.rt_rt i), if_pos rfl, M.E_mul _ _ _ _ (M.rt_rt i) rfl, if_pos rfl]

variable (P f) in
/-- `f_i − x_i y_i ∈ F¹`. -/
def nL (i : Fin M.n) : B := f i - xL P M f i * yL P M f i

include hσf in
theorem σ_nL (i : Fin M.n) : σ' (nL P M f i) = 0 := by
  rw [nL, map_sub, map_mul, σ_xL M hσf, σ_yL M hσf, σ0_apply, hσf, M.diag_e, M.E_rt_mul,
    sub_self]

include hσf in
theorem nL_mem (i : Fin M.n) : nL P M f i ∈ P.F 1 :=
  (P.σ_ker 0 _ (P.mem_zero _)).1 (σ_nL M hσf i)

include hf in
theorem f_nL (i : Fin M.n) : f i * nL P M f i = nL P M f i := by
  rw [nL, mul_sub, (hf.idem i).eq, ← mul_assoc, f_xL M hf]

include hf in
theorem nL_f (i : Fin M.n) : nL P M f i * f i = nL P M f i := by
  rw [nL, sub_mul, (hf.idem i).eq, mul_assoc, yL_f M hf]

include hσf in
theorem nL_pow (i : Fin M.n) : nL P M f i ^ (P.M + 1) = 0 := by
  have := P.pow_mem (nL_mem M hσf i) P.M
  rw [P.eq_bot_of_le (Nat.le_succ P.M)] at this
  exact (Submodule.mem_bot k).1 this

variable (P f) in
/-- The geometric series `Σ_{t ≤ M} n_i^t`, an inverse of `1 − n_i`. -/
def sL (i : Fin M.n) : B := ∑ t ∈ range (P.M + 1), nL P M f i ^ t

include hσf in
theorem one_sub_mul_sL (i : Fin M.n) : (1 - nL P M f i) * sL P M f i = 1 := by
  rw [sL, mul_neg_geom_sum, nL_pow M hσf, sub_zero]

include hσf in
theorem sL_mul_one_sub (i : Fin M.n) : sL P M f i * (1 - nL P M f i) = 1 := by
  rw [sL, geom_sum_mul_neg, nL_pow M hσf, sub_zero]

include hf in
theorem commute_f_sL (i : Fin M.n) : Commute (f i) (sL P M f i) := by
  have hc : Commute (f i) (nL P M f i) := by
    change f i * _ = _ * f i; rw [f_nL M hf, nL_f M hf]
  exact Commute.sum_right _ _ _ fun t _ ↦ hc.pow_right t

variable (P f) in
/-- `v_i = f_i s_i`, the inverse of `x_i y_i` in the corner `f_iBf_i`. -/
def vL (i : Fin M.n) : B := f i * sL P M f i

include hf hσf in
theorem xy_vL (i : Fin M.n) : xL P M f i * yL P M f i * vL P M f i = f i := by
  have h1 : xL P M f i * yL P M f i = f i * (1 - nL P M f i) := by
    rw [mul_sub, mul_one, f_nL M hf, nL, sub_sub_cancel]
  have h2 : (1 - nL P M f i) * f i = f i * (1 - nL P M f i) := by
    rw [sub_mul, one_mul, nL_f M hf, mul_sub, mul_one, f_nL M hf]
  rw [h1, vL]
  calc f i * (1 - nL P M f i) * (f i * sL P M f i)
      = f i * ((1 - nL P M f i) * f i) * sL P M f i := by simp only [mul_assoc]
    _ = (f i * f i) * ((1 - nL P M f i) * sL P M f i) := by rw [h2]; simp only [mul_assoc]
    _ = f i := by rw [(hf.idem i).eq, one_sub_mul_sL M hσf, mul_one]

include hf in
theorem vL_f (i : Fin M.n) : vL P M f i * f i = vL P M f i := by
  rw [vL, mul_assoc, ← (commute_f_sL M hf i).eq, ← mul_assoc, (hf.idem i).eq]

include hσf in
theorem σ_vL (i : Fin M.n) : σ' (vL P M f i) = M.E i i := by
  have hs : σ' (sL P M f i) = 1 := by
    have := congrArg σ' (one_sub_mul_sL M hσf i)
    rwa [map_mul, map_sub, map_one, σ_nL M hσf, sub_zero, one_mul] at this
  rw [vL, map_mul, hs, mul_one, σ0_apply, hσf, M.diag_e]

variable (P f) in
/-- `y'_i = y_i v_i`, with `x_i y'_i = f_i`. -/
def yL' (i : Fin M.n) : B := yL P M f i * vL P M f i

include hf hσf in
theorem xL_yL' (i : Fin M.n) : xL P M f i * yL' P M f i = f i := by
  rw [yL', ← mul_assoc, xy_vL M hf hσf]

include hf in
theorem yL'_f (i : Fin M.n) : yL' P M f i * f i = yL' P M f i := by
  rw [yL', mul_assoc, vL_f M hf]

include hf in
theorem f_yL' (i : Fin M.n) : f (M.rt i) * yL' P M f i = yL' P M f i := by
  rw [yL', ← mul_assoc, f_yL M hf]

include hσf in
theorem σ_yL' (i : Fin M.n) : σ' (yL' P M f i) = M.E (M.rt i) i := by
  rw [yL', map_mul, σ_yL M hσf, σ_vL M hσf, M.E_mul _ _ _ _ (M.rt_rt i) rfl, if_pos rfl]

include hf hσf in
/-- **`y'_i x_i = f_{rt i}`**: an idempotent of the corner `f_{rt i}Bf_{rt i}` congruent to
`f_{rt i}` modulo the nilpotent ideal `F¹`. -/
theorem yL'_xL (i : Fin M.n) : yL' P M f i * xL P M f i = f (M.rt i) := by
  set g := yL' P M f i * xL P M f i
  have hfg : f (M.rt i) * g = g := by rw [← mul_assoc, f_yL' M hf]
  have hgf : g * f (M.rt i) = g := by rw [mul_assoc, xL_f M hf]
  have hgg : g * g = g := by
    calc g * g = yL' P M f i * (xL P M f i * yL' P M f i) * xL P M f i := by simp only [g, mul_assoc]
      _ = g := by rw [xL_yL' M hf hσf, yL'_f M hf]
  have hidem : IsIdempotentElem (f (M.rt i) - g) := by
    change (f (M.rt i) - g) * (f (M.rt i) - g) = f (M.rt i) - g
    rw [mul_sub, sub_mul, sub_mul, (hf.idem _).eq, hfg, hgf, hgg]; abel
  have hσ : σ' (f (M.rt i) - g) = 0 := by
    rw [map_sub, σ0_apply, hσf, M.diag_e, map_mul, σ_yL' M hσf, σ_xL M hσf,
      M.E_mul _ _ _ _ (M.rt_rt i) (M.rt_rt i).symm, if_pos rfl, sub_self]
  have h1 : f (M.rt i) - g ∈ P.F 1 := (P.σ_ker 0 _ (P.mem_zero _)).1 hσ
  exact (sub_eq_zero.1 (P.idem_eq_zero hidem h1)).symm

variable (P f) in
/-- **The lifted matrix units** `L_{ij} = x_i y'_j`. -/
def L (i j : Fin M.n) : B := if M.rt i = M.rt j then xL P M f i * yL' P M f j else 0

include hf hσf in
theorem L_mul {i j l m : Fin M.n} (hij : M.rt i = M.rt j) (hlm : M.rt l = M.rt m) :
    L P M f i j * L P M f l m = if j = l then L P M f i m else 0 := by
  rw [L, L, if_pos hij, if_pos hlm]
  by_cases hjl : j = l
  · subst hjl
    rw [if_pos rfl, L, if_pos (hij.trans hlm)]
    calc xL P M f i * yL' P M f j * (xL P M f j * yL' P M f m)
        = xL P M f i * (yL' P M f j * xL P M f j) * yL' P M f m := by simp only [mul_assoc]
      _ = _ := by rw [yL'_xL M hf hσf, ← hij, xL_f M hf]
  · rw [if_neg hjl]
    calc xL P M f i * yL' P M f j * (xL P M f l * yL' P M f m)
        = xL P M f i * (yL' P M f j * f j) * (f l * xL P M f l) * yL' P M f m := by
          rw [yL'_f M hf, f_xL M hf]; simp only [mul_assoc]
      _ = 0 := by
          rw [show xL P M f i * (yL' P M f j * f j) * (f l * xL P M f l) =
              xL P M f i * yL' P M f j * (f j * f l) * xL P M f l by simp only [mul_assoc],
            hf.ortho hjl, mul_zero, zero_mul, zero_mul]

include hf hσf in
theorem L_diag (i : Fin M.n) : L P M f i i = f i := by
  rw [L, if_pos rfl, xL_yL' M hf hσf]

include hf hσf in
theorem σ_L (i j : Fin M.n) : σ' (L P M f i j) = M.E i j := by
  unfold L
  split_ifs with h
  · rw [map_mul, σ_xL M hσf, σ_yL' M hσf, M.E_mul _ _ _ _ (M.rt_rt i).symm (M.rt_rt j),
      if_pos h]
  · rw [map_zero, M.E_off i j h]

/-! ### The transported splitting -/

variable (P f) in
/-- **The splitting transported from the root corners**:
`Φ(a) = Σ_{i,j} L_{i,rt i} φ0(E_{rt i,i} a E_{j,rt j}) L_{rt j,j}`. -/
def Φ : Λ →ₗ[k] B :=
  ∑ i, ∑ j, (LinearMap.mulLeft k (L P M f i (M.rt i)) ∘ₗ LinearMap.mulRight k (L P M f (M.rt j) j))
    ∘ₗ φ0 (V := M.diag) hf hσf ∘ₗ
      (LinearMap.mulLeft k (M.E (M.rt i) i) ∘ₗ LinearMap.mulRight k (M.E j (M.rt j)))

theorem Φ_apply (a : Λ) : Φ P M f hf hσf a = ∑ i, ∑ j, L P M f i (M.rt i) *
    φ0 (V := M.diag) hf hσf (M.E (M.rt i) i * a * M.E j (M.rt j)) * L P M f (M.rt j) j := by
  simp [Φ, LinearMap.sum_apply, mul_assoc]

theorem E_rt_isHom {d : ℕ} {a : Λ} (ha : G.IsHom d a) (i j : Fin M.n) :
    G.IsHom d (M.E (M.rt i) i * a * M.E j (M.rt j)) := by
  simpa using G.isHom_mul (G.isHom_mul (M.deg0 _ _) ha) (M.deg0 _ _)

/-- **Leading term the identity.** -/
theorem Φ_lead (d : ℕ) (a : Λ) (ha : G.IsHom d a) :
    Φ P M f hf hσf a ∈ P.F d ∧ P.σ d (Φ P M f hf hσf a) = a := by
  rw [Φ_apply]
  have hφ := fun i j ↦ φ0_hom (V := M.diag) hf hσf (E_rt_isHom M ha i j)
  refine ⟨Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
    P.mul_mem_right _ (P.mul_mem_left _ (hφ i j).1), ?_⟩
  rw [map_sum]
  simp_rw [map_sum]
  have key : ∀ i j, P.σ d (L P M f i (M.rt i) *
      φ0 (V := M.diag) hf hσf (M.E (M.rt i) i * a * M.E j (M.rt j)) * L P M f (M.rt j) j) =
      M.E i i * a * M.E j j := by
    intro i j
    rw [P.σ_mul_right d _ _ (P.mul_mem_left _ (hφ i j).1), P.σ_mul_left d _ _ (hφ i j).1,
      (hφ i j).2, ← σ0_apply P M.diag, ← σ0_apply P M.diag, σ_L M hf hσf, σ_L M hf hσf]
    calc M.E i (M.rt i) * (M.E (M.rt i) i * a * M.E j (M.rt j)) * M.E (M.rt j) j
        = (M.E i (M.rt i) * M.E (M.rt i) i) * a * (M.E j (M.rt j) * M.E (M.rt j) j) := by
          simp only [mul_assoc]
      _ = _ := by rw [M.E_rt_mul, M.E_rt_mul]
  simp_rw [key]
  simp_rw [← Finset.mul_sum, M.sum_E, mul_one, ← Finset.sum_mul, M.sum_E, one_mul]

/-- **`Φ` is left `S`-linear.** -/
theorem Φ_left {l m : Fin M.n} (hlm : M.rt l = M.rt m) (a : Λ) :
    Φ P M f hf hσf (M.E l m * a) = L P M f l m * Φ P M f hf hσf a := by
  have hL : Φ P M f hf hσf (M.E l m * a) = ∑ j, L P M f l (M.rt l) *
      φ0 (V := M.diag) hf hσf (M.E (M.rt l) m * a * M.E j (M.rt j)) * L P M f (M.rt j) j := by
    rw [Φ_apply, Finset.sum_eq_single l]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← mul_assoc (M.E (M.rt l) l), M.E_mul _ _ _ _ (M.rt_rt l) hlm, if_pos rfl]
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [← mul_assoc (M.E (M.rt i) i), M.E_mul _ _ _ _ (M.rt_rt i) hlm, if_neg hi, zero_mul,
        zero_mul, map_zero, mul_zero, zero_mul]
    · intro h; exact absurd (mem_univ l) h
  have hR : L P M f l m * Φ P M f hf hσf a = ∑ j, L P M f l (M.rt m) *
      φ0 (V := M.diag) hf hσf (M.E (M.rt m) m * a * M.E j (M.rt j)) * L P M f (M.rt j) j := by
    rw [Φ_apply, Finset.mul_sum, Finset.sum_eq_single m]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← mul_assoc, ← mul_assoc, L_mul M hf hσf hlm (M.rt_rt m).symm, if_pos rfl]
    · intro i _ hi
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [← mul_assoc, ← mul_assoc, L_mul M hf hσf hlm (M.rt_rt i).symm, if_neg (Ne.symm hi),
        zero_mul, zero_mul]
    · intro h; exact absurd (mem_univ m) h
  rw [hL, hR, hlm]

/-- **`Φ` is right `S`-linear.** -/
theorem Φ_right {l m : Fin M.n} (hlm : M.rt l = M.rt m) (a : Λ) :
    Φ P M f hf hσf (a * M.E l m) = Φ P M f hf hσf a * L P M f l m := by
  rw [Φ_apply, Φ_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_eq_single m, Finset.sum_eq_single l]
  · have e1 : M.E (M.rt i) i * (a * M.E l m) * M.E m (M.rt m) =
        M.E (M.rt i) i * a * M.E l (M.rt l) := by
      rw [mul_assoc, mul_assoc, M.E_mul _ _ _ _ hlm (M.rt_rt m).symm, if_pos rfl, hlm,
        ← mul_assoc]
    rw [e1, mul_assoc _ (L P M f (M.rt l) l), L_mul M hf hσf (M.rt_rt l) hlm, if_pos rfl, hlm]
  · intro j _ hj
    rw [mul_assoc _ (L P M f (M.rt j) j), L_mul M hf hσf (M.rt_rt j) hlm, if_neg hj, mul_zero]
  · intro h; exact absurd (mem_univ l) h
  · intro j _ hj
    rw [mul_assoc (M.E (M.rt i) i), mul_assoc a, M.E_mul _ _ _ _ hlm (M.rt_rt j).symm,
      if_neg (Ne.symm hj), mul_zero, mul_zero, map_zero, mul_zero, zero_mul]
  · intro h; exact absurd (mem_univ m) h

/-- **`Φ` is unital.** -/
theorem Φ_one : Φ P M f hf hσf 1 = 1 := by
  rw [Φ_apply, ← hf.complete]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i]
  · rw [mul_one, M.E_mul _ _ _ _ (M.rt_rt i) (M.rt_rt i).symm, if_pos rfl,
      show M.E (M.rt i) (M.rt i) = M.diag.e (M.rt i) from rfl, φ0_e, ← L_diag M hf hσf,
      L_mul M hf hσf (M.rt_rt i).symm rfl, if_pos rfl, L_mul M hf hσf (M.rt_rt i).symm (M.rt_rt i),
      if_pos rfl, L_diag M hf hσf]
  · intro j _ hj
    rw [mul_one, M.E_mul _ _ _ _ (M.rt_rt i) (M.rt_rt j).symm, if_neg (Ne.symm hj), map_zero,
      mul_zero, zero_mul]
  · intro h; exact absurd (mem_univ i) h

theorem Φ_E (l m : Fin M.n) : Φ P M f hf hσf (M.E l m) = L P M f l m := by
  by_cases h : M.rt l = M.rt m
  · have := Φ_left M hf hσf h 1
    rwa [mul_one, Φ_one, mul_one] at this
  · rw [M.E_off _ _ h, map_zero, L, if_neg h]

theorem Φ_mul_left {s : Λ} (hs : G.IsHom 0 s) (a : Λ) :
    Φ P M f hf hσf (s * a) = Φ P M f hf hσf s * Φ P M f hf hσf a := by
  obtain ⟨c, rfl⟩ := M.span0 s hs
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
  congr 1
  by_cases h : M.rt l = M.rt m
  · rw [Φ_left M hf hσf h, Φ_E]
  · rw [M.E_off _ _ h, zero_mul, map_zero, zero_mul]

theorem Φ_mul_right {s : Λ} (hs : G.IsHom 0 s) (a : Λ) :
    Φ P M f hf hσf (a * s) = Φ P M f hf hσf a * Φ P M f hf hσf s := by
  obtain ⟨c, rfl⟩ := M.span0 s hs
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
  congr 1
  by_cases h : M.rt l = M.rt m
  · rw [Φ_right M hf hσf h, Φ_E]
  · rw [M.E_off _ _ h, mul_zero, map_zero, mul_zero]

end Lift

variable (P) in
/-- **Lemma 6.4** (`lem:split-positive-deformation`) for a split semisimple `S = Λ₀` (given by
matrix units `MatUnits`): there is a splitting `φ : Λ ≅ B` (a filtered linear isomorphism,
`φ 1 = 1`, inducing the identification `gr B = Λ`) which is multiplicative on `S` (so `S` lifts
to the unital subalgebra `φ(S)`) and `S`-bilinear on both sides; the transported multiplication
is `μ₀ + Σ_{q>0} μ_q` with `μ₀` the multiplication of `Λ`, each `μ_q` raising the degree by
`q`, `S`-relative and vanishing when an input belongs to `S`. -/
theorem splitPositiveDeformation_ss (M : MatUnits G) :
    ∃ S : Split P, (∀ s a, G.IsHom 0 s → S.φ (s * a) = S.φ s * S.φ a) ∧
      (∀ s a, G.IsHom 0 s → S.φ (a * s) = S.φ a * S.φ s) ∧
      (∀ d a, G.IsHom d a → P.σ d (S.φ a) = a) ∧
      (∀ d, Submodule.map S.φ.toLinearMap (G.geSub d) = P.F d) ∧
      (∀ a b, S.φ a * S.φ b = S.φ (∑ q ∈ range G.N, S.μ q a b)) ∧
      (∀ a b, S.μ 0 a b = a * b) ∧
      (∀ q d e a b, G.IsHom d a → G.IsHom e b → G.IsHom (d + e + q) (S.μ q a b)) ∧
      ∀ q, 0 < q → IsRelS G (S.μ q) := by
  obtain ⟨f, hf, hσf⟩ := P.exists_lift M.diag
  let S := splitOfLead (Φ P M f hf hσf) (Φ_lead M hf hσf) (Φ_one M hf hσf)
  have hsl : ∀ s a, G.IsHom 0 s → S.φ (s * a) = S.φ s * S.φ a := fun s a hs ↦
    Φ_mul_left M hf hσf hs a
  have hsr : ∀ s a, G.IsHom 0 s → S.φ (a * s) = S.φ a * S.φ s := fun s a hs ↦
    Φ_mul_right M hf hσf hs a
  refine ⟨S, hsl, hsr, S.σφ, S.F_eq, fun a b ↦ ?_, S.μ_zero_apply,
    fun q d e a b ha hb ↦ S.μ_isHom ha hb, fun q hq ↦ S.μ_isRelS hsl hsr hq⟩
  rw [← S.star_eq_sum, S.φ_star]

variable (P) in
/-- **A splitting exists for a split semisimple `Λ₀`**, so Proposition 6.5 (`exists_fLift_of_split`,
`fLift_unique_of_split`, `fLift_map_of_split`, `fLift_leading_of_split`, `fLift_gr_hom_of_split`,
`fLift_orderGe_zero_of_split`, `isRad_iff`, `mem_radPow_iff`) applies; the splitting is
multiplicative on the left by every `e ∈ Λ₀`, so `Split.regularLift` gives the regular lifts
`eB` of `eΛ` for every idempotent `e` of `Λ₀`. -/
theorem nonempty_split_ss (M : MatUnits G) : Nonempty (Split P) :=
  ⟨(splitPositiveDeformation_ss P M).choose⟩

end PosFiltration

end MultiplicativeBasisDeformations
