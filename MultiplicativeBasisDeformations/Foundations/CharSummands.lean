import MultiplicativeBasisDeformations.Foundations.CharDecomp

/-!
# Independence of character summands of `HH²` (Proposition 7.6)

`weights-and-parameters.tex:405–410`: "Proposition 6.1 and the distinct characters `χ_i` now give
the asserted decomposition and the one-dimensionality of every nonzero summand." For cocycles
`μ_i` of pairwise distinct characters `χ_i`, the character-`χ_i` part of `Σ_j c_j μ_j` is
`c_i μ_i` (`cpr2_sum_char`), and the coboundary commutes with character parts
(`cobdry_cpr1`). Hence, in each internal degree, a combination of classes which are not
coboundaries is a coboundary only when all coefficients vanish (`coef_eq_zero_of_cobdry`), and
a cocycle of character `χ_i` is a multiple of `μ_i` modulo coboundaries once it lies in the
span (`eq_smul_add_cobdry`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace LatGrading

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {L : Type} [AddCommGroup L]
  [DecidableEq L] (W : LatGrading k Λ L)

/-- **The character-`χ_i` part of a combination of cochains of distinct characters.** -/
theorem cpr2_sum_char {ι : Type*} [DecidableEq ι] (s : Finset ι) (cf : ι → k)
    (μ : ι → Λ →ₗ[k] Λ →ₗ[k] Λ) {χ : ι → L} (hχ : Function.Injective χ)
    (hμ : ∀ j, W.Char₂ (χ j) (μ j)) (i : ι) :
    W.cpr2 (χ i) (∑ j ∈ s, cf j • μ j) = if i ∈ s then cf i • μ i else 0 := by
  refine W.ext2_of_hom fun α β a b ha hb ↦ ?_
  rw [W.cpr2_hom _ _ ha hb, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_sum,
    Finset.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, map_smul]
  have h1 : ∀ j, W.proj (α + β + χ i) (μ j a b) = if j = i then μ j a b else 0 := by
    intro j
    rw [W.proj_of_isHom (hμ j α β a b ha hb)]
    by_cases hj : j = i
    · rw [if_pos (by rw [hj]), if_pos hj]
    · rw [if_neg (fun h ↦ hj (hχ (add_left_cancel h))), if_neg hj]
  simp_rw [h1, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs <;> rfl

omit [DecidableEq L] in
theorem cobdry_smul (t : k) (f : Λ →ₗ[k] Λ) : cobdry k (t • f) = t • cobdry k f := by
  ext a b
  simp only [cobdry_apply, LinearMap.smul_apply, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_add]

omit [DecidableEq L] in
theorem hasDeg₁_smul {G : LenGrading k Λ} {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : HasDeg₁ G q f) (t : k) :
    HasDeg₁ G q (t • f) := fun d a ha ↦ by
  unfold LenGrading.IsHom
  rw [LinearMap.smul_apply, map_smul, hf d a ha]

variable {G : LenGrading k Λ}
  (compat : ∀ d l x, G.proj d (W.proj l x) = W.proj l (G.proj d x))

include compat in
/-- **Independence**: in internal degree `q`, a combination of cocycles of distinct characters
which are not coboundaries is a coboundary only with zero coefficients. -/
theorem coef_eq_zero_of_cobdry {n : ℕ} (μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ) (qd : Fin n → ℕ)
    {χ : Fin n → L} (hχ : Function.Injective χ) (hμ : ∀ j, W.Char₂ (χ j) (μ j))
    (hμnz : ∀ i, ¬ ∃ H, HasDeg₁ G (qd i) H ∧ μ i = cobdry k H) (q : ℕ) (cf : Fin n → k)
    (f : Λ →ₗ[k] Λ) (hf : HasDeg₁ G q f)
    (h : ∑ j ∈ Finset.univ.filter (fun j ↦ qd j = q), cf j • μ j = cobdry k f)
    (i : Fin n) (hi : qd i = q) : cf i = 0 := by
  by_contra hc
  have e := congrArg (W.cpr2 (χ i)) h
  rw [cpr2_sum_char W _ cf μ hχ hμ i, if_pos (show i ∈ Finset.univ.filter (fun j ↦ qd j = q) from
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩), ← W.cobdry_cpr1] at e
  refine hμnz i ⟨(cf i)⁻¹ • W.cpr1 (χ i) f, hasDeg₁_smul (hi ▸ W.hasDeg₁_cpr1 compat hf _) _, ?_⟩
  rw [cobdry_smul, ← e, smul_smul, inv_mul_cancel₀ hc, one_smul]

include compat in
/-- **One-dimensionality**: a cocycle of character `χ_i` in the span of the `μ_j` modulo
coboundaries is a multiple of `μ_i` modulo coboundaries. -/
theorem eq_smul_add_cobdry {n : ℕ} (μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ) (qd : Fin n → ℕ)
    {χ : Fin n → L} (hχ : Function.Injective χ) (hμ : ∀ j, W.Char₂ (χ j) (μ j)) (i : Fin n)
    {q : ℕ} {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : W.Char₂ (χ i) φ) (cf : Fin n → k)
    (f : Λ →ₗ[k] Λ) (hf : HasDeg₁ G q f)
    (h : φ = ∑ j ∈ Finset.univ.filter (fun j ↦ qd j = q), cf j • μ j + cobdry k f) :
    ∃ (t : k) (f' : Λ →ₗ[k] Λ), HasDeg₁ G q f' ∧ φ = t • μ i + cobdry k f' := by
  classical
  have e := congrArg (W.cpr2 (χ i)) h
  rw [W.cpr2_of_char₂ hφ] at e
  have hadd : W.cpr2 (χ i) (∑ j ∈ Finset.univ.filter (fun j ↦ qd j = q), cf j • μ j +
      cobdry k f) = W.cpr2 (χ i) (∑ j ∈ Finset.univ.filter (fun j ↦ qd j = q), cf j • μ j) +
      W.cpr2 (χ i) (cobdry k f) :=
    W.ext2_of_hom fun α β a b ha hb ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, W.cpr2_hom _ _ ha hb, W.cpr2_hom _ _ ha hb,
        W.cpr2_hom _ _ ha hb, LinearMap.add_apply, LinearMap.add_apply, map_add]
  rw [hadd, cpr2_sum_char W _ cf μ hχ hμ i, ← W.cobdry_cpr1] at e
  refine ⟨if i ∈ Finset.univ.filter (fun j ↦ qd j = q) then cf i else 0, W.cpr1 (χ i) f,
    W.hasDeg₁_cpr1 compat hf _, ?_⟩
  rw [e]
  split_ifs <;> simp

end LatGrading

end MultiplicativeBasisDeformations
