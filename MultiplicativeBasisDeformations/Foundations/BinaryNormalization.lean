module

public import MultiplicativeBasisDeformations.Foundations.FamilyNormalization

/-!
# Binary normalization

Corollary 7.8 (`cor:binary-normalization`, `characteristic-two-construction.tex`):
if `Λ` also has a compatible grading by a lattice `L`, with `S` in degree zero,
`μ_i` raising `L`-degree by `χ_i`, and the `χ_i` part of an integer basis of
`L`, then every positive filtered deformation is isomorphic to a fibre with all
parameters zero or one, and two parameter vectors with the same zero coordinates
give isomorphic fibres. "For `a : L → k^*`, multiply a vector of weight `ℓ` by
`a(ℓ)`. This is an automorphism of `(Λ, m)`, and transporting `m_λ` along it
changes its coefficients to `λ'_i = λ_i a(χ_i)`."

The lattice grading is `LatGrading` (finitely supported projections, as for the
length grading); characters are additive maps `L → Additive kˣ`, extended from
the prescribed values on the `χ_i` through the basis (`exists_character`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

variable (k : Type u) [Field k] (Λ : Type v) [Ring Λ] [Algebra k Λ] (L : Type) [AddCommGroup L]
  [DecidableEq L]

/-- A grading by an abelian group `L`, with finitely many nonzero components. -/
structure LatGrading where
  proj : L → Λ →ₗ[k] Λ
  supp : Finset L
  proj_proj : ∀ l l' x, proj l (proj l' x) = if l' = l then proj l' x else 0
  proj_out : ∀ l, l ∉ supp → proj l = 0
  sum : ∀ x, x = ∑ l ∈ supp, proj l x
  mul_hom : ∀ l l' x y, proj (l + l') (proj l x * proj l' y) = proj l x * proj l' y

variable {k Λ L} (W : LatGrading k Λ L)

namespace LatGrading

/-- A homogeneous element of weight `l`. -/
def IsHom (l : L) (x : Λ) : Prop := W.proj l x = x

theorem isHom_proj (l : L) (x : Λ) : W.IsHom l (W.proj l x) := by
  unfold IsHom; rw [W.proj_proj, if_pos rfl]

theorem isHom_mul {l l' : L} {x y : Λ} (hx : W.IsHom l x) (hy : W.IsHom l' y) :
    W.IsHom (l + l') (x * y) := by
  unfold IsHom; rw [← hx, ← hy]; exact W.mul_hom l l' x y

theorem proj_of_isHom {l l' : L} {x : Λ} (hx : W.IsHom l x) :
    W.proj l' x = if l = l' then x else 0 := by
  rw [← hx, W.proj_proj, hx]

/-- Rescaling by a character `a`: multiply the weight-`l` part by `a(l)`. -/
def rescale (a : L → kˣ) : Λ →ₗ[k] Λ := ∑ l ∈ W.supp, ((a l : kˣ) : k) • W.proj l

theorem rescale_hom (a : L → kˣ) {l : L} {x : Λ} (hx : W.IsHom l x) :
    W.rescale a x = ((a l : kˣ) : k) • x := by
  classical
  simp only [rescale, LinearMap.sum_apply, LinearMap.smul_apply, W.proj_of_isHom hx, smul_ite,
    smul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have : x = 0 := by rw [← hx, W.proj_out l h, LinearMap.zero_apply]
    rw [this, smul_zero]

theorem rescale_apply (a : L → kˣ) (x : Λ) :
    W.rescale a x = ∑ l ∈ W.supp, ((a l : kˣ) : k) • W.proj l x := by
  simp [rescale, LinearMap.sum_apply]

variable {W}

theorem rescale_mul {a : L → kˣ} (ha : ∀ l l', a (l + l') = a l * a l') (x y : Λ) :
    W.rescale a (x * y) = W.rescale a x * W.rescale a y := by
  conv_lhs => rw [W.sum x, W.sum y, Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum]
  rw [W.rescale_apply a x, W.rescale_apply a y, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun l' _ ↦ ?_
  rw [W.rescale_hom a (W.isHom_mul (W.isHom_proj l x) (W.isHom_proj l' y)), ha,
    smul_mul_smul_comm, Units.val_mul]

theorem rescale_of_raises {a : L → kˣ} (ha : ∀ l l', a (l + l') = a l * a l') {χ : L}
    {μ : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (hμ : ∀ l l' x y, W.IsHom l x → W.IsHom l' y → W.IsHom (l + l' + χ) (μ x y)) (x y : Λ) :
    W.rescale a (μ x y) = ((a χ : kˣ) : k) • μ (W.rescale a x) (W.rescale a y) := by
  conv_lhs => rw [W.sum x, W.sum y]
  simp only [map_sum, LinearMap.sum_apply]
  rw [W.rescale_apply a x, W.rescale_apply a y]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun l' _ ↦ ?_
  rw [W.rescale_hom a (hμ _ _ _ _ (W.isHom_proj _ x) (W.isHom_proj _ y)), ha, ha]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, Units.val_mul]
  congr 1
  ring

theorem rescale_comp {a b : L → kˣ} (x : Λ) :
    W.rescale a (W.rescale b x) = W.rescale (fun l ↦ a l * b l) x := by
  conv_lhs => rw [W.rescale_apply b x]
  rw [map_sum, W.rescale_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_smul, W.rescale_hom a (W.isHom_proj l x), smul_smul, Units.val_mul, mul_comm]

theorem rescale_one (x : Λ) : W.rescale (fun _ ↦ 1) x = x := by
  rw [W.rescale_apply]
  simp only [Units.val_one, one_smul]
  exact (W.sum x).symm

/-- The rescaling as a linear automorphism. -/
def rescaleEquiv (a : L → kˣ) : Λ ≃ₗ[k] Λ :=
  LinearEquiv.ofLinearMap (W.rescale a) (W.rescale fun l ↦ (a l)⁻¹)
    (by ext x; simp [rescale_comp, rescale_one])
    (by ext x; simp [rescale_comp, rescale_one])

theorem rescaleEquiv_apply (a : L → kˣ) (x : Λ) : W.rescaleEquiv a x = W.rescale a x := rfl

theorem rescaleEquiv_symm_apply (a : L → kˣ) (x : Λ) :
    (W.rescaleEquiv a).symm x = W.rescale (fun l ↦ (a l)⁻¹) x := rfl

end LatGrading

/-- **Characters from part of a basis**: prescribed values on part of an
integer basis extend to a character `L → k^*`. -/
theorem exists_character {ι : Type} (b : Module.Basis ι ℤ L) {n : ℕ} (j : Fin n → ι)
    (hj : Function.Injective j) (w : Fin n → kˣ) :
    ∃ a : L → kˣ, (∀ l l', a (l + l') = a l * a l') ∧ a 0 = 1 ∧ ∀ i, a (b (j i)) = w i := by
  classical
  let v : ι → Additive kˣ := fun t ↦
    if h : ∃ i, j i = t then Additive.ofMul (w (Classical.choose h)) else 0
  let ψ : L →ₗ[ℤ] Additive kˣ := b.constr ℤ v
  refine ⟨fun l ↦ Additive.toMul (ψ l), fun l l' ↦ by simp [map_add], by simp, fun i ↦ ?_⟩
  simp only [ψ, Module.Basis.constr_basis, v]
  have h : ∃ i', j i' = j i := ⟨i, rfl⟩
  rw [dif_pos h, hj (Classical.choose_spec h)]
  rfl

namespace LenGrading

variable {G : LenGrading k Λ} {V : Vertices G} {W}
  (compat : ∀ d l x, G.proj d (W.proj l x) = W.proj l (G.proj d x))

include compat in
theorem proj_rescale (a : L → kˣ) (d : ℕ) (x : Λ) :
    G.proj d (W.rescale a x) = W.rescale a (G.proj d x) := by
  rw [W.rescale_apply, W.rescale_apply, map_sum]
  simp only [map_smul, compat]

include compat in
theorem ge_rescale (a : L → kˣ) {d : ℕ} {x : Λ} (hx : G.Ge d x) : G.Ge d (W.rescale a x) :=
  fun e he ↦ by rw [proj_rescale compat, hx e he, map_zero]

variable {n : ℕ} {μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ} {χ : Fin n → L}
  (hχ : ∀ i l l' x y, W.IsHom l x → W.IsHom l' y → W.IsHom (l + l' + χ i) (μ i x y))

include hχ in
theorem rescale_mLam {a : L → kˣ} (ha : ∀ l l', a (l + l') = a l * a l') (lam : Fin n → k)
    (x y : Λ) :
    W.rescale a (mLam μ lam x y) =
      mLam μ (fun i ↦ lam i * ((a (χ i) : kˣ) : k)) (W.rescale a x) (W.rescale a y) := by
  rw [mLam_apply, mLam_apply, map_add, LatGrading.rescale_mul ha, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, LatGrading.rescale_of_raises ha (hχ i), smul_smul, mul_comm]

include compat hχ in
/-- **Corollary 7.8** (binary normalization). -/
theorem binaryNormalization {qd : Fin n → ℕ} (H : FamilyHyp V μ qd)
    (he0 : ∀ i, W.IsHom 0 (V.e i))
    (hbasis : ∃ (ι : Type) (b : Module.Basis ι ℤ L) (j : Fin n → ι),
      Function.Injective j ∧ ∀ i, b (j i) = χ i)
    {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B) :
    (∃ lam : Fin n → k, (∀ i, lam i = 0 ∨ lam i = 1) ∧ ∃ Ψ : Λ ≃ₗ[k] B,
      (∀ a b, Ψ (mLam μ lam a b) = Ψ a * Ψ b) ∧ CompleteOrthogonalIdempotents (fun i ↦ Ψ (V.e i)) ∧
      (∀ d, Submodule.map Ψ.toLinearMap (G.geSub d) = P.F d) ∧
      ∃ c : L → kˣ, ∀ d l x, G.IsHom d x → W.IsHom l x → P.σ d (Ψ x) = ((c l : kˣ) : k) • x) ∧
    ∀ lam lam' : Fin n → k, (∀ i, lam i = 0 ↔ lam' i = 0) →
      ∃ R : Λ ≃ₗ[k] Λ, ∀ a b, R (mLam μ lam a b) = mLam μ lam' (R a) (R b) := by
  classical
  obtain ⟨ι, bL, j, hj, hbj⟩ := hbasis
  -- a character with prescribed values on the `χ_i`
  have hchar : ∀ w : Fin n → kˣ, ∃ a : L → kˣ, (∀ l l', a (l + l') = a l * a l') ∧ a 0 = 1 ∧
      ∀ i, a (χ i) = w i := fun w ↦ by
    obtain ⟨a, ha, ha0, haw⟩ := exists_character bL j hj w
    exact ⟨a, ha, ha0, fun i ↦ by rw [← hbj]; exact haw i⟩
  refine ⟨?_, fun lam lam' hzero ↦ ?_⟩
  · obtain ⟨lam, Ψ, hΨ, hΨe, hσ, hF⟩ := finiteFamilyNormalization H P
    obtain ⟨a, ha, ha0, haw⟩ := hchar fun i ↦
      if h : lam i = 0 then 1 else (Units.mk0 (lam i) h)⁻¹
    set R := W.rescaleEquiv a
    have hRe : ∀ i, R.symm (V.e i) = V.e i := fun i ↦ by
      rw [LatGrading.rescaleEquiv_symm_apply, W.rescale_hom _ (he0 i), ha0, inv_one,
        Units.val_one, one_smul]
    refine ⟨fun i ↦ lam i * ((a (χ i) : kˣ) : k), fun i ↦ ?_, R.symm.trans Ψ, fun x y ↦ ?_, ?_,
      fun d ↦ ?_, fun l ↦ (a l)⁻¹, fun d l x hd hl ↦ ?_⟩
    · show lam i * ((a (χ i) : kˣ) : k) = 0 ∨ lam i * ((a (χ i) : kˣ) : k) = 1
      rw [haw]
      by_cases h : lam i = 0
      · left; simp [h]
      · right; simp [h]
    · have h1 := rescale_mLam hχ ha lam (R.symm x) (R.symm y)
      rw [← LatGrading.rescaleEquiv_apply, ← LatGrading.rescaleEquiv_apply,
        ← LatGrading.rescaleEquiv_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at h1
      rw [LinearEquiv.trans_apply, ← h1, LinearEquiv.symm_apply_apply, hΨ]
      rfl
    · simpa [hRe] using hΨe
    · rw [← hF d]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨R.symm y, ge_rescale compat _ hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨R y, ge_rescale compat _ hy, by simp⟩
    · rw [LinearEquiv.trans_apply, LatGrading.rescaleEquiv_symm_apply, W.rescale_hom _ hl,
        map_smul, map_smul, hσ d x hd]
  · obtain ⟨a, ha, -, haw⟩ := hchar fun i ↦
      if h : lam i = 0 then 1 else Units.mk0 (lam' i / lam i)
        (div_ne_zero (fun h' ↦ h ((hzero i).2 h')) h)
    refine ⟨W.rescaleEquiv a, fun x y ↦ ?_⟩
    rw [LatGrading.rescaleEquiv_apply, rescale_mLam hχ ha]
    have hl : (fun i ↦ lam i * ((a (χ i) : kˣ) : k)) = lam' := by
      funext i
      rw [haw]
      by_cases h : lam i = 0
      · simp [h, (hzero i).1 h]
      · simp [h, mul_div_cancel₀ _ h]
    rw [hl]
    rfl

end LenGrading

end MultiplicativeBasisDeformations
