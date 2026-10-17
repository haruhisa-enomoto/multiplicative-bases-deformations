import MultiplicativeBasisDeformations.Foundations.HochschildCochains

/-!
# Finite normalization of an associative family

Theorem 7.7 (`thm:finite-family-normalization`,
`characteristic-two-construction.tex:9–58`). Let `Λ` be graded with `Λ₀ = S`
spanned by vertex idempotents, `μ_i` normalized `S`-relative two-cocycles of
positive degrees whose classes span `HH²(Λ)_{>0}`, and `m_t = m + Σ t_i μ_i`
associative. Then every positive filtered deformation of `Λ` is isomorphic to a
fibre `m_λ`, by a filtered map with identity leading terms fixing the lifted
vertex idempotents.

"By Lemma 6.4, after lifting the vertex idempotents and splitting the
filtration, the deformation has multiplication `⋆` on the vector space `Λ` […]
Suppose it agrees with `m_λ` in degrees less than `q` […] Let `φ_q` be the
degree-`q` part of `⋆ - m_λ`. […] The remaining equation is `dφ_q = 0`. The
spanning assumption therefore gives scalars `c_i` and a normalized one-cochain
`f_q` of degree `q` such that `φ_q = Σ_{q_i = q} c_iμ_i + df_q`. Assign
`λ_i = c_i` for `q_i = q` […] Pull `⋆` back by `1 - f_q`."

Here the stage invariant is `Stage` (the error `⋆_g - m_λ` raises degree by
`q`); `degPart_cocycle` is `dφ_q = 0`, `stage_succ` the change of variables.
The associativity of `m_t` over `k[t]` is used only through its specializations
(`FamilyHyp.assoc`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  (V : Vertices G)

theorem proj_e_mul (i : Fin V.n) (a : Λ) (d : ℕ) : G.proj d (V.e i * a) = V.e i * G.proj d a := by
  conv_lhs => rw [G.sum a, Finset.mul_sum, map_sum]
  have h : ∀ d', G.proj d (V.e i * G.proj d' a) = if d' = d then V.e i * G.proj d' a else 0 :=
    fun d' ↦ G.proj_of_isHom (by simpa using G.isHom_mul (V.deg0 i) (G.isHom_proj d' a))
  simp_rw [h]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [G.proj_ge d (by simpa using hd), LinearMap.zero_apply, mul_zero]

theorem proj_mul_e (i : Fin V.n) (a : Λ) (d : ℕ) : G.proj d (a * V.e i) = G.proj d a * V.e i := by
  conv_lhs => rw [G.sum a, Finset.sum_mul, map_sum]
  have h : ∀ d', G.proj d (G.proj d' a * V.e i) = if d' = d then G.proj d' a * V.e i else 0 :=
    fun d' ↦ G.proj_of_isHom (by simpa using G.isHom_mul (G.isHom_proj d' a) (V.deg0 i))
  simp_rw [h]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [G.proj_ge d (by simpa using hd), LinearMap.zero_apply, zero_mul]

theorem proj_e (i : Fin V.n) (d : ℕ) : G.proj d (V.e i) = if d = 0 then V.e i else 0 := by
  rw [G.proj_of_isHom (V.deg0 i)]
  by_cases h : d = 0 <;> simp [h, eq_comm]

variable {V} in
theorem IsRel₂.degPart_rel {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsRel₂ V μ) (q : ℕ) :
    IsRel₂ V (degPart (G := G) q μ) := by
  refine ⟨fun i a b ↦ ?_, fun i a b ↦ ?_, fun i a b ↦ ?_, fun i b ↦ ?_, fun i a ↦ ?_⟩
  · simp only [degPart, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      Finset.mul_sum, proj_e_mul, hμ.left]
  · simp only [degPart, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      proj_e_mul, proj_mul_e, hμ.mid]
  · simp only [degPart, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      Finset.sum_mul, proj_mul_e, hμ.right]
  · simp only [degPart, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      proj_e]
    refine Finset.sum_eq_zero fun d _ ↦ Finset.sum_eq_zero fun e _ ↦ ?_
    split_ifs <;> simp [hμ.unitL]
  · simp only [degPart, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      proj_e]
    refine Finset.sum_eq_zero fun d _ ↦ Finset.sum_eq_zero fun e _ ↦ ?_
    split_ifs <;> simp [hμ.unitR]

/-- The cocycle expression is additive in each argument, so it suffices to
check it on homogeneous elements. -/
theorem isCocycle₂_of_hom {μ : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (h : ∀ d e l a b c, G.IsHom d a → G.IsHom e b → G.IsHom l c →
      a * μ b c - μ (a * b) c + μ a (b * c) - μ a b * c = 0) : IsCocycle₂ μ := by
  intro a b c
  set P : Λ → Λ → Λ → Λ := fun a b c ↦ a * μ b c - μ (a * b) c + μ a (b * c) - μ a b * c
  change P a b c = 0
  have hA : ∀ b c a, P a b c = ∑ d ∈ Finset.range G.N, P (G.proj d a) b c := by
    intro b c a
    let L : Λ →ₗ[k] Λ :=
      { toFun := fun a ↦ P a b c
        map_add' := fun x y ↦ by simp only [P, add_mul, map_add, LinearMap.add_apply]; abel
        map_smul' := fun r x ↦ by
          simp only [P, smul_mul_assoc, map_smul, LinearMap.smul_apply, smul_sub, smul_add,
            RingHom.id_apply] }
    conv_lhs => rw [G.sum a]
    exact map_sum L _ _
  have hB : ∀ a c b, P a b c = ∑ e ∈ Finset.range G.N, P a (G.proj e b) c := by
    intro a c b
    let L : Λ →ₗ[k] Λ :=
      { toFun := fun b ↦ P a b c
        map_add' := fun x y ↦ by
          simp only [P, add_mul, mul_add, map_add, LinearMap.add_apply]; abel
        map_smul' := fun r x ↦ by
          simp only [P, smul_mul_assoc, mul_smul_comm, map_smul, LinearMap.smul_apply, smul_sub,
            smul_add, RingHom.id_apply] }
    conv_lhs => rw [G.sum b]
    exact map_sum L _ _
  have hC : ∀ a b c, P a b c = ∑ l ∈ Finset.range G.N, P a b (G.proj l c) := by
    intro a b c
    let L : Λ →ₗ[k] Λ :=
      { toFun := fun c ↦ P a b c
        map_add' := fun x y ↦ by simp only [P, mul_add, map_add]; abel
        map_smul' := fun r x ↦ by
          simp only [P, mul_smul_comm, map_smul, smul_sub, smul_add, RingHom.id_apply] }
    conv_lhs => rw [G.sum c]
    exact map_sum L _ _
  rw [hA]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rw [hB]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [hC]
  exact Finset.sum_eq_zero fun l _ ↦
    h d e l _ _ _ (G.isHom_proj d a) (G.isHom_proj e b) (G.isHom_proj l c)

theorem proj_eq_zero_of_ge {m t : ℕ} {x : Λ} (hx : G.Ge m x) (ht : t < m) : G.proj t x = 0 :=
  hx t ht

variable {n : ℕ}

/-- `m_λ = m + Σ λ_i μ_i`. -/
def mLam (μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ) (lam : Fin n → k) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  LinearMap.mul k Λ + ∑ i, lam i • μ i

theorem mLam_apply (μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ) (lam : Fin n → k) (a b : Λ) :
    mLam μ lam a b = a * b + ∑ i, lam i • μ i a b := by
  simp [mLam, LinearMap.sum_apply]

/-- The hypotheses of Theorem 7.8. -/
structure FamilyHyp (μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ) (qd : Fin n → ℕ) : Prop where
  pos : ∀ i, 0 < qd i
  rel : ∀ i, IsRel₂ V (μ i)
  deg : ∀ i, HasDeg₂ G (qd i) (μ i)
  assoc : ∀ (lam : Fin n → k) (a b c : Λ),
    mLam μ lam (mLam μ lam a b) c = mLam μ lam a (mLam μ lam b c)
  span : ∀ q, 0 < q → ∀ φ, IsRel₂ V φ → HasDeg₂ G q φ → IsCocycle₂ φ →
    ∃ (c : Fin n → k) (f : Λ →ₗ[k] Λ), IsRel₁ V f ∧ HasDeg₁ G q f ∧
      φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i) + cobdry k f

/-- Conjugation of a product by a linear automorphism: `g⁻¹(T(ga, gb))`. -/
def conj (g : Λ ≃ₗ[k] Λ) (T : Λ →ₗ[k] Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  (T.compl₁₂ g.toLinearMap g.toLinearMap).compr₂ g.symm.toLinearMap

theorem conj_apply (g : Λ ≃ₗ[k] Λ) (T : Λ →ₗ[k] Λ →ₗ[k] Λ) (a b : Λ) :
    conj g T a b = g.symm (T (g a) (g b)) := rfl

/-- The transported product `a ⋆ b = φ⁻¹(φa φb)`. -/
def star {B : Type w} [Ring B] [Algebra k B] (φ : Λ ≃ₗ[k] B) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  LinearMap.mk₂ k (fun a b ↦ φ.symm (φ a * φ b))
    (fun a a' b ↦ by simp [add_mul]) (fun c a b ↦ by simp [smul_mul_assoc])
    (fun a b b' ↦ by simp [mul_add]) (fun c a b ↦ by simp [mul_smul_comm])

theorem star_apply {B : Type w} [Ring B] [Algebra k B] (φ : Λ ≃ₗ[k] B) (a b : Λ) :
    star φ a b = φ.symm (φ a * φ b) := rfl

section Normalization

variable {V} {μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ} {qd : Fin n → ℕ} (H : FamilyHyp V μ qd)
  {B : Type w} [Ring B] [Algebra k B] {P : PosFiltration G B} {φ : Λ ≃ₗ[k] B}
  (hφl : ∀ i a, φ (V.e i * a) = φ (V.e i) * φ a) (hφr : ∀ i a, φ (a * V.e i) = φ a * φ (V.e i))
  (hσφ : ∀ d a, G.IsHom d a → P.σ d (φ a) = a)
  (hFφ : ∀ d, Submodule.map φ.toLinearMap (G.geSub d) = P.F d)

theorem star_assoc (a b c : Λ) : star φ (star φ a b) c = star φ a (star φ b c) := by
  simp [star_apply, mul_assoc]

include hφl in
theorem star_e_left (i : Fin V.n) (b : Λ) : star φ (V.e i) b = V.e i * b := by
  rw [star_apply, ← hφl, LinearEquiv.symm_apply_apply]

include hφr in
theorem star_e_right (i : Fin V.n) (a : Λ) : star φ a (V.e i) = a * V.e i := by
  rw [star_apply, ← hφr, LinearEquiv.symm_apply_apply]

include hFφ in
theorem mem_F_of_ge {d : ℕ} {a : Λ} (ha : G.Ge d a) : φ a ∈ P.F d := by
  rw [← hFφ]; exact ⟨a, ha, rfl⟩

include hFφ in
theorem ge_of_mem_F {d : ℕ} {x : B} (hx : x ∈ P.F d) : G.Ge d (φ.symm x) := by
  rw [← hFφ] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have : φ.symm (φ.toLinearMap a) = a := φ.symm_apply_apply a
  rw [this]; exact ha

include hσφ hFφ in
/-- The transported product differs from `m` in positive degrees (Lemma 6.4). -/
theorem star_raises : Raises₂ G 1 (star φ - LinearMap.mul k Λ) := by
  intro d e a b ha hb
  have hfa := mem_F_of_ge hFφ (G.ge_of_isHom ha)
  have hfb := mem_F_of_ge hFφ (G.ge_of_isHom hb)
  have hab := G.isHom_mul ha hb
  have hx : φ a * φ b - φ (a * b) ∈ P.F (d + e) :=
    Submodule.sub_mem _ (P.F_mul _ _ _ _ hfa hfb) (mem_F_of_ge hFφ (G.ge_of_isHom hab))
  have hx1 : φ a * φ b - φ (a * b) ∈ P.F (d + e + 1) := by
    refine (P.σ_ker _ _ hx).1 ?_
    rw [map_sub, P.σ_mul _ _ _ _ hfa hfb, hσφ _ _ ha, hσφ _ _ hb, hσφ _ _ hab, sub_self]
  have := ge_of_mem_F hFφ hx1
  rw [map_sub, LinearEquiv.symm_apply_apply] at this
  simpa [star_apply] using this

/-- **The stage invariant**: after the change of variables `g`, the product
agrees with `m_λ` below degree `q`. -/
structure Stage (q : ℕ) (g : Λ ≃ₗ[k] Λ) (lam : Fin n → k) : Prop where
  unit : ∀ i, g (V.e i) = V.e i
  left : ∀ i a, g (V.e i * a) = V.e i * g a
  right : ∀ i a, g (a * V.e i) = g a * V.e i
  lead : Raises₁ G 1 (g.toLinearMap - LinearMap.id)
  leadInv : Raises₁ G 1 (g.symm.toLinearMap - LinearMap.id)
  err : Raises₂ G q (conj g (star φ) - mLam μ lam)
  zero : ∀ i, q ≤ qd i → lam i = 0

include H in
theorem mLam_left (lam : Fin n → k) (i : Fin V.n) (a b : Λ) :
    mLam μ lam (V.e i * a) b = V.e i * mLam μ lam a b := by
  simp only [mLam_apply, (H.rel _).left, mul_add, mul_assoc, Finset.mul_sum, mul_smul_comm]

include H in
theorem mLam_mid (lam : Fin n → k) (i : Fin V.n) (a b : Λ) :
    mLam μ lam (a * V.e i) b = mLam μ lam a (V.e i * b) := by
  simp only [mLam_apply, (H.rel _).mid, mul_assoc]

include H in
theorem mLam_right (lam : Fin n → k) (i : Fin V.n) (a b : Λ) :
    mLam μ lam a (b * V.e i) = mLam μ lam a b * V.e i := by
  simp only [mLam_apply, (H.rel _).right, add_mul, mul_assoc, Finset.sum_mul, smul_mul_assoc]

include H in
theorem mLam_e_left (lam : Fin n → k) (i : Fin V.n) (b : Λ) :
    mLam μ lam (V.e i) b = V.e i * b := by
  simp [mLam_apply, (H.rel _).unitL]

include H in
theorem mLam_e_right (lam : Fin n → k) (i : Fin V.n) (a : Λ) :
    mLam μ lam a (V.e i) = a * V.e i := by
  simp [mLam_apply, (H.rel _).unitR]

include H in
theorem mLam_sub_mul (lam : Fin n → k) : Raises₂ G 1 (mLam μ lam - LinearMap.mul k Λ) := by
  intro d e a b ha hb
  simp only [LinearMap.sub_apply, mLam_apply, LinearMap.mul_apply', add_sub_cancel_left]
  refine ge_sum _ _ fun i _ ↦ G.ge_smul _ ?_
  exact G.ge_mono (by have := H.pos i; omega) (G.ge_of_isHom ((H.deg i) d e a b ha hb))

variable {q : ℕ} {g : Λ ≃ₗ[k] Λ} {lam : Fin n → k}
  (hS : Stage (V := V) (μ := μ) (qd := qd) (φ := φ) q g lam)

include hS hφl in
theorem T_e_left (i : Fin V.n) (b : Λ) : conj g (star φ) (V.e i) b = V.e i * b := by
  rw [conj_apply, hS.unit, star_e_left hφl, ← hS.left, LinearEquiv.symm_apply_apply]

include hS hφr in
theorem T_e_right (i : Fin V.n) (a : Λ) : conj g (star φ) a (V.e i) = a * V.e i := by
  rw [conj_apply, hS.unit, star_e_right hφr, ← hS.right, LinearEquiv.symm_apply_apply]

theorem T_assoc (a b c : Λ) :
    conj g (star φ) (conj g (star φ) a b) c = conj g (star φ) a (conj g (star φ) b c) := by
  simp only [conj_apply, LinearEquiv.apply_symm_apply, star_assoc]

include H hS hφl hφr in
/-- The error `⋆_g - m_λ` is a normalized relative two-cochain. -/
theorem err_rel : IsRel₂ V (conj g (star φ) - mLam μ lam) := by
  set T := conj g (star φ)
  have hTl : ∀ i a b, T (V.e i * a) b = V.e i * T a b := fun i a b ↦ by
    rw [← T_e_left hφl hS i a, T_assoc, T_e_left hφl hS]
  have hTm : ∀ i a b, T (a * V.e i) b = T a (V.e i * b) := fun i a b ↦ by
    rw [← T_e_right hφr hS i a, T_assoc, T_e_left hφl hS]
  have hTr : ∀ i a b, T a (b * V.e i) = T a b * V.e i := fun i a b ↦ by
    rw [← T_e_right hφr hS i b, ← T_assoc, T_e_right hφr hS]
  refine ⟨fun i a b ↦ ?_, fun i a b ↦ ?_, fun i a b ↦ ?_, fun i b ↦ ?_, fun i a ↦ ?_⟩
  · simp only [LinearMap.sub_apply, hTl, mLam_left H, mul_sub]
  · simp only [LinearMap.sub_apply, hTm, mLam_mid H]
  · simp only [LinearMap.sub_apply, hTr, mLam_right H, sub_mul]
  · have h1 : T (V.e i) b = V.e i * b := T_e_left hφl hS i b
    simp only [LinearMap.sub_apply, h1, mLam_e_left H, sub_self]
  · have h1 : T a (V.e i) = a * V.e i := T_e_right hφr hS i a
    simp only [LinearMap.sub_apply, h1, mLam_e_right H, sub_self]

include H hS in
theorem T_sub_mul_raises (hq : 1 ≤ q) : Raises₂ G 1 (conj g (star φ) - LinearMap.mul k Λ) := by
  intro d e a b ha hb
  have h1 := hS.err.mono hq d e a b ha hb
  have h2 := mLam_sub_mul H lam d e a b ha hb
  have := G.ge_add h1 h2
  simpa [LinearMap.sub_apply] using this

include H hS in
/-- **`dφ_q = 0`**: the degree-`q` part of the error is a cocycle. -/
theorem stage_cocycle (hq : 1 ≤ q) :
    IsCocycle₂ (degPart (G := G) q (conj g (star φ) - mLam μ lam)) := by
  set T := conj g (star φ)
  set M := mLam μ lam
  set D := T - M
  set φq := degPart (G := G) q D
  have hTM : ∀ x y, T x y = M x y + D x y := fun x y ↦ by simp [D]
  have hDr : Raises₂ G (q + 1) (D - φq) := sub_degPart hS.err
  have hφqd : HasDeg₂ G q φq := degPart_hasDeg q D
  have hTm := T_sub_mul_raises H hS hq
  have hMm := mLam_sub_mul H lam
  -- the associativity identity
  have hstar : ∀ a b c, D (T a b) c + M (D a b) c = D a (T b c) + M a (D b c) := by
    intro a b c
    have h1 : M (T a b) c + D (T a b) c = M a (T b c) + D a (T b c) := by
      rw [← hTM, ← hTM]; exact T_assoc a b c
    have eA : M (T a b) c = M (M a b) c + M (D a b) c := by
      rw [hTM a b, map_add, LinearMap.add_apply]
    have eB : M a (T b c) = M a (M b c) + M a (D b c) := by rw [hTM b c, map_add]
    calc D (T a b) c + M (D a b) c = (M (T a b) c + D (T a b) c) - M (M a b) c := by
          rw [eA]; abel
      _ = (M a (T b c) + D a (T b c)) - M a (M b c) := by rw [h1, H.assoc lam a b c]
      _ = D a (T b c) + M a (D b c) := by rw [eB]; abel
  -- `M(D(a,b), c)` in the top degree
  have hMD : ∀ d e l a b c, G.IsHom d a → G.IsHom e b → G.IsHom l c →
      G.proj (d + e + l + q) (M (D a b) c) = φq a b * c := by
    intro d e l a b c ha hb hc
    have hD : G.Ge (d + e + q) (D a b) := hS.err d e a b ha hb
    have hsplit : M (D a b) c = φq a b * c + (D - φq) a b * c +
        (M - LinearMap.mul k Λ) (D a b) c := by
      simp only [LinearMap.sub_apply, LinearMap.mul_apply', sub_mul, mul_sub]; abel
    rw [hsplit, map_add, map_add, G.proj_of_isHom (G.isHom_mul (hφqd d e a b ha hb) hc),
      if_pos (by omega)]
    rw [proj_eq_zero_of_ge (G.ge_mul (hDr d e a b ha hb) (G.ge_of_isHom hc)) (by omega),
      proj_eq_zero_of_ge (hMm.ge hD (G.ge_of_isHom hc)) (by omega), add_zero, add_zero]
  have hMD' : ∀ d e l a b c, G.IsHom d a → G.IsHom e b → G.IsHom l c →
      G.proj (d + e + l + q) (M a (D b c)) = a * φq b c := by
    intro d e l a b c ha hb hc
    have hD : G.Ge (e + l + q) (D b c) := hS.err e l b c hb hc
    have hsplit : M a (D b c) = a * φq b c + a * (D - φq) b c +
        (M - LinearMap.mul k Λ) a (D b c) := by
      simp only [LinearMap.sub_apply, LinearMap.mul_apply', sub_mul, mul_sub]; abel
    rw [hsplit, map_add, map_add, G.proj_of_isHom (G.isHom_mul ha (hφqd e l b c hb hc)),
      if_pos (by omega)]
    rw [proj_eq_zero_of_ge (G.ge_mul (G.ge_of_isHom ha) (hDr e l b c hb hc)) (by omega),
      proj_eq_zero_of_ge (hMm.ge (G.ge_of_isHom ha) hD) (by omega), add_zero, add_zero]
  -- `D(T(a,b), c)` in the top degree
  have hDT : ∀ d e l a b c, G.IsHom d a → G.IsHom e b → G.IsHom l c →
      G.proj (d + e + l + q) (D (T a b) c) = φq (a * b) c := by
    intro d e l a b c ha hb hc
    have hab := G.isHom_mul ha hb
    have hs : G.Ge (d + e + 1) ((T - LinearMap.mul k Λ) a b) := hTm d e a b ha hb
    have hsplit : D (T a b) c = φq (a * b) c + (D - φq) (a * b) c +
        D ((T - LinearMap.mul k Λ) a b) c := by
      simp only [LinearMap.sub_apply, LinearMap.mul_apply', map_sub, LinearMap.sub_apply]; abel
    rw [hsplit, map_add, map_add, G.proj_of_isHom (hφqd _ _ _ _ hab hc), if_pos (by omega)]
    rw [proj_eq_zero_of_ge (hDr _ _ _ _ hab hc) (by omega),
      proj_eq_zero_of_ge (hS.err.ge hs (G.ge_of_isHom hc)) (by omega), add_zero, add_zero]
  have hDT' : ∀ d e l a b c, G.IsHom d a → G.IsHom e b → G.IsHom l c →
      G.proj (d + e + l + q) (D a (T b c)) = φq a (b * c) := by
    intro d e l a b c ha hb hc
    have hbc := G.isHom_mul hb hc
    have hs : G.Ge (e + l + 1) ((T - LinearMap.mul k Λ) b c) := hTm e l b c hb hc
    have hsplit : D a (T b c) = φq a (b * c) + (D - φq) a (b * c) +
        D a ((T - LinearMap.mul k Λ) b c) := by
      simp only [LinearMap.sub_apply, LinearMap.mul_apply', map_sub, LinearMap.sub_apply]; abel
    rw [hsplit, map_add, map_add, G.proj_of_isHom (hφqd _ _ _ _ ha hbc),
      if_pos (by omega)]
    rw [proj_eq_zero_of_ge (hDr _ _ _ _ ha hbc) (by omega),
      proj_eq_zero_of_ge (hS.err.ge (G.ge_of_isHom ha) hs) (by omega), add_zero, add_zero]
  refine isCocycle₂_of_hom (G := G) fun d e l a b c ha hb hc ↦ ?_
  have := congrArg (G.proj (d + e + l + q)) (hstar a b c)
  rw [map_add, map_add, hDT d e l a b c ha hb hc, hMD d e l a b c ha hb hc,
    hDT' d e l a b c ha hb hc, hMD' d e l a b c ha hb hc] at this
  rw [show a * φq b c - φq (a * b) c + φq a (b * c) - φq a b * c =
    (φq a (b * c) + a * φq b c) - (φq (a * b) c + φq a b * c) by abel, ← this, sub_self]

theorem ge_of_N_eq_zero (hN : G.N = 0) (m : ℕ) (x : Λ) : G.Ge m x := fun d _ ↦ by
  rw [G.proj_ge d (by omega), LinearMap.zero_apply]

theorem Raises₁.pow {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : Raises₁ G q f) (m : ℕ) :
    Raises₁ G (m * q) (f ^ m) := by
  induction m with
  | zero => intro d a ha; simpa using G.ge_of_isHom ha
  | succ m ih =>
      intro d a ha
      rw [pow_succ, Module.End.mul_apply]
      have := ih.ge (hf d a ha)
      rwa [show d + q + m * q = d + (m + 1) * q by ring] at this

theorem Raises₁.pow_eq_zero {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : Raises₁ G q f) (hq : 1 ≤ q) :
    f ^ (G.N + 1) = 0 := by
  ext a
  have := (hf.pow (G.N + 1)).ge (G.ge_zero a)
  rw [LinearMap.zero_apply]
  exact G.eq_zero_of_ge this (by nlinarith)

/-- `1 - f` for a degree-raising `f`, with inverse `Σ fⁱ`. -/
def oneSub {q : ℕ} (f : Λ →ₗ[k] Λ) (hf : Raises₁ G q f) (hq : 1 ≤ q) : Λ ≃ₗ[k] Λ :=
  LinearEquiv.ofLinearMap (1 - f) (∑ i ∈ Finset.range (G.N + 1), f ^ i)
    (by rw [← Module.End.mul_eq_comp, mul_neg_geom_sum, hf.pow_eq_zero hq, sub_zero]; rfl)
    (by rw [← Module.End.mul_eq_comp, geom_sum_mul_neg, hf.pow_eq_zero hq, sub_zero]; rfl)

theorem oneSub_apply {q : ℕ} (f : Λ →ₗ[k] Λ) (hf : Raises₁ G q f) (hq : 1 ≤ q) (a : Λ) :
    oneSub f hf hq a = a - f a := rfl

theorem oneSub_symm_apply {q : ℕ} (f : Λ →ₗ[k] Λ) (hf : Raises₁ G q f) (hq : 1 ≤ q) (a : Λ) :
    (oneSub f hf hq).symm a = a + ∑ i ∈ Finset.range G.N, (f ^ (i + 1)) a := by
  change (∑ i ∈ Finset.range (G.N + 1), f ^ i) a = _
  rw [Finset.sum_range_succ', LinearMap.add_apply, LinearMap.sum_apply, pow_zero,
    Module.End.one_apply, add_comm]

include H hS hφl hφr in
/-- **The change of variables `1 - f_q`**: the stage invariant passes from `q`
to `q + 1`. -/
theorem stage_succ (hq : 1 ≤ q) :
    ∃ g' lam', Stage (V := V) (μ := μ) (qd := qd) (φ := φ) (q + 1) g' lam' := by
  classical
  set T := conj g (star φ)
  set M := mLam μ lam
  set D := T - M
  set φq := degPart (G := G) q D
  obtain ⟨c, f, hfrel, hfdeg, hφq⟩ := H.span q hq φq ((err_rel H hφl hφr hS).degPart_rel q)
    (degPart_hasDeg q D) (stage_cocycle H hS hq)
  have hfr : Raises₁ G q f := hfdeg.raises
  set h := oneSub f hfr hq
  set lam' : Fin n → k := fun i ↦ if qd i = q then c i else lam i
  have hTm := T_sub_mul_raises H hS hq
  have hT0 : Raises₂ G 0 T := fun d e a b ha hb ↦ by
    have h1 := hTm d e a b ha hb
    have h2 := raises_mul d e a b ha hb
    have := G.ge_add (G.ge_mono (by omega) h1) h2
    simpa using this
  refine ⟨h.trans g, lam', ⟨fun i ↦ ?_, fun i a ↦ ?_, fun i a ↦ ?_, ?_, ?_, ?_, fun i hi ↦ ?_⟩⟩
  · simp [h, oneSub_apply, hfrel.unit, hS.unit]
  · simp [h, oneSub_apply, hfrel.left, hS.left, mul_sub]
  · simp [h, oneSub_apply, hfrel.right, hS.right, sub_mul]
  · intro d a ha
    have hfa := hfr d a ha
    have h1 : G.Ge (d + 1) (g (a - f a) - (a - f a)) := by
      have := hS.lead.ge (G.ge_sub (G.ge_of_isHom ha) (G.ge_mono (by omega) hfa))
      simpa using this
    have := G.ge_sub h1 (G.ge_mono (by omega) hfa)
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearMap.id_apply, h, oneSub_apply]
    convert this using 1
    abel
  · intro d a ha
    have hga : G.Ge (d + 1) (g.symm a - a) := by simpa using hS.leadInv d a ha
    have hga' : G.Ge d (g.symm a) := by
      have := G.ge_add (G.ge_mono (Nat.le_succ d) hga) (G.ge_of_isHom ha)
      simpa using this
    have hsum : G.Ge (d + 1) (∑ i ∈ Finset.range G.N, (f ^ (i + 1)) (g.symm a)) :=
      ge_sum _ _ fun i _ ↦ G.ge_mono (by nlinarith) ((hfr.pow (i + 1)).ge hga')
    have := G.ge_add hga hsum
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.symm_trans_apply,
      LinearMap.id_apply, h, oneSub_symm_apply]
    convert this using 1
    abel
  · intro d e a b ha hb
    have hφab := congrArg (fun F : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ F a b) hφq
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, cobdry_apply] at hφab
    set fa := f a
    set fb := f b
    set z := T (h a) (h b)
    have hz : z = T a b - T fa b - T a fb + T fa fb := by
      simp only [z, h, oneSub_apply, map_sub, LinearMap.sub_apply]; abel
    have hfa : G.Ge (d + q) fa := hfr d a ha
    have hfb : G.Ge (e + q) fb := hfr e b hb
    -- `z ≡ ab` modulo degree `d + e + 1`
    have hzab : G.Ge (d + e + 1) (z - a * b) := by
      rw [hz]
      have h1 : G.Ge (d + e + 1) ((T - LinearMap.mul k Λ) a b) := hTm d e a b ha hb
      have h2 := hT0.ge hfa (G.ge_of_isHom hb)
      have h3 := hT0.ge (G.ge_of_isHom ha) hfb
      have h4 := hT0.ge hfa hfb
      have := G.ge_add (G.ge_sub (G.ge_sub h1 (G.ge_mono (by omega) h2))
        (G.ge_mono (by omega) h3)) (G.ge_mono (by omega) h4)
      convert this using 1
      simp only [LinearMap.sub_apply, LinearMap.mul_apply']; abel
    have hzd : G.Ge (d + e) z := by
      have := G.ge_add (G.ge_mono (by omega) hzab) (G.ge_of_isHom (G.isHom_mul ha hb))
      simpa using this
    -- the pieces
    have P1 : G.Ge (d + e + (q + 1)) (∑ i ∈ Finset.range G.N, (f ^ (i + 1)) z - f z) := by
      rcases Nat.eq_zero_or_pos G.N with hN | hN
      · exact ge_of_N_eq_zero hN _ _
      · obtain ⟨N', hN'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hN)
        rw [hN', Finset.sum_range_succ', zero_add, pow_one, add_sub_cancel_right]
        exact ge_sum _ _ fun i _ ↦ G.ge_mono (by nlinarith) ((hfr.pow (i + 1 + 1)).ge hzd)
    have P2 : G.Ge (d + e + (q + 1)) (f (z - a * b)) := by
      have := hfr.ge hzab; rwa [show d + e + 1 + q = d + e + (q + 1) by omega] at this
    have P3 : G.Ge (d + e + (q + 1)) (z - (M a b + φq a b - fa * b - a * fb)) := by
      have h1 : G.Ge (d + e + (q + 1)) ((D - φq) a b) := sub_degPart hS.err d e a b ha hb
      have h2 := hTm.ge hfa (G.ge_of_isHom hb)
      have h3 := hTm.ge (G.ge_of_isHom ha) hfb
      have h4 := hT0.ge hfa hfb
      have := G.ge_add (G.ge_sub (G.ge_sub h1 (G.ge_mono (by omega) h2))
        (G.ge_mono (by omega) h3)) (G.ge_mono (by omega) h4)
      convert this using 1
      rw [hz]
      simp only [D, LinearMap.sub_apply, LinearMap.mul_apply']; abel
    have P4 : f (a * b) + M a b + φq a b - fa * b - a * fb - mLam μ lam' a b = 0 := by
      have hM' : mLam μ lam' a b = M a b +
          ∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i a b := by
        simp only [M, mLam_apply, add_assoc, add_right_inj, Finset.sum_filter]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hi : qd i = q
        · simp [lam', hi, hS.zero i (le_of_eq hi.symm)]
        · simp [lam', hi]
      rw [hM', hφab]
      abel
    have key : (conj (h.trans g) (star φ) - mLam μ lam') a b =
        (∑ i ∈ Finset.range G.N, (f ^ (i + 1)) z - f z) + f (z - a * b) +
          (z - (M a b + φq a b - fa * b - a * fb)) +
          (f (a * b) + M a b + φq a b - fa * b - a * fb - mLam μ lam' a b) := by
      have : conj (h.trans g) (star φ) a b = h.symm z := by
        simp only [conj_apply, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, z, T]
      rw [LinearMap.sub_apply, LinearMap.sub_apply, this, oneSub_symm_apply, map_sub]
      abel
    rw [key, P4, add_zero]
    exact G.ge_add (G.ge_add P1 P2) P3
  · have hi' : qd i ≠ q := by omega
    simp only [lam', hi', if_false]
    exact hS.zero i (by omega)

include hσφ hFφ in
theorem stage_one : Stage (V := V) (μ := μ) (qd := qd) (φ := φ) 1 (LinearEquiv.refl k Λ) 0 := by
  refine ⟨fun i ↦ rfl, fun i a ↦ rfl, fun i a ↦ rfl, fun d a _ ↦ ?_, fun d a _ ↦ ?_, ?_,
    fun i _ ↦ rfl⟩
  · simpa using ge_zero' (G := G) (d + 1)
  · simpa using ge_zero' (G := G) (d + 1)
  · intro d e a b ha hb
    have := star_raises hσφ hFφ d e a b ha hb
    simpa [conj_apply, mLam_apply] using this

include H hσφ hFφ hφl hφr in
theorem exists_stage (m : ℕ) :
    ∃ g lam, Stage (V := V) (μ := μ) (qd := qd) (φ := φ) (m + 1) g lam := by
  induction m with
  | zero => exact ⟨_, _, stage_one hσφ hFφ⟩
  | succ m ih =>
      obtain ⟨g, lam, hS⟩ := ih
      exact stage_succ H hφl hφr hS (by omega)

end Normalization

variable {V} in
/-- **Theorem 7.7** (finite normalization of an associative family). -/
theorem finiteFamilyNormalization {μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ} {qd : Fin n → ℕ}
    (H : FamilyHyp V μ qd) {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B) :
    ∃ (lam : Fin n → k) (Ψ : Λ ≃ₗ[k] B), (∀ a b, Ψ (mLam μ lam a b) = Ψ a * Ψ b) ∧
      CompleteOrthogonalIdempotents (fun i ↦ Ψ (V.e i)) ∧
      (∀ d a, G.IsHom d a → P.σ d (Ψ a) = a) ∧
      ∀ d, Submodule.map Ψ.toLinearMap (G.geSub d) = P.F d := by
  obtain ⟨φ, hφe, hφl, hφr, hσφ, hFφ⟩ := P.exists_split V
  obtain ⟨g, lam, hS⟩ := exists_stage H hφl hφr hσφ hFφ G.N
  have hT : conj g (star φ) = mLam μ lam := by
    ext a b
    have := eq_zero_of_raises hS.err (by omega) a b
    rwa [LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at this
  have hg : ∀ d x, G.Ge d x → G.Ge d (g x) := fun d x hx ↦ by
    have := G.ge_add (G.ge_mono (Nat.le_succ d) (hS.lead.ge hx)) hx
    simpa using this
  have hg' : ∀ d x, G.Ge d x → G.Ge d (g.symm x) := fun d x hx ↦ by
    have := G.ge_add (G.ge_mono (Nat.le_succ d) (hS.leadInv.ge hx)) hx
    simpa using this
  refine ⟨lam, g.trans φ, fun a b ↦ ?_, ?_, fun d a ha ↦ ?_, fun d ↦ ?_⟩
  · rw [← hT, conj_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, star_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  · simpa [hS.unit] using hφe
  · have hr : G.Ge (d + 1) (g a - a) := by simpa using hS.lead d a ha
    have h1 := mem_F_of_ge hFφ hr
    have h2 := (P.σ_ker d _ (P.F_succ_le d h1)).2 h1
    rw [map_sub, map_sub, hσφ d a ha, sub_eq_zero] at h2
    exact h2
  · rw [← hFφ d]
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, hg d a ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g.symm a, hg' d a ha, by simp⟩


end LenGrading

end MultiplicativeBasisDeformations
