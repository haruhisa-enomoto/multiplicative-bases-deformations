import MultiplicativeBasisDeformations.Refinements.SplitDeformation
import MultiplicativeBasisDeformations.Foundations.HochschildCochains

/-!
# Lemma 6.4 as stated

`lem:split-positive-deformation` (`positive-deformations.tex`): "`S` lifts to a unital
subalgebra of `B`, and the filtration of `B` splits as `S`-bimodules. The resulting
identification of `B` with `Λ` as filtered vector spaces induces the prescribed identification
`gr B = Λ`, and the multiplication of `B` becomes `μ₀ + Σ_{q>0} μ_q`, where `μ₀` is the
multiplication of `Λ` and each `μ_q` raises internal degree by `q`, is `S`-relative, and vanishes
when an input belongs to `S`."

For `S = Λ₀` with its vertex idempotents (`Vertices`): the splitting of `exists_split` is
`S`-bilinear on both sides, so the transported product is `S`-relative (`star_s_*`) and each
`μ_q`, `q > 0`, is a normalized `S`-relative cochain (`μ_isRelS`), and the statement is assembled
in `splitPositiveDeformation`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

namespace PosFiltration

open LenGrading

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type*} [Ring B] [Algebra k B] {P : PosFiltration G B} (V : Vertices G)

theorem proj_hom_mul' {m : ℕ} {e : Λ} (he : G.IsHom m e) (a : Λ) (d : ℕ) :
    G.proj (m + d) (e * a) = e * G.proj d a := by
  conv_lhs => rw [G.sum a, Finset.mul_sum, map_sum]
  simp_rw [G.proj_of_isHom (G.isHom_mul he (G.isHom_proj _ a)), add_right_inj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [G.proj_ge d (by simpa using h), LinearMap.zero_apply, mul_zero]

theorem proj_mul_hom' {m : ℕ} {e : Λ} (he : G.IsHom m e) (a : Λ) (d : ℕ) :
    G.proj (d + m) (a * e) = G.proj d a * e := by
  conv_lhs => rw [G.sum a, Finset.sum_mul, map_sum]
  simp_rw [G.proj_of_isHom (G.isHom_mul (G.isHom_proj _ a) he), add_left_inj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [G.proj_ge d (by simpa using h), LinearMap.zero_apply, zero_mul]

variable (G) in
/-- **`S`-relative and normalized**, for `S = Λ₀`: `μ(sa, b) = sμ(a, b)`, `μ(as, b) = μ(a, sb)`,
`μ(a, bs) = μ(a, b)s`, and `μ` vanishes when an input belongs to `S`. -/
def IsRelS (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop :=
  ∀ s, G.IsHom 0 s → (∀ a b, μ (s * a) b = s * μ a b) ∧ (∀ a b, μ (a * s) b = μ a (s * b)) ∧
    (∀ a b, μ a (b * s) = μ a b * s) ∧ (∀ b, μ s b = 0) ∧ ∀ a, μ a s = 0

theorem IsRelS.isRel₂ {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (h : IsRelS G μ) : IsRel₂ V μ :=
  ⟨fun i ↦ (h _ (V.deg0 i)).1, fun i ↦ (h _ (V.deg0 i)).2.1, fun i ↦ (h _ (V.deg0 i)).2.2.1,
    fun i ↦ (h _ (V.deg0 i)).2.2.2.1, fun i ↦ (h _ (V.deg0 i)).2.2.2.2⟩

namespace Split

variable (S : Split P) (hl : ∀ s a, G.IsHom 0 s → S.φ (s * a) = S.φ s * S.φ a)
  (hr : ∀ s a, G.IsHom 0 s → S.φ (a * s) = S.φ a * S.φ s)

include hl in
theorem star_s_left {s : Λ} (hs : G.IsHom 0 s) (a b : Λ) : S.star (s * a) b = s * S.star a b := by
  apply S.φ.injective
  rw [φ_star, hl _ _ hs, hl _ _ hs, φ_star, mul_assoc]

include hl hr in
theorem star_s_mid {s : Λ} (hs : G.IsHom 0 s) (a b : Λ) : S.star (a * s) b = S.star a (s * b) := by
  apply S.φ.injective
  rw [φ_star, φ_star, hr _ _ hs, hl _ _ hs, mul_assoc]

include hr in
theorem star_s_right {s : Λ} (hs : G.IsHom 0 s) (a b : Λ) : S.star a (b * s) = S.star a b * s := by
  apply S.φ.injective
  rw [φ_star, hr _ _ hs, hr _ _ hs, φ_star, mul_assoc]

include hl in
theorem star_s_unit_left {s : Λ} (hs : G.IsHom 0 s) (b : Λ) : S.star s b = s * b := by
  apply S.φ.injective; rw [φ_star, hl _ _ hs]

include hr in
theorem star_s_unit_right {s : Λ} (hs : G.IsHom 0 s) (a : Λ) : S.star a s = a * s := by
  apply S.φ.injective; rw [φ_star, hr _ _ hs]

/-- Bilinear maps agreeing on homogeneous pairs agree. -/
theorem bilin_eq {f g : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (h : ∀ d e a b, G.IsHom d a → G.IsHom e b → f a b = g a b) : f = g := by
  ext a b
  rw [G.sum a, G.sum b]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    h _ _ _ _ (G.isHom_proj _ _) (G.isHom_proj _ _)

/-- Linear maps agreeing on homogeneous elements agree. -/
theorem lin_eq {f g : Λ →ₗ[k] Λ} (h : ∀ d a, G.IsHom d a → f a = g a) : f = g := by
  ext a
  rw [G.sum a]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ h _ _ (G.isHom_proj _ _)

include hl hr in
/-- **Each `μ_q`, `q > 0`, is a normalized `S`-relative cochain**, for `S = Λ₀`, when the
splitting is `S`-bilinear. -/
theorem μ_isRelS {q : ℕ} (hq : 0 < q) : IsRelS G (S.μ q) := by
  intro s hs
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_, fun b ↦ ?_, fun a ↦ ?_⟩
  · have := bilin_eq (f := (S.μ q).comp (LinearMap.mulLeft k s))
      (g := (S.μ q).compr₂ (LinearMap.mulLeft k s)) fun d e a b ha hb ↦ by
        change S.μ q (s * a) b = s * S.μ q a b
        rw [S.μ_hom (zero_add d ▸ G.isHom_mul hs ha) hb, S.μ_hom ha hb,
          star_s_left S hl hs, show d + e + q = 0 + (d + e + q) by omega, proj_hom_mul' hs,
          zero_add]
    exact congrArg (fun φ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ φ a b) this
  · have := bilin_eq (f := (S.μ q).comp (LinearMap.mulRight k s))
      (g := (S.μ q).compl₂ (LinearMap.mulLeft k s)) fun d e a b ha hb ↦ by
        change S.μ q (a * s) b = S.μ q a (s * b)
        rw [S.μ_hom (add_zero d ▸ G.isHom_mul ha hs) hb,
          S.μ_hom ha (zero_add e ▸ G.isHom_mul hs hb), star_s_mid S hl hr hs]
    exact congrArg (fun φ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ φ a b) this
  · have := bilin_eq (f := (S.μ q).compl₂ (LinearMap.mulRight k s))
      (g := (S.μ q).compr₂ (LinearMap.mulRight k s)) fun d e a b ha hb ↦ by
        change S.μ q a (b * s) = S.μ q a b * s
        rw [S.μ_hom ha (add_zero e ▸ G.isHom_mul hb hs), S.μ_hom ha hb,
          star_s_right S hr hs, show d + e + q = (d + e + q) + 0 by omega,
          proj_mul_hom' hs, add_zero]
    exact congrArg (fun φ : Λ →ₗ[k] Λ →ₗ[k] Λ ↦ φ a b) this
  · have := lin_eq (f := S.μ q s) (g := 0) fun e b hb ↦ by
      rw [S.μ_hom hs hb, star_s_unit_left S hl hs,
        G.proj_of_isHom (zero_add e ▸ G.isHom_mul hs hb), if_neg (by omega)]
      rfl
    exact congrArg (fun φ : Λ →ₗ[k] Λ ↦ φ b) this
  · have := lin_eq (f := (S.μ q).flip s) (g := 0) fun d a ha ↦ by
      change S.μ q a s = 0
      rw [S.μ_hom ha hs, star_s_unit_right S hr hs,
        G.proj_of_isHom (add_zero d ▸ G.isHom_mul ha hs), if_neg (by omega)]
    exact congrArg (fun φ : Λ →ₗ[k] Λ ↦ φ a) this

end Split

/-- **Lemma 6.4** (`lem:split-positive-deformation`): a positive filtered deformation `B` of `Λ`
splits: there is a filtered linear isomorphism `φ : Λ ≅ B` inducing the identification
`gr B = Λ`, restricting on `S = Λ₀` to a unital algebra map (the vertex idempotents go to a
complete set of orthogonal idempotents) and `S`-bilinear on both sides; the transported
multiplication is `μ₀ + Σ_{q>0} μ_q` with `μ₀` the multiplication of `Λ`, each `μ_q` raising
the degree by `q`, `S`-relative and vanishing when an input belongs to `S`. -/
theorem splitPositiveDeformation :
    ∃ S : Split P, CompleteOrthogonalIdempotents (fun i ↦ S.φ (V.e i)) ∧
      (∀ s a, G.IsHom 0 s → S.φ (s * a) = S.φ s * S.φ a) ∧
      (∀ s a, G.IsHom 0 s → S.φ (a * s) = S.φ a * S.φ s) ∧
      (∀ d a, G.IsHom d a → P.σ d (S.φ a) = a) ∧
      (∀ d, Submodule.map S.φ.toLinearMap (G.geSub d) = P.F d) ∧
      (∀ a b, S.φ a * S.φ b = S.φ (∑ q ∈ range G.N, S.μ q a b)) ∧
      (∀ a b, S.μ 0 a b = a * b) ∧
      (∀ q d e a b, G.IsHom d a → G.IsHom e b → G.IsHom (d + e + q) (S.μ q a b)) ∧
      ∀ q, 0 < q → IsRel₂ V (S.μ q) := by
  obtain ⟨φ, hc, hl, hr, hσ, hF⟩ := P.exists_split V
  let S : Split P := ⟨φ, by rw [← V.complete.complete, map_sum, hc.complete], hσ, hF⟩
  have hl' : ∀ i a, S.φ (V.e i * a) = S.φ (V.e i) * S.φ a := hl
  have hr' : ∀ i a, S.φ (a * V.e i) = S.φ a * S.φ (V.e i) := hr
  have hsl : ∀ s a, G.IsHom 0 s → S.φ (s * a) = S.φ s * S.φ a := by
    intro s a hs
    obtain ⟨c, rfl⟩ := V.span0 s hs
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hl']
  have hsr : ∀ s a, G.IsHom 0 s → S.φ (a * s) = S.φ a * S.φ s := by
    intro s a hs
    obtain ⟨c, rfl⟩ := V.span0 s hs
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, hr']
  refine ⟨S, hc, hsl, hsr, hσ, hF, fun a b ↦ ?_, S.μ_zero_apply, fun q d e a b ha hb ↦ S.μ_isHom ha hb,
    fun q hq ↦ (S.μ_isRelS hsl hsr hq).isRel₂ V⟩
  rw [← S.star_eq_sum, S.φ_star]

end PosFiltration

end MultiplicativeBasisDeformations
