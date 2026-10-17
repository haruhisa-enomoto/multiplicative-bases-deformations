import MultiplicativeBasisDeformations.Foundations.Char2Core
import MultiplicativeBasisDeformations.Foundations.IndicatorRel
import MultiplicativeBasisDeformations.Foundations.GradedBasis

/-!
# The indicator family on a graded algebra `Λ ≅ kP`

For `Θ : kP ≅ Λ` carrying ray vectors to homogeneous elements (degree `deg ℓ(r)` and weight
`ℓ(r)`): transported supported cochains satisfying the equalities of Proposition 11.2 are
cocycles; they are normalized relative to the transported identities; an indicator of a class
of character `χ` has character `χ` and internal degree `deg χ`; and the family
`m + Σ t_E μ_E` is associative (Proposition 11.3(1)). These are the hypotheses of
Theorem 7.7 other than spanning (`binary-families.tex`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  (hfin : IsRepresentationFinite k (S.P.Lin k))
  {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)

local notation:max "⌜" r "⌝" => Sys.rr S r

/-- The transported ray basis. -/
def basisΛ : Module.Basis R k Λ := (S.P.basis k).map Θ.toLinearEquiv

theorem basisΛ_apply (r : R) : S.basisΛ k Θ r = Θ (S.P.b k r) := by
  rw [basisΛ, Module.Basis.map_apply, Mult.basis_apply]; rfl

/-! ### Cocycles and associativity -/

theorem transp_isCocycle {μ : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k}
    (hμ : LenGrading.IsCocycle₂ μ) : LenGrading.IsCocycle₂ (S.transp k Θ μ) := by
  intro a b c
  have h := congrArg Θ (hμ (Θ.symm a) (Θ.symm b) (Θ.symm c))
  simp only [map_sub, map_add, map_mul, map_zero, AlgEquiv.apply_symm_apply] at h
  simp only [transp_apply, map_mul]
  exact h

include hfin in
theorem transp_coch_isCocycle {a : R → R → k} (ha : S.EdgeOK k a) :
    LenGrading.IsCocycle₂ (S.transp k Θ (S.coch k a)) :=
  S.transp_isCocycle k Θ ((S.coch_isCocycle_iff k k hfin a).2 ha)

theorem edgeOK_add {a a' : R → R → k} (ha : S.EdgeOK k a) (ha' : S.EdgeOK k a') :
    S.EdgeOK k (a + a') := fun u v w h ↦ by simp only [Pi.add_apply, ha u v w h, ha' u v w h]

theorem edgeOK_smul (t : k) {a : R → R → k} (ha : S.EdgeOK k a) : S.EdgeOK k (t • a) :=
  fun u v w h ↦ by simp only [Pi.smul_apply, ha u v w h]

theorem edgeOK_indComb {n : ℕ} (E : Fin n → Quotient S.pairSetoid) (lam : Fin n → k) :
    S.EdgeOK k (S.indComb k E lam) := by
  unfold indComb
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => intro u v w _; simp
  | insert i s _ ih =>
    rw [Finset.sum_insert ‹_›]
    exact S.edgeOK_add k (S.edgeOK_smul k _ (S.edgeOK_ind k (E i))) ih

include hfin in
/-- **The transported indicator family is associative** (Proposition 11.3(1)). -/
theorem transp_family_assoc {n : ℕ} (E : Fin n → Quotient S.pairSetoid) (lam : Fin n → k)
    (x y z : Λ) :
    LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam
        (LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam x y) z =
      LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam x
        (LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam y z) := by
  rw [← Θ.apply_symm_apply x, ← Θ.apply_symm_apply y, ← Θ.apply_symm_apply z,
    S.transp_family k Θ E lam, S.transp_family k Θ E lam, S.transp_family k Θ E lam,
    S.transp_family k Θ E lam]
  congr 1
  exact S.family_assoc k k hfin (S.edgeOK_indComb k E lam) _ _ _

/-! ### Relative cochains -/

include hfin in
/-- **Transported supported cochains are normalized relative cochains.** -/
theorem transp_isRel {G : LenGrading k Λ} (Vx : LenGrading.Vertices G)
    (hVx : ∀ i, ∃ x, Vx.e i = Θ (S.P.b k (S.P.e x))) (a : R → R → k) :
    LenGrading.IsRel₂ Vx (S.transp k Θ (S.coch k a)) := by
  refine ⟨fun i x y ↦ ?_, fun i x y ↦ ?_, fun i x y ↦ ?_, fun i y ↦ ?_, fun i x ↦ ?_⟩
  all_goals obtain ⟨v, hv⟩ := hVx i
  all_goals rw [hv]
  · simp only [transp_apply, map_mul, AlgEquiv.symm_apply_apply]
    rw [S.coch_e_mul k hfin, map_mul]
  · simp only [transp_apply, map_mul, AlgEquiv.symm_apply_apply]
    rw [S.coch_mul_e k hfin]
  · simp only [transp_apply, map_mul, AlgEquiv.symm_apply_apply]
    rw [S.coch_mul_e_right k hfin, map_mul]
  · simp only [transp_apply, AlgEquiv.symm_apply_apply]
    rw [S.coch_e_left k hfin, map_zero]
  · simp only [transp_apply, AlgEquiv.symm_apply_apply]
    rw [S.coch_e_right k hfin, map_zero]

/-! ### Degrees and characters -/

section Graded

variable {G : LenGrading k Λ} {W : LatGrading k Λ L}
  (hG : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (Θ (S.P.b k r)))
  (hW : ∀ r, W.IsHom (S.P.wt r) (Θ (S.P.b k r)))

include hfin hW in
/-- **An indicator of a class of character `χ` has character `χ`.** -/
theorem transp_muE_char {E : Quotient S.pairSetoid} {χ : L}
    (hE : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ) :
    W.Char₂ χ (S.transp k Θ (S.muE k E)) := by
  refine W.char₂_of_basis (S.basisΛ k Θ) S.P.wt (fun r ↦ by rw [basisΛ_apply]; exact hW r) χ _
    fun u v ↦ ?_
  rw [basisΛ_apply, basisΛ_apply, transp_apply, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]
  rcases S.muE_value k hfin hE u v with h | ⟨t, ht, hw, -⟩
  · rw [h, map_zero]; exact W.isHom_zero _
  · rw [ht, ← hw]; exact hW t

include hfin hG in
/-- **An indicator of a class of character `χ` has internal degree `deg χ`.** -/
theorem transp_muE_deg {E : Quotient S.pairSetoid} {χ : L}
    (hE : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ)
    (hχ : 0 ≤ S.P.deg χ) :
    LenGrading.HasDeg₂ G (S.P.deg χ).toNat (S.transp k Θ (S.muE k E)) := by
  refine G.hasDeg₂_of_basis (S.basisΛ k Θ) (fun r ↦ (S.P.deg (S.P.wt r)).toNat)
    (fun r ↦ by rw [basisΛ_apply]; exact hG r) _ _ fun u v ↦ ?_
  rw [basisΛ_apply, basisΛ_apply, transp_apply, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]
  rcases S.muE_value k hfin hE u v with h | ⟨t, ht, hw, -⟩
  · rw [h, map_zero]; exact G.isHom_zero' _
  · rw [ht]
    have := hG t
    have h1 := S.P.deg_nonneg u
    have h2 := S.P.deg_nonneg v
    rw [hw, map_add, map_add] at this
    convert this using 1
    omega

theorem transp_add (μ ν : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) :
    S.transp k Θ (μ + ν) = S.transp k Θ μ + S.transp k Θ ν := by
  ext a b; simp [transp_apply]

theorem transp_smul (t : k) (μ : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) :
    S.transp k Θ (t • μ) = t • S.transp k Θ μ := by
  ext a b; simp [transp_apply]

theorem transp_sum {ι : Type*} (s : Finset ι) (μ : ι → S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) :
    S.transp k Θ (∑ i ∈ s, μ i) = ∑ i ∈ s, S.transp k Θ (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext a b; simp [transp_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, transp_add, ih]

theorem muE_eq_zero {E : Quotient S.pairSetoid}
    (h : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 = 0) : S.muE k E = 0 :=
  S.bilin_ext k fun u v ↦ by
    classical
    rw [muE_b, LinearMap.zero_apply, LinearMap.zero_apply]
    split_ifs with h'
    · rw [h (u, v) h', vecM_zero]
    · rfl

/-- A coboundary of internal degree `q`. -/
def IsCobdry (G : LenGrading k Λ) (q : ℕ) (φ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop :=
  ∃ H, LenGrading.HasDeg₁ G q H ∧ φ = LenGrading.cobdry k H

theorem isCobdry_zero (G : LenGrading k Λ) (q : ℕ) : IsCobdry k G q (0 : Λ →ₗ[k] Λ →ₗ[k] Λ) :=
  ⟨0, fun _ _ _ ↦ by simp [LenGrading.IsHom], by ext a b; simp [LenGrading.cobdry_apply]⟩

theorem isCobdry_smul {G : LenGrading k Λ} {q : ℕ} (t : k) {φ : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (h : IsCobdry k G q φ) : IsCobdry k G q (t • φ) := by
  obtain ⟨H, hH, rfl⟩ := h
  refine ⟨t • H, fun d a ha ↦ ?_, ?_⟩
  · have := hH d a ha
    unfold LenGrading.IsHom at this ⊢
    rw [LinearMap.smul_apply, map_smul, this]
  · ext a b; simp [LenGrading.cobdry_apply, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add]

theorem isCobdry_sum {G : LenGrading k Λ} {q : ℕ} {ι : Type*} (s : Finset ι)
    {φ : ι → Λ →ₗ[k] Λ →ₗ[k] Λ} (h : ∀ i ∈ s, IsCobdry k G q (φ i)) :
    IsCobdry k G q (∑ i ∈ s, φ i) := by
  classical
  choose H hH hφ using h
  refine ⟨∑ i ∈ s.attach, H i.1 i.2, LenGrading.hasDeg₁_sum _ fun i _ ↦ hH i.1 i.2, ?_⟩
  rw [LenGrading.cobdry_sum, ← Finset.sum_attach s φ]
  exact Finset.sum_congr rfl fun i _ ↦ hφ i.1 i.2

include hfin in
/-- **Selection of an indicator** (proof of Proposition 8.3): a supported cocycle of character
`χ` with nonzero class is a combination of indicators of that character, at least one of which
has nonzero class. -/
theorem select_class {G : LenGrading k Λ} {a : R → R → k} (ha : S.EdgeOK k a) {χ : L}
    (hsupp : ∀ z : R × R, a z.1 z.2 ≠ 0 → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ) {q : ℕ}
    (hnz : ¬ IsCobdry k G q (S.transp k Θ (S.coch k a))) :
    ∃ E : Quotient S.pairSetoid,
      (∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ) ∧
        ¬ IsCobdry k G q (S.transp k Θ (S.muE k E)) := by
  classical
  haveI : Fintype (Quotient S.pairSetoid) := Fintype.ofFinite _
  by_contra hall
  push Not at hall
  apply hnz
  have hdec := S.coch_eq_sum_muE k k hfin ((S.coch_isCocycle_iff k k hfin a).2 ha)
  rw [hdec, transp_sum]
  refine isCobdry_sum k _ fun E _ ↦ ?_
  rw [transp_smul]
  by_cases hE0 : a (Quotient.out E).1 (Quotient.out E).2 = 0
  · rw [hE0, zero_smul]; exact isCobdry_zero k G q
  by_cases hz : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 = 0
  · rw [S.muE_eq_zero k hz, show S.transp k Θ (0 : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) = 0
      by ext; simp [transp_apply], smul_zero]
    exact isCobdry_zero k G q
  refine isCobdry_smul k _ (hall E fun z hzE hz0 ↦ hsupp z ?_ hz0)
  have := S.const_of_edgeOK k ha (z := z) (z' := Quotient.out E) (by rw [hzE, Quotient.out_eq])
  rw [this]; exact hE0

include hfin in
/-- A class with a nonzero correction has only one character. -/
theorem classChar_unique {E : Quotient S.pairSetoid} {χ χ' : L}
    (h1 : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ)
    (h2 : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ')
    {G : LenGrading k Λ} {q : ℕ} (hnz : ¬ IsCobdry k G q (S.transp k Θ (S.muE k E))) : χ = χ' := by
  by_contra hne
  apply hnz
  have : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 = 0 := by
    intro z hz
    by_contra h0
    exact hne ((h1 z hz h0).symm.trans (h2 z hz h0))
  rw [S.muE_eq_zero k this, show S.transp k Θ (0 : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) = 0
    by ext; simp [transp_apply]]
  exact isCobdry_zero k G q

include hG hW in
/-- **A nonzero cochain of internal degree `q` and character `χ` has `deg χ = q`.** -/
theorem deg_eq_of_ne_zero {φ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hφ : φ ≠ 0) {q : ℕ}
    (hd : LenGrading.HasDeg₂ G q φ) {χ : L} (hc : W.Char₂ χ φ) : S.P.deg χ = q := by
  classical
  have hex : ∃ u v, φ (Θ (S.P.b k u)) (Θ (S.P.b k v)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    refine (S.basisΛ k Θ).ext fun u ↦ (S.basisΛ k Θ).ext fun v ↦ ?_
    rw [basisΛ_apply, basisΛ_apply, h u v]; rfl
  obtain ⟨u, v, huv⟩ := hex
  set y := φ (Θ (S.P.b k u)) (Θ (S.P.b k v))
  have hy1 := hd _ _ _ _ (hG u) (hG v)
  have hy2 := hc _ _ _ _ (hW u) (hW v)
  obtain ⟨t, ht⟩ : ∃ t, (S.basisΛ k Θ).repr y t ≠ 0 := by
    by_contra h
    push Not at h
    apply huv
    rw [← (S.basisΛ k Θ).sum_repr y]
    exact Finset.sum_eq_zero fun t _ ↦ by rw [h t, zero_smul]
  have e1 : (S.P.deg (S.P.wt t)).toNat = (S.P.deg (S.P.wt u)).toNat +
      (S.P.deg (S.P.wt v)).toNat + q := by
    by_contra hne
    exact ht (G.repr_eq_zero_of_isHom (S.basisΛ k Θ) _
      (fun r ↦ by rw [basisΛ_apply]; exact hG r) hy1 hne)
  have e2 : S.P.wt t = S.P.wt u + S.P.wt v + χ := by
    by_contra hne
    exact ht (W.repr_eq_zero_of_isHom (S.basisΛ k Θ) _
      (fun r ↦ by rw [basisΛ_apply]; exact hW r) hy2 hne)
  have h0t := S.P.deg_nonneg t
  have h0u := S.P.deg_nonneg u
  have h0v := S.P.deg_nonneg v
  rw [e2, map_add, map_add] at e1 h0t
  omega

end Graded

end Sys

end RaySys

end MultiplicativeBasisDeformations
