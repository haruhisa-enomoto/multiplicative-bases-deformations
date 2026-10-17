import MultiplicativeBasisDeformations.Foundations.RayPres
import MultiplicativeBasisDeformations.Foundations.BinaryNormalization

/-!
# The family criterion with indicator cocycles

Proposition 7.9 (`characteristic-two-construction.tex:87–118`) for the selected binary
family of the proof of Proposition 8.3 (`main-theorems.tex:7–40`): with `A₀ ≅ kP` through
`Θ`, chosen indicator cocycles `μ_i = μ_{E_i}` of distinct classes satisfying the hypotheses
of Theorem 7.7 and characters forming part of an integer basis, Corollary 7.8 gives a binary
fibre isomorphic to `A`; by Proposition 11.3(3) the transported rays are a normed
multiplicative basis and a ray transversal of `A`.

The hypotheses on `μ_i` (relative, homogeneous, associative family, spanning) are taken as
the `FamilyHyp` of Theorem 7.7; they are discharged where `A₀`, its gradings and the
indicator classes are constructed.
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

omit [IsAlgClosed k] in
/-- A bilinear map on `kP` transported along `Θ`. -/
def transp {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)
    (μ : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  (μ.compl₁₂ Θ.symm.toLinearMap Θ.symm.toLinearMap).compr₂ Θ.toLinearMap

omit [IsAlgClosed k] in
theorem transp_apply {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)
    (μ : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k) (a b : Λ) :
    S.transp k Θ μ a b = Θ (μ (Θ.symm a) (Θ.symm b)) := rfl

/-- The coefficient function of a combination of distinct indicator classes. -/
def indComb {n : ℕ} (E : Fin n → Quotient S.pairSetoid) (lam : Fin n → k) : R → R → k :=
  ∑ i, lam i • S.ind k (E i)

theorem indComb_binary {n : ℕ} {E : Fin n → Quotient S.pairSetoid} (hE : Function.Injective E)
    {lam : Fin n → k} (hlam : ∀ i, lam i = 0 ∨ lam i = 1) (r s : R) :
    S.indComb k E lam r s = 0 ∨ S.indComb k E lam r s = 1 := by
  classical
  simp only [indComb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ind]
  by_cases h : ∃ i, (⟦(r, s)⟧ : Quotient S.pairSetoid) = E i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [if_neg (fun h' ↦ hj (hE (h'.symm.trans hi))),
      mul_zero]) (fun h ↦ absurd (Finset.mem_univ i) h), if_pos hi, mul_one]
    exact hlam i
  · left
    exact Finset.sum_eq_zero fun i _ ↦ by rw [if_neg fun h' ↦ h ⟨i, h'⟩, mul_zero]

theorem transp_family {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ) {n : ℕ}
    (E : Fin n → Quotient S.pairSetoid) (lam : Fin n → k) (a b : S.P.Lin k) :
    LenGrading.mLam (fun i ↦ S.transp k Θ (S.muE k (E i))) lam (Θ a) (Θ b) =
      Θ (a * b + S.coch k (S.indComb k E lam) a b) := by
  rw [LenGrading.mLam_apply, map_add, map_mul, indComb, S.coch_sum, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [S.coch_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, transp_apply,
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  rfl

/-- **The selected binary family recovers `A` with a normed multiplicative ray basis**
(Proposition 7.9 with Propositions 11.2, 11.3 and Corollary 7.8). -/
theorem char2_core {Λ : Type u} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
    {Vx : LenGrading.Vertices G} {L' : Type} [AddCommGroup L'] [DecidableEq L']
    {W : LatGrading k Λ L'} (compat : ∀ d l x, G.proj d (W.proj l x) = W.proj l (G.proj d x))
    (Θ : S.P.Lin k ≃ₐ[k] Λ) {n : ℕ} {E : Fin n → Quotient S.pairSetoid} (hE : Function.Injective E)
    {χ : Fin n → L'}
    (hχ : ∀ i l l' x y, W.IsHom l x → W.IsHom l' y →
      W.IsHom (l + l' + χ i) (S.transp k Θ (S.muE k (E i)) x y))
    {qd : Fin n → ℕ} (H : LenGrading.FamilyHyp Vx (fun i ↦ S.transp k Θ (S.muE k (E i))) qd)
    (he0 : ∀ i, W.IsHom 0 (Vx.e i))
    (hbasis : ∃ (ι : Type) (b : Module.Basis ι ℤ L') (j : Fin n → ι),
      Function.Injective j ∧ ∀ i, b (j i) = χ i)
    {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B] (P : PosFiltration G B) :
    ∃ (lam : Fin n → k) (_ : ∀ i, lam i = 0 ∨ lam i = 1) (Ψ : Λ ≃ₗ[k] B)
      (hΨ : ∀ a z, (Θ.toLinearEquiv.trans Ψ) (a * z + S.coch k (S.indComb k E lam) a z) =
        (Θ.toLinearEquiv.trans Ψ) a * (Θ.toLinearEquiv.trans Ψ) z),
      IsNormedMultiplicativeBasis (S.fibreBasis k hfin (S.indComb k E lam)
        (Θ.toLinearEquiv.trans Ψ) hΨ) ∧
      (S.fibreIdem k hfin _ _ hΨ).IsRayTransversal
        (S.fibreBasis k hfin (S.indComb k E lam) (Θ.toLinearEquiv.trans Ψ) hΨ) ∧
      (S.fibreIdem k hfin _ _ hΨ).IsRayPres (k := k) S.P.toMult (S.fibreIdx k hfin _ _ hΨ)
        (S.βv k (Θ.toLinearEquiv.trans Ψ)) := by
  obtain ⟨⟨lam, hlam, Ψ, hΨ, -⟩, -⟩ := LenGrading.binaryNormalization compat hχ H he0 hbasis P
  have hΨ' : ∀ a z, (Θ.toLinearEquiv.trans Ψ) (a * z + S.coch k (S.indComb k E lam) a z) =
      (Θ.toLinearEquiv.trans Ψ) a * (Θ.toLinearEquiv.trans Ψ) z := by
    intro a z
    simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply]
    rw [← hΨ, S.transp_family k Θ E lam]
  exact ⟨lam, hlam, Ψ, hΨ', S.fibreBasis_normed k hfin _ _ hΨ' (S.indComb_binary k hE hlam),
    S.fibreBasis_isRayTransversal k hfin _ _ hΨ', S.fibre_rayPres k hfin _ _ hΨ'⟩

end Sys

end RaySys

end MultiplicativeBasisDeformations
