import MultiplicativeBasisDeformations.Foundations.Cor105Bridge
import MultiplicativeBasisDeformations.Foundations.Induction
import MultiplicativeBasisDeformations.Foundations.FiltrationDim

/-!
# Corollary 10.5 for `A₀`, given Proposition 10.3

`cor:zero-supported-coverage` (`integral-deformations.tex:238–277`) for the ray system of
`A₀` with the dual weights (`Char2A0.Cor105`): the hypotheses of Theorem 9.1(3) come from the
induction hypothesis of Proposition 8.3 through Lemma 9.2 (`hWl_of_liftBelow`), and the only
remaining input is Proposition 10.3 in coefficients (`IStar`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

/-- **The lifting hypothesis of Theorem 9.1(3) from the induction hypothesis** (Lemma 9.2). -/
theorem hWl_of_liftBelow (k : Type u) [Field k] [IsAlgClosed k]
    (hfin : IsRepresentationFinite k (S.P.Lin k)) {χ : L} (hχ : 0 < S.P.deg χ) (hprim : Prim χ)
    (hLB : LiftBelow k (Fintype.card R)) :
    ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r := by
  classical
  by_cases hx : ∃ x, S.Supp χ x
  · exact S.hW_of_Qχ hχ hprim (fun w hw ↦ hLB _ _ _ (S.Qχ hχ hprim) (S.card_Qχ_lt hχ hprim hx)
      (S.Qχ_isRepresentationFinite hχ hprim k hfin) w hw)
  · intro w _
    have hTB : ∀ r, ¬ S.TB χ r := by
      intro r hr
      apply hr.2.1
      rw [S.qh_of_not_supp χ (fun h ↦ hx ⟨_, h⟩), zero_mul]
    exact ⟨0, fun r _ _ hr _ _ _ ↦ absurd hr (hTB r), fun r hr ↦ absurd hr (hTB r)⟩

/-- **Theorem 9.1** (`thm:integral-partial-lifting`), as stated in r38: if the lifting assertion
of Proposition 8.2 holds for every table with representation-finite linearization and fewer
than `dim A₀` rays, every solution modulo two of the Leibniz equations lifts to an integer
solution (and hence to `ℤ/4`). -/
theorem integralPartialLifting (k : Type u) [Field k] [IsAlgClosed k]
    (hfin : IsRepresentationFinite k (S.P.Lin k)) {χ : L} (hχ : 0 < S.P.deg χ) (hprim : Prim χ)
    (hLB : LiftBelow k (Fintype.card R)) {d : R → ZMod 2} (hd : S.IsSol χ d) :
    ∃ D : R → ℤ, S.IsSol χ D ∧ ∀ r, (D r : ZMod 2) = d r :=
  S.integral_lifting k hfin hχ hprim (S.hWl_of_liftBelow k hfin hχ hprim hLB) hd

/-- Every vertex idempotent occurs among the vertices of a grading. -/
theorem hVx_of (k : Type u) [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]
    (Θ : S.P.Lin k ≃ₐ[k] Λ) {G : LenGrading k Λ} (Vx : LenGrading.Vertices G)
    (h : ∀ i, ∃ x, Vx.e i = Θ (S.P.b k (S.P.e x))) :
    ∀ x, ∃ i, Vx.e i = Θ (S.P.b k (S.P.e x)) := by
  intro x
  by_contra hx
  push Not at hx
  apply S.P.b_ne_zero k (S.P.e x)
  apply Θ.injective
  rw [map_zero]
  calc Θ (S.P.b k (S.P.e x)) = Θ (S.P.b k (S.P.e x)) * ∑ i, Vx.e i := by
        rw [Vx.complete.complete, mul_one]
    _ = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        obtain ⟨y, hy⟩ := h i
        rw [hy, ← map_mul, Mult.b_mul_e, S.P.tgt_e, if_neg, map_zero]
        rintro rfl
        exact hx i hy

end Sys

end RaySys

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

section A0

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)

variable [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt Q ℤ)

/-- **Proposition 10.3 for `A₀`** in coefficients, for the rows `Rw`. -/
def IStarA0 [CharP k 2] (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) : Prop :=
  ∀ i, 0 < (SysD D v₀ hF Wd).P.deg (rowWt (dualWt Wd) (Rw i)) →
    (SysD D v₀ hF Wd).IStar (rowWt (dualWt Wd) (Rw i))

/-- **Corollary 10.5 for `A₀`** given Proposition 10.3 and the induction hypothesis. -/
theorem cor105_of_IStarA0 [CharP k 2] (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0)
    (hLB : LiftBelow k (Fintype.card (RayA0 D v₀)))
    (hI : IStarA0 D v₀ hF Wd Rw) : Cor105 D v₀ hF Wd Rw := by
  classical
  intro i ⟨q, hq, φ, hr, hd, hcoc, hc, hnc⟩
  set S := SysD D v₀ hF Wd
  set Θ := ΘD D v₀ hF Wd
  have hfinS : IsRepresentationFinite k (S.P.Lin k) :=
    A0TabL_isRepresentationFinite D v₀ hF (dualWt Wd) lenCoord (hdg_dual D v₀ Wd)
  have hG := ΘD_lenHom D v₀ hF Wd
  have hW := ΘD_latHom D v₀ hF Wd
  have hφ0 : φ ≠ 0 := by rintro rfl; exact hnc (RaySys.Sys.isCobdry_zero k _ q)
  have hχ : 0 < S.P.deg (rowWt (dualWt Wd) (Rw i)) := by
    rw [S.deg_eq_of_ne_zero k Θ hG hW hφ0 hd hc]; exact_mod_cast hq
  have hprim : RaySys.Sys.Prim (rowWt (dualWt Wd) (Rw i)) := by
    rw [rowWt_dual_eq Wd hWd i]; exact prim_of_basis _ _
  have hVx := S.hVx_of k Θ (VxA0 D v₀ hF Wd) (VxA0_e D v₀ hF Wd)
  exact S.cor105_of_IStar _ k Θ hfinS hχ hprim (S.hWl_of_liftBelow k hfinS hχ hprim hLB) (hI i hχ)
    hG hW (VxA0 D v₀ hF Wd) hVx hr hd hcoc hc hnc

end A0

end MeshWalk

namespace IndSkeleton

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Proposition 10.3 for the algebra `A₀` of `A`**, for every choice of rows and dual weights. -/
def IStarAR [CharP k 2] : Prop :=
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  ∀ (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWalk.MeshWt S.arTranslationQuiver ℤ)
    (Rw : ι → Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1),
    MeshWalk.IStarA0 (S.arMeshData b) v₀ hF Wd Rw

/-- **Corollary 10.5 for `A₀`**, given Proposition 10.3 and the induction hypothesis. -/
theorem cor105AR_of_IStar [CharP k 2] (hbasic : IsBasicAlgebra A)
    (hLB : LiftBelow k (Module.finrank k A)) (hI : S.IStarAR b) : S.Cor105AR b := by
  classical
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro v₀ hF ι _ _ Wd Rw hWd
  obtain ⟨n, e, he, hprim, hbas⟩ := hbasic
  haveI : Finite (MeshWalk.RayA0 (S.arMeshData b) v₀) := MeshWalk.instFiniteRayA0 (S.arMeshData b) v₀
  haveI : Fintype (MeshWalk.RayA0 (S.arMeshData b) v₀) :=
    MeshWalk.instFintypeRayA0 (S.arMeshData b) v₀
  have hB := MeshWalk.basisR (S.arMeshData b) v₀ hF
  haveI : FiniteDimensional k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ := Module.Finite.of_basis hB
  have hdim : Fintype.card (MeshWalk.RayA0 (S.arMeshData b) v₀) ≤ Module.finrank k A := by
    rw [← Module.finrank_eq_card_basis hB, (S.posFiltA b he hprim hbas).finrank_eq]
  exact MeshWalk.cor105_of_IStarA0 _ v₀ hF Wd Rw hWd
    (hLB.mono (by convert hdim using 2)) (hI v₀ hF Wd Rw)

end IndSkeleton

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Proposition 10.3** for every basic representation-finite algebra (in coefficients). -/
def IStarHyp [CharP k 2] : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ],
    IsBasicAlgebra A → IsRepresentationFinite k A → ∀ (S : IndSkeleton k A) (b : S.ArrowBases),
      S.IStarAR b

/-- **Corollary 10.5 under the induction hypothesis**, given Proposition 10.3. -/
theorem cor105Hyp_of_IStar [CharP k 2] (hI : IStarHyp k) : Cor105Hyp k :=
  fun A _ _ _ _ hbasic hA hLB S b ↦ S.cor105AR_of_IStar b hbasic hLB (hI A hbasic hA S b)

end MultiplicativeBasisDeformations
