import MultiplicativeBasisDeformations.Foundations.IntegralPsi
import MultiplicativeBasisDeformations.Foundations.Cor105A0
import MultiplicativeBasisDeformations.Foundations.PrimeTable
import MultiplicativeBasisDeformations.Foundations.PrimeCoker

/-!
# Proposition 10.3 in coefficients

`integral-deformations.tex` (`prop:integral-bockstein`): "In Lemma 10.2, the map `j` is
zero by (mod-four-mesh-annihilator). Injectivity of `Ψ₄` gives `i_* = 0`."

In coefficients (`RaySys.Sys.IStar`): for a cochain `z` of character `χ` over `𝒪 = ℤ/4` with
`d₂z ∈ 2C³`, the cochain `2z` is `d₁` of a cochain. Its reduction `z̄` is a cocycle over `𝔽₂`;
the cocycle `Φ₂(2z) = 2Φ₂(z)` of `A⁽⁴⁾ = 𝒪P` is twice the cocycle `Φ₂(z̄)` of
`A⁽²⁾ ≅ 𝔽₂P`, a coboundary by `MeshWalk.exists_hcobdry_twice`, and the coefficients of a
coboundary are `d₁` of coefficients (`coef_of_hcobdry`). For `A` this runs in the prime-field
model `C⁽²⁾` with `Θ₂ : 𝔽₂P ≅ A⁽²⁾` (`IndSkeleton.tab₂`) and the rows of
`IndSkeleton.prime_cokerSpan`. This proves `IStarHyp`, hence `Cor105Hyp` (`cor105Hyp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (χ : L)

/-! ### Reduction of the realization -/

section Red

variable {O K : Type u} [CommRing O] [Nontrivial O] [CommRing K] [Nontrivial K] (red : O →+* K)

theorem redLin_vecW (o : Option R) : S.P.toMult.redLin red (S.vecW O o) = S.vecW K o := by
  cases o with
  | none => exact map_zero _
  | some t => exact S.P.toMult.redLin_b red t

theorem redLin_Φ2_b (c : S.C2 χ O) (u v : R) :
    S.P.toMult.redLin red (S.Φ2 χ O c (S.P.b O u) (S.P.b O v)) =
      S.Φ2 χ K (red ∘ c) (S.P.b K u) (S.P.b K v) := by
  classical
  rw [Φ2_b, Φ2_b]
  split_ifs
  · rw [Mult.redLin_smul, redLin_vecW]; rfl
  · exact map_zero _

theorem redLin_eq_sum (a : S.P.Lin O) :
    S.P.toMult.redLin red a = ∑ u, red ((S.P.basis O).repr a u) • S.P.b K u := by
  conv_lhs => rw [← (S.P.basis O).sum_repr a]
  simp only [map_sum, Mult.redLin_smul, Mult.basis_apply, Mult.redLin_b]

/-- **Reduction of coefficients commutes with `Φ₂`.** -/
theorem redLin_Φ2 (c : S.C2 χ O) (a b : S.P.Lin O) :
    S.P.toMult.redLin red (S.Φ2 χ O c a b) =
      S.Φ2 χ K (red ∘ c) (S.P.toMult.redLin red a) (S.P.toMult.redLin red b) := by
  conv_rhs => rw [redLin_eq_sum S red a, redLin_eq_sum S red b]
  conv_lhs => rw [← (S.P.basis O).sum_repr a, ← (S.P.basis O).sum_repr b]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [Mult.basis_apply, Mult.redLin_smul, map_sum, redLin_Φ2_b]

end Red

variable (O : Type u) [CommRing O] [Nontrivial O]

theorem Φ2_smul (t : O) (c : S.C2 χ O) : S.Φ2 χ O (t • c) = t • S.Φ2 χ O c := by
  classical
  refine (S.P.basis O).ext fun u ↦ (S.P.basis O).ext fun v ↦ ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, Mult.basis_apply, Mult.basis_apply, Φ2_b, Φ2_b]
  split_ifs
  · rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  · rw [smul_zero]

theorem isHCocycle_transp {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]
    (Θ : S.P.Lin k ≃ₐ[k] Λ) {μ : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k}
    (hμ : GExt.IsHCocycle μ) : GExt.IsHCocycle (S.transp k Θ μ) := by
  intro a b c
  simp only [transp_apply]
  apply Θ.symm.injective
  simp only [map_sub, map_add, map_mul, AlgEquiv.symm_apply_apply, map_zero]
  exact hμ _ _ _

end Sys

end RaySys

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift RaySys

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R LL : Type} [AddCommGroup LL] [DecidableEq LL] [Fintype R] [DecidableEq R]
  (S : Sys D.PV R LL) (T : TabIso D S.P.toMult) (hT : ∀ r, T.d r = S.P.deg (S.P.wt r))

include hT in
theorem Φ2_b_isHom (χ : LL) (hχ : 0 ≤ S.P.deg χ) (z : S.C2 χ 𝔽₂) (u v : R) :
    (galgA0 D (hfin2 (c := c))).gr.IsHom (T.d u + T.d v + S.P.deg χ)
      (T.Θ (S.Φ2 χ 𝔽₂ z (S.P.b 𝔽₂ u) (S.P.b 𝔽₂ v))) := by
  classical
  rw [Sys.Φ2_b]
  split_ifs with hI
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hI.2.2.2
    rw [ht, Sys.vecW_some, map_smul]
    refine (galgA0 D (hfin2 (c := c))).gr.isHom_smul _ ?_
    have hw := (S.w2_eq_some χ).1 ht
    have e : T.d u + T.d v + S.P.deg χ = ((T.d t).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (T.d_nonneg t), hT, hT, hT, hw.2.2, map_add, map_add]
    rw [e, galgA0_isHom_len']
    exact T.Θ_hom t
  · rw [map_zero]; exact (galgA0 D (hfin2 (c := c))).gr.isHom_zero _

include hT in
/-- **The cocycle `Φ₂(z)` on `A⁽²⁾` has degree `deg χ`.** -/
theorem hdeg_transp_Φ2 (χ : LL) (hχ : 0 ≤ S.P.deg χ) (z : S.C2 χ 𝔽₂) :
    HDeg (galgA0 D (hfin2 (c := c))) (S.transp 𝔽₂ T.Θ (S.Φ2 χ 𝔽₂ z)) (S.P.deg χ) := by
  intro p p' a b ha hb
  rcases lt_or_ge p 0 with hp | hp
  · rw [(galgA0_isHom_neg D (hfin2 (c := c)) hp a).1 ha, map_zero, LinearMap.zero_apply]
    exact (galgA0 D (hfin2 (c := c))).gr.isHom_zero _
  rcases lt_or_ge p' 0 with hp' | hp'
  · rw [(galgA0_isHom_neg D (hfin2 (c := c)) hp' b).1 hb, map_zero]
    exact (galgA0 D (hfin2 (c := c))).gr.isHom_zero _
  obtain ⟨P, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨P', rfl⟩ := Int.eq_ofNat_of_zero_le hp'
  have ha' := (galgA0_isHom_len' P a).1 ha
  have hb' := (galgA0_isHom_len' P' b).1 hb
  rw [Sys.transp_apply, ← (S.P.basis 𝔽₂).sum_repr (T.Θ.symm a),
    ← (S.P.basis 𝔽₂).sum_repr (T.Θ.symm b)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine (galgA0 D (hfin2 (c := c))).gr.isHom_sum _ _ fun v _ ↦ ?_
  by_cases hv : T.d v = P'
  · refine (galgA0 D (hfin2 (c := c))).gr.isHom_smul _
      ((galgA0 D (hfin2 (c := c))).gr.isHom_sum _ _ fun u _ ↦ ?_)
    by_cases hu : T.d u = P
    · refine (galgA0 D (hfin2 (c := c))).gr.isHom_smul _ ?_
      rw [RaySys.Mult.basis_apply, RaySys.Mult.basis_apply, ← hu, ← hv]
      exact Φ2_b_isHom S T hT χ hχ z u v
    · rw [repr_Θ_symm_eq_zero T P a ha' u hu, zero_smul]
      exact (galgA0 D (hfin2 (c := c))).gr.isHom_zero _
  · rw [repr_Θ_symm_eq_zero T P' b hb' v hv, zero_smul]
    exact (galgA0 D (hfin2 (c := c))).gr.isHom_zero _

theorem πO_Φ2 (χ : LL) (z : S.C2 χ (ZMod 4)) (a b : S.P.Lin (ZMod 4)) :
    πO T (S.Φ2 χ (ZMod 4) z a b) =
      S.transp 𝔽₂ T.Θ (S.Φ2 χ 𝔽₂ (Z4.red ∘ z)) (πO T a) (πO T b) := by
  change T.Θ (S.P.toMult.redLin Z4.red (S.Φ2 χ (ZMod 4) z a b)) =
    T.Θ (S.Φ2 χ 𝔽₂ (Z4.red ∘ z) (T.Θ.symm (T.Θ (S.P.toMult.redLin Z4.red a)))
      (T.Θ.symm (T.Θ (S.P.toMult.redLin Z4.red b))))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, Sys.redLin_Φ2]

variable (J : InjData D) (h1 : DegOne D) {RS : RowSet Q} (hspan : CokerSpan c RS)
  (htwo : TwoRows.{0} Q RS)

include hT J h1 hspan htwo in
/-- **Proposition 10.3** in coefficients (`prop:integral-bockstein`). -/
theorem istar (χ : LL) (hχ : 0 < S.P.deg χ) : S.IStar χ := by
  rintro z ⟨w, hw⟩
  have hd2 : ∀ t : S.T3 χ,
      S.d2raw χ (ZMod 4) z t.1.1 t.1.2.1 t.1.2.2 = (2 : ZMod 4) * w t := fun t ↦ congrFun hw t
  -- the reduction is a cocycle
  have hc : GExt.IsHCocycle (S.Φ2 χ 𝔽₂ (Z4.red ∘ z)) := by
    refine (S.isHCocycle_Φ2_iff χ 𝔽₂ _).2 fun u v x hx ↦ ?_
    have := S.d2raw_map χ (ZMod 4) Z4.red.toAddMonoidHom z u v x
    change S.d2raw χ 𝔽₂ (Z4.red ∘ z) u v x = _ at this
    rw [this, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, hd2 ⟨(u, v, x), hx⟩, map_mul,
      Z4.red_two, zero_mul]
  -- twice `z` is a cocycle over `𝒪`
  have hcO : GExt.IsHCocycle (S.Φ2 χ (ZMod 4) ((2 : ZMod 4) • z)) := by
    refine (S.isHCocycle_Φ2_iff χ (ZMod 4) _).2 fun u v x hx ↦ ?_
    rw [S.d2raw_smul, hd2 ⟨(u, v, x), hx⟩, ← mul_assoc, Z4.four_eq_zero, zero_mul]
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le hχ.le
  have hq1 : 1 ≤ q := by omega
  have hdeg := hdeg_transp_Φ2 S T hT χ hχ.le (Z4.red ∘ z)
  rw [hq] at hdeg
  have hμO : ∀ a b x, πO T x =
      S.transp 𝔽₂ T.Θ (S.Φ2 χ 𝔽₂ (Z4.red ∘ z)) (πO T a) (πO T b) →
      S.Φ2 χ (ZMod 4) ((2 : ZMod 4) • z) a b = (2 : ZMod 4) • x := by
    intro a b x hx
    rw [Sys.Φ2_smul, LinearMap.smul_apply, LinearMap.smul_apply]
    obtain ⟨y, hy⟩ := πO_ker T (S.Φ2 χ (ZMod 4) z a b - x)
      (by rw [map_sub, πO_Φ2, hx, sub_self])
    rw [← sub_eq_zero, ← smul_sub, hy, smul_smul, Z4.four_eq_zero, zero_smul]
  obtain ⟨h, hh⟩ := exists_hcobdry_twice (T := T) J h1 hspan htwo hq1
    (S.isHCocycle_transp T.Θ hc) hdeg hμO hcO
  exact ⟨S.coef1 (ZMod 4) h, S.coef_of_hcobdry (ZMod 4) _ h hh⟩

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u'

variable (k : Type u') [Field k] [IsAlgClosed k]

/-- **Proposition 10.3** for every basic representation-finite algebra (in coefficients). -/
theorem istarHyp [CharP k 2] : IStarHyp k := by
  classical
  intro A _ _ _ _ hbasic hA S b
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : ∀ x y : S.ARVertex, FiniteDimensional (ZMod 2)
      (MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) y) := S.prime_fd b
  intro v₀ hF ι _ _ Wd Rw i hχ
  obtain ⟨RS, hspan, htwo⟩ := S.prime_cokerSpan b
  exact MeshWalk.istar (MeshWalk.SysD (S.arMeshData b) v₀ hF Wd) (S.tab₂ b v₀ hF Wd)
    (fun _ ↦ rfl) (S.primeInjData b) (S.primeDegOne b) hspan htwo _ hχ

section Beta

attribute [local instance] Classical.decEq

/-- **Proposition 10.3** (`prop:integral-bockstein`), as stated: for every basic
representation-finite algebra in characteristic two and every positive character `χ` of the
dual weights, the connecting map is surjective — every two-cocycle `c` over `𝔽₂` of character
`χ` (of `A⁽²⁾ ≅ 𝔽₂P`) is `(dδ)/2` for a one-cochain `δ` over `ℤ/4` whose reduction is a
derivation. -/
theorem integralBockstein [CharP k 2] (A : Type u') [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ] (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A)
    (S : IndSkeleton k A) (b : S.ArrowBases) :
    haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    haveI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    ∀ (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
      {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWalk.MeshWt S.arTranslationQuiver ℤ)
      (Rw : ι → Σ x : S.arTranslationQuiver.nonprojective,
        Quiver.Path (S.arTranslationQuiver.tau x).1 x.1) (i : ι),
      0 < (MeshWalk.SysD (S.arMeshData b) v₀ hF Wd).P.deg
        (MeshWalk.rowWt (MeshWalk.dualWt Wd) (Rw i)) →
      ∀ c, (MeshWalk.SysD (S.arMeshData b) v₀ hF Wd).d2L
          (MeshWalk.rowWt (MeshWalk.dualWt Wd) (Rw i)) (ZMod 2) c = 0 →
        ∃ δ, (MeshWalk.SysD (S.arMeshData b) v₀ hF Wd).d1L
            (MeshWalk.rowWt (MeshWalk.dualWt Wd) (Rw i)) (ZMod 4) δ = (2 : ZMod 4) • (Z4.lift ∘ c) ∧
          (MeshWalk.SysD (S.arMeshData b) v₀ hF Wd).d1
            (MeshWalk.rowWt (MeshWalk.dualWt Wd) (Rw i)) (ZMod 2) (Z4.red ∘ δ) = 0 := by
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro v₀ hF ι _ _ Wd Rw i hχ c hc
  exact RaySys.Sys.beta_surjective (MeshWalk.SysD (S.arMeshData b) v₀ hF Wd) _
    (istarHyp k A hbasic hA S b v₀ hF Wd Rw i hχ) c hc

end Beta

/-- **Corollary 10.5 under the induction hypothesis** (`cor:zero-supported-coverage`). -/
theorem cor105Hyp [CharP k 2] : Cor105Hyp k := cor105Hyp_of_IStar k (istarHyp k)

end MultiplicativeBasisDeformations
