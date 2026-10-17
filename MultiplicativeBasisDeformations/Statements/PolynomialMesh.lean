import MultiplicativeBasisDeformations.Refinements.PolynomialMeshComparison
import MultiplicativeBasisDeformations.Foundations.FamilyCriterionGen
import MultiplicativeBasisDeformations.Foundations.Char2Basic

/-!
# Proposition 12.8 for `A₀` and for a representation-finite algebra

`prop:polynomial-mesh-comparison` (`deformation-refinements.tex`): "Let `m + Σ_{i∈I} t_i μ_i`
be an associative family satisfying the hypotheses of Proposition 7.9, such as
eq. selected-binary-family, now indexed by `I = I₀`. There are polynomial lifts […] for which the
retained mesh coefficients are `F_i(t) = a_i t_i`, `a_i ∈ k^*`. After every specialization to
`k`, these modules exhaust the indecomposables of the fibre algebra."

In the setting of Proposition 7.9 (`familyCriterion_A0`): the rows `R_i` and dual mesh weights of
Proposition 6.1 (rows of length at least three, the degree `2s + 2` of Proposition 6.1), the
characters `χ_i` (`rowChar`), and a family `μ_i` indexed by all rows with the hypotheses of
Proposition 7.9 (normalized relative, of character `χ_i`, not a coboundary, associative family).
The internal degree `len R_i − 2` of `μ_i` is derived from its character
(`RaySys.Sys.hasDeg₂_of_char`), the coordinates `χ_i ↦ e_i` are the dual weights, and the
generic `polynomialMeshComparison` applies (`polynomialMeshComparison_A0`); for `A₀` of a
representation-finite algebra the mesh hypotheses are the Auslander–Reiten ones
(`IndSkeleton.polynomialMeshComparison_ar`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration MGr PathReal FlatPert

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt Q ℤ)
  (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)

/-- The dual-weight coordinates `ℤ^ι × ℤ → ℤ^ι`. -/
def dualCoords : DLat ι →+ (ι → ℤ) := AddMonoidHom.fst (ι → ℤ) ℤ

theorem dualCoords_rowChar (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0)
    (i : ι) : dualCoords (rowChar Wd Rw i) = Pi.single i 1 := by
  funext j
  show (fun l : DLat ι ↦ (l : (ι → ℤ) × ℤ).1 j) (rowChar Wd Rw i) = _
  simp only [rowChar, rowWt_dualWt]
  rw [hWd, Pi.single_apply]
  simp only [eq_comm]

variable [Infinite k]

/-- The conclusion of Proposition 12.8 for the family `μ` with the rows `Rw` and characters
`rowChar`. -/
def PolyMeshStmt (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (μ : ι → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) : Prop :=
    ∃ (H : FamHyp D (hfinObj (c := c)) μ (fun i ↦ (Rw i).2.length - 2))
      (hχ : ∀ i, HasChar (dualWt Wd) (hfinObj (c := c)) D (rowChar Wd Rw i) (μ i))
      (hco : ∀ i, dualCoords (rowChar Wd Rw i) = Pi.single i 1)
      (hlen : ∀ i, (Rw i).2.length = (Rw i).2.length - 2 + 2)
      (hwt : ∀ i, (dualWt Wd).pw (Rw i).2 = (dualWt Wd).ν (Rw i).1 + rowChar Wd Rw i)
      (A : ArrowL H (dualWt Wd) hχ J h1 hco) (a : ι → k) (N : ℕ), (∀ i, a i ≠ 0) ∧
      (∀ X : V, IsPoly fun t ↦ (famAct H (dualWt Wd) hχ J h1 hco t X).tot) ∧
      (∀ {y x : V} (b : y ⟶ x), IsPoly fun t ↦ toLin (twArrow A t b)) ∧
      ∀ t : ι → k,
        (∀ x, realizeR k (twArrow A t) _ _ (meshRelation c x) =
          ∑ i, (a i * t i) • realizeR k (twArrow A t) _ _ (rowQ (k := k) Rw i x)) ∧
        (∀ {y x : V} (f : FB (famLifts H (dualWt Wd) hχ J h1 hco t) y ⟶
            FB (famLifts H (dualWt Wd) hχ J h1 hco t) x),
          ∃ F, realizeR k (twArrow A t) y x F = f) ∧
        (∀ {y x : V} (F : Hm k y x), realizeR k (twArrow A t) y x F = 0 ↔
          F ∈ (idealB (meshPres c) (ftp Rw a t) (ftp_mem (H := H) hlen hwt a t) N).I y x) ∧
        -- the lifted modules are pairwise nonisomorphic indecomposables
        (∀ x, IsFiniteIndecomposable k (Fib (famAM H t))
            (FB (famLifts H (dualWt Wd) hχ J h1 hco t) x)) ∧
        (∀ x y, Nonempty (FB (famLifts H (dualWt Wd) hχ J h1 hco t) x ≅
            FB (famLifts H (dualWt Wd) hχ J h1 hco t) y) → x = y) ∧
        (∀ M : RightModuleCat (Fib (famAM H t)), IsFiniteIndecomposable k (Fib (famAM H t)) M →
          ∃ x, Nonempty (M ≅ FB (famLifts H (dualWt Wd) hχ J h1 hco t) x))

/-- **Proposition 12.8 on `A₀`**, in the setting of Proposition 7.9. -/
theorem polynomialMeshComparison_A0 (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y)
    (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0)
    (hS : CokerSpan c (Set.range Rw)) (hlen3 : ∀ i, 3 ≤ (Rw i).2.length)
    (μ : ι → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (hrel : ∀ i, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) (μ i))
    (hchar : ∀ i, (latA0 (dualWt Wd) (hfinObj (c := c)) D).Char₂ (rowChar Wd Rw i) (μ i))
    (hnz : ∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f)
    (hassoc : ∀ (t : ι → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMul D μ t (famMul D μ t a b) z = famMul D μ t a (famMul D μ t b z)) :
    PolyMeshStmt D Wd Rw J h1 μ := by
  set Sy := SysD D v₀ hF Wd
  set Θ := ΘD D v₀ hF Wd
  have hG := ΘD_lenHom D v₀ hF Wd
  have hW := ΘD_latHom D v₀ hF Wd
  have hdegχ : ∀ i, Sy.P.deg (rowChar Wd Rw i) = ((Rw i).2.length : ℤ) - 2 := by
    intro i
    change lenCoord (rowWt (dualWt Wd) (Rw i)) = _
    rw [rowWt_dualWt]
    rfl
  have hdeg : ∀ i, LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) ((Rw i).2.length - 2) (μ i) := by
    intro i
    have h := Sy.hasDeg₂_of_char k Θ hG hW (by rw [hdegχ]; have := hlen3 i; omega) (hchar i)
    have e : (Sy.P.deg (rowChar Wd Rw i)).toNat = (Rw i).2.length - 2 := by
      rw [hdegχ]; have := hlen3 i; omega
    rwa [e] at h
  have hone' : ∀ i a, μ i 1 a = 0 := by
    intro i a
    rw [← (VxA0 D v₀ hF Wd).complete.complete, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun j _ ↦ (hrel i).unitL j a
  have hone'' : ∀ i a, μ i a 1 = 0 := by
    intro i a
    rw [← (VxA0 D v₀ hF Wd).complete.complete, map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ (hrel i).unitR j a
  have H : FamHyp D (hfinObj (c := c)) μ (fun i ↦ (Rw i).2.length - 2) :=
    ⟨fun i ↦ by have := hlen3 i; omega, fun i ↦ hDeg_of_hasDeg₂ (hfinObj (c := c)) (hdeg i),
      hone', hone'', hassoc⟩
  have hχ : ∀ i, HasChar (dualWt Wd) (hfinObj (c := c)) D (rowChar Wd Rw i) (μ i) :=
    fun i α β a b ha hb ↦ hchar i α β a b ha hb
  have hco : ∀ i, dualCoords (rowChar Wd Rw i) = Pi.single i 1 := dualCoords_rowChar Wd Rw hWd
  have hlen : ∀ i, (Rw i).2.length = (Rw i).2.length - 2 + 2 := fun i ↦ by
    have := hlen3 i; omega
  have hwt : ∀ i, (dualWt Wd).pw (Rw i).2 = (dualWt Wd).ν (Rw i).1 + rowChar Wd Rw i := fun i ↦ by
    simp only [rowChar, rowWt]; abel
  have hnc : ∀ j, ¬ ∃ Hc : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
      (∀ p a, (galgA0 D (hfinObj (c := c))).gr.IsHom p a →
        (galgA0 D (hfinObj (c := c))).gr.IsHom (p + ((Rw j).2.length - 2 : ℕ)) (Hc a)) ∧
        μ j = hcobdry Hc := by
    rintro j ⟨Hc, -, h⟩
    exact hnz j ⟨Hc, h⟩
  exact ⟨H, hχ, hco, hlen, hwt, polynomialMeshComparison H (dualWt Wd) hχ hco J h1 hrad Rw hlen hwt
    hS hnc⟩

/-! ### Characters in any lattice -/

section Gen

variable {Lt : Type} [AddCommGroup Lt] (W : MeshWt Q Lt) (dg : Lt →+ ℤ)
  (hdg : dg.comp (W.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D)
  (coords : Lt →+ (ι → ℤ))

/-- The conclusion of Proposition 12.8 for the family `μ` with the rows `Rw` and characters
`rowChar`. -/
def PolyMeshStmtG (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (μ : ι → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) : Prop :=
    ∃ (H : FamHyp D (hfinObj (c := c)) μ (fun i ↦ (Rw i).2.length - 2))
      (hχ : ∀ i, HasChar W (hfinObj (c := c)) D (rowCharG W Rw i) (μ i))
      (hco : ∀ i, coords (rowCharG W Rw i) = Pi.single i 1)
      (hlen : ∀ i, (Rw i).2.length = (Rw i).2.length - 2 + 2)
      (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + rowCharG W Rw i)
      (A : ArrowL H W hχ J h1 hco) (a : ι → k) (N : ℕ), (∀ i, a i ≠ 0) ∧
      (∀ X : V, IsPoly fun t ↦ (famAct H W hχ J h1 hco t X).tot) ∧
      (∀ {y x : V} (b : y ⟶ x), IsPoly fun t ↦ toLin (twArrow A t b)) ∧
      ∀ t : ι → k,
        (∀ x, realizeR k (twArrow A t) _ _ (meshRelation c x) =
          ∑ i, (a i * t i) • realizeR k (twArrow A t) _ _ (rowQ (k := k) Rw i x)) ∧
        (∀ {y x : V} (f : FB (famLifts H W hχ J h1 hco t) y ⟶
            FB (famLifts H W hχ J h1 hco t) x),
          ∃ F, realizeR k (twArrow A t) y x F = f) ∧
        (∀ {y x : V} (F : Hm k y x), realizeR k (twArrow A t) y x F = 0 ↔
          F ∈ (idealB (meshPres c) (ftp Rw a t) (ftp_mem (H := H) hlen hwt a t) N).I y x) ∧
        -- the lifted modules are pairwise nonisomorphic indecomposables
        (∀ x, IsFiniteIndecomposable k (Fib (famAM H t))
            (FB (famLifts H W hχ J h1 hco t) x)) ∧
        (∀ x y, Nonempty (FB (famLifts H W hχ J h1 hco t) x ≅
            FB (famLifts H W hχ J h1 hco t) y) → x = y) ∧
        (∀ M : RightModuleCat (Fib (famAM H t)), IsFiniteIndecomposable k (Fib (famAM H t)) M →
          ∃ x, Nonempty (M ≅ FB (famLifts H W hχ J h1 hco t) x))

/-- **Proposition 12.8 on `A₀`**, in the setting of Proposition 7.9. -/
theorem polynomialMeshComparison_G (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y)
    (hco : ∀ i, coords (rowCharG W Rw i) = Pi.single i 1)
    (hS : CokerSpan c (Set.range Rw)) (hlen3 : ∀ i, 3 ≤ (Rw i).2.length)
    (hdgrow : ∀ i, dg (rowCharG W Rw i) = ((Rw i).2.length : ℤ) - 2)
    (μ : ι → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (hrel : ∀ i, LenGrading.IsRel₂ (VxG D v₀ hF W dg hdg) (μ i))
    (hchar : ∀ i, (latA0 W (hfinObj (c := c)) D).Char₂ (rowCharG W Rw i) (μ i))
    (hnz : ∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f)
    (hassoc : ∀ (t : ι → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMul D μ t (famMul D μ t a b) z = famMul D μ t a (famMul D μ t b z)) :
    PolyMeshStmtG D (W := W) (coords := coords) (Rw := Rw) J h1 μ := by
  set Sy := SysG D v₀ hF W dg hdg
  set Θ := ΘG D v₀ hF W dg hdg
  have hG := ΘG_lenHom D v₀ hF W dg hdg
  have hW := ΘG_latHom D v₀ hF W dg hdg
  have hdegχ : ∀ i, Sy.P.deg (rowCharG W Rw i) = ((Rw i).2.length : ℤ) - 2 := hdgrow
  have hdeg : ∀ i, LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) ((Rw i).2.length - 2) (μ i) := by
    intro i
    have h := Sy.hasDeg₂_of_char k Θ hG hW (by rw [hdegχ]; have := hlen3 i; omega) (hchar i)
    have e : (Sy.P.deg (rowCharG W Rw i)).toNat = (Rw i).2.length - 2 := by
      rw [hdegχ]; have := hlen3 i; omega
    rwa [e] at h
  have hone' : ∀ i a, μ i 1 a = 0 := by
    intro i a
    rw [← (VxG D v₀ hF W dg hdg).complete.complete, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun j _ ↦ (hrel i).unitL j a
  have hone'' : ∀ i a, μ i a 1 = 0 := by
    intro i a
    rw [← (VxG D v₀ hF W dg hdg).complete.complete, map_sum]
    exact Finset.sum_eq_zero fun j _ ↦ (hrel i).unitR j a
  have H : FamHyp D (hfinObj (c := c)) μ (fun i ↦ (Rw i).2.length - 2) :=
    ⟨fun i ↦ by have := hlen3 i; omega, fun i ↦ hDeg_of_hasDeg₂ (hfinObj (c := c)) (hdeg i),
      hone', hone'', hassoc⟩
  have hχ : ∀ i, HasChar W (hfinObj (c := c)) D (rowCharG W Rw i) (μ i) :=
    fun i α β a b ha hb ↦ hchar i α β a b ha hb
  have hlen : ∀ i, (Rw i).2.length = (Rw i).2.length - 2 + 2 := fun i ↦ by
    have := hlen3 i; omega
  have hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + rowCharG W Rw i := fun i ↦ by
    simp only [rowCharG, rowWt]; abel
  have hnc : ∀ j, ¬ ∃ Hc : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
      (∀ p a, (galgA0 D (hfinObj (c := c))).gr.IsHom p a →
        (galgA0 D (hfinObj (c := c))).gr.IsHom (p + ((Rw j).2.length - 2 : ℕ)) (Hc a)) ∧
        μ j = hcobdry Hc := by
    rintro j ⟨Hc, -, h⟩
    exact hnz j ⟨Hc, h⟩
  exact ⟨H, hχ, hco, hlen, hwt, polynomialMeshComparison H W hχ hco J h1 hrad Rw hlen hwt
    hS hnc⟩

end Gen

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

open MeshWalk

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Proposition 12.8** (`prop:polynomial-mesh-comparison`) for `A₀` of a basic
representation-finite algebra `A`: for the rows and dual weights of Proposition 6.1 and a family
`μ_i` indexed by all rows with the hypotheses of Proposition 7.9, the conclusions of
`polynomialMeshComparison` hold (polynomial lifts, retained mesh coefficients `a_i t_i` with
`a_i ≠ 0`, the mesh presentation of every fibre, and exhaustion of its indecomposables). -/
theorem polynomialMeshComparison_ar (v₀ : S.ARVertex) {ι : Type} [Fintype ι]
    [DecidableEq ι] (Wd : ι → MeshWt S.arTranslationQuiver ℤ)
    (Rw : ι → Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    (∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0) →
    ScalarMeshCategory.CokerSpan (S.arCoefficients b) (Set.range Rw) →
    (∀ i, 3 ≤ (Rw i).2.length) →
    ∀ μ : ι → (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
        (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ,
    (∀ i, LenGrading.IsRel₂ (VxA0 (S.arMeshData b) v₀ hF Wd) (μ i)) →
    (∀ i, (latA0 (dualWt Wd) (hfinObj (c := S.arCoefficients b)) (S.arMeshData b)).Char₂
      (rowChar Wd Rw i) (μ i)) →
    (∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f) →
    (∀ (t : ι → k) (a b' z : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ),
      famMul (S.arMeshData b) μ t (famMul (S.arMeshData b) μ t a b') z =
        famMul (S.arMeshData b) μ t a (famMul (S.arMeshData b) μ t b' z)) →
    PolyMeshStmt (S.arMeshData b) Wd Rw (S.arInjData b) (S.arDegOne b) μ := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  intro hF hWd hS hlen3 μ hrel hchar hnz hassoc
  exact polynomialMeshComparison_A0 (S.arMeshData b) v₀ hF Wd Rw (S.arInjData b) (S.arDegOne b)
    (S.arHrad b) hWd hS hlen3 μ hrel hchar hnz hassoc

end MultiplicativeBasisDeformations.IndSkeleton
