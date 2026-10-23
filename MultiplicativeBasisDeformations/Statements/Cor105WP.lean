module

public import MultiplicativeBasisDeformations.Statements.FamilyCriterionWP
public import MultiplicativeBasisDeformations.Foundations.Cor105A0
public import MultiplicativeBasisDeformations.Foundations.Prop103

/-!
# Corollary 10.5 with the residual characters in `W(P)`

`cor:zero-supported-coverage` (`integral-deformations.tex`): "Assume the smaller-table lifting
hypothesis of Theorem 9.1. Then every nonzero line `HH²(A₀)_{χ_i}`, with `i ∈ I₀`, has a nonzero
representative supported on composable pairs `(r, s)` with `rs = 0` and `r * s ≠ 0` […]. Its
value at such a pair lies in the line `U_{r*s}`."

The statement of `Char2A0.Cor105` and its proof (`Cor105A0.lean`) for an arbitrary mesh weight `W`
with values in a lattice and a degree map (`Cor105G`, `IStarG`, `cor105G_of_IStar`; the characters
are only required to be primitive), and the instance for `A₀` of a basic connected
representation-finite algebra in characteristic two with the characters in `L = W(P)`
(`IndSkeleton.zeroSupportedCoverage_WP`): Proposition 10.3 for this weight by the generic
`MeshWalk.istar` with the prime-field table, and primitivity from the integer basis of
Proposition 7.5.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

section Gen

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {Lt : Type} [AddCommGroup Lt] (W : MeshWt Q Lt) (dg : Lt →+ ℤ)
  (hdg : dg.comp (W.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D)
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Corollary 10.5 for `A₀`** with characters `rowWt W (Rw i)`. -/
def Cor105G (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) : Prop :=
  ∀ i, (∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ (VxG D v₀ hF W dg hdg) φ ∧
        LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) q φ ∧
        LenGrading.IsCocycle₂ φ ∧ (latA0 W (hfinObj (c := c)) D).Char₂
          (rowWt W (Rw i)) φ ∧
        ¬ RaySys.Sys.IsCobdry k (lenA0 D (hfinObj (c := c))) q φ) →
      ∃ a : RayA0 D v₀ → RayA0 D v₀ → k, (SysG D v₀ hF W dg hdg).EdgeOK k a ∧
        (∀ z : RayA0 D v₀ × RayA0 D v₀, a z.1 z.2 ≠ 0 → (SysG D v₀ hF W dg hdg).eps z.1 z.2 ≠ 0 →
          (SysG D v₀ hF W dg hdg).pairChar z = rowWt W (Rw i)) ∧
        ¬ RaySys.Sys.IsCobdry k (lenA0 D (hfinObj (c := c)))
          ((SysG D v₀ hF W dg hdg).P.deg (rowWt W (Rw i))).toNat
          ((SysG D v₀ hF W dg hdg).transp k (ΘG D v₀ hF W dg hdg) ((SysG D v₀ hF W dg hdg).coch k a))

/-- **Proposition 10.3 for `A₀`** in coefficients, for the rows `Rw`. -/
def IStarG [CharP k 2] (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) : Prop :=
  ∀ i, 0 < (SysG D v₀ hF W dg hdg).P.deg (rowWt W (Rw i)) →
    (SysG D v₀ hF W dg hdg).IStar (rowWt W (Rw i))

/-- **Corollary 10.5 for `A₀`** given Proposition 10.3 and the induction hypothesis. -/
theorem cor105G_of_IStar [CharP k 2] (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hprimR : ∀ i, RaySys.Sys.Prim (rowWt W (Rw i)))
    (hLB : LiftBelow k (Fintype.card (RayA0 D v₀)))
    (hI : IStarG D v₀ hF W dg hdg Rw) : Cor105G D v₀ hF W dg hdg Rw := by
  classical
  intro i ⟨q, hq, φ, hr, hd, hcoc, hc, hnc⟩
  set S := SysG D v₀ hF W dg hdg
  set Θ := ΘG D v₀ hF W dg hdg
  have hfinS : IsRepresentationFinite k (S.P.Lin k) :=
    A0TabL_isRepresentationFinite D v₀ hF W dg hdg
  have hG := ΘG_lenHom D v₀ hF W dg hdg
  have hW := ΘG_latHom D v₀ hF W dg hdg
  have hφ0 : φ ≠ 0 := by rintro rfl; exact hnc (RaySys.Sys.isCobdry_zero k _ q)
  have hχ : 0 < S.P.deg (rowWt W (Rw i)) := by
    rw [S.deg_eq_of_ne_zero k Θ hG hW hφ0 hd hc]; exact_mod_cast hq
  have hprim : RaySys.Sys.Prim (rowWt W (Rw i)) := hprimR i
  have hVx := S.hVx_of k Θ (VxG D v₀ hF W dg hdg) (VxG_e D v₀ hF W dg hdg)
  exact S.cor105_of_IStar _ k Θ hfinS hχ hprim (S.hWl_of_liftBelow k hfinS hχ hprim hLB) (hI i hχ)
    hG hW (VxG D v₀ hF W dg hdg) hVx hr hd hcoc hc hnc

end Gen

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

open MeshWalk

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **Corollary 10.5** (`cor:zero-supported-coverage`) with the residual characters in `W(P)`:
for a basic connected representation-finite algebra in characteristic two, under the
smaller-table lifting hypothesis of Theorem 9.1 (`LiftBelow`), for the rows of Proposition 6.1
and the universal mesh weight, every row with a nonzero class in `HH²(A₀)_{χ_i}` (`i ∈ I₀`) has a
non-coboundary representative supported on the pairs with zero product and nonzero stem product,
with values in the stem lines (`Cor105G`). -/
theorem zeroSupportedCoverage_WP [CharP k 2] (hbasic : IsBasicAlgebra A) (hconn : IsConnectedRing A)
    (v₀ : S.ARVertex) (hLB : LiftBelow k (Module.finrank k A)) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    let dg := (lenW (Q := S.arTranslationQuiver)).res (v₀ := v₀) (S.arCoefficients b)
      (S.arMeshData b)
    ∃ (m : ℕ) (Rw : Fin m → Σ x : S.arTranslationQuiver.nonprojective,
        Quiver.Path (S.arTranslationQuiver.tau x).1 x.1)
      (Wu : MeshWt S.arTranslationQuiver
        (WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)))
      (hdg : dg.comp (Wu.res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)) =
        (lenW (Q := S.arTranslationQuiver)).res (S.arCoefficients b) (S.arMeshData b)),
      Wu.res (S.arCoefficients b) (S.arMeshData b) = AddMonoidHom.id _ ∧
      Function.Injective Rw ∧ (∀ i, (Rw i).1.1 ∈ S.arTranslationQuiver.periodic) ∧
      (∀ i j, (Rw j).1.1 ∈ S.arTranslationQuiver.component (Rw i).1.1 → i = j) ∧
      ScalarMeshCategory.CokerSpan (S.arCoefficients b) (Set.range Rw) ∧
      Cor105G (S.arMeshData b) v₀ hF Wu dg hdg Rw := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : ∀ x y : S.ARVertex, FiniteDimensional (ZMod 2)
      (MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) y) := S.prime_fd b
  intro hF dg
  obtain ⟨m, Rw, Wu, hWu, hRinj, hper, hcomp, hS, -, -, ⟨κ, bL, jι, hjι, hb⟩, -⟩ :=
    S.rowsWP b CharTwo.two_eq_zero hbasic hconn v₀
  have hdg : dg.comp (Wu.res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)) =
      (lenW (Q := S.arTranslationQuiver)).res (S.arCoefficients b) (S.arMeshData b) := by
    rw [hWu]; rfl
  refine ⟨m, Rw, Wu, hdg, hWu, hRinj, hper, hcomp, hS, ?_⟩
  -- the table size
  obtain ⟨n, e, he, hprim, hbas⟩ := hbasic
  have hB := MeshWalk.basisR (S.arMeshData b) v₀ hF
  haveI : FiniteDimensional k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ := Module.Finite.of_basis hB
  have hdim : Fintype.card (MeshWalk.RayA0 (S.arMeshData b) v₀) ≤ Module.finrank k A := by
    rw [← Module.finrank_eq_card_basis hB, (S.posFiltA b he hprim hbas).finrank_eq]
  -- Proposition 10.3 for the characters in `W(P)`
  have hI : IStarG (S.arMeshData b) v₀ hF Wu dg hdg Rw := by
    intro i hχ
    obtain ⟨RS, hspan, htwo⟩ := S.prime_cokerSpan b
    let Wd0 : Fin 0 → MeshWt S.arTranslationQuiver ℤ := Fin.elim0
    refine MeshWalk.istar (SysG (S.arMeshData b) v₀ hF Wu dg hdg) (S.tab₂ b v₀ hF Wd0)
      (fun r ↦ ?_) (S.primeInjData b) (S.primeDegOne b) hspan htwo _ hχ
    change lenCoord (wtLat (S.arMeshData b) v₀ (dualWt Wd0) r) = dg (wtLat (S.arMeshData b) v₀ Wu r)
    rw [dg_wtLat _ v₀ (dualWt Wd0) lenCoord (hdg_dual (S.arMeshData b) v₀ Wd0),
      dg_wtLat _ v₀ Wu dg hdg]
  exact cor105G_of_IStar (S.arMeshData b) v₀ hF Wu dg hdg Rw
    (fun i ↦ by rw [← hb i]; exact prim_of_basis bL (jι i)) (hLB.mono (by convert hdim using 2)) hI

end MultiplicativeBasisDeformations.IndSkeleton
