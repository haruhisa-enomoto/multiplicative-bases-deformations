import MultiplicativeBasisDeformations.Statements.IntegerWeights
import MultiplicativeBasisDeformations.Foundations.CharSummands
import MultiplicativeBasisDeformations.Refinements.LiftedCorner

/-!
# Proposition 7.6, the characteristic-two decomposition, for a representation-finite algebra

`prop:hochschild-mesh-restriction` (`weights-and-parameters.tex:296–312`): "In characteristic two,
there is a subset `I₀ ⊆ I` such that `HH²(A₀)_{>0} = ⊕_{i ∈ I₀} HH²(A₀)_{χ_i}`,
`dim_k HH²(A₀)_{χ_i} = 1`." Here `HH²(A₀)_{>0}` is computed by normalized relative cocycles
modulo coboundaries in each internal degree `q > 0` (`exists_rel_cobdry`), the characters are
taken in `L = W(P)` through the universal mesh weight (Lemma 7.4), and the rows are those of
Proposition 6.1. The injection `Ψ` of the first part is `fullHochschildComparison_ar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

universe u

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)
  (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}

/-- The vertex idempotents of `A₀` have mesh weight zero. -/
theorem vxIdem_weight (i : Fin (vxIdem D hfin).n) : (latA0 W hfin D).IsHom 0 ((vxIdem D hfin).e i) := by
  classical
  rw [latA0_isHom, grA0_isHom]
  intro p q
  change CatAlg.idem (F := D.F0) ((Fintype.equivFin D.PV).symm i) p q ∈ _
  rw [idem_apply']
  set x := (Fintype.equivFin D.PV).symm i
  by_cases hp : p = x
  · by_cases hq : x = q
    · rw [hp, ← hq, CatAlg.idTo_self, Category.comp_id]
      have := pathMor_mem_wP (c := c) W (Quiver.Path.nil : Quiver.Path x.1 x.1)
      rw [pathMor_nil, MeshWt.pw] at this
      exact this
    · rw [CatAlg.idTo_ne hq, Limits.comp_zero]; exact Submodule.zero_mem _
  · rw [CatAlg.idTo_ne hp, Limits.zero_comp]; exact Submodule.zero_mem _

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

set_option maxHeartbeats 1000000 in
/-- **Proposition 7.6, characteristic two** (`prop:hochschild-mesh-restriction`), for `A₀` of a
basic connected representation-finite algebra: with the rows `p_i` of Proposition 6.1
and the characters `χ_i = w(p_i) − ν_{v_i}` in `L = W(P)` (pairwise distinct), there are
`I₀ = {R₀, …, R_{n−1}} ⊆ I` and normalized relative cocycles `μ_i` of character `χ_{R_i}` and
positive degree, not coboundaries, such that `HH²(A₀)_{χ_R} = 0` for rows outside `I₀`, the
classes of the `μ_i` span `HH²(A₀)_{>0}` in every internal degree, are independent (the sum is
direct), and every class of character `χ_{R_i}` is a multiple of `[μ_i]`
(`dim HH²(A₀)_{χ_i} = 1`). -/
theorem hochschildDecomposition_char2 (h2 : (2 : k) = 0) (v₀ : S.ARVertex)
    (hbasic : IsBasicAlgebra A) (hconn : IsConnectedRing A) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    let G := MeshWalk.lenA0 (S.arMeshData b) (S.hfinA0 b)
    let V := MeshWalk.vxIdem (S.arMeshData b) (S.hfinA0 b)
    ∃ (SR : ScalarMeshCategory.RowSet S.arTranslationQuiver)
      (Wu : MeshWalk.MeshWt S.arTranslationQuiver
        (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b))),
      (∀ R ∈ SR, R.1.1 ∈ S.arTranslationQuiver.periodic) ∧
      (∀ R ∈ SR, ∀ R' ∈ SR, R'.1.1 ∈ S.arTranslationQuiver.component R.1.1 → R = R') ∧
      ScalarMeshCategory.CokerSpan (S.arCoefficients b) SR ∧ SR.Finite ∧
      Wu.res (S.arCoefficients b) (S.arMeshData b) = AddMonoidHom.id _ ∧
      (∀ R ∈ SR, ∀ R' ∈ SR, MeshWalk.rowWt Wu R = MeshWalk.rowWt Wu R' → R = R') ∧
      let Wl := MeshWalk.latA0 Wu (S.hfinA0 b) (S.arMeshData b)
      ∃ (n : ℕ) (R : Fin n → Σ x : S.arTranslationQuiver.nonprojective,
          Quiver.Path (S.arTranslationQuiver.tau x).1 x.1)
        (μ : Fin n → (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
          (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
        (qd : Fin n → ℕ),
        Function.Injective R ∧ (∀ i, R i ∈ SR) ∧
        (∀ i, 0 < qd i ∧ LenGrading.IsRel₂ V (μ i) ∧ LenGrading.HasDeg₂ G (qd i) (μ i) ∧
          LenGrading.IsCocycle₂ (μ i) ∧ Wl.Char₂ (MeshWalk.rowWt Wu (R i)) (μ i) ∧
          ¬ ∃ H, LenGrading.HasDeg₁ G (qd i) H ∧ μ i = LenGrading.cobdry k H) ∧
        (∀ R' ∈ SR, R' ∉ Set.range R → ∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ →
          LenGrading.HasDeg₂ G q φ → LenGrading.IsCocycle₂ φ →
          Wl.Char₂ (MeshWalk.rowWt Wu R') φ →
          ∃ H, LenGrading.HasDeg₁ G q H ∧ φ = LenGrading.cobdry k H) ∧
        (∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ → LenGrading.HasDeg₂ G q φ →
          LenGrading.IsCocycle₂ φ →
          ∃ (cf : Fin n → k) (f : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
              (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ),
            LenGrading.IsRel₁ V f ∧ LenGrading.HasDeg₁ G q f ∧
            φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), cf i • μ i) +
              LenGrading.cobdry k f) ∧
        (∀ q (cf : Fin n → k) (f : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
            (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ), LenGrading.HasDeg₁ G q f →
          (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), cf i • μ i) = LenGrading.cobdry k f →
          ∀ i, qd i = q → cf i = 0) ∧
        ∀ i q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ → LenGrading.HasDeg₂ G q φ →
          LenGrading.IsCocycle₂ φ → Wl.Char₂ (MeshWalk.rowWt Wu (R i)) φ →
          ∃ (t : k) (f : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
              (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ),
            LenGrading.HasDeg₁ G q f ∧ φ = t • μ i + LenGrading.cobdry k f := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  haveI : DecidablePred (· ∈ S.arTranslationQuiver.nonprojective) := Classical.decPred _
  intro G V
  have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  obtain ⟨z, -⟩ := MeshWalk.exists_supp (D := S.arMeshData b) (c := S.arCoefficients b)
    ((v₀, 1) : S.ARVertex × MeshWalk.Deck S.arTranslationQuiver v₀)
  have hA0 := S.a0Conn_ar b hbasic hconn v₀ z.1
  have hK := MeshWalk.hK_of_A0Conn (D := S.arMeshData b) (c := S.arCoefficients b) (v₀ := v₀) z.1 hA0
  haveI := MeshWalk.WP_free hF hA0
  haveI : Module.Finite ℤ (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀
    (S.arMeshData b)) := MeshWalk.WP_finite
  obtain ⟨SR, hper, hcomp, hspan, hdual⟩ := residual_dual (S.arCoefficients b)
    S.hasAtMostOneArrow h2 (S.hfinA0 b) (S.brickHypothesis b)
  have hfinSR : SR.Finite := by
    refine Set.Finite.of_finite_image (f := fun R ↦ R.1.1) (Set.toFinite _) ?_
    intro R hR R' hR' h
    exact hcomp R hR R' hR' (by
      have : R'.1.1 = R.1.1 := h.symm
      rw [this]; exact TranslationQuiver.mem_component_self (hper R hR))
  obtain ⟨Wu, hWu⟩ := MeshWalk.exists_meshWt_lift (hF := hF) (hK := hK)
    (AddMonoidHom.id (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)))
  -- distinct characters (Proposition 7.5)
  have hdist : ∀ R ∈ SR, ∀ R' ∈ SR, MeshWalk.rowWt Wu R = MeshWalk.rowWt Wu R' → R = R' := by
    haveI : Fintype SR := hfinSR.fintype
    let e := (Fintype.equivFin SR).symm
    obtain ⟨ι, bs, j, hj, hb⟩ := MeshWalk.chars_part_of_basis z.1 hK (S.ar_hmid b) Wu hWu
      (fun i ↦ (e i).1) (fun i ↦ by
        obtain ⟨W, hW⟩ := hdual (e i).1 (e i).2
        refine ⟨W, fun j' ↦ ?_⟩
        unfold MeshWalk.rowWt
        rw [hW (e j').1 (e j').2]
        by_cases h : j' = i
        · rw [if_pos (by rw [h]), if_pos h]
        · rw [if_neg (fun h' ↦ h (e.injective (Subtype.ext h'))), if_neg h])
    intro R hR R' hR' h
    have h1 := hb (e.symm ⟨R, hR⟩)
    have h2 := hb (e.symm ⟨R', hR'⟩)
    rw [Equiv.apply_symm_apply] at h1 h2
    have := hj (bs.injective (h1.trans (h.trans h2.symm)))
    exact congrArg Subtype.val (e.symm.injective this)
  refine ⟨SR, Wu, hper, hcomp, hspan, hfinSR, hWu, hdist, ?_⟩
  intro Wl
  -- the rows with a nonzero class
  let good : (Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1) → Prop := fun R ↦
    ∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ V φ ∧ LenGrading.HasDeg₂ G q φ ∧
      LenGrading.IsCocycle₂ φ ∧ Wl.Char₂ (MeshWalk.rowWt Wu R) φ ∧
      ¬ ∃ H, LenGrading.HasDeg₁ G q H ∧ φ = LenGrading.cobdry k H
  haveI := Classical.decPred good
  let I₀ := hfinSR.toFinset.filter good
  let e : Fin I₀.card ≃ I₀ := I₀.equivFin.symm
  let R : Fin I₀.card → Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1 := fun i ↦ (e i).1
  have hRgood : ∀ i, good (R i) := fun i ↦ (Finset.mem_filter.1 (e i).2).2
  have hRS : ∀ i, R i ∈ SR := fun i ↦ (Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 (e i).2).1
  choose qd hqd μ hμ using hRgood
  have hRinj : Function.Injective R := fun i j h ↦ e.injective (Subtype.ext h)
  have hχ : Function.Injective fun i ↦ MeshWalk.rowWt Wu (R i) := fun i j h ↦
    hRinj (hdist _ (hRS i) _ (hRS j) h)
  have he0 := MeshWalk.vxIdem_weight Wu (S.hfinA0 b) (D := S.arMeshData b)
  have hcover : ∀ R' ∈ SR, (∃ i, R i = R') ∨ ∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ →
      LenGrading.HasDeg₂ G q φ → LenGrading.IsCocycle₂ φ → Wl.Char₂ (MeshWalk.rowWt Wu R') φ →
      ∃ H, LenGrading.HasDeg₁ G q H ∧ φ = LenGrading.cobdry k H := by
    intro R' hR'
    by_cases hg : good R'
    · left
      have hmem : R' ∈ I₀ := Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hR', hg⟩
      exact ⟨e.symm ⟨R', hmem⟩, by simp [R]⟩
    · right
      intro q hq φ hφr hφd hφc hφχ
      by_contra hno
      exact hg ⟨q, hq, φ, hφr, hφd, hφc, hφχ, hno⟩
  have hspanA0 := MeshWalk.span_A0 Wu (S.hfinA0 b) (S.arInjData b) (S.arDegOne b) hspan hdist V
    he0 μ qd R hRS (fun i ↦ (hμ i).1) (fun i ↦ (hμ i).2.2.1) (fun i ↦ (hμ i).2.1) hqd
    (fun i ↦ (hμ i).2.2.2.1) (fun i ↦ (hμ i).2.2.2.2) hcover
  refine ⟨I₀.card, R, μ, qd, hRinj, hRS, fun i ↦ ⟨hqd i, hμ i⟩, ?_, hspanA0, ?_, ?_⟩
  · intro R' hR' hnot
    rcases hcover R' hR' with ⟨i, hi⟩ | h
    · exact absurd ⟨i, hi⟩ hnot
    · exact h
  · intro q cf f hf h i hi
    exact LatGrading.coef_eq_zero_of_cobdry Wl (MeshWalk.compat_A0 Wu (S.hfinA0 b)) μ qd hχ
      (fun i ↦ (hμ i).2.2.2.1) (fun i ↦ (hμ i).2.2.2.2) q cf f hf h i hi
  · intro i q hq φ hφr hφd hφc hφχ
    obtain ⟨cf, f, -, hf, hφ⟩ := hspanA0 q hq φ hφr hφd hφc
    exact LatGrading.eq_smul_add_cobdry Wl (MeshWalk.compat_A0 Wu (S.hfinA0 b)) μ qd hχ
      (fun i ↦ (hμ i).2.2.2.1) i hφχ cf f hf hφ

end MultiplicativeBasisDeformations.IndSkeleton
