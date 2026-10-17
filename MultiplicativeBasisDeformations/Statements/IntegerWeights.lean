import MultiplicativeBasisDeformations.Foundations.MeshWeightsConn
import MultiplicativeBasisDeformations.Foundations.Char2Basic
import MultiplicativeBasisDeformations.Foundations.MeshRadical
import MultiplicativeBasisDeformations.Foundations.ConnectedIdempotents
import MultiplicativeBasisDeformations.Foundations.FilteredA
import MultiplicativeBasisDeformations.Refinements.LiftedCorner

/-!
# Lemma 7.4 and Proposition 7.5 for a representation-finite algebra

`lem:integer-weight-lifting` and `prop:primitive-parameter-characters`
(`weights-and-parameters.tex:154–260`), for the algebra `A₀` of a basic representation-finite
algebra `A`, connected as in the source (`IsConnectedRing`: only the central idempotents `0`
and `1`). Connectedness passes to `A₀` (`a0Conn_ar`), which gives the lifted walks from a base
projective used in the proofs (`hK_of_A0Conn`; the source cites [ARS, Theorem VII.2.1] for the
connectedness of `Γ_A`). Every mesh of `Γ_A` has a nonzero middle term (`ar_hmid`, from the
exactness of the mesh data).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

include b in
/-- **Every mesh of `Γ_A` has a nonzero middle term.** -/
theorem ar_hmid (x : S.arTranslationQuiver.nonprojective) :
    Nonempty (Σ y : S.ARVertex, y ⟶ x.1) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hx : ¬ (S.arMeshData b).proj x.1 := not_not.2 x.2
  have h0 := (S.arMeshData b).cov_mono x.1 hx _ (𝟙 _) (fun a ↦ (h.false a).elim)
  exact MeshWalk.id_ne_zero (c := S.arCoefficients b) _ h0

/-- **A connected basic algebra has a connected `A₀`**: the splitting of `A` over `A₀`
(Lemma 6.4 for the radical filtration, `posFiltA`) carries the vertex idempotents of `A₀` to a
complete set of nonzero orthogonal idempotents of `A` and their corners to corners, so the
corner graph of `A₀` is connected (`eqvGen_corner`). -/
theorem a0Conn_ar (hbasic : IsBasicAlgebra A) (hconn : IsConnectedRing A) (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    ∀ x₀ : (S.arMeshData b).PV,
      MeshWalk.A0Conn S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b) x₀ := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  intro x₀
  obtain ⟨n, e, he, hprim, hb⟩ := hbasic
  set V := MeshWalk.vxIdem (S.arMeshData b) (S.hfinA0 b)
  obtain ⟨φ, hc, hl, hr, -, -⟩ := (S.posFiltA b he hprim hb).exists_split V
  have hV : ∀ i, V.e i ≠ 0 := by
    intro i h
    have h' := congrArg (fun a : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ ↦
      a.unop ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm i)) h
    change CatAlg.idTo _ _ ≫ CatAlg.idTo _ _ = (0 : CatAlg.Alg (S.arMeshData b).F0) _ _ at h'
    rw [CatAlg.idTo_self, Category.comp_id] at h'
    exact MeshWalk.idTo_ne_zero' (S.arMeshData b) _ h'
  have hne : ∀ i, φ (V.e i) ≠ 0 := fun i h ↦ hV i (φ.injective (by rw [h, map_zero]))
  have hcor := eqvGen_corner hconn hc hne
  refine MeshWalk.A0Conn_of_corners (fun p q ↦ ?_) x₀
  have key : ∀ i j, Relation.EqvGen (fun i j ↦ ∃ a, φ (V.e i) * a * φ (V.e j) ≠ 0) i j →
      Relation.EqvGen (fun p q : (S.arMeshData b).PV ↦ ∃ x : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ,
        MulOpposite.op (CatAlg.idem (F := (S.arMeshData b).F0) p) * x *
          MulOpposite.op (CatAlg.idem (F := (S.arMeshData b).F0) q) ≠ 0)
        ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm j) := by
    intro i j hij
    induction hij with
    | rel i j hr' =>
      obtain ⟨a, ha⟩ := hr'
      refine Relation.EqvGen.rel _ _ ⟨φ.symm a, fun h0 ↦ ha ?_⟩
      have : φ (V.e i * φ.symm a * V.e j) = φ (V.e i) * a * φ (V.e j) := by
        rw [hr, hl, LinearEquiv.apply_symm_apply]
      rw [← this]
      change φ (MulOpposite.op _ * φ.symm a * MulOpposite.op _) = 0
      rw [h0, map_zero]
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have := key _ _ (hcor (Fintype.equivFin _ p) (Fintype.equivFin _ q))
  simpa using this

/-- **Lemma 7.4** (`lem:integer-weight-lifting`) for `A₀ = kP` of a basic connected `A`: a
mesh weight restricts to a ray weight (`MeshWt.res`), and
`0 → {ζ : ζ_P = 0} → H^mesh → H → 0` is exact (with values in any abelian group `M`):
every ray weight is a restriction; a mesh weight restricts to zero exactly when it is
`w(a) = ζ_{target a} − ζ_{source a}`, `ν_v = ζ_v − ζ_{τv}` for object values vanishing at the
projectives; and such object values are determined by their differences. -/
theorem integerWeightLifting (v₀ : S.ARVertex) (hbasic : IsBasicAlgebra A) (hconn : IsConnectedRing A) (M : Type)
    [AddCommGroup M] :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    (∀ h : MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b) →+ M,
      ∃ W : MeshWalk.MeshWt S.arTranslationQuiver M, W.res (S.arCoefficients b) (S.arMeshData b) = h) ∧
    (∀ W : MeshWalk.MeshWt S.arTranslationQuiver M,
      W.res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b) = 0 ↔
        ∃ ζ : S.ARVertex → M, (∀ p : (S.arMeshData b).PV, ζ p.1 = 0) ∧
          (∀ {y x : S.ARVertex} (a : y ⟶ x), W.w a = ζ x - ζ y) ∧
          ∀ x : S.arTranslationQuiver.nonprojective,
            W.ν x = ζ x.1 - ζ (S.arTranslationQuiver.tau x).1) ∧
    ∀ ζ : S.ARVertex → M, (∀ p : (S.arMeshData b).PV, ζ p.1 = 0) →
      (∀ {y x : S.ARVertex} (_ : y ⟶ x), ζ x = ζ y) → ζ = 0 := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
  obtain ⟨z, -⟩ := MeshWalk.exists_supp (D := S.arMeshData b) (c := S.arCoefficients b)
    ((v₀, 1) : S.ARVertex × MeshWalk.Deck S.arTranslationQuiver v₀)
  have hA0 := S.a0Conn_ar b hbasic hconn v₀ z.1
  have hK := MeshWalk.hK_of_A0Conn (D := S.arMeshData b) (c := S.arCoefficients b) (v₀ := v₀) z.1 hA0
  exact ⟨fun h ↦ MeshWalk.exists_meshWt_lift (hF := hF) (hK := hK) h,
    fun W ↦ MeshWalk.res_eq_zero_iff (hK := hK) (S.ar_hmid b) W,
    fun ζ h0 harr ↦ MeshWalk.eq_zero_of_diff (hK := hK) ζ h0 harr⟩

/-- **Proposition 7.5** (`prop:primitive-parameter-characters`) for `A₀ = kP` of `A` with
basic and connected `A`, in characteristic two: for rows `p_i` at `v_i` as in Proposition 6.1(2) (at
periodic vertices, one per component, spanning the cokernels), the residual characters
`χ_i = w(p_i) − ν_{v_i}` of the universal mesh weight `w` (restricting to the identity of
`L = W(P)`, Lemma 7.4) are part of an integer basis of `W(P)`. -/
theorem primitiveParameterCharacters (h2 : (2 : k) = 0) (v₀ : S.ARVertex)
    (hbasic : IsBasicAlgebra A) (hconn : IsConnectedRing A) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    ∃ SR : ScalarMeshCategory.RowSet S.arTranslationQuiver,
      (∀ R ∈ SR, R.1.1 ∈ S.arTranslationQuiver.periodic) ∧
      (∀ R ∈ SR, ∀ R' ∈ SR, R'.1.1 ∈ S.arTranslationQuiver.component R.1.1 → R = R') ∧
      ScalarMeshCategory.CokerSpan (S.arCoefficients b) SR ∧ SR.Finite ∧
      (∃ Wu : MeshWalk.MeshWt S.arTranslationQuiver
          (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)),
        Wu.res (S.arCoefficients b) (S.arMeshData b) = AddMonoidHom.id _) ∧
      ∀ Wu : MeshWalk.MeshWt S.arTranslationQuiver
          (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)),
        Wu.res (S.arCoefficients b) (S.arMeshData b) = AddMonoidHom.id _ →
        ∃ (ι : Type) (bs : Module.Basis ι ℤ
            (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)))
          (j : SR → ι), Function.Injective j ∧ ∀ R : SR, bs (j R) = MeshWalk.rowWt Wu R.1 := by
  classical
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
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
  have hWu := MeshWalk.exists_meshWt_lift (hF := hF) (hK := hK)
    (AddMonoidHom.id (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)))
  refine ⟨SR, hper, hcomp, hspan, hfinSR, hWu, fun Wu hWu' ↦ ?_⟩
  haveI : Fintype SR := hfinSR.fintype
  let e := (Fintype.equivFin SR).symm
  obtain ⟨ι, bs, j, hj, hb⟩ := MeshWalk.chars_part_of_basis z.1 hK (S.ar_hmid b) Wu hWu'
    (fun i ↦ (e i).1) (fun i ↦ by
      obtain ⟨W, hW⟩ := hdual (e i).1 (e i).2
      refine ⟨W, fun j' ↦ ?_⟩
      unfold MeshWalk.rowWt
      rw [hW (e j').1 (e j').2]
      by_cases h : j' = i
      · rw [if_pos (by rw [h]), if_pos h]
      · rw [if_neg (fun h' ↦ h (e.injective (Subtype.ext h'))), if_neg h])
  refine ⟨ι, bs, fun R ↦ j (e.symm R), hj.comp e.symm.injective, fun R ↦ ?_⟩
  have := hb (e.symm R)
  rwa [Equiv.apply_symm_apply] at this

end MultiplicativeBasisDeformations.IndSkeleton
