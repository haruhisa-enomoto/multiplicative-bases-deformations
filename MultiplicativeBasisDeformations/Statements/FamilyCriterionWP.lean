import MultiplicativeBasisDeformations.Statements.IntegerWeights
import MultiplicativeBasisDeformations.Statements.PolynomialMesh
import MultiplicativeBasisDeformations.Foundations.FamilyCriterionGen

/-!
# Propositions 7.9 and 12.8 with characters in `W(P)`

`prop:family-criterion` and `prop:polynomial-mesh-comparison`, for a basic connected
representation-finite algebra `A` in characteristic two, with the residual characters
`χ_i = w(p_i) − ν_{v_i}` in the weight lattice `L = W(P)` of the universal mesh weight `w`
(Lemma 7.4), as in the source. The rows are those of Proposition 6.1 (`residual_dual`), of length
at least three (shorter rows carry no cokernel class); their characters are pairwise distinct and
part of an integer basis of `W(P)` (Proposition 7.5), and have degree `len p_i − 2`
(`rowsWP`). The family statements are the generic ones of `FamilyCriterionGen.lean` and
`PolynomialMesh.lean` for this weight.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace ScalarMeshCategory

variable {k : Type*} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

/-- Rows of length below three carry no cokernel class. -/
theorem cokerSpan_filter {S : RowSet Q} (hS : CokerSpan c S) :
    CokerSpan c {R | R ∈ S ∧ 3 ≤ R.2.length} := by
  intro m hm x w hw
  refine Submodule.span_mono ?_ (hS m hm x w hw)
  rintro _ ⟨R, ⟨hR, hl⟩, rfl⟩
  exact ⟨R, ⟨⟨hR, by omega⟩, hl⟩, rfl⟩

end ScalarMeshCategory

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe u

open MeshWalk

attribute [local instance] Classical.decEq

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **The rows of Proposition 6.1 with their characters in `W(P)`.** -/
theorem rowsWP (h2 : (2 : k) = 0) (hbasic : IsBasicAlgebra A) (hconn : IsConnectedRing A)
    (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    ∃ (n : ℕ) (Rw : Fin n → Σ x : S.arTranslationQuiver.nonprojective,
        Quiver.Path (S.arTranslationQuiver.tau x).1 x.1)
      (Wu : MeshWt S.arTranslationQuiver
        (WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b))),
      Wu.res (S.arCoefficients b) (S.arMeshData b) = AddMonoidHom.id _ ∧
      Function.Injective Rw ∧ (∀ i, (Rw i).1.1 ∈ S.arTranslationQuiver.periodic) ∧
      (∀ i j, (Rw j).1.1 ∈ S.arTranslationQuiver.component (Rw i).1.1 → i = j) ∧
      ScalarMeshCategory.CokerSpan (S.arCoefficients b) (Set.range Rw) ∧
      (∀ i, 3 ≤ (Rw i).2.length) ∧
      Function.Injective (fun i ↦ rowWt Wu (Rw i)) ∧
      (∃ (κ : Type) (bL : Module.Basis κ ℤ
          (WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b))) (jι : Fin n → κ),
        Function.Injective jι ∧ ∀ i, bL (jι i) = rowWt Wu (Rw i)) ∧
      ∀ i, (lenW (Q := S.arTranslationQuiver)).res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)
        (rowWt Wu (Rw i)) = ((Rw i).2.length : ℤ) - 2 := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI hfd : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  haveI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  haveI : DecidablePred (· ∈ S.arTranslationQuiver.nonprojective) := Classical.decPred _
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
  set SR' : ScalarMeshCategory.RowSet S.arTranslationQuiver := {R | R ∈ SR ∧ 3 ≤ R.2.length}
  have hfinSR : SR'.Finite := by
    refine Set.Finite.of_finite_image (f := fun R ↦ R.1.1) (Set.toFinite _) ?_
    intro R hR R' hR' h
    exact hcomp R hR.1 R' hR'.1 (by
      have : R'.1.1 = R.1.1 := h.symm
      rw [this]; exact TranslationQuiver.mem_component_self (hper R hR.1))
  haveI : Fintype SR' := hfinSR.fintype
  set e : Fin (Fintype.card SR') ≃ SR' := (Fintype.equivFin SR').symm
  set Rw : Fin (Fintype.card SR') → Σ x : S.arTranslationQuiver.nonprojective,
      Quiver.Path (S.arTranslationQuiver.tau x).1 x.1 := fun i ↦ (e i).1
  have hRinj : Function.Injective Rw := fun i j h ↦ e.injective (Subtype.ext h)
  have hrange : Set.range Rw = SR' := by
    ext R; constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hR; exact ⟨e.symm ⟨R, hR⟩, by simp [Rw]⟩
  obtain ⟨Wu, hWu⟩ := MeshWalk.exists_meshWt_lift (hF := hF) (hK := hK)
    (AddMonoidHom.id (MeshWalk.WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)))
  obtain ⟨κ, bs, jj, hjj, hb⟩ := MeshWalk.chars_part_of_basis z.1 hK (S.ar_hmid b) Wu hWu Rw
    (fun i ↦ by
      obtain ⟨W, hW⟩ := hdual (Rw i) (e i).2.1
      refine ⟨W, fun j ↦ ?_⟩
      unfold MeshWalk.rowWt
      rw [hW (Rw j) (e j).2.1]
      by_cases h : j = i
      · rw [if_pos (by rw [h]), if_pos h]
      · rw [if_neg (fun h' ↦ h (hRinj h')), if_neg h])
  refine ⟨_, Rw, Wu, hWu, hRinj, fun i ↦ hper _ (e i).2.1, fun i j h ↦ hRinj
    (hcomp _ (e i).2.1 _ (e j).2.1 h), ?_, fun i ↦ (e i).2.2, fun i j h ↦ hjj
    (bs.injective ((hb i).trans (h.trans (hb j).symm))), ⟨κ, bs, jj, hjj, hb⟩, fun i ↦ ?_⟩
  · rw [hrange]; exact ScalarMeshCategory.cokerSpan_filter _ hspan
  · set dg := (lenW (Q := S.arTranslationQuiver)).res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)
    have hres : (Wu.map dg).res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b) =
        (lenW (Q := S.arTranslationQuiver)).res (S.arCoefficients b) (S.arMeshData b) := by
      rw [MeshWt.res_map, hWu]; rfl
    have h1 := MeshWalk.rowWt_eq_of_res z.1 hK (S.ar_hmid b) (Wu.map dg) lenW hres (Rw i)
    rw [MeshWalk.rowWt_map] at h1
    rw [h1]
    unfold MeshWalk.rowWt
    rw [lenW_pw]
    rfl

/-- The coordinates of an integer basis on chosen basis vectors. -/
def basisCoords {L : Type} [AddCommGroup L] {κ : Type} (bL : Module.Basis κ ℤ L) {n : ℕ}
    (jι : Fin n → κ) : L →+ (Fin n → ℤ) where
  toFun l i := bL.repr l (jι i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem basisCoords_apply {L : Type} [AddCommGroup L] {κ : Type} (bL : Module.Basis κ ℤ L) {n : ℕ}
    {jι : Fin n → κ} (hjι : Function.Injective jι) (i : Fin n) :
    basisCoords bL jι (bL (jι i)) = Pi.single i 1 := by
  funext j
  change bL.repr (bL (jι i)) (jι j) = _
  rw [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg (fun h' ↦ h (hjι h').symm), if_neg h]

/-- **Proposition 7.9** (`prop:family-criterion`) for a basic connected representation-finite
algebra `A` in characteristic two, with the residual characters in `W(P)`: for the rows of
Proposition 6.1 and the universal mesh weight, every family `μ_i`, `i ∈ I₀`, of normalized
relative cocycles of character `χ_i ∈ W(P)` with nonzero classes, associative, whose binary fibres
have the basis of `kP` as a normed multiplicative ray basis, gives `A` as a binary fibre with a
normed multiplicative ray basis presenting `P` (`FamilyCriterionStmt` for `B = A`). -/
theorem familyCriterion_WP (h2 : (2 : k) = 0) {n : ℕ} {e : Fin n → A}
    (he : CompleteOrthogonalIdempotents e) (hprim : ∀ i, IsPrimitiveIdempotent (e i))
    (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
      y * x = e j) → i = j) (hconn : IsConnectedRing A) (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
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
      FamilyCriterionStmt (S.arMeshData b) v₀ hF Wu dg hdg Rw (S.posFiltA b he hprim hbasic) := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  intro hF dg
  obtain ⟨m, Rw, Wu, hWu, hRinj, hper, hcomp, hS, -, hχinj, hbasis, -⟩ :=
    S.rowsWP b h2 ⟨n, e, he, hprim, hbasic⟩ hconn v₀
  have hdg : dg.comp (Wu.res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)) =
      (lenW (Q := S.arTranslationQuiver)).res (S.arCoefficients b) (S.arMeshData b) := by
    rw [hWu]; rfl
  exact ⟨m, Rw, Wu, hdg, hWu, hRinj, hper, hcomp, hS,
    familyCriterionStmt_G (S.arMeshData b) v₀ hF Wu dg hdg Rw (S.arInjData b) (S.arDegOne b) hS
      hχinj hbasis (S.posFiltA b he hprim hbasic)⟩

set_option maxHeartbeats 1000000 in
/-- **Proposition 12.8** (`prop:polynomial-mesh-comparison`) for a basic connected
representation-finite algebra in characteristic two, with the residual characters in `W(P)`:
for the rows of Proposition 6.1 (of length at least three) and the universal mesh weight, every
family `μ_i` indexed by `I = I₀` with the hypotheses of Proposition 7.9 has polynomial lifts with
retained mesh coefficients `a_i t_i`, `a_i ≠ 0`, presenting every fibre, whose modules exhaust
the indecomposables of the fibre (`PolyMeshStmtG`). -/
theorem polynomialMeshComparison_WP (h2 : (2 : k) = 0) (hbasic : IsBasicAlgebra A)
    (hconn : IsConnectedRing A) (v₀ : S.ARVertex) :
    letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    letI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
    let hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    let dg := (lenW (Q := S.arTranslationQuiver)).res (v₀ := v₀) (S.arCoefficients b)
      (S.arMeshData b)
    ∃ (m : ℕ) (Rw : Fin m → Σ x : S.arTranslationQuiver.nonprojective,
        Quiver.Path (S.arTranslationQuiver.tau x).1 x.1)
      (Wu : MeshWt S.arTranslationQuiver
        (WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)))
      (hdg : dg.comp (Wu.res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)) =
        (lenW (Q := S.arTranslationQuiver)).res (S.arCoefficients b) (S.arMeshData b))
      (coords : WP S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b) →+ (Fin m → ℤ)),
      Wu.res (S.arCoefficients b) (S.arMeshData b) = AddMonoidHom.id _ ∧
      Function.Injective Rw ∧ (∀ i, (Rw i).1.1 ∈ S.arTranslationQuiver.periodic) ∧
      (∀ i j, (Rw j).1.1 ∈ S.arTranslationQuiver.component (Rw i).1.1 → i = j) ∧
      ScalarMeshCategory.CokerSpan (S.arCoefficients b) (Set.range Rw) ∧
      (∀ i, 3 ≤ (Rw i).2.length) ∧
      (∀ i, coords (rowCharG Wu Rw i) = Pi.single i 1) ∧
      ∀ μ : Fin m → (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
          (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ,
        (∀ i, LenGrading.IsRel₂ (VxG (S.arMeshData b) v₀ hF Wu dg hdg) (μ i)) →
        (∀ i, (latA0 Wu (hfinObj (c := S.arCoefficients b)) (S.arMeshData b)).Char₂
          (rowCharG Wu Rw i) (μ i)) →
        (∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f) →
        (∀ (t : Fin m → k) (a b' z : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ),
          famMul (S.arMeshData b) μ t (famMul (S.arMeshData b) μ t a b') z =
            famMul (S.arMeshData b) μ t a (famMul (S.arMeshData b) μ t b' z)) →
        PolyMeshStmtG (S.arMeshData b) (W := Wu) (coords := coords) (Rw := Rw) (S.arInjData b)
          (S.arDegOne b) μ := by
  letI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  letI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  letI : Fintype S.arTranslationQuiver.nonprojective := Fintype.ofFinite _
  intro hF dg
  obtain ⟨m, Rw, Wu, hWu, hRinj, hper, hcomp, hS, hlen3, -, ⟨κ, bL, jι, hjι, hb⟩, hdgrow⟩ :=
    S.rowsWP b h2 hbasic hconn v₀
  have hdg : dg.comp (Wu.res (v₀ := v₀) (S.arCoefficients b) (S.arMeshData b)) =
      (lenW (Q := S.arTranslationQuiver)).res (S.arCoefficients b) (S.arMeshData b) := by
    rw [hWu]; rfl
  have hco : ∀ i, basisCoords bL jι (rowCharG Wu Rw i) = Pi.single i 1 := fun i ↦ by
    rw [rowCharG, ← hb i, basisCoords_apply bL hjι]
  refine ⟨m, Rw, Wu, hdg, basisCoords bL jι, hWu, hRinj, hper, hcomp, hS, hlen3, hco,
    fun μ hrel hchar hnz hassoc ↦ ?_⟩
  exact polynomialMeshComparison_G (S.arMeshData b) v₀ hF (W := Wu) (dg := dg) (hdg := hdg)
    (coords := basisCoords bL jι) (Rw := Rw) (S.arInjData b) (S.arDegOne b) (S.arHrad b) hco hS hlen3 hdgrow μ hrel hchar hnz hassoc

end MultiplicativeBasisDeformations.IndSkeleton
