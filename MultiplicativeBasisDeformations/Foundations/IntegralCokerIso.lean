import MultiplicativeBasisDeformations.Foundations.IntegralCoker
import MultiplicativeBasisDeformations.Foundations.MeshGrading
import MultiplicativeBasisDeformations.Foundations.ResidualSpaces

/-!
# Lemma B.2 as an isomorphism: `⊕ coker D_m(E₄) ≅ ⊕_{i∈I} 𝒪/(2)`

`characteristic-two-mesh-calculations.tex` (`lem:integral-mesh-cokernels`): with
`𝒪 = ℤ/4` and `E₄` the mesh category with unit coefficients `u` reducing to the all-one
coefficients of `C⁽²⁾`, `⊕_{m≥2} coker D_m(E₄) ≅ ⊕_{i∈I} (𝒪/(2))_{χ_i}`, the summand `i` lying
in `coker D_{d_i−1}`, `d_i = 2s_i + 2`.

For rows `S` spanning the cokernels over `𝔽₂` with independent classes and killed by two over
every ring (Proposition 6.1, `residualCorrectionSpaces`), in each degree `m + 1 ≥ 3`:
every family of degree `m + 1` over `𝒪` is an `𝒪`-combination of the rows of `S` modulo the
image of `D_m` (`integral_rows_span`; a remainder with zero reduction is twice a family of the
same degree, by the degree projections of `C(Q, u)`, `degProj`), twice each row is a
derivative (`two_smul_mem_imageD`), and a combination is a derivative exactly when all its
coefficients are even (`integral_rows_indep`). Thus `coker D_m(E₄)` is `⊕ 𝒪/(2)` over the rows
of `S` of degree `m + 1` (`integralMeshCokernels`). The weight labels `χ_i` are not formalized
(no weight grading on `E₄` is used).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

open LinearPaths TranslationQuiver

variable {V : Type v} [Quiver.{w} V]
  [Fintype V] [DecidableEq V] [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {Q : TranslationQuiver V} [DecidablePred (· ∈ Q.nonprojective)] [Fintype Q.nonprojective]
  {c : MeshCoefficients 𝔽₂ Q} {u : MeshCoefficients (ZMod 4) Q}
  (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))

/-- The degree projection lands in the degree part. -/
theorem degProj_mem' {k : Type*} [CommRing k] {Q : TranslationQuiver V}
    (c : MeshCoefficients k Q) (d : ℕ) {x y : V} (φ : obj c x ⟶ obj c y) :
    degProj c d x y φ ∈ degreePart c d x y := by
  obtain ⟨F, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) φ
  rw [degProj_apply]
  exact ⟨_, LinearPaths.proj_mem F, rfl⟩

/-- The degree projection fixes the degree part. -/
theorem degProj_fix {k : Type*} [CommRing k] {Q : TranslationQuiver V}
    (c : MeshCoefficients k Q) {d : ℕ} {x y : V} {φ : obj c x ⟶ obj c y}
    (hφ : φ ∈ degreePart c d x y) : degProj c d x y φ = φ := by
  obtain ⟨F, hF, rfl⟩ := hφ
  exact (degProj_apply c d F).trans (by rw [LinearPaths.proj_of_mem hF, if_pos rfl]; rfl)

include hred in
/-- Reduction maps derivatives to derivatives. -/
theorem redF_imageD {m : ℕ} {g : MeshFamily u} (hg : g ∈ imageD u m) :
    redF Z4.red u c g ∈ imageD c m := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨redA Z4.red u c f, fun a ↦ redE_degreePart hred (hf a), by
    rw [meshDerivativeₗ_apply, meshDerivativeₗ_apply, redF_meshDerivative hred]⟩

/-- A sum over a family of rows, regrouped over the distinct rows. -/
theorem sum_regroup {n : ℕ} (R : Fin n → (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1))
    (a : Fin n → ZMod 4) :
    ∑ i, a i • row u (R i).1 (R i).2 = ∑ T ∈ Finset.univ.image R,
      (∑ i ∈ Finset.univ.filter (fun i ↦ R i = T), a i) • row u T.1 T.2 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := R) (t := Finset.univ.image R)
    (fun i _ ↦ Finset.mem_image_of_mem R (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [(Finset.mem_filter.1 hi).2]

omit [Fintype V] [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  [Fintype Q.nonprojective] in
theorem row_deg {k : Type*} [CommRing k] {Q : TranslationQuiver V}
    [DecidablePred (· ∈ Q.nonprojective)] (c : MeshCoefficients k Q) {m : ℕ}
    (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) (hw : w.length = m + 1)
    (y : Q.nonprojective) : row c x w y ∈ degreePart c (m + 1) (Q.tau y).1 y.1 := by
  rw [row]
  by_cases h : y = x
  · subst h; rw [Pi.single_eq_same, ← hw]; exact pathMor_mem_degreePart c w
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem comp_mem_deg {k : Type*} [CommRing k] {Q : TranslationQuiver V}
    (c : MeshCoefficients k Q) {d e : ℕ} {x y z : V} {f : obj c x ⟶ obj c y}
    {g : obj c y ⟶ obj c z} (hf : f ∈ degreePart c d x y) (hg : g ∈ degreePart c e y z) :
    f ≫ g ∈ degreePart c (d + e) x z := by
  obtain ⟨F, hF, rfl⟩ := hf
  obtain ⟨G, hG, rfl⟩ := hg
  refine ⟨F ≫ G, LinearPaths.comp_mem_degreePart hF hG, ?_⟩
  change (RelationCategory.functor k (meshRelations c)).map (F ≫ G) = _
  rw [Functor.map_comp]; rfl

/-- The mesh derivative raises degrees by one. -/
theorem meshD_deg {k : Type*} [CommRing k] {Q : TranslationQuiver V} (c : MeshCoefficients k Q)
    {m : ℕ} (f : ArrowFamily c) (hf : ∀ a, f a ∈ degreePart c m a.1 a.2.1) (x : Q.nonprojective) :
    meshDerivative c f x ∈ degreePart c (m + 1) (Q.tau x).1 x.1 := by
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem ?_ ?_)
  · exact comp_mem_deg c (hf ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)
      ⟨_, LinearPaths.arrow_mem_degreePart a.2, rfl⟩
  · have := comp_mem_deg c ⟨_, LinearPaths.arrow_mem_degreePart
      (Q.mate x a.1 a.2), rfl⟩ (hf ⟨a.1, x.1, a.2⟩)
    rwa [add_comm] at this

include hred in
/-- **Spanning over `𝒪`**: a family of degree `m + 1 ≥ 3` is an `𝒪`-combination of the rows of
`S` modulo the image of `D_m`. -/
theorem integral_rows_span {S : RowSet Q} (hspan : CokerSpan c S) (htwo : TwoRows.{0} Q S)
    {m : ℕ} (hm : 2 ≤ m) {g : MeshFamily u}
    (hg : ∀ x, g x ∈ degreePart u (m + 1) (Q.tau x).1 x.1) :
    ∃ (F : Finset (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1))
      (l : (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) → ZMod 4),
      (↑F : Set _) ⊆ S ∧ (∀ R ∈ F, R.2.length = m + 1) ∧
        g - ∑ R ∈ F, l R • row u R.1 R.2 ∈ imageD u m := by
  classical
  have hgk : ∀ x, redF Z4.red u c g x ∈ degreePart c (m + 1) (Q.tau x).1 x.1 :=
    fun x ↦ redE_degreePart hred (hg x)
  have hmem := mk_mem_rowSpan hspan hm hgk
  obtain ⟨n, f, g', hfg⟩ := (Submodule.mem_span_set' (R := 𝔽₂)).1 hmem
  choose R hR hgR using fun i ↦ (g' i).2
  have hrow : redF Z4.red u c g - ∑ i, f i • row c (R i).1 (R i).2 ∈ imageD c m := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hfg, sub_eq_zero]
    change _ = (imageD c m).mkQ (∑ i, f i • row c (R i).1 (R i).2)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, ← hgR i]; rfl
  obtain ⟨fk, hfk, hDfk⟩ := hrow
  choose fO hfO hfOk using fun a ↦ exists_lift_degreePart hred Z4.red_surjective (hfk a)
  set r : MeshFamily u := g - ∑ i, Z4.lift (f i) • row u (R i).1 (R i).2 - meshDerivative u fO
  have hr : ∀ x, redE Z4.red u c (r x) = 0 := by
    intro x
    have e : redF Z4.red u c r = 0 := by
      simp only [r]
      rw [redF_sub hred, redF_sub hred, redF_sum hred, redF_meshDerivative hred]
      have ha : redA Z4.red u c fO = fk := funext fun a ↦ hfOk a
      rw [ha, ← meshDerivativeₗ_apply, hDfk]
      simp only [redF_smul hred, redF_row hred, Z4.red_lift]
      abel
    exact congrFun e x
  -- `r` has degree `m + 1`
  have hrd : ∀ x, r x ∈ degreePart u (m + 1) (Q.tau x).1 x.1 := by
    intro x
    have e : r x = g x - ∑ i, Z4.lift (f i) • row u (R i).1 (R i).2 x - meshDerivative u fO x := by
      simp only [r, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [e]
    exact sub_mem (sub_mem (hg x) (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (row_deg u (R i).1 (R i).2 (hR i).2 x))) (meshD_deg u fO (fun a ↦ hfO a) x)
  choose ψ hψ using fun x ↦ eq_two_smul_of_redE hred (hr x)
  set ψ' : MeshFamily u := fun x ↦ degProj u (m + 1) _ _ (ψ x)
  have hr2 : r = (2 : ZMod 4) • ψ' := by
    funext x
    change r x = (2 : ZMod 4) • degProj u (m + 1) _ _ (ψ x)
    rw [← map_smul, ← hψ x, degProj_fix u (hrd x)]
  have hψ'2 : (2 : ZMod 4) • ψ' ∈ imageD u m :=
    two_smul_mem_imageD hred hspan htwo hm (fun x ↦ degProj_mem' u (m + 1) (ψ x))
  refine ⟨Finset.univ.image R, fun T ↦ ∑ i ∈ Finset.univ.filter (fun i ↦ R i = T),
    Z4.lift (f i), ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT
    exact (hR i).1
  · intro T hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT
    exact (hR i).2
  · rw [← sum_regroup]
    have e : g - ∑ i, Z4.lift (f i) • row u (R i).1 (R i).2 = meshDerivative u fO + r := by
      simp only [r]; abel
    rw [e, hr2]
    exact add_mem ⟨fO, fun a ↦ hfO a, rfl⟩ hψ'2

include hred in
/-- **Independence over `𝒪`**: a combination of rows of `S` of degree `m + 1` is a derivative
exactly when all its coefficients are even. -/
theorem integral_rows_indep {S : RowSet Q} (hspan : CokerSpan c S) (htwo : TwoRows.{0} Q S)
    (hind : ∀ (m : ℕ) (F : Finset (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)),
      (↑F : Set _) ⊆ S → (∀ R ∈ F, R.2.length = m + 1) →
      ∀ l : (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) → 𝔽₂,
        ∑ R ∈ F, l R • row c R.1 R.2 ∈ imageD c m → ∀ R ∈ F, l R = 0)
    {m : ℕ} (hm : 2 ≤ m) (F : Finset (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1))
    (hF : (↑F : Set _) ⊆ S) (hFl : ∀ R ∈ F, R.2.length = m + 1)
    (l : (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) → ZMod 4) :
    ∑ R ∈ F, l R • row u R.1 R.2 ∈ imageD u m ↔ ∀ R ∈ F, Z4.red (l R) = 0 := by
  classical
  constructor
  · intro h
    have h' := redF_imageD hred (m := m) h
    rw [redF_sum hred] at h'
    simp only [redF_smul hred, redF_row hred] at h'
    exact hind m F hF hFl (fun R ↦ Z4.red (l R)) h'
  · intro h
    refine Submodule.sum_mem _ fun R hR ↦ ?_
    have h2 : (2 : ZMod 4) • row u R.1 R.2 ∈ imageD u m := by
      have := two_smul_mem_imageD hred hspan htwo hm (g := row u R.1 R.2)
        (row_deg u R.1 R.2 (hFl R hR))
      exact this
    have hl : l R = 0 ∨ l R = 2 := by
      have := h R hR
      revert this; generalize l R = a; revert a; decide
    rcases hl with hl | hl
    · rw [hl, zero_smul]; exact zero_mem _
    · rw [hl]; exact h2

include hred in
/-- **Lemma B.2** (`lem:integral-mesh-cokernels`), as an isomorphism. In characteristic two,
under the hypotheses of Proposition 6.1 for `C⁽²⁾ = C(Q, c)`, with `E₄ = C(Q, u)` over
`𝒪 = ℤ/4`: there is a set `S` of rows, one for each residual component `i`, of degree
`d_i = 2s_i + 2`, such that in each degree `m + 1 ≥ 3` the classes of the rows of `S` of
degree `m + 1` generate `coker D_m(E₄)`, each has order two, and a combination vanishes exactly
when all its coefficients are even; that is, `coker D_m(E₄) ≅ ⊕_{i : d_i = m + 1} 𝒪/(2)`. -/
theorem integralMeshCokernels (hQ : HasAtMostOneArrow V)
    [DecidablePred (· ∈ Q.periodic)]
    (hfin : ∀ x y : V, FiniteDimensional 𝔽₂ (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ S : RowSet Q, (∀ R ∈ S, R.1.1 ∈ Q.periodic) ∧
      (∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R') ∧
      (∀ r ∈ Q.periodic, Residual c r ↔ ∃ R ∈ S, R.1.1 ∈ Q.component r) ∧
      (∀ R ∈ S, ∃ x, x ∈ Q.periodic ∧ R.1.1 ∈ Q.component x ∧
        ∃ R₀ : (Σ y : (TranslationQuiver.restrict (TranslationQuiver.isTauClosed_component
            (Q := Q) x)).nonprojective,
          Quiver.Path ((TranslationQuiver.restrict (TranslationQuiver.isTauClosed_component
            (Q := Q) x)).tau y).1 y.1),
          StarTrace.DEModel (TranslationQuiver.restrict_isStable (Q := Q) x) R₀ ∧
            R₀.2.length = R.2.length) ∧
      ∀ m, 2 ≤ m →
        (∀ g : MeshFamily u, (∀ x, g x ∈ degreePart u (m + 1) (Q.tau x).1 x.1) →
          ∃ (F : Finset (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1))
            (l : (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) → ZMod 4),
            (↑F : Set _) ⊆ S ∧ (∀ R ∈ F, R.2.length = m + 1) ∧
              g - ∑ R ∈ F, l R • row u R.1 R.2 ∈ imageD u m) ∧
        (∀ R ∈ S, R.2.length = m + 1 → row u R.1 R.2 ∉ imageD u m ∧
          (2 : ZMod 4) • row u R.1 R.2 ∈ imageD u m) ∧
        ∀ (F : Finset (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)),
          (↑F : Set _) ⊆ S → (∀ R ∈ F, R.2.length = m + 1) →
          ∀ l : (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) → ZMod 4,
            ∑ R ∈ F, l R • row u R.1 R.2 ∈ imageD u m ↔ ∀ R ∈ F, Z4.red (l R) = 0 := by
  classical
  have hchar : (2 : 𝔽₂) = 0 := by decide
  obtain ⟨S, hper, huniq, hspan, -, hind, hres, hmod, htwo⟩ :=
    residualCorrectionSpaces c hQ hchar hfin hbrick
  refine ⟨S, hper, huniq, hres, hmod, fun m hm ↦ ⟨fun g hg ↦ integral_rows_span hred hspan htwo hm hg,
    fun R hR hl ↦ ⟨fun h ↦ ?_, ?_⟩, fun F hF hFl l ↦ integral_rows_indep hred hspan htwo hind hm F hF
      hFl l⟩⟩
  · have := (integral_rows_indep hred hspan htwo hind hm {R} (by simpa using hR) (by simpa using hl)
      (fun _ ↦ 1)).1 (by simpa using h) R (by simp)
    exact absurd this (by decide)
  · have := (integral_rows_indep hred hspan htwo hind hm {R} (by simpa using hR) (by simpa using hl)
      (fun _ ↦ 2)).2 (fun _ _ ↦ by decide)
    simpa using this

end ScalarMeshCategory

end MultiplicativeBasisDeformations
