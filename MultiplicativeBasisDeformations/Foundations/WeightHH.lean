import MultiplicativeBasisDeformations.Foundations.WeightCoker
import MultiplicativeBasisDeformations.Foundations.CharDecomp
import MultiplicativeBasisDeformations.Foundations.PsiInjective

/-!
# The characteristic-two decomposition of `HH²(A₀)_{>0}` (Proposition 7.6)

`weights-and-parameters.tex:405–410`: "Proposition 6.1 and the distinct characters `χ_i`
now give the asserted decomposition and the one-dimensionality of every nonzero summand,
with `I₀` the set of `i` for which `HH²(A₀)_{χ_i} ≠ 0`."

Here: `S` is a set of rows spanning the derivative cokernels, with distinct relative
weights `relW R = w(p_R) − ν_{v_R}`. A cocycle of positive degree and character `χ` is a
coboundary unless `χ = relW R` for a row `R ∈ S`; and if a cocycle `μ_i` of character
`relW R` has nonzero class, every cocycle of that character is a multiple of `μ_i` up to a
coboundary, in the same internal degree (`char_part`). With the character decomposition
this gives the spanning hypothesis of Theorem 7.7 (`span_A0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  [Fintype Q.nonprojective]

/-- The relative weight of a row. -/
def rowWt (R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) : M := W.pw R.2 - W.ν R.1

theorem mem_rowsOf {χ : M} {S : RowSet Q} {R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1} :
    R ∈ rowsOf W χ S ↔ R ∈ S ∧ rowWt W R = χ := by
  simp only [rowsOf, rowWt, Set.mem_setOf_eq, sub_eq_iff_eq_add']

/-- A vector in the span of at most one row. -/
theorem mem_rowSpan_le_single {m : ℕ} {T : RowSet Q}
    {R₀ : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1} (hT : T ⊆ {R₀}) {v : Coker c m}
    (hv : v ∈ rowSpan c m T) :
    v = 0 ∨ (R₀.2.length = m + 1 ∧ ∃ a : k, v = a • rowClass c m R₀.1 R₀.2) := by
  have hle := rowSpan_mono c hT hv
  rw [rowSpan] at hle
  by_cases hl : R₀.2.length = m + 1
  · have : (fun R ↦ rowClass c m R.1 R.2) '' {R | R ∈ ({R₀} : RowSet Q) ∧ R.2.length = m + 1} =
        {rowClass c m R₀.1 R₀.2} := by
      ext v
      constructor
      · rintro ⟨R, ⟨hR, -⟩, rfl⟩; rw [Set.mem_singleton_iff.1 hR]; rfl
      · rintro rfl; exact ⟨R₀, ⟨rfl, hl⟩, rfl⟩
    rw [this, Submodule.mem_span_singleton] at hle
    obtain ⟨a, rfl⟩ := hle
    exact Or.inr ⟨hl, a, rfl⟩
  · have : (fun R ↦ rowClass c m R.1 R.2) '' {R | R ∈ ({R₀} : RowSet Q) ∧ R.2.length = m + 1} = ∅ := by
      ext v
      simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨R, ⟨hR, hRl⟩, -⟩
      rw [Set.mem_singleton_iff.1 hR] at hRl
      exact hl hRl
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hle
    exact Or.inl hle

/-! ### Bridging the two cochain formalisms -/

theorem hDeg_of_hasDeg₂ {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (h : LenGrading.HasDeg₂ (lenA0 D hfin) q μ) : HDeg (galgA0 D hfin) μ (q : ℤ) := by
  intro p p' a b ha hb
  rcases lt_or_ge p 0 with hp | hp
  · rw [(galgA0_isHom_neg D hfin hp a).1 ha]; simp only [map_zero, LinearMap.zero_apply]
    exact ZGr.isHom_zero _ _
  rcases lt_or_ge p' 0 with hp' | hp'
  · rw [(galgA0_isHom_neg D hfin hp' b).1 hb]; simp only [map_zero]
    exact ZGr.isHom_zero _ _
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hp'
  rw [show (d : ℤ) + e + q = ((d + e + q : ℕ) : ℤ) by push_cast; ring, galgA0_isHom]
  rw [galgA0_isHom] at ha hb
  have h1 : (lenA0 D hfin).IsHom d a := (ZGr.ofLen_isHom _ d a).1 ((galgA0_isHom D hfin d a).2 ha)
  have h2 : (lenA0 D hfin).IsHom e b := (ZGr.ofLen_isHom _ e b).1 ((galgA0_isHom D hfin e b).2 hb)
  exact (galgA0_isHom D hfin _ _).1 ((ZGr.ofLen_isHom _ _ _).2 (h d e a b h1 h2))

theorem hasDeg₁_of {q : ℕ} {H : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (h : ∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + q) (H a)) :
    LenGrading.HasDeg₁ (lenA0 D hfin) q H := fun d a ha ↦ by
  have := h d a ((ZGr.ofLen_isHom _ d a).2 ha)
  rw [show (d : ℤ) + q = ((d + q : ℕ) : ℤ) by push_cast; ring] at this
  exact (ZGr.ofLen_isHom _ _ _).1 this

theorem hcobdry_eq (H : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) :
    hcobdry H = LenGrading.cobdry k H := by
  ext a b; rfl

variable (J : D.InjData) (h1 : DegOne D)

include J h1 in
/-- **Proposition 7.6, injectivity, in the cochain formalism of Theorem 7.8.** -/
theorem cobdry_of_Ψc {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (hμ : LenGrading.IsCocycle₂ μ) (hμd : LenGrading.HasDeg₂ (lenA0 D hfin) q μ)
    (Ld : LiftData D hfin q μ) (h : Ψc Ld = 0) :
    ∃ H, LenGrading.HasDeg₁ (lenA0 D hfin) q H ∧ μ = LenGrading.cobdry k H := by
  obtain ⟨H, hH, hμH⟩ := eq_hcobdry_of_Ψc_eq_zero J h1 hμ (hDeg_of_hasDeg₂ hfin hμd) Ld h
  exact ⟨H, hasDeg₁_of hfin hH, by rw [hμH, hcobdry_eq]⟩

include J h1 in
theorem exists_liftData' {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (hμ : LenGrading.IsCocycle₂ μ) (hμd : LenGrading.HasDeg₂ (lenA0 D hfin) q μ) :
    Nonempty (LiftData D hfin q μ) :=
  let ⟨Ld, _⟩ := exists_liftData J h1 hμ (hDeg_of_hasDeg₂ hfin hμd)
  ⟨Ld⟩

/-! ### Characters with a spanning row -/

variable {S : RowSet Q} (hS : CokerSpan c S)
  (hdist : ∀ R ∈ S, ∀ R' ∈ S, rowWt W R = rowWt W R' → R = R')

include J h1 hS hdist in
/-- **One character part.** -/
theorem char_part (V : LenGrading.Vertices (lenA0 D hfin)) {n : ℕ}
    (μ : Fin n → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (qd : Fin n → ℕ) (R : Fin n → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hRS : ∀ i, R i ∈ S) (hμc : ∀ i, LenGrading.IsCocycle₂ (μ i))
    (hμd : ∀ i, LenGrading.HasDeg₂ (lenA0 D hfin) (qd i) (μ i)) (hqpos : ∀ i, 0 < qd i)
    (hμχ : ∀ i, (latA0 W hfin D).Char₂ (rowWt W (R i)) (μ i))
    (hμnz : ∀ i, ¬ ∃ H, LenGrading.HasDeg₁ (lenA0 D hfin) (qd i) H ∧ μ i = LenGrading.cobdry k H)
    (hcover : ∀ R' ∈ S, (∃ i, R i = R') ∨ ∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ →
      LenGrading.HasDeg₂ (lenA0 D hfin) q φ →
      LenGrading.IsCocycle₂ φ → (latA0 W hfin D).Char₂ (rowWt W R') φ →
      ∃ H, LenGrading.HasDeg₁ (lenA0 D hfin) q H ∧ φ = LenGrading.cobdry k H)
    (q : ℕ) (hq : 0 < q) (χ : M) (φ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (hφr : LenGrading.IsRel₂ V φ)
    (hφd : LenGrading.HasDeg₂ (lenA0 D hfin) q φ) (hφc : LenGrading.IsCocycle₂ φ)
    (hφχ : (latA0 W hfin D).Char₂ χ φ) :
    ∃ (cf : Fin n → k) (f : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ),
      LenGrading.HasDeg₁ (lenA0 D hfin) q f ∧
        φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), cf i • μ i) + LenGrading.cobdry k f := by
  have hzero : ∀ H, LenGrading.HasDeg₁ (lenA0 D hfin) q H → φ = LenGrading.cobdry k H →
      ∃ (cf : Fin n → k) (f : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ),
        LenGrading.HasDeg₁ (lenA0 D hfin) q f ∧
          φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), cf i • μ i) + LenGrading.cobdry k f :=
    fun H hH hφH ↦ ⟨0, H, hH, by simp [hφH]⟩
  obtain ⟨Ldφ⟩ := exists_liftData' hfin J h1 hφc hφd
  have hΨφ := Ψc_mem_rowSpan_char W hfin χ J h1 hφχ hS (by omega) Ldφ
  by_cases hrow : ∃ R₀ ∈ S, rowWt W R₀ = χ
  swap
  · push Not at hrow
    have hempty : rowsOf W χ S = ∅ := by
      ext R'; simp only [mem_rowsOf, Set.mem_empty_iff_false, iff_false, not_and]
      exact hrow R'
    rw [hempty, rowSpan_empty, Submodule.mem_bot] at hΨφ
    obtain ⟨H, hH, hφH⟩ := cobdry_of_Ψc hfin J h1 hφc hφd Ldφ hΨφ
    exact hzero H hH hφH
  obtain ⟨R₀, hR₀S, hR₀χ⟩ := hrow
  have hsub : ∀ χ', rowWt W R₀ = χ' → rowsOf W χ' S ⊆ {R₀} := fun χ' hχ' R' hR' ↦ by
    rw [mem_rowsOf] at hR'
    exact hdist R' hR'.1 R₀ hR₀S (hR'.2.trans hχ'.symm)
  rcases hcover R₀ hR₀S with ⟨i, hi⟩ | hcob
  swap
  · obtain ⟨H, hH, hφH⟩ := hcob q hq φ hφr hφd hφc (hR₀χ ▸ hφχ)
    exact hzero H hH hφH
  rcases mem_rowSpan_le_single (hsub χ hR₀χ) hΨφ with h0 | ⟨hlen, a, ha⟩
  · obtain ⟨H, hH, hφH⟩ := cobdry_of_Ψc hfin J h1 hφc hφd Ldφ h0
    exact hzero H hH hφH
  -- the degree of `μ_i` is `q`
  have hqi : qd i = q := by
    obtain ⟨Ldμ⟩ := exists_liftData' hfin J h1 (hμc i) (hμd i)
    have hΨμ := Ψc_mem_rowSpan_char W hfin _ J h1 (hμχ i) hS (hqpos i) Ldμ
    rcases mem_rowSpan_le_single (hsub _ (by rw [hi])) hΨμ with h0 | ⟨hlen', -⟩
    · exact absurd (cobdry_of_Ψc hfin J h1 (hμc i) (hμd i) Ldμ h0) (hμnz i)
    · omega
  have hμdq : LenGrading.HasDeg₂ (lenA0 D hfin) q (μ i) := hqi ▸ hμd i
  have hnz : ¬ ∃ H, LenGrading.HasDeg₁ (lenA0 D hfin) q H ∧ μ i = LenGrading.cobdry k H := by
    rw [← hqi]; exact hμnz i
  obtain ⟨Ldμ⟩ := exists_liftData' hfin J h1 (hμc i) hμdq
  have hΨμ := Ψc_mem_rowSpan_char W hfin _ J h1 (hμχ i) hS (by omega) Ldμ
  rcases mem_rowSpan_le_single (hsub _ (by rw [hi])) hΨμ with h0 | ⟨-, b, hb⟩
  · exact absurd (cobdry_of_Ψc hfin J h1 (hμc i) hμdq Ldμ h0) hnz
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hb
    exact hnz (cobdry_of_Ψc hfin J h1 (hμc i) hμdq Ldμ hb)
  set t := a / b
  have hΨ' : Ψc (Ldφ.add (Ldμ.smul (-t))) = 0 := by
    rw [Ψc_add, Ψc_smul, ha, hb, smul_smul, ← add_smul]
    rw [show a + -t * b = 0 by simp only [t]; field_simp; ring, zero_smul]
  have hc' : LenGrading.IsCocycle₂ (φ + (-t) • μ i) := fun x y z ↦ by
    have e1 := hφc x y z
    have e2 := hμc i x y z
    simp only [LinearMap.add_apply, LinearMap.smul_apply, mul_add, add_mul, mul_smul_comm,
      smul_mul_assoc]
    rw [show x * φ y z + -t • (x * μ i y z) - (φ (x * y) z + -t • μ i (x * y) z) +
        (φ x (y * z) + -t • μ i x (y * z)) - (φ x y * z + -t • (μ i x y * z)) =
      (x * φ y z - φ (x * y) z + φ x (y * z) - φ x y * z) +
        -t • (x * μ i y z - μ i (x * y) z + μ i x (y * z) - μ i x y * z) by
      simp only [smul_sub, smul_add]; abel, e1, e2, smul_zero, add_zero]
  have hd' : LenGrading.HasDeg₂ (lenA0 D hfin) q (φ + (-t) • μ i) := fun d e x y hx hy ↦ by
    have e1 := hφd d e x y hx hy
    have e2 := hμdq d e x y hx hy
    unfold LenGrading.IsHom at e1 e2 ⊢
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, e1, e2]
  obtain ⟨H, hH, hH'⟩ := cobdry_of_Ψc hfin J h1 hc' hd' (Ldφ.add (Ldμ.smul (-t))) hΨ'
  refine ⟨Pi.single i t, H, hH, ?_⟩
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h ↦ absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, hqi⟩) h), Pi.single_eq_same, ← hH']
  ext x y
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [neg_smul]; abel


/-- The weight and length gradings of `A₀` commute. -/
theorem compat_A0 (d : ℕ) (l : M) (x : (Alg D.F0)ᵐᵒᵖ) :
    (lenA0 D hfin).proj d ((latA0 W hfin D).proj l x) =
      (latA0 W hfin D).proj l ((lenA0 D hfin).proj d x) := by
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p p'
  change degProj c d p.1 p'.1 (wπ c W l p.1 p'.1 (x.unop p p')) =
    wπ c W l p.1 p'.1 (degProj c d p.1 p'.1 (x.unop p p'))
  rw [wπ_degProj]

include J h1 hS hdist in
/-- **Proposition 7.6, the decomposition, in the form of the spanning hypothesis of
Theorem 7.7**: chosen cocycles `μ_i` of the characters of the spanning rows, with nonzero
classes, span the positive-degree Hochschild cohomology of `A₀` when every other spanning
row has zero cohomology in its character. -/
theorem span_A0 (V : LenGrading.Vertices (lenA0 D hfin))
    (he0 : ∀ i, (latA0 W hfin D).IsHom 0 (V.e i)) {n : ℕ}
    (μ : Fin n → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (qd : Fin n → ℕ) (R : Fin n → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hRS : ∀ i, R i ∈ S) (hμrel : ∀ i, LenGrading.IsRel₂ V (μ i))
    (hμc : ∀ i, LenGrading.IsCocycle₂ (μ i))
    (hμd : ∀ i, LenGrading.HasDeg₂ (lenA0 D hfin) (qd i) (μ i)) (hqpos : ∀ i, 0 < qd i)
    (hμχ : ∀ i, (latA0 W hfin D).Char₂ (rowWt W (R i)) (μ i))
    (hμnz : ∀ i, ¬ ∃ H, LenGrading.HasDeg₁ (lenA0 D hfin) (qd i) H ∧ μ i = LenGrading.cobdry k H)
    (hcover : ∀ R' ∈ S, (∃ i, R i = R') ∨ ∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ →
      LenGrading.HasDeg₂ (lenA0 D hfin) q φ →
      LenGrading.IsCocycle₂ φ → (latA0 W hfin D).Char₂ (rowWt W R') φ →
      ∃ H, LenGrading.HasDeg₁ (lenA0 D hfin) q H ∧ φ = LenGrading.cobdry k H) :
    ∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ V φ → LenGrading.HasDeg₂ (lenA0 D hfin) q φ →
      LenGrading.IsCocycle₂ φ →
      ∃ (cf : Fin n → k) (f : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ), LenGrading.IsRel₁ V f ∧
        LenGrading.HasDeg₁ (lenA0 D hfin) q f ∧
          φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), cf i • μ i) + LenGrading.cobdry k f :=
  LenGrading.span_of_char V (latA0 W hfin D) (compat_A0 W hfin) he0 hμrel
    fun q hq χ φ hφr hφd hφc hφχ ↦ char_part W hfin J h1 hS hdist V μ qd R hRS hμc hμd hqpos hμχ
      hμnz hcover q hq χ φ hφr hφd hφc hφχ

end MeshWalk

end MultiplicativeBasisDeformations
