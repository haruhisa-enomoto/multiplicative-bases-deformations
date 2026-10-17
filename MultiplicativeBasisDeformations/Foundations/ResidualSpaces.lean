import MultiplicativeBasisDeformations.Foundations.ResidualCorrection
import MultiplicativeBasisDeformations.Foundations.PeriodicIso

/-!
# Proposition 6.1: residual correction spaces

`positive-deformations.tex:23–48` (`prop:residual-correction-spaces`). In characteristic two,
under the brick hypothesis, call a periodic component *residual* if `⊕_m coker D_m(C)` has a
nonzero class supported on it. Then each residual component is `ℤΔ/⟨τ^{s_i}ρ⟩` with `Δ` of
type `D` or `E`, there is a path `p_i : τ v_i → v_i` of degree `d_i = 2s_i + 2`, and
`⊕_{m≥2} coker D_m(C) = ⊕_{i∈I} k[p_i]`.

The spanning by at most one row per periodic component is `residual_cokerSpan`. Here:

* the mesh derivative commutes with the projection to a union of components of a quiver
  (`D_projA`), so the image of `D` is stable under it (`projM_mem_imageD`);
* after the localization of Proposition 5.1 to the periodic vertices (where periodic
  components are unions of connected components), a family supported on one periodic
  component lies in the image of `D` as soon as it does modulo families supported elsewhere
  (`mem_imageD_of_supported`);
* hence rows in distinct periodic components with nonzero classes are linearly independent
  (`rows_independent`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

open TranslationQuiver

/-! ### Projection to a union of components -/

section Proj

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q) (P : V → Prop) [DecidablePred P]

/-- The arrow family kept on the arrows with target in `P`. -/
def projA (f : ArrowFamily c) : ArrowFamily c := fun a ↦ if P a.2.1 then f a else 0

/-- The mesh family kept on the vertices in `P`. -/
def projM (g : MeshFamily c) : MeshFamily c := fun x ↦ if P x.1 then g x else 0

variable {P}

/-- **The mesh derivative commutes with the projection to a union of components.** -/
theorem D_projA (hP : ∀ (x y : V) (_ : x ⟶ y), P x ↔ P y) (f : ArrowFamily c) :
    meshDerivative c (projA c P f) = projM c P (meshDerivative c f) := by
  funext x
  simp only [meshDerivative, projM, projA]
  by_cases hx : P x.1
  · rw [if_pos hx]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hy : P a.1 := (hP _ _ a.2).2 hx
    rw [if_pos hy, if_pos hx]
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    have hy : ¬ P a.1 := fun h ↦ hx ((hP _ _ a.2).1 h)
    rw [if_neg hy, if_neg hx]
    simp

theorem projM_mem_imageD (hP : ∀ (x y : V) (_ : x ⟶ y), P x ↔ P y) {m : ℕ} {g : MeshFamily c}
    (hg : g ∈ imageD c m) : projM c P g ∈ imageD c m := by
  obtain ⟨f, hf, rfl⟩ := hg
  refine ⟨projA c P f, fun a ↦ ?_, ?_⟩
  · unfold projA
    split_ifs
    · exact hf a
    · exact zero_mem _
  · simp only [meshDerivativeₗ_apply]
    exact D_projA c hP f

end Proj

/-! ### Families supported on one periodic component -/

section Support

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [Fintype V] [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.periodic)]
  [DecidablePred (· ∈ Q.nonprojective)] [Fintype Q.nonprojective]

theorem mem_component_iff {r x : V} (hx : x ∈ Q.periodic) :
    x ∈ Q.component r ↔ Q.component x = Q.component r :=
  ⟨component_eq_of_mem, fun h ↦ h ▸ mem_component_self hx⟩

theorem component_eq' {u v : V} (h : Relation.EqvGen Q.PeriodicAdj u v) :
    Q.component u = Q.component v := by
  ext w
  exact ⟨fun ⟨hw, h'⟩ ↦ ⟨hw, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) h'⟩,
    fun ⟨hw, h'⟩ ↦ ⟨hw, Relation.EqvGen.trans _ _ _ h h'⟩⟩

/-- Membership in a periodic component is preserved along arrows between periodic vertices. -/
theorem comp_iff_of_arrow (r : V) (a b : FullSub Q.periodic) (e : a ⟶ b) :
    a.val ∈ Q.component r ↔ b.val ∈ Q.component r := by
  rw [mem_component_iff a.val_mem, mem_component_iff b.val_mem,
    component_eq' (Relation.EqvGen.rel _ _ ⟨a.val_mem, b.val_mem, Or.inl ⟨e⟩⟩)]

/-- **A family supported on one periodic component** lies in the image of `D_m` as soon as
it does modulo a family supported off that component. -/
theorem mem_imageD_of_supported {m : ℕ} (r : V) {g h : MeshFamily c} (hg : g ∈ famDeg c (m + 1))
    (hgs : ∀ x : Q.nonprojective, x.1 ∉ Q.component r → g x = 0)
    (hhs : ∀ x : Q.nonprojective, x.1 ∈ Q.component r → h x = 0) (hgh : g + h ∈ imageD c m) :
    g ∈ imageD c m := by
  classical
  have hT := isTauClosed_periodic (Q := Q)
  have h1 := resF_imageD hT c hgh
  have h2 := projM_mem_imageD (c.restrict hT)
    (P := fun v : FullSub Q.periodic ↦ v.val ∈ Q.component r) (comp_iff_of_arrow r) h1
  have h3 : projM (c.restrict hT) (fun v : FullSub Q.periodic ↦ v.val ∈ Q.component r)
      (resF hT c (g + h)) = resF hT c g := by
    funext xS
    simp only [projM, resF]
    split_ifs with hx
    · rw [Pi.add_apply, hhs _ hx, add_zero]
    · rw [hgs _ hx, resE_zero]
  rw [h3] at h2
  have hz : cokerRes hT c m (Submodule.Quotient.mk ⟨g, hg⟩) = 0 := by
    change Submodule.Quotient.mk (⟨resF hT c g, resF_famDeg hT c hg⟩ : famDeg _ (m + 1)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact h2
  rw [← map_zero (cokerRes hT c m)] at hz
  have := (periodicLocalization c m).1 hz
  rw [Submodule.Quotient.mk_eq_zero] at this
  exact this

theorem row_mem_famDeg {m : ℕ} (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1)
    (hw : w.length = m + 1) (t : k) : t • row c x w ∈ famDeg c (m + 1) := by
  classical
  intro y
  rw [Pi.smul_apply, row]
  by_cases h : y = x
  · subst h; rw [Pi.single_eq_same, ← hw]; exact Submodule.smul_mem _ _ (pathMor_mem_degreePart c w)
  · rw [Pi.single_eq_of_ne h, smul_zero]; exact zero_mem _

/-- **Rows in distinct periodic components with nonzero classes are linearly independent.** -/
theorem rows_independent {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Q.nonprojective)
    (w : ∀ i, Quiver.Path (Q.tau (x i)).1 (x i).1) (hw : ∀ i, (w i).length = m + 1)
    (hper : ∀ i, (x i).1 ∈ Q.periodic) (hcomp : ∀ i j, (x j).1 ∈ Q.component (x i).1 → i = j)
    (hne : ∀ i, row c (x i) (w i) ∉ imageD c m) (l : ι → k)
    (h : ∑ i, l i • row c (x i) (w i) ∈ imageD c m) : ∀ i, l i = 0 := by
  classical
  intro j
  by_contra hl
  apply hne j
  have key : l j • row c (x j) (w j) ∈ imageD c m := by
    refine mem_imageD_of_supported c (x j).1 (h := ∑ i ∈ Finset.univ.erase j,
      l i • row c (x i) (w i)) (row_mem_famDeg c _ _ (hw j) _) (fun y hy ↦ ?_) (fun y hy ↦ ?_) ?_
    · have hyx : y ≠ x j := fun e ↦ hy (by rw [e]; exact mem_component_self (hper j))
      simp [row, hyx]
    · simp only [Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      have hyx : y ≠ x i := by
        rintro rfl
        exact hij (hcomp j i hy).symm
      simp [row, hyx]
    · rw [Finset.add_sum_erase Finset.univ (fun i ↦ l i • row c (x i) (w i)) (Finset.mem_univ j)]
      exact h
  have := Submodule.smul_mem _ (l j)⁻¹ key
  rwa [smul_smul, inv_mul_cancel₀ hl, one_smul] at this

/-! ### Rows and the cokernel -/

/-- The families of degree `m + 1` are spanned by the rows. -/
theorem famDeg_le_rows (m : ℕ) : famDeg c (m + 1) ≤
    Submodule.span k {f | ∃ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1),
      w.length = m + 1 ∧ f = row c x w} := by
  classical
  intro g hg
  rw [← Finset.univ_sum_single g]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hx := hg x
  rw [degreePart_eq_span] at hx
  generalize g x = φ at hx ⊢
  induction hx using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      exact Submodule.subset_span ⟨x, p, hp, rfl⟩
  | zero => rw [Pi.single_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Pi.single_add]; exact add_mem ha hb
  | smul t a _ ha => rw [Pi.single_smul]; exact Submodule.smul_mem _ t ha

/-- The span of the rows of `S` of degree `m + 1`, in the families. -/
def rowSpanF (m : ℕ) (S : RowSet Q) : Submodule k (MeshFamily c) :=
  Submodule.span k ((fun R ↦ row c R.1 R.2) '' {R | R ∈ S ∧ R.2.length = m + 1})

theorem rowSpan_eq_map (m : ℕ) (S : RowSet Q) :
    rowSpan c m S = (rowSpanF c m S).map (imageD c m).mkQ := by
  rw [rowSpan, rowSpanF, Submodule.map_span, ← Set.image_comp]
  rfl

/-- **A family of degree `m + 1` is a combination of the rows of a spanning set**, modulo
the image of `D_m`. -/
theorem exists_rowSpanF {S : RowSet Q} (hS : CokerSpan c S) {m : ℕ} (hm : 2 ≤ m)
    {g : MeshFamily c} (hg : g ∈ famDeg c (m + 1)) :
    ∃ n ∈ rowSpanF c m S, g - n ∈ imageD c m := by
  have h1 : g ∈ (rowSpan c m S).comap (imageD c m).mkQ := by
    refine Submodule.span_le.2 ?_ (famDeg_le_rows c m hg)
    rintro _ ⟨x, w, hw, rfl⟩
    exact hS m hm x w hw
  rw [Submodule.mem_comap, rowSpan_eq_map] at h1
  obtain ⟨n, hn, he⟩ := h1
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
  change (imageD c m).mkQ g - (imageD c m).mkQ n = 0
  rw [he, sub_self]

theorem rowSpanF_supported {m : ℕ} {S : RowSet Q} {r : V}
    (hS : ∀ R ∈ S, R.1.1 ∉ Q.component r) {n : MeshFamily c} (hn : n ∈ rowSpanF c m S) :
    ∀ x : Q.nonprojective, x.1 ∈ Q.component r → n x = 0 := by
  classical
  induction hn using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨R, ⟨hR, -⟩, rfl⟩ := hf
      intro x hx
      have hxR : x ≠ R.1 := fun e ↦ hS R hR (e ▸ hx)
      simp [row, hxR]
  | zero => intro x _; rfl
  | add a b _ _ ha hb => intro x hx; simp [ha x hx, hb x hx]
  | smul t a _ ha => intro x hx; simp [ha x hx]

/-- A periodic component is *residual* if `⊕_{m≥2} coker D_m(C)` has a nonzero class
supported on it. -/
def Residual (r : V) : Prop :=
  ∃ m, 2 ≤ m ∧ ∃ g ∈ famDeg c (m + 1), (∀ x : Q.nonprojective, x.1 ∉ Q.component r → g x = 0) ∧
    g ∉ imageD c m

/-! ### Proposition 6.1 -/

/-- **Proposition 6.1** (`prop:residual-correction-spaces`). In characteristic two, for a
finite-dimensional scalar mesh category on a finite translation quiver with at most one arrow
between ordered vertices, satisfying the brick hypothesis, there is a set `S` of rows `p_i`
at periodic vertices, at most one in each periodic component, such that:
* the classes `[p_i]` span `⊕_{m≥2} coker D_m(C)`, are nonzero, and are linearly independent
  (so `⊕_{m≥2} coker D_m(C) = ⊕_i k[p_i]`);
* a periodic component is residual exactly when it carries a row of `S` (so `S` is indexed by
  the residual components `I`);
* the component of each `p_i` is `ℤΔ/⟨τ^{s_i}ρ⟩` with `Δ` of type `D` or `E`, `ρ` fixing the
  centre, and `p_i` has degree `d_i = 2s_i + 2` (`StarTrace.DEModel`; in particular `d_i` is
  the only degree of a nonzero class on the component);
* the rows are killed by two over every coefficient ring (used for Lemma B.2). -/
theorem residualCorrectionSpaces [∀ x y : V, Fintype (x ⟶ y)] (hQ : HasAtMostOneArrow V)
    (hchar : (2 : k) = 0)
    (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ S : RowSet Q, (∀ R ∈ S, R.1.1 ∈ Q.periodic) ∧
      (∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R') ∧ CokerSpan c S ∧
      (∀ R ∈ S, row c R.1 R.2 ∉ imageD c (R.2.length - 1)) ∧
      (∀ (m : ℕ) (F : Finset (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)),
        (↑F : Set _) ⊆ S → (∀ R ∈ F, R.2.length = m + 1) →
        ∀ l : (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) → k,
          ∑ R ∈ F, l R • row c R.1 R.2 ∈ imageD c m → ∀ R ∈ F, l R = 0) ∧
      (∀ r ∈ Q.periodic, Residual c r ↔ ∃ R ∈ S, R.1.1 ∈ Q.component r) ∧
      (∀ R ∈ S, ∃ x, x ∈ Q.periodic ∧ R.1.1 ∈ Q.component x ∧
        ∃ R₀ : (Σ y : (restrict (isTauClosed_component (Q := Q) x)).nonprojective,
          Quiver.Path ((restrict (isTauClosed_component (Q := Q) x)).tau y).1 y.1),
          StarTrace.DEModel (TranslationQuiver.restrict_isStable (Q := Q) x) R₀ ∧
            R₀.2.length = R.2.length) ∧
      TwoRows.{0} Q S := by
  classical
  obtain ⟨S₀, hper, huniq, hspan, htwo₀, hmod⟩ := residual_cokerSpan_model.{_, _, _, 0} c hQ hchar hfin hbrick
  set S : RowSet Q := {R | R ∈ S₀ ∧ row c R.1 R.2 ∉ imageD c (R.2.length - 1)}
  have hSS : S ⊆ S₀ := fun R hR ↦ hR.1
  -- the lengths of the rows
  have hlen : ∀ R ∈ S₀, 4 ≤ R.2.length := by
    intro R hR
    obtain ⟨x, -, -, R₀, ⟨L, π, ρ, s, g, -, -, -, -, -, -, hs, -, -, hl⟩, he⟩ := hmod R hR
    rw [← he, hl]; omega
  -- spanning by the rows with nonzero classes
  have hspanS : CokerSpan c S := by
    intro m hm x w hw
    have h := hspan m hm x w hw
    refine (Submodule.span_le.2 ?_) h
    rintro _ ⟨R, ⟨hR, hRl⟩, rfl⟩
    by_cases hz : row c R.1 R.2 ∈ imageD c (R.2.length - 1)
    · have : rowClass c m R.1 R.2 = 0 := by
        rw [rowClass, Submodule.Quotient.mk_eq_zero]
        rwa [hRl, Nat.add_sub_cancel] at hz
      change rowClass c m R.1 R.2 ∈ rowSpan c m S
      rw [this]; exact zero_mem _
    · exact Submodule.subset_span ⟨R, ⟨⟨hR, hz⟩, hRl⟩, rfl⟩
  refine ⟨S, fun R hR ↦ hper R (hSS hR), fun R hR R' hR' h ↦ huniq R (hSS hR) R' (hSS hR') h,
    hspanS, fun R hR ↦ hR.2, ?_, ?_, fun R hR ↦ hmod R (hSS hR), htwo₀.mono hSS⟩
  · -- independence
    intro m F hF hFl l hl
    have key := rows_independent c (m := m) (ι := F) (fun R ↦ R.1.1) (fun R ↦ R.1.2)
      (fun R ↦ hFl R.1 R.2) (fun R ↦ hper R.1 (hSS (hF R.2)))
      (fun R R' h ↦ Subtype.ext (huniq R.1 (hSS (hF R.2)) R'.1 (hSS (hF R'.2)) h))
      (fun R ↦ by
        have := (hF R.2).2
        rwa [hFl R.1 R.2, Nat.add_sub_cancel] at this)
      (fun R ↦ l R.1) (by rwa [Finset.sum_coe_sort F (fun R ↦ l R • row c R.1 R.2)])
    exact fun R hR ↦ key ⟨R, hR⟩
  · intro r hr
    constructor
    · rintro ⟨m, hm, g, hg, hgs, hgn⟩
      by_contra hno
      push Not at hno
      obtain ⟨n, hn, hgn'⟩ := exists_rowSpanF c hspanS hm hg
      apply hgn
      refine mem_imageD_of_supported c r hg hgs (h := -n) (fun x hx ↦ ?_) (by rwa [← sub_eq_add_neg])
      rw [Pi.neg_apply, rowSpanF_supported c hno hn x hx, neg_zero]
    · rintro ⟨R, hR, hRr⟩
      refine ⟨R.2.length - 1, by have := hlen R (hSS hR); omega, row c R.1 R.2, ?_, fun x hx ↦ ?_,
        hR.2⟩
      · have := row_mem_famDeg c R.1 R.2 (m := R.2.length - 1)
          (by have := hlen R (hSS hR); omega) 1
        rwa [one_smul] at this
      · have hxR : x ≠ R.1 := by
          rintro rfl
          apply hx
          exact hRr
        simp [row, hxR]

end Support

end ScalarMeshCategory

end MultiplicativeBasisDeformations
