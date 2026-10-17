import MultiplicativeBasisDeformations.Foundations.ComponentTransfer
import MultiplicativeBasisDeformations.Foundations.RowSpan

/-!
# Periodic localization for spanning rows

`prop:periodic-localization` (`scalar-normalization.tex`), as used in Appendix B: "The
quotient maps in Proposition 5.1 specify the direct-sum identification." We extend the
transfer `row_mem_imageD_of_restrict` from one row to any family of path combinations
on a `τ`-closed subquiver `Q_S` (`inclRow_mem_imageD`): if its classes lie in the image of
`D_m(C(Q_S))`, its inclusion lies in the image of `D_m(C(Q))`, provided the rows through
vertices outside `S` do. Consequently spanning rows transfer
(`rowClass_mem_rowSpan_of_restrict`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

open ScalarMeshCategory TranslationQuiver

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {S : Set V} (hS : Q.IsTauClosed S)
  (c : MeshCoefficients k Q) [DecidablePred (· ∈ S)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]

/-- A family of morphisms of `kQ_S` at the rows of `Q_S`. -/
abbrev RowFam :=
  ∀ xS : (restrict hS).nonprojective,
    LinearPaths.obj (k := k) ((restrict hS).tau xS).1 ⟶ LinearPaths.obj (k := k) xS.1

/-- The inclusion of a family on `Q_S` into the mesh families of `Q`. -/
def inclRow (G : RowFam (k := k) hS) : MeshFamily c := fun x ↦
  if hx : x.1 ∈ S then
    (RelationCategory.functor k (meshRelations c)).map
      (FullSub.inclL k _ _ (G ⟨FullSub.mk x.1 hx, x.2⟩))
  else 0

theorem inclRow_add (G G' : RowFam (k := k) hS) :
    inclRow hS c (G + G') = inclRow hS c G + inclRow hS c G' := by
  funext x
  simp only [inclRow, Pi.add_apply]
  split_ifs
  · rw [map_add, Functor.map_add]
  · rw [add_zero]

theorem inclRow_smul (a : k) (G : RowFam (k := k) hS) :
    inclRow hS c (a • G) = a • inclRow hS c G := by
  funext x
  simp only [inclRow, Pi.smul_apply]
  split_ifs
  · rw [map_smul, Functor.map_smul]
  · rw [smul_zero]

theorem inclRow_zero : inclRow hS c (0 : RowFam (k := k) hS) = 0 := by
  funext x
  simp only [inclRow, Pi.zero_apply]
  split_ifs
  · rw [map_zero, Functor.map_zero]
  · rfl

theorem inclRow_sum {ι : Type*} (s : Finset ι) (G : ι → RowFam (k := k) hS) :
    inclRow hS c (∑ i ∈ s, G i) = ∑ i ∈ s, inclRow hS c (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact inclRow_zero hS c
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, inclRow_add, ih]

theorem inclRow_sub (G G' : RowFam (k := k) hS) :
    inclRow hS c (G - G') = inclRow hS c G - inclRow hS c G' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, inclRow_add, ← neg_one_smul k G', inclRow_smul, neg_one_smul]

variable [Fintype V]

set_option maxHeartbeats 800000 in
/-- **Proposition 5.1, transfer of families to a `τ`-closed subquiver.** -/
theorem inclRow_mem_imageD {m : ℕ}
    (hout : ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
      x.1 ∈ S → (∃ v ∈ w.vertices, v ∉ S) → row c x w ∈ imageD c m)
    (G : RowFam (k := k) hS) (hGd : ∀ xS, G xS ∈ LinearPaths.degreePart (k := k) (m + 1) _ _)
    (hG : (fun xS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map (G xS)) ∈
      imageD (c.restrict hS) m) : inclRow hS c G ∈ imageD c m := by
  obtain ⟨f, hf, hDf⟩ := hG
  choose F hF hFf using fun b ↦ hf b
  have hFf' : f = fun b ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map
      (F b) := funext fun b ↦ (hFf b).symm
  have hlift := liftFamily_mem c F hF
  suffices h : meshDerivative c (liftFamily c F) - inclRow hS c G ∈ imageD c m by
    have := sub_mem (Submodule.mem_map.2 ⟨liftFamily c F, hlift, rfl⟩ :
      meshDerivative c (liftFamily c F) ∈ imageD c m) h
    rwa [sub_sub_cancel] at this
  classical
  rw [← Finset.univ_sum_single (meshDerivative c (liftFamily c F) - inclRow hS c G)]
  refine sum_mem fun x' _ ↦ ?_
  by_cases hx' : x'.1 ∈ S
  · let x'S : (TranslationQuiver.restrict hS).nonprojective := ⟨FullSub.mk x'.1 hx', x'.2⟩
    have hD := meshDerivative_liftFamily hS c F x'S
    have hDS := congrFun hDf x'S
    rw [hFf', meshDerivativeₗ_apply, ← map_derivPath] at hDS
    have e1 : (meshDerivative c (liftFamily c F) - inclRow hS c G) x' =
        (RelationCategory.functor k (meshRelations c)).map
          (inclDeriv hS c F x'S - FullSub.inclL k _ _ (G x'S)) := by
      rw [Pi.sub_apply, inclRow, dif_pos hx', Functor.map_sub, ← hD]
    rw [e1]
    refine single_mem_imageD_of_mem_sup c hout x' hx' ?_ ?_
    · have hE : derivPath hS c F x'S - G x'S ∈ meshIdealSub (c.restrict hS) _ _ := by
        have := (RelationCategory.functor_map_eq_zero_iff (k := k) _ _).1
          (show (RelationCategory.functor k (meshRelations (c.restrict hS))).map
            (derivPath hS c F x'S - G x'S) = 0 by
              rw [Functor.map_sub, hDS]; exact sub_self _)
        exact this
      have := inclL_mem_ideal_sup_outside hS c hE
      rw [map_sub] at this
      exact this
    · exact sub_mem (LinearPaths.mapPaths_mem_degreePart (FullSub.incl S)
        (derivPath_mem hS c F hF x'S)) (LinearPaths.mapPaths_mem_degreePart (FullSub.incl S) (hGd x'S))
  · rw [Pi.sub_apply, meshDerivative_liftFamily_of_not_mem hS c F x' hx', inclRow, dif_neg hx',
      sub_zero, Pi.single_zero]
    exact zero_mem _

/-! ### Spanning rows -/

/-- The family of one row of `Q_S`. -/
def rowP (xS : (restrict hS).nonprojective) (p : Quiver.Path ((restrict hS).tau xS).1 xS.1) :
    RowFam (k := k) hS :=
  Pi.single xS (LinearPaths.path p)

theorem map_rowP (xS : (restrict hS).nonprojective) (p : Quiver.Path ((restrict hS).tau xS).1 xS.1) :
    (fun yS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map (rowP hS xS p yS)) =
      row (c.restrict hS) xS p := by
  funext yS
  by_cases h : yS = xS
  · subst h; simp [rowP, row, pathMor]
  · simp [rowP, row, Pi.single_eq_of_ne h]

theorem map_rowP_apply (xS : (restrict hS).nonprojective)
    (p : Quiver.Path ((restrict hS).tau xS).1 xS.1) (yS : (restrict hS).nonprojective) :
    (RelationCategory.functor k (meshRelations (c.restrict hS))).map (rowP hS xS p yS) =
      row (c.restrict hS) xS p yS :=
  congrFun (map_rowP hS c xS p) yS

theorem inclRow_rowP (xS : (restrict hS).nonprojective)
    (p : Quiver.Path ((restrict hS).tau xS).1 xS.1) :
    inclRow hS c (rowP hS xS p) = row c (restrictNonproj hS xS) ((FullSub.incl S).mapPath p) := by
  funext x
  unfold inclRow
  split_ifs with hx
  · by_cases h : (⟨FullSub.mk x.1 hx, x.2⟩ : (restrict hS).nonprojective) = xS
    · subst h
      simp only [rowP, row, Pi.single_eq_same]
      rw [LinearPaths.mapPaths_path]; rfl
    · have h' : x ≠ restrictNonproj hS xS := fun e ↦ h (by subst e; rfl)
      simp only [rowP, row, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', map_zero, Functor.map_zero]
  · have h' : x ≠ restrictNonproj hS xS := fun e ↦ hx (by subst e; exact xS.1.2)
    simp only [row, Pi.single_eq_of_ne h']

theorem rowP_mem {m : ℕ} (xS : (restrict hS).nonprojective)
    (p : Quiver.Path ((restrict hS).tau xS).1 xS.1) (hp : p.length = m + 1)
    (yS : (restrict hS).nonprojective) :
    rowP (k := k) hS xS p yS ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := by
  by_cases h : yS = xS
  · subst h; simp only [rowP, Pi.single_eq_same, ← hp]; exact LinearPaths.path_mem_degreePart _
  · simp only [rowP, Pi.single_eq_of_ne h]; exact zero_mem _

/-- The rows of `Q_S` as rows of `Q`. -/
def inclRows (ST : RowSet (restrict hS)) : RowSet Q :=
  (fun R ↦ (⟨restrictNonproj hS R.1, (FullSub.incl S).mapPath R.2⟩ :
    Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)) '' ST

set_option maxHeartbeats 800000 in
/-- **Rows killed by two transfer from `Q_S` to `Q`.** -/
theorem two_rowClass_of_restrict {m : ℕ}
    (hout : ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
      x.1 ∈ S → (∃ v ∈ w.vertices, v ∉ S) → row c x w ∈ imageD c m)
    (xS : (restrict hS).nonprojective) (wS : Quiver.Path ((restrict hS).tau xS).1 xS.1)
    (hwS : wS.length = m + 1) (hT : (2 : k) • rowClass (c.restrict hS) m xS wS = 0) :
    (2 : k) • rowClass c m (restrictNonproj hS xS) ((FullSub.incl S).mapPath wS) = 0 := by
  classical
  have hG : (fun yS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map
      (((2 : k) • rowP hS xS wS) yS)) ∈ imageD (c.restrict hS) m := by
    have e : (fun yS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map
        (((2 : k) • rowP hS xS wS) yS)) = (2 : k) • row (c.restrict hS) xS wS := by
      funext yS
      rw [Pi.smul_apply, Functor.map_smul, map_rowP_apply, Pi.smul_apply]
    rw [e]
    rw [rowClass, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hT
    exact hT
  have h := inclRow_mem_imageD hS c hout ((2 : k) • rowP hS xS wS)
    (fun yS ↦ Submodule.smul_mem _ _ (rowP_mem hS xS wS hwS yS)) hG
  rw [inclRow_smul, inclRow_rowP] at h
  rw [rowClass, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h

set_option maxHeartbeats 800000 in
/-- **Spanning rows transfer from `Q_S` to `Q`.** -/
theorem rowClass_mem_rowSpan_of_restrict {m : ℕ}
    (hout : ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
      x.1 ∈ S → (∃ v ∈ w.vertices, v ∉ S) → row c x w ∈ imageD c m)
    (ST : RowSet (restrict hS)) (xS : (restrict hS).nonprojective)
    (wS : Quiver.Path ((restrict hS).tau xS).1 xS.1) (hwS : wS.length = m + 1)
    (hT : rowClass (c.restrict hS) m xS wS ∈ rowSpan (c.restrict hS) m ST) :
    rowClass c m (restrictNonproj hS xS) ((FullSub.incl S).mapPath wS) ∈
      rowSpan c m (inclRows hS ST) := by
  classical
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set' (R := k)).1 hT
  choose R hR hgR using fun i ↦ (g i).2
  -- the family `row xS wS - ∑ f i • row (R i)`
  set G : RowFam (k := k) hS := rowP hS xS wS - ∑ i, f i • rowP hS (R i).1 (R i).2
  have hGd : ∀ yS, G yS ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := by
    intro yS
    simp only [G, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    exact sub_mem (rowP_mem hS xS wS hwS yS)
      (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (rowP_mem hS _ _ (hR i).2 yS))
  have hG : (fun yS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map (G yS)) ∈
      imageD (c.restrict hS) m := by
    have e : (fun yS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map (G yS)) =
        row (c.restrict hS) xS wS - ∑ i, f i • row (c.restrict hS) (R i).1 (R i).2 := by
      funext yS
      simp only [G, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Functor.map_sub,
        Functor.map_sum, Functor.map_smul, map_rowP_apply]
    rw [e, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← rowClass, ← hfg,
      ← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, ← hgR, rowClass]
    exact sub_self _
  have h := inclRow_mem_imageD hS c hout G hGd hG
  rw [inclRow_sub, inclRow_rowP, inclRow_sum, ← Submodule.Quotient.mk_eq_zero] at h
  simp only [inclRow_smul, inclRow_rowP] at h
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at h
  simp only [← Submodule.mkQ_apply] at h
  rw [map_sum] at h
  rw [rowClass, ← Submodule.mkQ_apply, h]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_smul, Submodule.mkQ_apply]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨⟨R i, (hR i).1, rfl⟩, ?_⟩, rfl⟩)
  simp only
  rw [LinearPaths.length_mapPath]; exact (hR i).2

end MultiplicativeBasisDeformations
