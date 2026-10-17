import MultiplicativeBasisDeformations.Foundations.ResidualCorrection
import MultiplicativeBasisDeformations.Foundations.ConnectedWt
import MultiplicativeBasisDeformations.Foundations.DualWeight

/-!
# Proposition 6.1 with dual mesh weights (for Proposition 7.5)

`residual_dual`: in characteristic two, under the hypotheses of Proposition 6.1, there is a
set `S` of spanning rows, at most one in each periodic component, together with integer
mesh weights `W_R` (`R ∈ S`) such that the weight of the row `R'` minus `ν` of its vertex
is `1` if `R' = R` and `0` otherwise. This is the input of Proposition 7.5: by Lemma 7.4
these give integer ray weights dual to the residual characters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

open ScalarMeshCategory TranslationQuiver MeshWalk

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {Q : TranslationQuiver V} [DecidablePred (· ∈ Q.nonprojective)] [Fintype Q.nonprojective]
  (c : MeshCoefficients k Q)

/-- **Proposition 6.1 with dual mesh weights.** -/
theorem residual_dual (hQ : HasAtMostOneArrow V) (hchar : (2 : k) = 0)
    (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ S : RowSet Q, (∀ R ∈ S, R.1.1 ∈ Q.periodic) ∧
      (∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R') ∧ CokerSpan c S ∧
      ∀ R ∈ S, ∃ W : MeshWt Q ℤ, ∀ R' ∈ S, W.pw R'.2 - W.ν R'.1 = if R' = R then 1 else 0 := by
  classical
  have : ∀ x y : V, Subsingleton (x ⟶ y) := hQ
  have hcomp : ∀ x : V, x ∈ Q.periodic →
      ∃ ST : RowSet (restrict (isTauClosed_component (Q := Q) x)),
        ST.Subsingleton ∧ CokerSpan (c.restrict (isTauClosed_component x)) ST ∧
        ∀ R ∈ ST, ∃ W : MeshWt (restrict (isTauClosed_component (Q := Q) x)) ℤ,
          W.pw R.2 - W.ν R.1 = 1 := by
    intro x hx
    have hS := TranslationQuiver.isTauClosed_component (Q := Q) x
    exact StarTrace.connected_cokerSpan_wt (TranslationQuiver.restrict_isStable (Q := Q) x)
      (c.restrict hS) (finiteDimensional_restrict hS c hfin) hchar
      (brickHypothesis_restrict hS c hbrick) (FullSub.mk x (mem_component_self hx))
      (TranslationQuiver.restrict_conn x hx)
  choose! ST hST hSTspan hSTwt using hcomp
  set S : RowSet Q := {R | ∃ x, x ∈ Q.periodic ∧ x = repr (Q := Q) (Q.component x) x ∧
    R ∈ inclRows (isTauClosed_component (Q := Q) x) (ST x)}
  -- the three properties of Proposition 6.1, as in `residual_cokerSpan`
  have hper : ∀ R ∈ S, R.1.1 ∈ Q.periodic := by
    rintro R ⟨x, hx, -, R₀, -, rfl⟩
    exact component_subset_periodic x R₀.1.1.2
  have hcomp1 : ∀ x x', x ∈ Q.periodic → x = repr (Q := Q) (Q.component x) x →
      x' ∈ Q.periodic → x' = repr (Q := Q) (Q.component x') x' →
      Q.component x' = Q.component x → x = x' := by
    intro x x' hx hxr hx' hxr' h
    rw [hxr, hxr']
    exact repr_congr h.symm ⟨x, hx, mem_component_self hx⟩ x x'
  have huniq : ∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R' := by
    rintro R ⟨x, hx, hxr, R₀, hR₀, rfl⟩ R' ⟨x', hx', hxr', R₀', hR₀', rfl⟩ hcomp'
    have h1 : Q.component R₀.1.1.val = Q.component x := component_eq_of_mem R₀.1.1.2
    have h2 : Q.component R₀'.1.1.val = Q.component x' := component_eq_of_mem R₀'.1.1.2
    have h3 : Q.component R₀'.1.1.val = Q.component R₀.1.1.val := component_eq_of_mem hcomp'
    obtain rfl := hcomp1 x x' hx hxr hx' hxr' (by rw [← h2, h3, h1])
    rw [hST x hx hR₀ hR₀']
  have hspan : CokerSpan c S := by
    -- the argument of `residual_cokerSpan`
    intro m hm x w hw
    by_cases hT : ∀ v ∈ w.vertices, v ∈ Q.periodic
    swap
    · push Not at hT
      obtain ⟨v, hv, hvT⟩ := hT
      have := row_mem_imageD_of_not_periodic c x w hw hv hvT
      rw [rowClass, (Submodule.Quotient.mk_eq_zero _).2 this]
      exact zero_mem _
    have hxT : x.1 ∈ Q.periodic := hT _ (Quiver.Path.end_mem_vertices w)
    set r := repr (Q := Q) (Q.component x.1) x.1
    have hrc : Q.component r = Q.component x.1 := repr_component hxT
    have hr : r ∈ Q.periodic := component_subset_periodic _ (repr_mem hxT)
    have hrr : r = repr (Q := Q) (Q.component r) r :=
      (repr_congr hrc (⟨x.1, hxT, hrc ▸ mem_component_self hxT⟩) r x.1).symm
    have hxr : x.1 ∈ Q.component r := by rw [hrc]; exact mem_component_self hxT
    set hS := isTauClosed_component (Q := Q) r
    have hin : ∀ v ∈ w.vertices, v ∈ Q.component r :=
      vertices_mem_component ((hS x.1 x.2).1 hxr) w hT
    let xS : (restrict hS).nonprojective := ⟨FullSub.mk x.1 hxr, x.2⟩
    let wS : Quiver.Path ((restrict hS).tau xS).1 xS.1 := FullSub.liftPath _ _ w hin
    have hwS : wS.length = m + 1 := by rw [FullSub.length_liftPath, hw]
    have hout : ∀ (x' : Q.nonprojective) (w' : Quiver.Path (Q.tau x').1 x'.1), w'.length = m + 1 →
        x'.1 ∈ Q.component r → (∃ v ∈ w'.vertices, v ∉ Q.component r) → row c x' w' ∈ imageD c m := by
      intro x' w' hw' hx' hout
      by_cases hT' : ∀ v ∈ w'.vertices, v ∈ Q.periodic
      · exfalso
        obtain ⟨v, hv, hvK⟩ := hout
        have hstart : (Q.tau x').1 ∈ Q.component r := (hS x'.1 x'.2).1 hx'
        exact hvK (vertices_mem_component hstart w' hT' v hv)
      · push Not at hT'
        obtain ⟨v, hv, hvT⟩ := hT'
        exact row_mem_imageD_of_not_periodic c x' w' hw' hv hvT
    have := rowClass_mem_rowSpan_of_restrict hS c hout (ST r) xS wS hwS
      (hSTspan r hr m hm xS wS hwS)
    rw [FullSub.incl_mapPath_liftPath] at this
    exact rowSpan_mono c (fun R hR ↦ show R ∈ S from ⟨r, hr, hrr, hR⟩) this
  refine ⟨S, hper, huniq, hspan, ?_⟩
  -- the dual mesh weights
  rintro R ⟨x, hx, hxr, R₀, hR₀, rfl⟩
  obtain ⟨WT, hWT⟩ := hSTwt x hx R₀ hR₀
  obtain ⟨W, hw, hν, hoff⟩ := exists_ext_wt c hfin x WT
  refine ⟨W, ?_⟩
  rintro R' ⟨x', hx', hxr', R₀', hR₀', rfl⟩
  by_cases hc : Q.component x' = Q.component x
  · obtain rfl := hcomp1 x x' hx hxr hx' hxr' hc
    obtain rfl := hST x hx hR₀ hR₀'
    rw [if_pos rfl]
    change W.pw ((FullSub.incl _).mapPath R₀.2) - W.ν ⟨R₀.1.1.val, R₀.1.2⟩ = 1
    rw [pw_incl_of _ W WT (fun {a b} e ↦ hw e a.2 b.2), hν _ R₀.1.1.2]
    exact hWT
  · have hne : (⟨⟨R₀'.1.1.val, R₀'.1.2⟩, (FullSub.incl _).mapPath R₀'.2⟩ :
        Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) ≠ ⟨⟨R₀.1.1.val, R₀.1.2⟩,
          (FullSub.incl _).mapPath R₀.2⟩ := by
      intro h
      apply hc
      have h1 := congrArg (fun R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1 ↦ R.1.1) h
      simp only at h1
      have e1 : Q.component R₀'.1.1.val = Q.component x' := component_eq_of_mem R₀'.1.1.2
      have e2 : Q.component R₀.1.1.val = Q.component x := component_eq_of_mem R₀.1.1.2
      rw [← e1, ← e2, h1]
    rw [if_neg hne]
    obtain ⟨hw', hν'⟩ := hoff x' hc
    change W.pw ((FullSub.incl _).mapPath R₀'.2) - W.ν ⟨R₀'.1.1.val, R₀'.1.2⟩ = 0
    rw [pw_incl_zero W (fun {a b} e ↦ hw' e a.2 b.2), hν' _ R₀'.1.1.2, sub_zero]

end MultiplicativeBasisDeformations
