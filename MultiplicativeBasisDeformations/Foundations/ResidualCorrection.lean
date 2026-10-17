import MultiplicativeBasisDeformations.Foundations.ConnectedChar2
import MultiplicativeBasisDeformations.Foundations.ComponentSpan
import MultiplicativeBasisDeformations.Foundations.ComponentGlue
import MultiplicativeBasisDeformations.Foundations.ObjectQuotients

/-!
# Proposition 6.1: residual correction spaces (spanning form)

`prop:residual-correction-spaces` (`positive-deformations.tex`) and Appendix B: in
characteristic two, under the brick hypothesis, "each periodic component contributes at
most one correction line, represented by a single path". We record: there is a set `S`
of rows at periodic vertices, at most one in each periodic component, whose classes
span all derivative cokernels in degrees at least three (`residual_cokerSpan`).

Deviation from the source: the source takes `I` to be exactly the components with a
nonzero class; we keep all components with a candidate row (a superset), which is what
the spanning statement needs. The component models and degrees of the rows are recorded
by `connected_cokerSpan` and the files `StarDSpan`, `StarESpan`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w u₂

open ScalarMeshCategory TranslationQuiver

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}

theorem component_eq_of_mem {x y : V} (hy : y ∈ Q.component x) : Q.component y = Q.component x := by
  ext v
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, Relation.EqvGen.trans _ _ _ hy.2 h⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hy.2) h⟩

end TranslationQuiver

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] [Fintype V] [DecidableEq V]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {Q : TranslationQuiver V} [DecidablePred (· ∈ Q.nonprojective)] [Fintype Q.nonprojective]
  (c : MeshCoefficients k Q)

open Classical in
/-- A canonical vertex of a set of vertices. -/
def repr (T : Set V) (d : V) : V := if h : ∃ x ∈ Q.periodic, x ∈ T then Classical.choose h else d

theorem repr_congr {T T' : Set V} (h : T = T') (hT : ∃ y ∈ Q.periodic, y ∈ T) (d d' : V) :
    repr (Q := Q) T d = repr (Q := Q) T' d' := by
  classical
  subst h
  unfold repr
  rw [dif_pos hT, dif_pos hT]

theorem repr_mem {x : V} (hx : x ∈ Q.periodic) : repr (Q := Q) (Q.component x) x ∈ Q.component x := by
  classical
  have h : ∃ y ∈ Q.periodic, y ∈ Q.component x := ⟨x, hx, mem_component_self hx⟩
  unfold repr
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

theorem repr_component {x : V} (hx : x ∈ Q.periodic) :
    Q.component (repr (Q := Q) (Q.component x) x) = Q.component x :=
  component_eq_of_mem (repr_mem hx)

/-- **Proposition 6.1, spanning form with the model data**: as `residual_cokerSpan`, and each
spanning row comes from a row of its periodic component of type `D` or `E` and degree
`2s + 2` (`StarTrace.DEModel`). -/
theorem residual_cokerSpan_model (hQ : HasAtMostOneArrow V) (hchar : (2 : k) = 0)
    (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ S : RowSet Q, (∀ R ∈ S, R.1.1 ∈ Q.periodic) ∧
      (∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R') ∧ CokerSpan c S ∧
      TwoRows.{u₂} Q S ∧
      ∀ R ∈ S, ∃ x, x ∈ Q.periodic ∧ R.1.1 ∈ Q.component x ∧
        ∃ R₀ : (Σ y : (restrict (isTauClosed_component (Q := Q) x)).nonprojective,
          Quiver.Path ((restrict (isTauClosed_component (Q := Q) x)).tau y).1 y.1),
          StarTrace.DEModel (TranslationQuiver.restrict_isStable (Q := Q) x) R₀ ∧
            R₀.2.length = R.2.length := by
  classical
  have : ∀ x y : V, Subsingleton (x ⟶ y) := hQ
  -- the spanning row of each periodic component
  have hcomp : ∀ x : V, x ∈ Q.periodic → ∃ ST : RowSet (restrict (isTauClosed_component (Q := Q) x)),
      ST.Subsingleton ∧ CokerSpan (c.restrict (isTauClosed_component x)) ST ∧
        TwoRows.{u₂} (restrict (isTauClosed_component (Q := Q) x)) ST ∧
        ∀ R ∈ ST, StarTrace.DEModel (TranslationQuiver.restrict_isStable (Q := Q) x) R := by
    intro x hx
    have hS := TranslationQuiver.isTauClosed_component (Q := Q) x
    exact StarTrace.connected_cokerSpan_model (TranslationQuiver.restrict_isStable (Q := Q) x)
      (c.restrict hS) (finiteDimensional_restrict hS c hfin) hchar
      (brickHypothesis_restrict hS c hbrick) (FullSub.mk x (mem_component_self hx))
      (TranslationQuiver.restrict_conn x hx)
  choose! ST hST hSTspan hST2 hSTmod using hcomp
  set S : RowSet Q := {R | ∃ x, x ∈ Q.periodic ∧ x = repr (Q := Q) (Q.component x) x ∧
    R ∈ inclRows (isTauClosed_component (Q := Q) x) (ST x)}
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · rintro R ⟨x, hx, -, R₀, -, rfl⟩
    exact component_subset_periodic x R₀.1.1.2
  · rintro R ⟨x, hx, hxr, R₀, hR₀, rfl⟩ R' ⟨x', hx', hxr', R₀', hR₀', rfl⟩ hcomp'
    -- the two rows lie in the same periodic component
    have h1 : Q.component R₀.1.1.val = Q.component x := component_eq_of_mem R₀.1.1.2
    have h2 : Q.component R₀'.1.1.val = Q.component x' := component_eq_of_mem R₀'.1.1.2
    have h3 : Q.component R₀'.1.1.val = Q.component R₀.1.1.val := component_eq_of_mem hcomp'
    have hxx : x = x' := by
      rw [hxr, hxr']
      exact repr_congr (by rw [← h1, ← h3, h2]) ⟨x, hx, mem_component_self hx⟩ x x'
    subst hxx
    rw [hST x hx hR₀ hR₀']
  · intro m hm x w hw
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
  · -- the rows are killed by two over every coefficient ring
    intro O _ u m hm R hR hlen
    obtain ⟨x, hx, -, hRx⟩ := hR
    obtain ⟨R0, hR0, hRe⟩ := hRx
    subst hRe
    have hS := isTauClosed_component (Q := Q) x
    have hout : ∀ (x' : Q.nonprojective) (w' : Quiver.Path (Q.tau x').1 x'.1), w'.length = m + 1 →
        x'.1 ∈ Q.component x → (∃ v ∈ w'.vertices, v ∉ Q.component x) → row u x' w' ∈ imageD u m := by
      intro x' w' hw' hx' hout
      by_cases hT' : ∀ v ∈ w'.vertices, v ∈ Q.periodic
      · exfalso
        obtain ⟨v, hv, hvK⟩ := hout
        have hstart : (Q.tau x').1 ∈ Q.component x := (hS x'.1 x'.2).1 hx'
        exact hvK (vertices_mem_component hstart w' hT' v hv)
      · push Not at hT'
        obtain ⟨v, hv, hvT⟩ := hT'
        exact row_mem_imageD_of_not_periodic u x' w' hw' hv hvT
    have hlen' : R0.2.length = m + 1 := by
      have := hlen; simp only at this; rwa [LinearPaths.length_mapPath] at this
    exact two_rowClass_of_restrict hS u hout R0.1 R0.2 hlen'
      (hST2 x hx O (u.restrict hS) m hm R0 hR0 hlen')
  · rintro R ⟨x, hx, -, R₀, hR₀, rfl⟩
    exact ⟨x, hx, R₀.1.1.2, R₀, hSTmod x hx R₀ hR₀, by simp [LinearPaths.length_mapPath]⟩

/-- **Proposition 6.1, spanning form** (`prop:residual-correction-spaces`). In
characteristic two, for a finite-dimensional scalar mesh category on a finite translation
quiver with at most one arrow between ordered vertices, satisfying the brick hypothesis,
there is a set of rows at periodic vertices, at most one in each periodic component,
whose classes span the cokernels of all `D_m`, `m ≥ 2`. -/
theorem residual_cokerSpan (hQ : HasAtMostOneArrow V) (hchar : (2 : k) = 0)
    (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ S : RowSet Q, (∀ R ∈ S, R.1.1 ∈ Q.periodic) ∧
      (∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R') ∧ CokerSpan c S ∧
      TwoRows.{u₂} Q S := by
  obtain ⟨S, h1, h2, h3, h4, -⟩ := residual_cokerSpan_model.{_, _, _, u₂} c hQ hchar hfin hbrick
  exact ⟨S, h1, h2, h3, h4⟩

end MultiplicativeBasisDeformations
