import MultiplicativeBasisDeformations.Foundations.PeriodicComponents
import MultiplicativeBasisDeformations.Foundations.ObjectQuotients
import MultiplicativeBasisDeformations.Foundations.SectionalCover

/-!
# Periodic components are connected stable translation quivers

Proof of Proposition 5.3, reduction to components (`periodic-mesh-calculations.tex:
232–236`): on a finite translation quiver, a periodic component `K` is closed
under `τ^{±1}` and every vertex of `K` is the translate of a vertex of `K`, so
the full translation subquiver on `K` is stable; it is connected by arrows and
translation edges.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace MultiplicativeBasisDeformations

universe v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}

theorem periodic_nonproj {v : V} (hv : v ∈ Q.periodic) : v ∈ Q.nonprojective :=
  ((isTauPeriodic_iff v).1 hv).1

theorem periodic_tau {v : V} (hv : v ∈ Q.periodic) :
    (Q.tau ⟨v, periodic_nonproj hv⟩).1 ∈ Q.periodic :=
  ((isTauPeriodic_iff v).1 hv).2

/-- **On a finite quiver periodic vertices are translates**, hence noninjective. -/
theorem periodic_mem_noninjective [Finite V] {v : V} (hv : v ∈ Q.periodic) :
    v ∈ Q.noninjective := by
  let φ : Q.periodic → Q.periodic := fun w ↦ ⟨(Q.tau ⟨w.1, periodic_nonproj w.2⟩).1, periodic_tau w.2⟩
  have hφ : Function.Injective φ := by
    intro a b h
    have h1 := Subtype.ext_iff.1 h
    have h2 := Q.tau.injective (Subtype.ext h1)
    exact Subtype.ext (Subtype.mk.inj h2)
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hφ) ⟨v, hv⟩
  have : (Q.tau ⟨w.1, periodic_nonproj w.2⟩).1 = v := congrArg Subtype.val hw
  rw [← this]
  exact (Q.tau _).2

variable (x : V)

/-- **The full subquiver on a periodic component is stable.** -/
theorem restrict_isStable [Finite V] : (restrict (isTauClosed_component (Q := Q) x)).IsStable := by
  constructor
  · ext a; simp only [Set.mem_univ, iff_true]
    exact periodic_nonproj (component_subset_periodic x a.val_mem)
  · ext a; simp only [Set.mem_univ, iff_true]
    exact periodic_mem_noninjective (component_subset_periodic x a.val_mem)

/-- **A periodic component is connected** by arrows and translation edges. -/
theorem restrict_conn [Finite V] (hx : x ∈ Q.periodic) (a : FullSub (Q.component x)) :
    Relation.EqvGen (SecPath.ConnAdj (restrict_isStable (Q := Q) x))
      (FullSub.mk x (mem_component_self hx)) a := by
  have key : ∀ u v : V, Relation.EqvGen Q.PeriodicAdj u v →
      (u ∈ Q.component x ↔ v ∈ Q.component x) ∧
      ∀ (hu : u ∈ Q.component x) (hv : v ∈ Q.component x),
        Relation.EqvGen (SecPath.ConnAdj (restrict_isStable (Q := Q) x))
          (FullSub.mk u hu) (FullSub.mk v hv) := by
    intro u v huv
    induction huv with
    | rel u v h =>
        obtain ⟨huT, hvT, h'⟩ := id h
        refine ⟨⟨fun hu ↦ ⟨hvT, Relation.EqvGen.trans _ _ _ hu.2 (Relation.EqvGen.rel _ _ h)⟩,
          fun hv ↦ ⟨huT, Relation.EqvGen.trans _ _ _ hv.2
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h))⟩⟩, fun hu hv ↦ ?_⟩
        refine Relation.EqvGen.rel _ _ ?_
        rcases h' with he | ⟨hu', he⟩
        · exact Or.inl he
        · right
          apply FullSub.ext
          change v = (Q.tau ⟨u, _⟩).1
          exact he.symm
    | refl u => exact ⟨Iff.rfl, fun hu _ ↦ Relation.EqvGen.refl _⟩
    | symm u v _ ih =>
        exact ⟨ih.1.symm, fun hv hu ↦ Relation.EqvGen.symm _ _ (ih.2 hu hv)⟩
    | trans u v w _ _ ih1 ih2 =>
        refine ⟨ih1.1.trans ih2.1, fun hu hw ↦ ?_⟩
        have hv := ih1.1.1 hu
        exact Relation.EqvGen.trans _ _ _ (ih1.2 hu hv) (ih2.2 hv hw)
  exact (key x a.val a.val_mem.2).2 (mem_component_self hx) a.val_mem

end TranslationQuiver

end MultiplicativeBasisDeformations
