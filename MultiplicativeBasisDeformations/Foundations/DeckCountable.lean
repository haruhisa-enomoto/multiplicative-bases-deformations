module

public import MultiplicativeBasisDeformations.Foundations.DeckGrading
public import MultiplicativeBasisDeformations.Foundations.SectionalPaths

/-!
# The deck group is countable

The exhaustion of Lemma 4.12 enumerates the objects of `L`; for this the deck
group must be countable. Its elements are classes of walks in a finite complex:
paths in the symmetrized edge quiver are determined by their lists of edges
(`arrowList_injective`), and the fundamental groupoid is a quotient of the path
category.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace Quiver.Path

universe v w

variable {V : Type v} [Quiver.{w} V]

theorem arrowList_inj {x : V} : ∀ {y : V} (p q : Quiver.Path x y),
    arrowList p = arrowList q → p = q
  | _, Quiver.Path.nil, q, h => by
      cases q with
      | nil => rfl
      | cons q a => simp at h
  | _, Quiver.Path.cons p a, q, h => by
      cases q with
      | nil => simp at h
      | cons q b =>
          simp only [arrowList_cons] at h
          obtain ⟨h1, h2⟩ := List.append_inj' h rfl
          simp only [List.cons.injEq, Sigma.mk.injEq, and_true] at h2
          obtain ⟨rfl, h3⟩ := h2
          have h4 : a = b := by
            simpa using h3
          subst h4
          rw [arrowList_inj p q h1]

instance instCountable [Countable (Σ u v : V, u ⟶ v)] {x y : V} : Countable (Quiver.Path x y) :=
  Function.Injective.countable (fun p q h ↦ arrowList_inj p q h)

end Quiver.Path

namespace MultiplicativeBasisDeformations

namespace MeshWalk

variable {V : Type} [Quiver.{0} V] [Fintype V] (Q : TranslationQuiver V)
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (v₀ : V)

instance : Countable (Arr V) :=
  Function.Injective.countable (f := fun a : Arr V ↦ (⟨a.2.1, a.1, a.2.2⟩ : Σ X : V, Σ Y : V, Y ⟶ X))
    (by rintro ⟨y, x, a⟩ ⟨y', x', a'⟩ h; simp only [Sigma.mk.injEq] at h; obtain ⟨rfl, h⟩ := h;
        simp only [heq_eq_eq, Sigma.mk.injEq] at h; obtain ⟨rfl, h⟩ := h; cases h; rfl)

instance : Countable (Ed Q ⊕ V) := inferInstanceAs (Countable ((Arr V ⊕ Q.nonprojective) ⊕ V))

/-- **The deck group is countable.** -/
instance countable_deck : Countable (Deck Q v₀) := by
  let E := Morse.EQ (srcC Q v₀) (tgtC Q)
  let instE : Quiver E := Morse.instQuiverEQ _ _
  let instS : Quiver (Quiver.Symmetrify E) := @Quiver.symmetrifyQuiver E instE
  have hE : ∀ X Y : E, Countable (@Quiver.Hom E instE X Y) := fun X Y ↦
    inferInstanceAs (Countable {e : Ed Q ⊕ V // srcC Q v₀ e = X ∧ tgtC Q e = Y})
  have hV : Countable E := inferInstanceAs (Countable V)
  have hSig : Countable (Σ u v : Quiver.Symmetrify E, @Quiver.Hom _ instS u v) :=
    @instCountableSigma _ _ hV fun u ↦ @instCountableSigma _ _ hV fun v ↦
      @instCountableSum _ _ (hE u v) (hE v u)
  have hP : Countable (@Quiver.Path (Quiver.Symmetrify E) instS v₀ v₀) :=
    @Quiver.Path.instCountable _ instS hSig v₀ v₀
  let φ : @Quiver.Path (Quiver.Symmetrify E) instS v₀ v₀ → Deck Q v₀ := fun p ↦
    MulOpposite.op ((Morse.Qf (S := coneTris Q v₀)).map
      ((CategoryTheory.Quotient.functor (@Quiver.FreeGroupoid.redStep E instE)).map p))
  refine Function.Surjective.countable (f := φ) fun d ↦ ?_
  obtain ⟨f', hf'⟩ := (Morse.Qf (S := coneTris Q v₀)).map_surjective d.unop
  obtain ⟨p, hp⟩ := (CategoryTheory.Quotient.functor
    (@Quiver.FreeGroupoid.redStep E instE)).map_surjective f'
  exact ⟨p, by
    apply MulOpposite.unop_injective
    change (Morse.Qf (S := coneTris Q v₀)).map _ = d.unop
    rw [hp, hf']⟩

end MeshWalk

end MultiplicativeBasisDeformations
