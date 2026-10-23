module

public import MultiplicativeBasisDeformations.Foundations.ObjectValues
public import MultiplicativeBasisDeformations.Foundations.Descent
public import MultiplicativeBasisDeformations.Foundations.A0Basis
public import MultiplicativeBasisDeformations.Foundations.DeckCountable
public import MultiplicativeBasisDeformations.Foundations.A0RepFinite
public import MultiplicativeBasisDeformations.Foundations.ProjectiveIdempotents

/-!
# Proposition 4.14 for a scalar mesh category

`prop:scalar-normalization` (`scalar-normalization.tex`), for the deck
grading of a scalar mesh category with at most one arrow between vertices and
mesh data (in the application, `k(Γ_A)` with `arMeshData`). The cover `L` of the
projective labels is thin with a multiplicative basis (Lemmas 4.8–4.12), the
deck group is free (Lemma 4.2) and countable, and weights on `L` are ratios of
object values (Lemma 4.13). The descent (`Descent.lean`) gives one vector on
each nonzero deck-homogeneous piece of `A₀`, closed under composition up to zero
(`exists_deckVectors`); these form a multiplicative basis of
`A₀ = (Alg F₀)ᵒᵖ` containing the primitive idempotents of the labels
(`exists_multBasis_A0`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

variable (Q c v₀ D) in
/-- The grading of `A₀` by the deck group. -/
abbrev D0 := grading0 D (deckGrading Q c v₀)

instance (x y : D.PV) : FiniteDimensional k (D.F0 x ⟶ D.F0 y) := hfd x.1 y.1

include hF in
/-- **Lemma 4.13 in the form used by the descent.** -/
theorem ratio_hyp (d : CovObj (D0 Q c v₀ D) → CovObj (D0 Q c v₀ D) → k)
    (hd : Thin.IsWeight Set.univ d) :
    ∃ ζ : CovObj (D0 Q c v₀ D) → k, (∀ o, ζ o ≠ 0) ∧
      ∀ (o o' : CovObj (D0 Q c v₀ D)) (f : o ⟶ o'), f ≠ 0 → d o o' = ζ o' / ζ o := by
  obtain ⟨ζ, hζ, h⟩ := weight_eq_ratio (d := d) hF hd
  exact ⟨ζ, hζ, fun o o' f hf ↦ h o o' f.1 f.2 (cov_ne_zero.1 hf)⟩

include hF in
/-- **Proposition 4.14, descent**: one vector on each nonzero deck-homogeneous
piece of `A₀`, with identities, closed under composition up to zero. -/
theorem exists_deckVectors :
    ∃ b : ∀ x y : D.PV, Deck Q v₀ → (D.F0 x ⟶ D.F0 y),
      (∀ x y g, b x y g ∈ (D0 Q c v₀ D).part g x y) ∧
      (∀ x y g (f : D.F0 x ⟶ D.F0 y), f ∈ (D0 Q c v₀ D).part g x y → ∃ c : k, f = c • b x y g) ∧
      (∀ x y g, (D0 Q c v₀ D).part g x y ≠ ⊥ → b x y g ≠ 0) ∧
      (∀ x, b x x 1 = 𝟙 (D.F0 x)) ∧
      (∀ x y z g h, b x y g ≫ b y z h = 0 ∨ b x y g ≫ b y z h = b x z (g * h)) := by
  have hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y) :=
    fun x y ↦ hfd x y
  haveI := isFreeGroup_deck Q v₀ c hfin
  set H0 := (deckHeight Q c v₀).comp (Subtype.val : D.PV → V) Subtype.val_injective
  have hT := isThin H0 hF
  obtain ⟨β, hβ⟩ := cov_exists_multBasis H0 hF
  have hratio := ratio_hyp (Q := Q) (c := c) (v₀ := v₀) hF
  exact ⟨bD hT hβ hratio, bD_mem hT hβ hratio, fun x y g f hf ↦ bD_span hT hβ hratio hf,
    fun x y g h ↦ bD_ne_zero hT hβ hratio h, bD_id hT hβ hratio, bD_mul hT hβ hratio⟩

include hF in
/-- **Proposition 4.14**: `A₀` has a multiplicative basis of deck-homogeneous
matrix units containing the primitive idempotents of the labels. -/
theorem exists_multBasis_A0 :
    ∃ (b : ∀ x y : D.PV, Deck Q v₀ → (D.F0 x ⟶ D.F0 y))
      (hmem : ∀ x y g, b x y g ∈ (D0 Q c v₀ D).part g x y)
      (hspan : ∀ x y g (f : D.F0 x ⟶ D.F0 y), f ∈ (D0 Q c v₀ D).part g x y →
        ∃ c : k, f = c • b x y g)
      (hne : ∀ x y g, (D0 Q c v₀ D).part g x y ≠ ⊥ → b x y g ≠ 0)
      (hid : ∀ x, b x x 1 = 𝟙 (D.F0 x)),
      IsMultiplicativeBasis (basisA0 b hmem hspan hne) ∧
        ∀ (hid0 : ∀ x, 𝟙 (D.F0 x) ≠ 0),
          CompleteOrthogonalIdempotents
            (fun x : D.PV ↦ basisA0 b hmem hspan hne (idIdx b hmem hid hid0 x)) ∧
          ∀ x, IsPrimitiveIdempotent (basisA0 b hmem hspan hne (idIdx b hmem hid hid0 x)) := by
  obtain ⟨b, hmem, hspan, hne, hid, hmul⟩ := exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) hF
  refine ⟨b, hmem, hspan, hne, hid, basisA0_isMultiplicative b hmem hspan hne hmul,
    fun hid0 ↦ ⟨idIdx_complete b hmem hspan hne hid hid0, idIdx_primitive b hmem hspan hne hid hid0
      (fun x φ hφ ↦ ?_)⟩⟩
  haveI := L.end_isLocalRing x.1
  rcases idem_eq_zero_or_one (R := End (meshFam Q c x.1)) (p := φ) hφ with h | h
  · exact Or.inl h
  · exact Or.inr h

end MeshWalk

end MultiplicativeBasisDeformations
