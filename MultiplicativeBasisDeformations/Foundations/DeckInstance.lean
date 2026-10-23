module

public import MultiplicativeBasisDeformations.Foundations.DeckGrading
public import MultiplicativeBasisDeformations.Foundations.Thinness

/-!
# The deck grading of a scalar mesh category, as a graded family

Subsection 4.2 (`scalar-normalization.tex`): the covering formula
`eq:walk-hom-sum` and the height. For a translation quiver with
homogeneous meshes, the walk-class weight `deg` of `DeckGrading.lean` grades the
Hom spaces of `C(Q, c)` between all vertices (`deckGrading`), and the length of
walk classes is a height in the sense of `HeightData` (`deckHeight`): nonzero
morphisms of degree `g` are combinations of paths of length `ℓ(g)`, and in
length zero only identities occur.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  (Q : TranslationQuiver V) [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  (v₀ : V)

open ScalarMeshCategory

attribute [local instance] Classical.decEq

/-- The mesh category objects as a family. -/
abbrev meshFam : V → ScalarMeshCategory k Q c := fun x ↦ obj c x

theorem pathMor_nil (x : V) : pathMor c (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (obj c x) := by
  unfold pathMor
  exact CategoryTheory.Functor.map_id _ _

/-- **The deck grading** of the Hom spaces between all vertices. -/
def deckGrading : CatAlg.HomGrading (k := k) (meshFam Q c) (Deck Q v₀) where
  proj g x y := wProj c (degW Q v₀) (meshHomogeneous Q v₀) g x y
  proj_proj g h x y f := wProj_of_mem _ (wProj_mem _ h f)
  sum x y f := eq_sum_wProj (meshHomogeneous Q v₀) f
  proj_comp g a b x y z f f' :=
    wProj_of_mem _ (comp_mem_wPart (wProj_mem _ a f) (wProj_mem _ b f'))
  proj_id g x := by
    have h : 𝟙 (obj c x) ∈ wPart c (degW Q v₀) 1 x x := by
      rw [← pathMor_nil, ← (degW Q v₀).deg_nil x]
      exact pathMor_mem_wPart _
    exact wProj_of_mem _ h

theorem isHom_iff {g : Deck Q v₀} {x y : V} {f : obj c x ⟶ obj c y} :
    (deckGrading Q c v₀).IsHom g f ↔ f ∈ wPart c (degW Q v₀) g x y := by
  constructor
  · intro h; rw [← h]; exact wProj_mem (meshHomogeneous Q v₀) g f
  · intro h; exact (wProj_of_mem (meshHomogeneous Q v₀) h).trans (if_pos rfl)

/-- Paths of a given weight: if none has a property, the weight part lies in the
span of those that do. -/
theorem wPart_le_span (g : Deck Q v₀) (x y : V) :
    wPart c (degW Q v₀) g x y ≤ Submodule.span k
      {f | ∃ p : Quiver.Path x y, (degW Q v₀).deg p = g ∧ pathMor c p = f} := by
  rintro f ⟨F, hF, rfl⟩
  induction hF using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **The height of the deck grading.** -/
def deckHeight : CatAlg.HeightData (deckGrading Q c v₀) where
  hgt := hgt Q v₀
  hgt_mul := hgt_mul Q v₀
  nonneg g x y f hf hf0 := by
    rw [isHom_iff] at hf
    by_contra hneg
    apply hf0
    have := wPart_le_span Q c v₀ g x y hf
    have hempty : {f | ∃ p : Quiver.Path x y, (degW Q v₀).deg p = g ∧ pathMor c p = f} = ∅ := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro p hp _
      have := hgt_degW Q v₀ p
      rw [hp] at this
      omega
    rw [hempty, Submodule.span_empty, Submodule.mem_bot] at this
    exact this
  scalar g x y f hf hf0 hg := by
    rw [isHom_iff] at hf
    have := wPart_le_span Q c v₀ g x y hf
    by_cases hxy : x = y
    · subst hxy
      refine ⟨rfl, ?_, ?_⟩
      · by_contra hg1
        apply hf0
        have hempty : {f | ∃ p : Quiver.Path x x, (degW Q v₀).deg p = g ∧ pathMor c p = f} = ∅ := by
          ext f
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
          intro p hp _
          have hl := hgt_degW Q v₀ p
          rw [hp, hg] at hl
          have hp0 : p = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p (by omega)
          subst hp0
          exact hg1 (hp.symm.trans ((degW Q v₀).deg_nil x))
        rw [hempty, Submodule.span_empty, Submodule.mem_bot] at this
        exact this
      · have hsub : {f | ∃ p : Quiver.Path x x, (degW Q v₀).deg p = g ∧ pathMor c p = f} ⊆
            {𝟙 (obj c x)} := by
          rintro f ⟨p, hp, rfl⟩
          have hl := hgt_degW Q v₀ p
          rw [hp, hg] at hl
          have hp0 : p = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p (by omega)
          subst hp0
          exact pathMor_nil Q c x
        have := Submodule.span_mono hsub this
        obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
        exact ⟨r, by simpa using hr.symm⟩
    · exfalso
      apply hf0
      have hempty : {f | ∃ p : Quiver.Path x y, (degW Q v₀).deg p = g ∧ pathMor c p = f} = ∅ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro p hp _
        have hl := hgt_degW Q v₀ p
        rw [hp, hg] at hl
        exact hxy (Quiver.Path.eq_of_length_zero p (by omega))
      rw [hempty, Submodule.span_empty, Submodule.mem_bot] at this
      exact this

end MeshWalk

end MultiplicativeBasisDeformations
