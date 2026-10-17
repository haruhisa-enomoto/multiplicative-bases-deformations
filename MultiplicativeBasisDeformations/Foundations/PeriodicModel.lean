import MultiplicativeBasisDeformations.Foundations.SectionalDynkin
import MultiplicativeBasisDeformations.Foundations.ModelDeck

/-!
# Proposition 4.1: the periodic tree model

`prop:periodic-tree-model` (`scalar-normalization.tex:51–75`), parts (1) and (3):
a finite connected stable translation quiver with at most one arrow between two
vertices, containing an arrow and carrying a finite-dimensional scalar mesh
category, is covered by the repetition `ℤΔ` of a Dynkin star model `Δ`; the
covering commutes with translation and is surjective. Combined with
`StarDeck.deck_cyclic`, its fibres are the orbits of an infinite cyclic group of
translation-commuting automorphisms acting freely.

The proof assembles Steps 1–4 (`SectionalCover`, `SectionalDynkin`,
`ModelDeck`), transporting the covering from the tree of sectional paths to the
star model along the isomorphism of Step 2 (`ZTransport`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}

theorem card_starV_zero (L : Fin 0 → ℕ) (x y : StarV L) : x = y := by
  rcases x with _ | ⟨i, _⟩
  · rcases y with _ | ⟨j, _⟩
    · rfl
    · exact j.elim0
  · exact i.elim0

variable {k : Type u} [Field k]

/-- **Proposition 4.1 (1)**: the periodic tree model of a component. -/
theorem periodic_model [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)]
    [∀ x y : V, Fintype (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (hQ : Q.IsStable)
    (c : MeshCoefficients k Q)
    (hfin : ∀ x y : V, FiniteDimensional k
      (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    {x₀ y₀ : V} (a₀ : x₀ ⟶ y₀) (hconn : ∀ v, Relation.EqvGen (SecPath.ConnAdj hQ) x₀ v) :
    ∃ (t : ℕ) (L : Fin t → ℕ) (π : (starTree L).ZVert ⥤q V),
      (t = 1 ∨ (t = 3 ∧ ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2)) ∧ π.IsCovering ∧
      (∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) ∧ Function.Surjective π.obj := by
  classical
  obtain ⟨N, hN⟩ := ScalarMeshCategory.exists_length_lt_of_isSectional c hfin
  haveI hfinite : Finite (Q.SecPath x₀) := SecPath.finite_of_bound N (fun y p hp ↦ hN _ _ p hp)
  haveI := Fintype.ofFinite (Q.SecPath x₀)
  obtain ⟨t, L, e, hadj, hcl⟩ := SecPath.sectional_star_model (x₀ := x₀) hQ c hfin
  set T := SecPath.tree (Q := Q) (x₀ := x₀)
  -- `Δ` has at least two vertices, so `t ≠ 0`
  have ht : t ≠ 0 := by
    intro h0
    subst h0
    let child : Q.SecPath x₀ := ⟨⟨y₀, Quiver.Path.nil.cons a₀⟩, by
      simp [IsSectional, Quiver.Path.arrowList_cons]⟩
    have hne : child ≠ SecPath.root Q x₀ := by
      intro h
      have := congrArg SecPath.len h
      simp [child, SecPath.len, SecPath.root] at this
    exact hne (e.injective (card_starV_zero L _ _))
  have hcl' : t = 1 ∨ (t = 3 ∧ ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2) := by
    rcases hcl with h | h
    · left; omega
    · right; exact h
  -- the parity shift
  have htree := SecPath.isTree (Q := Q) (x₀ := x₀)
  have hadj' : ∀ a b, T.G.Adj a b ↔ (starTree L).G.Adj (e a) (e b) := hadj
  have hshift := OrientedTree.exists_par_shift T (starTree L) e hadj' htree.1 (SecPath.root Q x₀)
  set c₀ := (starTree L).par (e (SecPath.root Q x₀)) - T.par (SecPath.root Q x₀)
  let δ : ℤ := (c₀.val : ℤ)
  have hδ : ∀ d, (starTree L).par (e d) = T.par d + δ := by
    intro d
    have := hshift d
    have hc : ((δ : ℤ) : ZMod 2) = c₀ := by simp [δ]
    rw [hc, ← this]; ring
  let zE := OrientedTree.zEquiv T (starTree L) e δ hδ
  have hzE : ∀ X Y, Nonempty (zE X ⟶ zE Y) ↔ Nonempty (X ⟶ Y) :=
    OrientedTree.nonempty_hom_zMap_iff T (starTree L) e hadj' δ hδ
  -- the transported covering
  have hmap : ∀ {Y Y' : (starTree L).ZVert}, (Y ⟶ Y') →
      Nonempty (SecPath.piV hQ x₀ (zE.symm Y) ⟶ SecPath.piV hQ x₀ (zE.symm Y')) := by
    intro Y Y' a
    have : Nonempty (zE.symm Y ⟶ zE.symm Y') := by
      rw [← hzE, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact ⟨a⟩
    obtain ⟨b⟩ := this
    exact SecPath.nonempty_piV hQ b
  let π : (starTree L).ZVert ⥤q V :=
    { obj := fun Y ↦ SecPath.piV hQ x₀ (zE.symm Y)
      map := fun a ↦ Classical.choice (hmap a) }
  refine ⟨t, L, π, hcl', ?_, ?_, ?_⟩
  · exact isCovering_transport zE hzE (SecPath.piQ hQ (x₀ := x₀)) (SecPath.piQ_isCovering hQ) π
      (fun Y ↦ rfl)
  · intro Y
    have e1 : zE.symm ((starTree L).ztau Y) = T.ztau (zE.symm Y) := by
      ext <;> simp [zE, OrientedTree.zEquiv, OrientedTree.zMapInv, OrientedTree.ztau] <;> ring
    change SecPath.piV hQ x₀ (zE.symm ((starTree L).ztau Y)) = _
    rw [e1, SecPath.piV_ztau]
  · intro v
    obtain ⟨X, hX⟩ := SecPath.piV_surjective_of_conn hQ (hconn v)
    exact ⟨zE X, by change SecPath.piV hQ x₀ (zE.symm (zE X)) = v; rw [Equiv.symm_apply_apply, hX]⟩

end TranslationQuiver

end MultiplicativeBasisDeformations
