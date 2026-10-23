module

public import MultiplicativeBasisDeformations.Foundations.MeshWeights

/-!
# The deck weight character (a lemma of an earlier draft)

An earlier draft of the manuscript (`lem:deck-weight-character`, not in the current
revision): "Define the character of a
closed walk in `K` to be the element of `L = Hom_ℤ(H_ℤ, ℤ)` sending an integer ray weight `h`
to the weight of the walk under a mesh-weight lift of `h`; by Lemma 7.4 this does not depend on
the lift. A closed walk whose lift joins `X̃` to `gX̃` has character `−θ_g`."

Formalization. The deck group is the fundamental group of the coned complex at the basepoint
(`Deck`), so a closed walk is a deck element `g` and its weight under a mesh weight `W` is the
transport `potW` of the edge weights along `g` (`MeshWt.walkWt`). The deck class `θ_g` is
`ζ(g o₀) − ζ(o₀)` for the object values `ζ` of the universal ray weight on the lifted projective
category (Proposition 7.2(2)), defined for `g` in the stabilizer `H` of the base component
(the deviation of Proposition 7.2(1)). Deviation: with the orientation conventions of the
formalization (arrows of `A₀` go along paths, `rv` is the weight of the path) the identity reads
`walkWt g = h(θ_g)` (`walkWt_eq`), the sign of the source coming from its opposite convention
for object values (`−b_x` at `P_x`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u z

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

variable {M : Type z} [AddCommGroup M]

variable (v₀) in
/-- **The weight of a closed walk** under a mesh weight: its transport along the deck element. -/
def MeshWt.walkWt (W : MeshWt Q M) (g : Deck Q v₀) : M :=
  Multiplicative.toAdd (potW W.WE W.WE_tri g.unop)

/-- The object value at a lifted vertex is the weight of its sheet. -/
theorem MeshWt.pot_eq_walkWt (W : MeshWt Q M) (X : V) (g : Deck Q v₀) :
    W.pot v₀ (X, g) = W.walkWt v₀ g := by
  have := potW_comp W.WE W.WE_tri (Sum.inr X) g.unop
  unfold MeshWt.pot MeshWt.walkWt
  exact (congrArg Multiplicative.toAdd this).trans (by
    change Multiplicative.toAdd (_ * 1) = _
    rw [mul_one]
    rfl)

theorem MeshWt.walkWt_one (W : MeshWt Q M) : W.walkWt v₀ 1 = 0 := by
  unfold MeshWt.walkWt
  change Multiplicative.toAdd (potW W.WE W.WE_tri (𝟙 _)) = 0
  unfold potW
  rw [CategoryTheory.Functor.map_id]
  rfl

variable {x₀ : D.PV}

/-- **The deck weight character** (an earlier draft's lemma): the weight of a closed walk `g` in the stabilizer of the base component
under any mesh-weight lift `W` of an integer ray weight `h` is `h(θ_g)`, where
`θ_g = ζ(g o₀) − ζ(o₀)` is the deck class of Proposition 7.2(1). -/
theorem walkWt_eq {ζ : LObj Q c v₀ D → WP Q c v₀ D}
    (hζ : ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o)
    (W : MeshWt Q M) (h : WP Q c v₀ D →+ M) (hW : W.res c D = h)
    (g : Deck Q v₀) (hg : g ∈ Hs Q c v₀ D x₀) :
    W.walkWt v₀ g = h (ζ (gL Q c v₀ D g (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀)) := by
  -- object values of `W` and of `h ∘ ζ` differ by a constant on each component of `L`
  have hline : ∀ z z' : D.PV × Deck Q v₀, Thin.Line (toL Q c v₀ D z) (toL Q c v₀ D z') →
      W.pot v₀ (z'.1.1, z'.2) - W.pot v₀ (z.1.1, z.2) =
        h (ζ (toL Q c v₀ D z') - ζ (toL Q c v₀ D z)) := by
    intro z z' hl
    obtain ⟨f, hf, hf0⟩ := line_iff.1 hl
    have hnz : NZ Q c v₀ D (z.1, z'.1, z.2⁻¹ * z'.2) := fun h0 ↦ hf0 (by
      have : f ∈ (D0 Q c v₀ D).part (z.2⁻¹ * z'.2) z.1 z'.1 := hf
      rw [h0] at this; exact this)
    obtain ⟨p, hp⟩ := exists_path_of_nz hnz
    have h1 := W.pot_path (v₀ := v₀) z.2 p
    have e : z.2 * (z.2⁻¹ * z'.2) = z'.2 := mul_inv_cancel_left (G := Deck Q v₀) _ _
    rw [hp, e] at h1
    have h2 := congrArg (fun φ ↦ φ (cls Q c v₀ D (z.1, z'.1, z.2⁻¹ * z'.2))) hW
    simp only [MeshWt.res_cls, W.rv_path hnz hp] at h2
    rw [h1, add_sub_cancel_left, h2, ← hζ _ _ hl]
    rfl
  have hconst : ∀ {o o' : LObj Q c v₀ D}, conn Q c v₀ D o o' →
      W.pot v₀ ((ofL Q c v₀ D o').1.1, (ofL Q c v₀ D o').2) - h (ζ o') =
        W.pot v₀ ((ofL Q c v₀ D o).1.1, (ofL Q c v₀ D o).2) - h (ζ o) := by
    intro o o' hc
    induction hc with
    | rel a d hl =>
      have := hline (ofL Q c v₀ D a) (ofL Q c v₀ D d) hl
      rw [map_sub] at this
      change _ - h (ζ d) = _ - h (ζ a)
      rw [sub_eq_sub_iff_sub_eq_sub]
      exact this
    | refl a => rfl
    | symm a d _ ih => exact ih.symm
    | trans a d e _ _ ih ih' => exact ih'.trans ih
  have hc : conn Q c v₀ D (o₀ Q c v₀ D x₀) (gL Q c v₀ D g (o₀ Q c v₀ D x₀)) := by
    have : gL Q c v₀ D g (o₀ Q c v₀ D x₀) = (x₀, g) := by
      change (x₀, g * 1) = (x₀, g); rw [mul_one]
    rw [this]; exact hg
  have := hconst hc
  have e1 : W.pot v₀ ((ofL Q c v₀ D (gL Q c v₀ D g (o₀ Q c v₀ D x₀))).1.1,
      (ofL Q c v₀ D (gL Q c v₀ D g (o₀ Q c v₀ D x₀))).2) = W.walkWt v₀ g := by
    rw [MeshWt.pot_eq_walkWt]
    change W.walkWt v₀ (g * 1) = _
    rw [mul_one]
  have e2 : W.pot v₀ ((ofL Q c v₀ D (o₀ Q c v₀ D x₀)).1.1, (ofL Q c v₀ D (o₀ Q c v₀ D x₀)).2) =
      0 := by
    rw [MeshWt.pot_eq_walkWt]
    exact W.walkWt_one
  rw [e1, e2, zero_sub, sub_eq_iff_eq_add] at this
  rw [this, map_sub]
  abel

/-- The character does not depend on the mesh-weight lift (`weights-and-parameters.tex`). -/
theorem walkWt_indep {ζ : LObj Q c v₀ D → WP Q c v₀ D}
    (hζ : ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o)
    (W W' : MeshWt Q M) (hW : W.res (v₀ := v₀) c D = W'.res c D) (g : Deck Q v₀) (hg : g ∈ Hs Q c v₀ D x₀) :
    W.walkWt v₀ g = W'.walkWt v₀ g := by
  rw [walkWt_eq hζ W _ hW g hg, walkWt_eq hζ W' _ rfl g hg]

end MeshWalk

end MultiplicativeBasisDeformations
