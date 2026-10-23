module

public import MultiplicativeBasisDeformations.Foundations.ConnectedChar2
public import MultiplicativeBasisDeformations.Foundations.FloorWeight

/-!
# The spanning row of a connected periodic quiver winds once

Strengthening of `connected_cokerSpan` for Proposition 7.5: the spanning row (if any) of
a finite connected stable translation quiver in characteristic two has a winding mesh
weight in which the weight of the row minus `ν` of its vertex is one
(`connected_cokerSpan_wt`; the weight is `floorWt`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge TranslationQuiver MeshWalk

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} (hQ : Q.IsStable) [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  {k : Type u} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

include hfin in
/-- **The spanning row winds once.** -/
theorem connected_cokerSpan_wt (hchar : (2 : k) = 0) (hbrick : BrickHypothesis c) (x₀ : V)
    (hconn : ∀ v, Relation.EqvGen (SecPath.ConnAdj hQ) x₀ v) :
    ∃ S : RowSet Q, S.Subsingleton ∧ CokerSpan c S ∧
      ∀ R ∈ S, ∃ W : MeshWt Q ℤ, W.pw R.2 - W.ν R.1 = 1 := by
  have hA : (∀ m, 2 ≤ m → MeshDerivativeSurjective c m) →
      ∃ S : RowSet Q, S.Subsingleton ∧ CokerSpan c S ∧
        ∀ R ∈ S, ∃ W : MeshWt Q ℤ, W.pw R.2 - W.ν R.1 = 1 :=
    fun h ↦ ⟨∅, Set.subsingleton_empty, (cokerSpan_empty_iff c).2 h, fun R hR ↦ absurd hR id⟩
  by_cases harrow : ∃ x y : V, Nonempty (x ⟶ y)
  · obtain ⟨x₁, y₁, ⟨a₀⟩⟩ := harrow
    have hconn₁ : ∀ v, Relation.EqvGen (SecPath.ConnAdj hQ) x₁ v :=
      fun v ↦ Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hconn x₁)) (hconn v)
    obtain ⟨t, L, π, hcl, hπ, hτ, hsurj⟩ := periodic_model hQ c hfin a₀ hconn₁
    have hsurj' : ∀ x : V, ∃ X, π.obj X = x := hsurj
    rcases hcl with ht1 | ⟨ht3, hsum⟩
    · subst ht1
      obtain ⟨ρ, hρ, c0, hρp, hc0, hρ', hdeck, hfib⟩ :=
        StarDeck.deck_data hQ π hπ hτ (by norm_num) (Or.inl rfl)
      refine hA fun m hm ↦ ?_
      rcases path_aut ρ hρ' with hid | hrev
      · exact surjective_A_id hQ π hπ hτ hsurj' ρ hρ hρ' c0 hc0 hρp hdeck hfib hid c m hm
      · rcases Nat.even_or_odd (L 0) with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact a_even_surj hQ π hπ hτ hsurj' ρ hρ c0 hc0 hρp hdeck hfib hchar c hbrick (r + 1)
            (by omega) (by omega) hrev m hm
        · exact a_reflect_surj hQ π hπ hτ hsurj' ρ hρ c0 hc0 hρp hdeck hfib c hbrick (r + 1)
            (by omega) (by omega) hrev m hm
    · subst ht3
      have hevenc : ∀ (ρ : StarV L ≃ StarV L)
          (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b) (c0 : ℕ)
          (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2)),
          ρ none = none → Even c0 := fun ρ hρ c0 hρp h0 ↦ by
        have := hρp none
        rw [h0, left_eq_add] at this
        exact (ZMod.natCast_eq_zero_iff_even).1 (by exact_mod_cast this)
      rcases three_arm_types L hsum with ⟨a, b, hab, hLa, hLb⟩ | hEL
      · obtain ⟨ρ, hρ, c0, hρp, hc0, hρ', hdeck, hfib⟩ :=
          StarDeck.deck_data hQ π hπ hτ (by norm_num) (Or.inr rfl)
        have h0 : ρ none = none := fixes_centre_three rfl ρ hρ'
        obtain ⟨c', hac, hbc⟩ := exists_third a b hab
        obtain ⟨W₀, hW₀, hW, -⟩ := d_cokerSpan.{_, _, _, 0} hQ c hπ hτ hsurj' ρ hρ c0 hρp hdeck hfib hbrick hρ' h0
          hc0 hab hac hbc hLa hLb
        exact ⟨_, candRow_subsingleton hQ π W₀, hW, fun R hR ↦
          ⟨_, floorWt_candRow hQ π hπ hτ hsurj' ρ hρ c0 hρp hc0 hdeck hfib
            (hevenc ρ hρ c0 hρp h0) W₀ hW₀ R hR⟩⟩
      · obtain ⟨ρ, hρ, c0, hρp, hc0, h0, hdeck, hfib, W₀, hW₀, hW, -⟩ :=
          e_cokerSpan.{_, _, _, 0} hQ c hbrick hchar L π hπ hτ hsurj' hEL
        exact ⟨_, candRow_subsingleton hQ π W₀, hW, fun R hR ↦
          ⟨_, floorWt_candRow hQ π hπ hτ hsurj' ρ hρ c0 hρp hc0 hdeck hfib
            (hevenc ρ hρ c0 hρp h0) W₀ hW₀ R hR⟩⟩
  · refine hA fun m hm ↦ ?_
    push Not at harrow
    rw [surjective_iff_rows]
    intro x w hw
    exfalso
    obtain ⟨y, e, w', -, -⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ w hw
    exact (harrow _ _).false e

end StarTrace

end MultiplicativeBasisDeformations
