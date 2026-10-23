module

public import MultiplicativeBasisDeformations.Foundations.StarESpan
public import MultiplicativeBasisDeformations.Foundations.AEvenChar2
public import MultiplicativeBasisDeformations.Foundations.ConnectedCase

/-!
# Mesh corrections on a connected periodic quiver in characteristic two

`characteristic-two-mesh-calculations.tex`: "We will show that each periodic
component contributes at most one correction line, represented by a single path."
On a finite connected stable translation quiver with a finite-dimensional scalar mesh
category satisfying the brick hypothesis, in characteristic two, the cokernels of the
mesh derivatives are spanned by the class of at most one row (`connected_cokerSpan`):
by Proposition 4.1 the quiver is covered by a star model; the types `A` give zero
cokernels, and the types `D`, `E` one row of degree `2s + 2` at the centre.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w u₂

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge TranslationQuiver

variable {V : Type v'} [Quiver.{w} V] [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} (hQ : Q.IsStable) [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  {k : Type u} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

/-- **The model of a row of type `D` or `E`** (Proposition 6.1(1)(2)): the quiver is
`ℤΔ/⟨g⟩` for a three-arm Dynkin star `Δ`, with `g(v, j) = (ρ v, j + 2s)` (that is,
`τ^{−s} ρ`), `ρ` an automorphism of `Δ` fixing the centre, `s ≥ 1`, and the row has degree
`2s + 2`. -/
def DEModel (R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) : Prop :=
  ∃ (L : Fin 3 → ℕ) (π : (starTree L).ZVert ⥤q V) (ρ : StarV L ≃ StarV L) (s : ℕ)
    (g : (starTree L).ZVert → (starTree L).ZVert),
    ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2 ∧ π.IsCovering ∧
    (∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) ∧ Function.Surjective π.obj ∧
    (∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) ∧ ρ none = none ∧ 1 ≤ s ∧
    (∀ X, (g X).v = ρ X.v ∧ (g X).t = X.t + 2 * s) ∧
    (∀ X Y, π.obj X = π.obj Y ↔ ∃ n : ℕ, Y = g^[n] X ∨ X = g^[n] Y) ∧
    R.2.length = 2 * s + 2

/-- The model data of a candidate row of a three-arm star. -/
theorem deModel_candRow (L : Fin 3 → ℕ) (π : (starTree L).ZVert ⥤q V) (hπ : π.IsCovering)
    (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) (hsurj : Function.Surjective π.obj)
    (hsum : ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2) (ρ : StarV L ≃ StarV L)
    (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b) (c0 : ℕ)
    (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2)) (hc0 : 0 < c0)
    (h0 : ρ none = none)
    (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
    (hfib : ∀ X Y, π.obj X = π.obj Y → ∃ n : ℕ,
      Y = (StarGauge.gZ ρ hρ c0 hρp)^[n] X ∨ X = (StarGauge.gZ ρ hρ c0 hρp)^[n] Y)
    (W₀ : List (Fin 3)) (hW₀ : W₀.length = c0 / 2 + 1) :
    ∀ R ∈ candRow hQ π W₀, DEModel hQ R := by
  intro R hR
  have hc0e : Even c0 := by
    have := hρp none
    rw [h0, left_eq_add] at this
    exact (ZMod.natCast_eq_zero_iff_even).1 (by exact_mod_cast this)
  obtain ⟨s, hs⟩ := hc0e
  have hiter : ∀ n Z, π.obj ((StarGauge.gZ ρ hρ c0 hρp)^[n] Z) = π.obj Z := by
    intro n
    induction n with
    | zero => intro Z; rfl
    | succ n ih => intro Z; rw [Function.iterate_succ_apply', hdeck, ih]
  refine ⟨L, π, ρ, s, StarGauge.gZ ρ hρ c0 hρp, hsum, hπ, hτ, hsurj, fun a b ↦ (hρ a b).symm, h0,
    by omega, fun X ↦ ⟨rfl, ?_⟩, fun X Y ↦ ⟨hfib X Y, ?_⟩, ?_⟩
  · change X.t + (c0 : ℤ) = X.t + 2 * s
    rw [hs]; push_cast; ring
  · rintro ⟨n, h | h⟩
    · rw [h, hiter]
    · rw [h, hiter]
  · rw [candRow_length hQ π W₀ R hR, hW₀]; omega

include hfin in
/-- **Mesh corrections on a connected periodic quiver in characteristic two**, with the model
data of Proposition 6.1(1)(2): the cokernels are spanned by the class of at most one row, of
type `D` or `E` and degree `2s + 2`. -/
theorem connected_cokerSpan_model (hchar : (2 : k) = 0) (hbrick : BrickHypothesis c) (x₀ : V)
    (hconn : ∀ v, Relation.EqvGen (SecPath.ConnAdj hQ) x₀ v) :
    ∃ S : RowSet Q, S.Subsingleton ∧ CokerSpan c S ∧ TwoRows.{u₂} Q S ∧
      ∀ R ∈ S, DEModel hQ R := by
  have hA : (∀ m, 2 ≤ m → MeshDerivativeSurjective c m) →
      ∃ S : RowSet Q, S.Subsingleton ∧ CokerSpan c S ∧ TwoRows.{u₂} Q S ∧
        ∀ R ∈ S, DEModel hQ R :=
    fun h ↦ ⟨∅, Set.subsingleton_empty, (cokerSpan_empty_iff c).2 h, twoRows_empty,
      fun R hR ↦ absurd hR id⟩
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
      rcases three_arm_types L hsum with ⟨a, b, hab, hLa, hLb⟩ | hEL
      · obtain ⟨ρ, hρ, c0, hρp, hc0, hρ', hdeck, hfib⟩ :=
          StarDeck.deck_data hQ π hπ hτ (by norm_num) (Or.inr rfl)
        have h0 : ρ none = none := fixes_centre_three rfl ρ hρ'
        obtain ⟨c', hac, hbc⟩ := exists_third a b hab
        obtain ⟨W₀, hW₀, hW, h2⟩ := d_cokerSpan hQ c hπ hτ hsurj' ρ hρ c0 hρp hdeck hfib hbrick
          hρ' h0 hc0 hab hac hbc hLa hLb
        exact ⟨_, candRow_subsingleton hQ π W₀, hW, h2,
          deModel_candRow hQ L π hπ hτ hsurj hsum ρ hρ c0 hρp hc0 h0 hdeck hfib W₀ hW₀⟩
      · obtain ⟨ρ, hρ, c0, hρp, hc0, h0, hdeck, hfib, W₀, hW₀, hW, h2⟩ :=
          e_cokerSpan hQ c hbrick hchar L π hπ hτ hsurj' hEL
        exact ⟨_, candRow_subsingleton hQ π W₀, hW, h2,
          deModel_candRow hQ L π hπ hτ hsurj hsum ρ hρ c0 hρp hc0 h0 hdeck hfib W₀ hW₀⟩
  · -- no arrows: no rows of positive length
    refine hA fun m hm ↦ ?_
    push Not at harrow
    rw [surjective_iff_rows]
    intro x w hw
    exfalso
    obtain ⟨y, e, w', -, -⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ w hw
    exact (harrow _ _).false e

include hfin in
/-- **Mesh corrections on a connected periodic quiver in characteristic two**: the
cokernels are spanned by the class of at most one row. -/
theorem connected_cokerSpan (hchar : (2 : k) = 0) (hbrick : BrickHypothesis c) (x₀ : V)
    (hconn : ∀ v, Relation.EqvGen (SecPath.ConnAdj hQ) x₀ v) :
    ∃ S : RowSet Q, S.Subsingleton ∧ CokerSpan c S ∧ TwoRows.{u₂} Q S := by
  obtain ⟨S, h1, h2, h3, -⟩ := connected_cokerSpan_model.{_, _, _, u₂} hQ c hfin hchar hbrick x₀ hconn
  exact ⟨S, h1, h2, h3⟩

end StarTrace

end MultiplicativeBasisDeformations
