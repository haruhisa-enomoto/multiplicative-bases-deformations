module

public import MultiplicativeBasisDeformations.Foundations.AEven
public import MultiplicativeBasisDeformations.Foundations.APaths
public import MultiplicativeBasisDeformations.Foundations.PeriodicModel
public import MultiplicativeBasisDeformations.Foundations.StarTypes

/-!
# Mesh corrections on a connected stable translation quiver

Appendix A, `periodic-mesh-calculations.tex`: "By Proposition 5.1 we
may restrict to periodic components; … a periodic component without arrows has
no rows of degree at least three. Proposition 4.1 then allows us to work with the
finite tree models." This file treats a finite connected stable translation
quiver: by Proposition 4.1 it is covered by a star model; the types `A` and `D`
are settled here, and the types `E` are passed in as a hypothesis (they are
treated with the brick hypothesis in `ECase.lean`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge TranslationQuiver

theorem exists_third : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by decide

variable {V : Type v'} [Quiver.{w} V] [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} (hQ : Q.IsStable) [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  {k : Type u} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

include hfin in
/-- **Mesh corrections vanish on a connected periodic quiver** of type `A` or
`D`; the types `E` are supplied by `hE`. -/
theorem connected_surjective (h2 : (2 : k) ≠ 0) (x₀ : V)
    (hconn : ∀ v, Relation.EqvGen (SecPath.ConnAdj hQ) x₀ v)
    (hE : ∀ (L : Fin 3 → ℕ) (π : (starTree L).ZVert ⥤q V), π.IsCovering →
      (∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) → (∀ x : V, ∃ X, π.obj X = x) →
      (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ L a = 0 ∧ L b = 1 ∧ 1 ≤ L c ∧ L c ≤ 3) →
      ∀ m, 2 ≤ m → MeshDerivativeSurjective c m)
    (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
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
      rcases path_aut ρ hρ' with hid | hrev
      · exact surjective_A_id hQ π hπ hτ hsurj' ρ hρ hρ' c0 hc0 hρp hdeck hfib hid c m hm
      · rcases Nat.even_or_odd (L 0) with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact surjective_A_even hQ π hπ hτ hsurj' ρ hρ c0 hc0 hρp hdeck hfib (r + 1) (by omega)
            (by omega) hrev h2 c m hm
        · exact surjective_A_odd_reflection hQ π hπ hτ hsurj' ρ hρ c0 hc0 hρp hdeck hfib (r + 1)
            (by omega) (by omega) hrev h2 c m hm
    · subst ht3
      rcases three_arm_types L hsum with ⟨a, b, hab, hLa, hLb⟩ | hEL
      · obtain ⟨ρ, hρ, c0, hρp, hc0, hρ', hdeck, hfib⟩ :=
          StarDeck.deck_data hQ π hπ hτ (by norm_num) (Or.inr rfl)
        have h0 : ρ none = none := fixes_centre_three rfl ρ hρ'
        obtain ⟨c', hac, hbc⟩ := exists_third a b hab
        exact surjective_of_fixed_centre hQ π hπ hτ hsurj' ρ hρ hρ' h0 c0 hc0 hρp hdeck hfib
          (fun θ _ M _ _ D _ w hw ↦ TraceAlg.trace_D_any D (TraceAlg.two_cancel h2) hab hac hbc
            hLa hLb hw) c m hm
      · exact hE L π hπ hτ hsurj' hEL m hm
  · -- no arrows: no rows of positive length
    push_neg at harrow
    rw [surjective_iff_rows]
    intro x w hw
    exfalso
    obtain ⟨y, e, w', -, -⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ w hw
    exact (harrow _ _).false e

end StarTrace

end MultiplicativeBasisDeformations
