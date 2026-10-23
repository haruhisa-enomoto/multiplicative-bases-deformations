module

public import MultiplicativeBasisDeformations.Foundations.StarGaugeQ

/-!
# Descending invariant scales from `ℤΔ` to `Q`

Relation scales `E X` and arrow scales `F Y X` on `ℤΔ` which are invariant under
the deck generator `g` descend to scales on `Q = ℤΔ / ⟨g⟩`: the fibres of `π`
are the `g`-orbits, and an arrow into a given vertex is determined by the image
of its source.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarGauge

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V) (hπ : π.IsCovering)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (σ : StarV L ≃ StarV L) (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hσp : ∀ v, (starTree L).par (σ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct σ hσ (c0 : ℤ) hσp).obj Z) = π.obj Z)
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ σ hσ c0 hσp)^[n] X ∨ X = (gZ σ hσ c0 hσp)^[n] Y)
  (E : (starTree L).ZVert → kˣ) (F : (starTree L).ZVert → (starTree L).ZVert → kˣ)
  (hE : ∀ X, E (gZ σ hσ c0 hσp X) = E X)
  (hF : ∀ Y X, F (gZ σ hσ c0 hσp Y) (gZ σ hσ c0 hσp X) = F Y X)

/-- The descended relation scales. -/
def ηD (x : Q.nonprojective) : kˣ := E (hsurj x.1).choose

/-- The descended arrow scales. -/
def μD {y x : V} (a : y ⟶ x) : kˣ :=
  F (lift_exists π hπ (hsurj x).choose
    (Quiver.Hom.cast rfl (hsurj x).choose_spec.symm a)).choose (hsurj x).choose

include hE in
theorem E_iter (n : ℕ) (X : (starTree L).ZVert) : E ((gZ σ hσ c0 hσp)^[n] X) = E X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hE, ih]

include hF in
theorem F_iter (n : ℕ) (Y X : (starTree L).ZVert) :
    F ((gZ σ hσ c0 hσp)^[n] Y) ((gZ σ hσ c0 hσp)^[n] X) = F Y X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hF, ih]

include hfib hE in
theorem ηD_eq (X : (starTree L).ZVert) :
    ηD π hsurj E ⟨π.obj X, hQ.mem_nonprojective _⟩ = E X := by
  unfold ηD
  have hX' : π.obj (hsurj (π.obj X)).choose = π.obj X := (hsurj _).choose_spec
  obtain ⟨n, h | h⟩ := hfib _ X hX'
  · conv_rhs => rw [h]
    rw [E_iter σ hσ c0 hσp E hE]
  · conv_lhs => rw [h]
    rw [E_iter σ hσ c0 hσp E hE]

include hπ hdeck hfib hF in
theorem F_fibre {X X' Y Y' : (starTree L).ZVert} (hX : π.obj X' = π.obj X)
    (hY : π.obj Y' = π.obj Y) (A : Y ⟶ X) (A' : Y' ⟶ X') : F Y' X' = F Y X := by
  obtain ⟨n, h | h⟩ := hfib X X' hX.symm
  · obtain ⟨B⟩ := gZ_arrow σ hσ c0 hσp n ⟨A⟩
    rw [← h] at B
    have hY' : Y' = (gZ σ hσ c0 hσp)^[n] Y :=
      lift_unique π hπ X' A' B (by rw [hY, π_gZ_iter π σ hσ c0 hσp hdeck])
    rw [hY', h, F_iter σ hσ c0 hσp F hF]
  · obtain ⟨B⟩ := gZ_arrow σ hσ c0 hσp n ⟨A'⟩
    rw [← h] at B
    have hY' : Y = (gZ σ hσ c0 hσp)^[n] Y' :=
      lift_unique π hπ X A B (by rw [π_gZ_iter π σ hσ c0 hσp hdeck, hY])
    rw [hY', h, F_iter σ hσ c0 hσp F hF]

include hdeck hfib hF in
theorem μD_eq {Y X : (starTree L).ZVert} (A : Y ⟶ X) :
    μD π hπ hsurj F (π.map A) = F Y X := by
  unfold μD
  have hX' := (hsurj (π.obj X)).choose_spec
  obtain ⟨⟨A'⟩, hY'⟩ := (lift_exists π hπ (hsurj (π.obj X)).choose
    (Quiver.Hom.cast rfl hX'.symm (π.map A))).choose_spec
  exact F_fibre π hπ σ hσ c0 hσp hdeck hfib F hF hX' hY' A A'

theorem μD_congr {y x y' x' : V} (a : y ⟶ x) (a' : y' ⟶ x') (hy : y = y') (hx : x = x') :
    μD π hπ hsurj F a = μD π hπ hsurj F a' := by
  subst hy hx; rw [Subsingleton.elim a a']

end StarGauge

end MultiplicativeBasisDeformations
