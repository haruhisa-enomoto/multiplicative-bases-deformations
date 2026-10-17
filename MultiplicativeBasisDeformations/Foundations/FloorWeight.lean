import MultiplicativeBasisDeformations.Foundations.StarESpan
import MultiplicativeBasisDeformations.Foundations.StarDSpan
import MultiplicativeBasisDeformations.Foundations.MeshWeights

/-!
# The winding mesh weight of a periodic component (Proposition 7.5)

`weights-and-parameters.tex` (`prop:primitive-parameter-characters`): "Lift `p_i`
to `ℤΔ`, starting at a vertex `(x, j)` over `τv_i`. Its endpoint lies over `v_i` […] The
closed walk `p_i t_{v_i}⁻¹` winds once around the component."

Deviation: instead of identifying `χ_i` with a deck class
and using a lemma on the periodic core, we construct, on a periodic component covered by `ℤΔ` with deck
transformations `(v, t) ↦ (ρ v, t + c₀)`, an integer mesh weight measuring this winding:
an arrow lifted to `X → Y` gets weight `⌊Y_t / c₀⌋ − ⌊X_t / c₀⌋`, which does not depend on
the lift (`floorWt`). For the candidate row of a word of length `c₀/2 + 1` (Appendix B) the
weight of the row minus `ν` is one (`floorWt_candRow`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace StarTrace

open OrientedTree StarGauge MeshWalk

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type} [Quiver.{0} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V) (hπ : π.IsCovering)
  (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hc0 : 0 < c0) (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y, π.obj X = π.obj Y → ∃ n : ℕ,
    Y = (StarGauge.gZ ρ hρ c0 hρp)^[n] X ∨ X = (StarGauge.gZ ρ hρ c0 hρp)^[n] Y)

/-- The winding level of a vertex of `ℤΔ`. -/
def fl (X : (starTree L).ZVert) : ℤ := X.t / (c0 : ℤ)

include hc0 in
theorem fl_gZ (n : ℕ) (X : (starTree L).ZVert) :
    fl c0 ((StarGauge.gZ ρ hρ c0 hρp)^[n] X) = fl c0 X + n := by
  unfold fl
  rw [(gZ_iter ρ hρ c0 hρp n X).2, Int.add_mul_ediv_right _ _ (by exact_mod_cast hc0.ne')]

theorem gZ_ztau (n : ℕ) (X : (starTree L).ZVert) :
    (StarGauge.gZ ρ hρ c0 hρp)^[n] ((starTree L).ztau X) =
      (starTree L).ztau ((StarGauge.gZ ρ hρ c0 hρp)^[n] X) := by
  obtain ⟨h1, h2⟩ := gZ_iter ρ hρ c0 hρp n ((starTree L).ztau X)
  obtain ⟨h3, h4⟩ := gZ_iter ρ hρ c0 hρp n X
  apply OrientedTree.ZVert.ext
  · rw [h1]; exact h3.symm
  · rw [h2]; change X.t - 2 + _ = ((StarGauge.gZ ρ hρ c0 hρp)^[n] X).t - 2; rw [h4]; ring

theorem star_eq {u a b : V} (ha : a = b) (e : u ⟶ a) (e' : u ⟶ b) :
    (⟨a, e⟩ : Quiver.Star u) = ⟨b, e'⟩ := by
  subst ha; rw [Subsingleton.elim e e']

include hπ in
/-- Two lifts of an arrow with lifted sources over the same vertex. -/
theorem lift_eq_of_src {X Y Y' : (starTree L).ZVert} (e : X ⟶ Y) (e' : X ⟶ Y')
    (h : π.obj Y = π.obj Y') : Y = Y' := by
  have := (hπ.star_bijective X).1 (a₁ := ⟨Y, e⟩) (a₂ := ⟨Y', e'⟩) (star_eq h _ _)
  exact congrArg Sigma.fst this

include hdeck in
theorem π_gZ (n : ℕ) (Z : (starTree L).ZVert) : π.obj ((StarGauge.gZ ρ hρ c0 hρp)^[n] Z) = π.obj Z := by
  induction n generalizing Z with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hdeck, ih]

include hπ hc0 hdeck in
theorem fl_arrow_aux (n : ℕ) {X Y Y' : (starTree L).ZVert} (e : X ⟶ Y)
    (e' : (StarGauge.gZ ρ hρ c0 hρp)^[n] X ⟶ Y') (hY : π.obj Y = π.obj Y') :
    fl c0 Y - fl c0 X = fl c0 Y' - fl c0 ((StarGauge.gZ ρ hρ c0 hρp)^[n] X) := by
  obtain ⟨e''⟩ := gZ_arrow ρ hρ c0 hρp n ⟨e⟩
  have := lift_eq_of_src π hπ e'' e' (by rw [π_gZ π ρ hρ c0 hρp hdeck, hY])
  rw [← this, fl_gZ ρ hρ c0 hρp hc0, fl_gZ ρ hρ c0 hρp hc0]
  ring

include hπ hc0 hdeck hfib in
/-- **The winding increment of an arrow does not depend on its lift.** -/
theorem fl_arrow {X Y X' Y' : (starTree L).ZVert} (e : X ⟶ Y) (e' : X' ⟶ Y')
    (hX : π.obj X = π.obj X') (hY : π.obj Y = π.obj Y') : fl c0 Y - fl c0 X = fl c0 Y' - fl c0 X' := by
  obtain ⟨n, h | h⟩ := hfib X X' hX
  · subst h; exact fl_arrow_aux π hπ ρ hρ c0 hρp hc0 hdeck n e e' hY
  · subst h; exact (fl_arrow_aux π hπ ρ hρ c0 hρp hc0 hdeck n e' e hY.symm).symm

include hc0 hdeck hfib in
theorem fl_tau {X X' : (starTree L).ZVert} (hX : π.obj X = π.obj X') :
    fl c0 X - fl c0 ((starTree L).ztau X) = fl c0 X' - fl c0 ((starTree L).ztau X') := by
  obtain ⟨n, h | h⟩ := hfib X X' hX
  · subst h
    rw [← gZ_ztau, fl_gZ ρ hρ c0 hρp hc0, fl_gZ ρ hρ c0 hρp hc0]; ring
  · subst h
    rw [← gZ_ztau, fl_gZ ρ hρ c0 hρp hc0, fl_gZ ρ hρ c0 hρp hc0]; ring

include hπ in
theorem exists_lift_to {y x : V} (a : y ⟶ x) (X : (starTree L).ZVert) (hX : π.obj X = x) :
    ∃ (Y : (starTree L).ZVert) (_ : Y ⟶ X), π.obj Y = y := by
  subst hX
  obtain ⟨⟨Y, e⟩, he⟩ := (hπ.costar_bijective X).2 ⟨y, a⟩
  exact ⟨Y, e, congrArg Sigma.fst he⟩

include hπ hsurj in
theorem exists_lift {y x : V} (a : y ⟶ x) :
    ∃ (X Y : (starTree L).ZVert) (_ : X ⟶ Y), π.obj X = y ∧ π.obj Y = x := by
  obtain ⟨Y, hY⟩ := hsurj x
  obtain ⟨X, e, hX⟩ := exists_lift_to π hπ a Y hY
  exact ⟨X, Y, e, hX, hY⟩

include hc0 hdeck hfib in
theorem w_def_eq {y x : V} (a : y ⟶ x) {X Y : (starTree L).ZVert} (e : X ⟶ Y) (hX : π.obj X = y)
    (hY : π.obj Y = x) :
    fl c0 (Classical.choose (Classical.choose_spec (exists_lift π hπ hsurj a))) -
      fl c0 (Classical.choose (exists_lift π hπ hsurj a)) = fl c0 Y - fl c0 X := by
  obtain ⟨e0, hX0, hY0⟩ := Classical.choose_spec (Classical.choose_spec (exists_lift π hπ hsurj a))
  exact fl_arrow π hπ ρ hρ c0 hρp hc0 hdeck hfib e0 e (hX0.trans hX.symm) (hY0.trans hY.symm)

include hc0 hdeck hfib in
theorem ν_def_eq (x : V) {X : (starTree L).ZVert} (hX : π.obj X = x) :
    fl c0 (Classical.choose (hsurj x)) - fl c0 ((starTree L).ztau (Classical.choose (hsurj x))) =
      fl c0 X - fl c0 ((starTree L).ztau X) :=
  fl_tau π ρ hρ c0 hρp hc0 hdeck hfib ((Classical.choose_spec (hsurj x)).trans hX.symm)

/-- **The winding mesh weight.** -/
def floorWt : MeshWt Q ℤ where
  w {y x} a := fl c0 (Classical.choose (Classical.choose_spec (exists_lift π hπ hsurj a))) -
    fl c0 (Classical.choose (exists_lift π hπ hsurj a))
  ν x := fl c0 (Classical.choose (hsurj x.1)) -
    fl c0 ((starTree L).ztau (Classical.choose (hsurj x.1)))
  mesh x a := by
    obtain ⟨X, hX⟩ := hsurj x.1
    obtain ⟨Y, e, hY⟩ := exists_lift_to π hπ a.2 X hX
    have e' : (starTree L).ztau X ⟶ Y :=
      ⟨⟨(starTree L).G.adj_symm e.down.1, by change Y.t = X.t - 2 + 1; have := e.down.2; omega⟩⟩
    have hτX : π.obj ((starTree L).ztau X) = (Q.tau x).1 := by
      rw [hτ, hX, hQ.tauE_apply]
    rw [w_def_eq π hπ hsurj ρ hρ c0 hρp hc0 hdeck hfib (Q.mate x a.1 a.2) e' hτX hY,
      w_def_eq π hπ hsurj ρ hρ c0 hρp hc0 hdeck hfib a.2 e hY hX,
      ν_def_eq π hsurj ρ hρ c0 hρp hc0 hdeck hfib _ hX]
    ring

theorem floorWt_w {y x : V} (a : y ⟶ x) {X Y : (starTree L).ZVert} (e : X ⟶ Y) (hX : π.obj X = y)
    (hY : π.obj Y = x) :
    (floorWt hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib).w a = fl c0 Y - fl c0 X :=
  w_def_eq π hπ hsurj ρ hρ c0 hρp hc0 hdeck hfib a e hX hY

theorem floorWt_pw {X Z : (starTree L).ZVert} (P : Quiver.Path X Z) :
    (floorWt hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib).pw (π.mapPath P) = fl c0 Z - fl c0 X := by
  induction P with
  | nil => simp [MeshWt.pw]
  | cons P e ih =>
    rw [Prefunctor.mapPath_cons, MeshWt.pw, ih,
      floorWt_w hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib (π.map e) e rfl rfl]
    ring

theorem floorWt_ν (x : Q.nonprojective) {X : (starTree L).ZVert} (hX : π.obj X = x.1) :
    (floorWt hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib).ν x =
      fl c0 X - fl c0 ((starTree L).ztau X) :=
  ν_def_eq π hsurj ρ hρ c0 hρp hc0 hdeck hfib x.1 hX

theorem MeshWt_pw_cast {M : Type} [AddCommGroup M] (W : MeshWt Q M) {y x y' x' : V}
    (p : Quiver.Path y x) (h1 : y = y') (h2 : x = x') : W.pw (p.cast h1 h2) = W.pw p := by
  subst h1 h2; rfl

/-- **The candidate row winds once.** -/
theorem floorWt_candRow (hc0e : Even c0) (W₀ : List (Fin t)) (hW : W₀.length = c0 / 2 + 1) :
    ∀ R ∈ candRow hQ π W₀, (floorWt hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib).pw R.2 -
      (floorWt hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib).ν R.1 = 1 := by
  rintro R ⟨e, rfl⟩
  simp only
  erw [MeshWt_pw_cast]
  rw [floorWt_pw, floorWt_ν hQ π hπ hτ hsurj ρ hρ c0 hρp hc0 hdeck hfib _ rfl]
  obtain ⟨s, hs⟩ := hc0e
  have hs1 : 1 ≤ s := by omega
  have hc : (c0 : ℤ) = 2 * s := by omega
  have hWs : (W₀.length : ℤ) = s + 1 := by omega
  simp only [fl, OrientedTree.ztau, OrientedTree.liftEnd, X₀]
  have hlen : ((StarCorner.wordP (L := L) W₀).length : ℤ) = 2 * W₀.length := by
    rw [StarCorner.length_wordP]; push_cast; ring
  erw [hlen]
  push_cast
  rw [hWs, hc]
  have h1 : (-2 + 2 * ((s : ℤ) + 1) - 2) / (2 * s) = 0 :=
    Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h2 : (-2 : ℤ) / (2 * s) = -1 :=
    ((Int.ediv_emod_unique (by omega)).2 ⟨(by ring : 2 * (s : ℤ) - 2 + 2 * s * -1 = -2),
      by omega, by omega⟩).1
  rw [h1, h2]; ring

end StarTrace

end MultiplicativeBasisDeformations
