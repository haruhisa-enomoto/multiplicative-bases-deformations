import MultiplicativeBasisDeformations.Foundations.DegreeDeck

/-!
# Mesh corrections on the odd quotients of even `A`

Appendix A, "The odd quotients of even A" (`periodic-mesh-calculations.tex`): after normalizing all mesh coefficients to one (Lemma A.1(2)), rows are
reduced by the sum of their levels to words in the middle arrows, which vanish
when two is invertible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge EvenA

variable {L : Fin 1 → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hc0 : 0 < c0)
  (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)

include hπ hτ hsurj hc0 hdeck hfib in
/-- **Type `A_{2h}`, odd quotients**: the deck generator reverses the path. -/
theorem surjective_A_even (h : ℕ) (hh : 1 ≤ h) (hL : L 0 = 2 * h - 2)
    (hrev : ∀ x, starDepth (ρ x) + starDepth x = L 0 + 1) (h2 : (2 : k) ≠ 0)
    (c : MeshCoefficients k Q) (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
  -- `c₀` is odd: the reversal changes the parity of depths
  have hodd : Odd c0 := by
    have h1 := hρp none
    have h3 := hrev none
    change ((starDepth (ρ none) : ℕ) : ZMod 2) = ((starDepth (none : StarV L) : ℕ) : ZMod 2) + _
      at h1
    have h3' : starDepth (ρ none) = 2 * h - 1 := by
      have h4 : starDepth (none : StarV L) = 0 := rfl
      rw [h4, add_zero, hL] at h3; omega
    rw [h3'] at h1
    simp only [starDepth, Nat.cast_zero, zero_add] at h1
    rcases Nat.even_or_odd c0 with he | ho
    · exfalso
      obtain ⟨r, hr⟩ := he
      rw [hr] at h1
      obtain ⟨q, hq⟩ : ∃ q, 2 * h - 1 = 2 * q + 1 := ⟨h - 1, by omega⟩
      rw [hq] at h1; push_cast at h1
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul, zero_add] at h1
      exact absurd h1 (by decide)
    · exact ho
  -- the levels are invariant under the reversal and its powers
  have hρlev : ∀ v, lev h (starDepth (ρ v)) = lev h (starDepth v) := by
    intro v
    have h1 := hrev v
    have h2' := depth_le v
    rw [hL] at h1 h2'
    rw [show starDepth (ρ v) = 2 * h - 1 - starDepth v by omega]
    exact lev_rev h _ (by omega)
  have hpowlev : ∀ (n : ℕ) v, lev h (starDepth ((ρ ^ n) v)) = lev h (starDepth v) := by
    intro n; induction n with
    | zero => intro v; rfl
    | succ n ih => intro v; rw [pow_succ', Equiv.Perm.mul_apply, hρlev, ih]
  -- normalize the coefficients to one
  obtain ⟨μ, η, hone⟩ := OddGauge.exists_one_gauge hQ π hπ c ρ hρ c0 hρp hdeck h hh hL hrev hτ
    hsurj hfib hodd
  set c' : MeshCoefficients k Q := fun x y a ↦ η x * c x y a * μ (Q.mate x y a) * μ a
  have hgauge : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c x y a = (η x)⁻¹ * c' x y a * (μ (Q.mate x y a))⁻¹ * (μ a)⁻¹ :=
    gauge_symm (fun a ↦ μ a) η c c' (fun _ _ _ ↦ rfl)
  refine surjective_gauge (fun a ↦ (μ a)⁻¹) (fun x ↦ (η x)⁻¹) c' c hgauge ?_
  have hc : ∀ x y a, c' x y a = 1 := (starTree L).one_of_pull hQ π c' hπ hsurj hone
  rw [surjective_iff_rows]
  intro x p hp
  rw [← Submodule.Quotient.mk_eq_zero]
  change rowClass c' m x p = 0
  obtain ⟨n, X, P, hn, hPlen, hrow⟩ := row_lift hQ π c' hπ hτ hsurj ρ hρ c0 hc0 hρp hfib
    (by omega) x p hp
  rw [hrow]
  -- the reduction by levels, at the deck transformation of the degree
  have hXX : (starTree L).ztauInv ((starTree L).ztau X) = X := by
    ext <;> simp [ztau, ztauInv]
  have hend : (gPow ρ hρ c0 hρp n).obj X = (starTree L).rowEnd (ρ ^ n) (adj_pow ρ hρ n)
      ((n * c0 : ℕ) : ℤ) (par_pow ρ c0 hρp n) ((starTree L).ztau X) := by
    rw [rowEnd, hXX]
  rw [← (starTree L).rowZ_cast hQ π c' m rfl hend P]
  have hs : (m : ℤ) + 1 = 2 + ((n * c0 : ℕ) : ℤ) := by omega
  exact reduce h hh hL (ρ ^ n) (adj_pow ρ hρ n) ((n * c0 : ℕ) : ℤ) (par_pow ρ c0 hρp n)
    (hpowlev n) hQ π c' hπ hτ hone hc (gPow_deck π ρ hρ c0 hρp hdeck n) m (by omega) hs
    (fun Z P' hP' hlev ↦ eps_zero h hh (ρ ^ n) (adj_pow ρ hρ n) ((n * c0 : ℕ) : ℤ)
      (par_pow ρ c0 hρp n) (hpowlev n) hQ π c' hτ hc (gPow_deck π ρ hρ c0 hρp hdeck n) ρ hρ c0
      hρp hdeck hodd hρlev h2 m Z P' hP' hlev)
    _ _ _ (by rw [length_cast]; exact hPlen) le_rfl

end StarTrace

end MultiplicativeBasisDeformations
