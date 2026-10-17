import MultiplicativeBasisDeformations.Foundations.OddQuotient

/-!
# The deck transformation of the degree of a row

Proof of Lemma A.2(1) (`periodic-mesh-calculations.tex:337–340`): "Lift a row
path from `τ(x, j)`. Its endpoint has the form `(ρ^l x, j - sl)`." For a deck
generator `g (v, t) = (ρ v, t + c₀)`, a row of length `m + 1` lifts to a path
from `τ X` to `g^n X` with `n c₀ = m - 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree ScalarMeshCategory StarGauge

variable {t : ℕ} {L : Fin t → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hc0 : 0 < c0)
  (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)

include hρp in
theorem par_pow (n : ℕ) (v : StarV L) :
    (starTree L).par ((ρ ^ n) v) = (starTree L).par v + (((n * c0 : ℕ) : ℤ) : ZMod 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hρp, ih]; push_cast; ring

/-- The deck transformation `g^n` in height form. -/
abbrev gPow (n : ℕ) : (starTree L).ZVert ⥤q (starTree L).ZVert :=
  (starTree L).zAct (ρ ^ n) (StarTrace.adj_pow ρ hρ n) ((n * c0 : ℕ) : ℤ) (par_pow ρ c0 hρp n)

theorem gPow_obj (n : ℕ) (Z : (starTree L).ZVert) :
    (gPow ρ hρ c0 hρp n).obj Z = (gZ ρ hρ c0 hρp)^[n] Z := by
  apply ZVert.ext
  · exact (gZ_iter ρ hρ c0 hρp n Z).1.symm
  · rw [(gZ_iter ρ hρ c0 hρp n Z).2]; change Z.t + ((n * c0 : ℕ) : ℤ) = _; push_cast; ring

include hdeck in
theorem gPow_deck (n : ℕ) (Z : (starTree L).ZVert) :
    π.obj ((gPow ρ hρ c0 hρp n).obj Z) = π.obj Z := by
  rw [gPow_obj]; exact π_gZ_iter π ρ hρ c0 hρp hdeck n Z

include hc0 hfib in
theorem gPow_fib (n : ℕ) (X E : (starTree L).ZVert) (h1 : π.obj E = π.obj X)
    (h2 : E.t = X.t + ((n * c0 : ℕ) : ℤ)) : E = (gPow ρ hρ c0 hρp n).obj X := by
  rw [gPow_obj]
  have hgt : ∀ (n : ℕ) (Z : (starTree L).ZVert), ((gZ ρ hρ c0 hρp)^[n] Z).t = Z.t + n * c0 :=
    fun n Z ↦ (gZ_iter ρ hρ c0 hρp n Z).2
  obtain ⟨n', hn' | hn'⟩ := hfib X E h1.symm
  · have := hgt n' X
    rw [← hn', h2] at this
    have : n' = n := by
      have h3 : (n' : ℤ) * c0 = n * c0 := by push_cast at this; omega
      exact_mod_cast mul_right_cancel₀ (by positivity) h3
    subst this; exact hn'
  · have := hgt n' E
    rw [← hn', h2] at this
    push_cast at this
    have h4 : (0 : ℤ) ≤ n * c0 := by positivity
    have h5 : (0 : ℤ) ≤ n' * c0 := by positivity
    have hn0 : n = 0 := by
      by_contra hne; have : (0 : ℤ) < n * c0 := by positivity
      omega
    have hn'0 : n' = 0 := by
      by_contra hne; have : (0 : ℤ) < n' * c0 := by positivity
      omega
    subst hn0 hn'0
    exact hn'.symm

include hπ hτ hsurj hc0 hfib in
/-- **Rows of length `m + 1` exist only in degrees `c₀ ∣ m - 1`**, and lift to
paths from `τ X` to `g^n X` with `n c₀ = m - 1`. -/
theorem row_lift {m : ℕ} (hm : 1 ≤ m) (x : Q.nonprojective) (p : Quiver.Path (Q.tau x).1 x.1)
    (hp : p.length = m + 1) :
    ∃ (n : ℕ) (X : (starTree L).ZVert) (P : Quiver.Path ((starTree L).ztau X)
      ((gPow ρ hρ c0 hρp n).obj X)), ((n * c0 : ℕ) : ℤ) = m - 1 ∧ P.length = m + 1 ∧
      rowClass c m x p = (starTree L).rowZ hQ π c m P := by
  obtain ⟨X, hX⟩ := hsurj x.1
  have e1 : π.obj ((starTree L).ztau X) = (Q.tau x).1 := by rw [hτ, hX]; rfl
  obtain ⟨E, hE, P, hP⟩ := RelSystem.exists_lift π hπ ((starTree L).ztau X) (p.cast e1.symm rfl)
  have hPlen : P.length = m + 1 := by
    rw [← LinearPaths.length_mapPath π P, hP, length_cast, length_cast, hp]
  have hEt : E.t = X.t + (m - 1 : ℤ) := by
    have := (starTree L).t_path P
    rw [hPlen] at this; simp only [ztau] at this; push_cast at this; omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((n * c0 : ℕ) : ℤ) = m - 1 := by
    have hgt : ∀ (n : ℕ) (Z : (starTree L).ZVert), ((gZ ρ hρ c0 hρp)^[n] Z).t = Z.t + n * c0 :=
      fun n Z ↦ (gZ_iter ρ hρ c0 hρp n Z).2
    obtain ⟨n, hn | hn⟩ := hfib X E (hE.trans hX.symm).symm
    · exact ⟨n, by have := hgt n X; rw [← hn] at this; push_cast; omega⟩
    · have h1 := hgt n E; rw [← hn] at h1
      have h2 : (0 : ℤ) ≤ n * c0 := by positivity
      exact ⟨0, by push_cast; omega⟩
  have hEX : E = (gPow ρ hρ c0 hρp n).obj X :=
    gPow_fib π ρ hρ c0 hc0 hρp hfib n X E (hE.trans hX.symm) (by rw [hEt, hn])
  subst hEX
  refine ⟨n, X, P, hn, hPlen, ?_⟩
  rw [OrientedTree.rowZ, hP, rowQ_cast, rowQ_cast]
  exact (rowQ_eq c hQ m p).symm

end StarTrace

end MultiplicativeBasisDeformations
