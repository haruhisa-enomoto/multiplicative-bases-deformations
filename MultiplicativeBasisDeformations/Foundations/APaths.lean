import MultiplicativeBasisDeformations.Foundations.StarCase
import MultiplicativeBasisDeformations.Foundations.ReRoot

/-!
# Mesh corrections for periodic models of type `A`

Appendix A, "Types A and D" (`periodic-mesh-calculations.tex:425–440`):
"When the twist is trivial … we may root the path at an endpoint and regard it
as a star with one arm … For the reflection of `A_{2n-1}`, rooted at its middle
vertex, the two closed paths at the centre are `x` and `-x`, and reflection sends
`x` to `-x`."
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarTrace

open OrientedTree StarCorner ScalarMeshCategory StarGauge

variable {L : Fin 1 → ℕ}
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  [Fintype Q.nonprojective]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b)
  (hρ' : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b))
  (c0 : ℕ) (hc0 : 0 < c0)
  (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ ρ hρ c0 hρp)^[n] X ∨ X = (gZ ρ hρ c0 hρp)^[n] Y)

include hπ hτ hsurj hρ' hc0 hdeck hfib in
/-- **Type `A`, trivial twist**: the deck generator preserves depths. -/
theorem surjective_A_id (hid : ∀ x, starDepth (ρ x) = starDepth x)
    (c : MeshCoefficients k Q) (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
  have h0 : ρ none = none := by
    have := hid none
    rcases h : ρ none with _ | x
    · rfl
    · rw [h] at this; simp [starDepth] at this
  exact surjective_of_fixed_centre hQ π hπ hτ hsurj ρ hρ hρ' h0 c0 hc0 hρp hdeck hfib
    (fun θ _ M _ _ D _ w hw ↦ TraceAlg.trace_A1 D (by rintro rfl; simp at hw)) c m hm

include hπ hτ hsurj hc0 hdeck hfib in
/-- **Type `A_{2h+1}`, reflection**: re-root at the middle vertex; the two closed
paths at the centre are `x` and `-x`. -/
theorem surjective_A_odd_reflection (h : ℕ) (hh : 1 ≤ h) (hL : L 0 = 2 * h - 1)
    (hrev : ∀ x, starDepth (ρ x) + starDepth x = L 0 + 1) (h2 : (2 : k) ≠ 0)
    (c : MeshCoefficients k Q) (m : ℕ) (hm : 2 ≤ m) : MeshDerivativeSurjective c m := by
  set e := ReRoot.midEquiv h hh L hL
  have he := ReRoot.midEquiv_adj h hh L hL
  have hδ := ReRoot.midEquiv_par h hh L hL
  have h0 : ReRoot.ρ' e ρ none = none := by
    apply ReRoot.pos_injective
    simp only [ReRoot.ρ', Equiv.trans_apply]
    rw [ReRoot.pos_midEquiv]
    have hmid : starDepth (e.symm none) = h := by
      have := ReRoot.pos_midEquiv h hh L hL (e.symm none)
      rw [Equiv.apply_symm_apply] at this
      simp [ReRoot.pos] at this; omega
    have := hrev (e.symm none)
    rw [hmid, hL] at this
    simp only [ReRoot.pos]; omega
  exact surjective_of_fixed_centre hQ (ReRoot.π' e he (h : ℤ) hδ π)
    (ReRoot.π'_isCovering e he (h : ℤ) hδ π hπ) (ReRoot.π'_tau e he (h : ℤ) hδ hQ π hτ)
    (ReRoot.π'_surj e he (h : ℤ) hδ π hsurj) (ReRoot.ρ' e ρ)
    (ReRoot.ρ'_adj e he ρ hρ) (ReRoot.ρ'_adj e he ρ hρ |> fun H a b ↦ (H a b).symm) h0 c0 hc0
    (ReRoot.ρ'_par e (h : ℤ) hδ ρ c0 hρp) (ReRoot.π'_deck e he (h : ℤ) hδ π ρ hρ c0 hρp hdeck)
    (ReRoot.π'_fib e he (h : ℤ) hδ π ρ hρ c0 hρp hfib)
    (fun θ _ M _ _ D _ w hw ↦ TraceAlg.trace_A2 D (TraceAlg.two_cancel h2)
      (by rintro rfl; simp at hw)) c m hm

end StarTrace

end MultiplicativeBasisDeformations
