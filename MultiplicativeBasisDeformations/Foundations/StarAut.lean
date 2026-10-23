module

public import MultiplicativeBasisDeformations.Foundations.StarModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Automorphisms of star models

Proof of Proposition 4.1, Step 4 (`periodic-mesh-calculations.tex`):
"For `D` and `E`, root the tree at the trivalent vertex; for odd `A`, root it at
its middle vertex. Every tree automorphism fixes that root."

* With three arms, every automorphism fixes the centre (`fixes_centre_three`).
* For a path (one arm), an automorphism is the identity or the reversal of
  depths (`path_aut`); a reversal preserving the parity of depths fixes the
  middle vertex.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

variable {t : ℕ} {L : Fin t → ℕ}

/-- A neighbour of an arm vertex has depth one less or one more, and is
determined by its depth. -/
theorem nbr_of_some {i : Fin t} {k : Fin (L i + 1)} {y y' : StarV L}
    (hy : starAdj (some ⟨i, k⟩) y) (hy' : starAdj (some ⟨i, k⟩) y')
    (hd : starDepth y = starDepth y') : y = y' := by
  rcases y with _ | ⟨j, l⟩ <;> rcases y' with _ | ⟨j', l'⟩ <;>
    simp only [starAdj, starDepth] at hy hy' hd
  · rfl
  · omega
  · omega
  · obtain ⟨rfl, -⟩ := hy
    obtain ⟨rfl, -⟩ := hy'
    have : l = l' := Fin.ext (by omega)
    rw [this]

theorem depth_nbr_of_some {i : Fin t} {k : Fin (L i + 1)} {y : StarV L}
    (hy : starAdj (some ⟨i, k⟩) y) : starDepth y = k ∨ starDepth y = k + 2 := by
  rcases y with _ | ⟨j, l⟩ <;> simp only [starAdj, starDepth] at hy ⊢ <;> omega

/-- **With three arms, every automorphism fixes the centre.** -/
theorem fixes_centre_three (ht : t = 3) (ρ : StarV L ≃ StarV L)
    (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) : ρ none = none := by
  subst ht
  by_contra hne
  obtain ⟨⟨i, k⟩, hik⟩ : ∃ x, ρ none = some x := Option.ne_none_iff_exists'.1 hne
  have hn : ∀ j : Fin 3, starAdj (some ⟨i, k⟩) (ρ (some ⟨j, 0⟩)) := by
    intro j
    rw [← hik, ← hρ]
    simp [starAdj]
  have hd : ∀ j : Fin 3, starDepth (ρ (some ⟨j, 0⟩)) = k ∨ starDepth (ρ (some ⟨j, 0⟩)) = k + 2 :=
    fun j ↦ depth_nbr_of_some (hn j)
  have hinj : ∀ j j' : Fin 3, starDepth (ρ (some ⟨j, 0⟩)) = starDepth (ρ (some ⟨j', 0⟩)) →
      j = j' := by
    intro j j' h
    have := ρ.injective (nbr_of_some (hn j) (hn j') h)
    simp only [Option.some.injEq, Sigma.mk.inj_iff] at this
    exact this.1
  rcases hd 0 with h0 | h0 <;> rcases hd 1 with h1 | h1 <;> rcases hd 2 with h2 | h2 <;>
    first
      | exact absurd (hinj 0 1 (h0.trans h1.symm)) (by decide)
      | exact absurd (hinj 0 2 (h0.trans h2.symm)) (by decide)
      | exact absurd (hinj 1 2 (h1.trans h2.symm)) (by decide)

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

variable {L : Fin 1 → ℕ}

/-- The vertex of a path at a given depth. -/
def ofDep (L : Fin 1 → ℕ) (d : ℕ) (hd : d ≤ L 0 + 1) : StarV L :=
  match d, hd with
  | 0, _ => none
  | d + 1, hd => some ⟨0, ⟨d, by omega⟩⟩

theorem starDepth_ofDep (d : ℕ) (hd : d ≤ L 0 + 1) : starDepth (ofDep L d hd) = d := by
  cases d <;> rfl

theorem depth_le (x : StarV L) : starDepth x ≤ L 0 + 1 := by
  rcases x with _ | ⟨i, k⟩
  · simp [starDepth]
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [starDepth]; have := k.2; omega

theorem depth_injective : Function.Injective (starDepth (L := L)) := by
  intro x y h
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩ <;> simp only [starDepth] at h
  · rfl
  · omega
  · omega
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    have : k = l := Fin.ext (by omega)
    rw [this]

theorem adj_ofDep (d : ℕ) (hd : d + 1 ≤ L 0 + 1) :
    starAdj (ofDep L d (by omega)) (ofDep L (d + 1) hd) := by
  cases d with
  | zero => simp [ofDep, starAdj]
  | succ d => simp [ofDep, starAdj]

/-- **Automorphisms of a path**: the identity or the reversal of depths. -/
theorem path_aut (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) :
    (∀ x, starDepth (ρ x) = starDepth x) ∨ (∀ x, starDepth (ρ x) + starDepth x = L 0 + 1) := by
  let g : ℕ → ℤ := fun d ↦ if hd : d ≤ L 0 + 1 then starDepth (ρ (ofDep L d hd)) else 0
  have hgx : ∀ x, g (starDepth x) = starDepth (ρ x) := by
    intro x
    simp only [g, dif_pos (depth_le x)]
    congr 3
    exact depth_injective (starDepth_ofDep _ _)
  have hstep : ∀ d, d + 1 ≤ L 0 + 1 → g (d + 1) = g d + 1 ∨ g d = g (d + 1) + 1 := by
    intro d hd
    have h := (hρ _ _).1 (adj_ofDep d hd)
    simp only [g, dif_pos hd, dif_pos (show d ≤ L 0 + 1 by omega)]
    rcases starAdj_depth h with h' | h' <;> omega
  have hne : ∀ d, d + 2 ≤ L 0 + 1 → g (d + 2) ≠ g d := by
    intro d hd h
    simp only [g, dif_pos hd, dif_pos (show d ≤ L 0 + 1 by omega)] at h
    have h' := depth_injective (Int.ofNat_inj.1 h)
    have := congrArg starDepth (ρ.injective h')
    rw [starDepth_ofDep, starDepth_ofDep] at this
    omega
  have hrange : ∀ d, d ≤ L 0 + 1 → 0 ≤ g d ∧ g d ≤ L 0 + 1 := by
    intro d hd
    simp only [g, dif_pos hd]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast depth_le _⟩
  set s := g 1 - g 0
  have hs : s = 1 ∨ s = -1 := by
    have h := hstep 0 (by omega)
    simp only [zero_add] at h
    rcases h with h | h <;> omega
  have hlin : ∀ d, d ≤ L 0 + 1 → g d = g 0 + d * s := by
    have key : ∀ d, d + 1 ≤ L 0 + 1 → g d = g 0 + d * s ∧ g (d + 1) = g 0 + (d + 1) * s := by
      intro d
      induction d with
      | zero => intro _; simp [s]
      | succ d ih =>
          intro hd
          obtain ⟨h1, h2⟩ := ih (by omega)
          refine ⟨by push_cast; linarith, ?_⟩
          have h3 := hstep (d + 1) hd
          have h4 := hne d (by omega)
          push_cast at h1 h2 ⊢
          rcases hs with hs | hs <;> rcases h3 with h3 | h3 <;> rw [hs] at h1 h2 ⊢ <;>
            first | linarith | (exfalso; apply h4; linarith)
    intro d hd
    cases d with
    | zero => simp
    | succ d => exact (key d hd).2
  have hlast := hlin (L 0 + 1) le_rfl
  have hr := hrange (L 0 + 1) le_rfl
  have hr0 := hrange 0 (by omega)
  rcases hs with hs | hs
  · left
    intro x
    have := hlin _ (depth_le x)
    rw [hgx] at this
    rw [hs] at hlast this
    push_cast at hlast this
    have : g 0 = 0 := by linarith
    omega
  · right
    intro x
    have := hlin _ (depth_le x)
    rw [hgx] at this
    rw [hs] at hlast this
    push_cast at hlast this
    omega

/-- A parity-preserving automorphism of a path fixes a vertex. -/
theorem path_aut_fixed (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b))
    (hpar : ∀ x, starDepth (ρ x) % 2 = starDepth x % 2) : ∃ x, ρ x = x := by
  rcases path_aut ρ hρ with h | h
  · exact ⟨none, depth_injective (h none)⟩
  · have h0 := h none
    have hp := hpar none
    simp only [starDepth] at h0 hp
    obtain ⟨m, hm⟩ : ∃ m, L 0 + 1 = 2 * m := ⟨(L 0 + 1) / 2, by omega⟩
    refine ⟨ofDep L m (by omega), depth_injective ?_⟩
    have := h (ofDep L m (by omega))
    rw [starDepth_ofDep] at this ⊢
    omega

end MultiplicativeBasisDeformations
