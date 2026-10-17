import MultiplicativeBasisDeformations.Foundations.StarAut
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Automorphisms of a star fixing its centre permute the arms

Used for the twists `θ = ρ^l` of Lemma A.2 (`periodic-mesh-calculations.tex:
322–343`): an automorphism of a star model fixing the centre preserves depths
and maps arm `i` onto an arm `θ i` of the same length, vertex by vertex.
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

variable {t : ℕ} {L : Fin t → ℕ}

section

variable (ρ : StarV L ≃ StarV L) (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b))
  (h0 : ρ none = none)

include hρ h0 in
/-- The image of the vertex `j` of arm `i` lies at depth `j + 1`, on some arm. -/
theorem arm_image (i : Fin t) :
    ∀ (j : ℕ) (hj : j < L i + 1), ∃ (i' : Fin t) (hj' : j < L i' + 1),
      ρ (some ⟨i, ⟨j, hj⟩⟩) = some ⟨i', ⟨j, hj'⟩⟩ ∧
      (∀ (j₀ : ℕ) (hj₀ : j₀ ≤ j) (hj₀' : j₀ < L i + 1), ∃ hj₀'' : j₀ < L i' + 1,
        ρ (some ⟨i, ⟨j₀, hj₀'⟩⟩) = some ⟨i', ⟨j₀, hj₀''⟩⟩) := by
  intro j
  induction j with
  | zero =>
      intro hj
      have hadj : starAdj (ρ none) (ρ (some ⟨i, ⟨0, hj⟩⟩)) := (hρ _ _).1 rfl
      rw [h0] at hadj
      obtain ⟨⟨i', ⟨j', hj'⟩⟩, he⟩ : ∃ x, ρ (some ⟨i, ⟨0, hj⟩⟩) = some x := by
        rcases h : ρ (some ⟨i, ⟨0, hj⟩⟩) with _ | x
        · rw [h] at hadj; exact (hadj : False).elim
        · exact ⟨x, rfl⟩
      rw [he] at hadj
      change j' = 0 at hadj
      subst hadj
      refine ⟨i', hj', he, fun j₀ hj₀ hj₀' ↦ ?_⟩
      obtain rfl : j₀ = 0 := by omega
      exact ⟨hj', he⟩
  | succ j ih =>
      intro hj
      obtain ⟨i', hj', he, hall⟩ := ih (by omega)
      have hadj : starAdj (ρ (some ⟨i, ⟨j, by omega⟩⟩)) (ρ (some ⟨i, ⟨j + 1, hj⟩⟩)) :=
        (hρ _ _).1 ⟨rfl, Or.inl rfl⟩
      rw [he] at hadj
      rcases h : ρ (some ⟨i, ⟨j + 1, hj⟩⟩) with _ | ⟨i'', ⟨j'', hj''⟩⟩
      · rw [h] at hadj
        change j = 0 at hadj
        subst hadj
        rw [← h0] at h
        have := ρ.injective h
        simp at this
      · rw [h] at hadj
        obtain ⟨rfl, hj2 | hj2⟩ := hadj
        · -- one step out
          change j'' = j + 1 at hj2
          subst hj2
          refine ⟨i', hj'', rfl, fun j₀ hj₀ hj₀' ↦ ?_⟩
          rcases Nat.lt_or_ge j₀ (j + 1) with hlt | hge
          · exact hall j₀ (by omega) hj₀'
          · obtain rfl : j₀ = j + 1 := by omega
            exact ⟨hj'', h⟩
        · -- one step in: the image would coincide with that of the parent
          change j = j'' + 1 at hj2
          subst hj2
          exfalso
          obtain ⟨hp', hp''⟩ := hall j'' (by omega) (by omega)
          have := congrArg (fun v : StarV L ↦ starDepth v) (ρ.injective (h.trans hp''.symm))
          simp only [starDepth] at this
          omega

include hρ h0 in
/-- **An automorphism fixing the centre permutes the arms**, preserving their
lengths. -/
theorem arm_perm : ∃ θ : Equiv.Perm (Fin t), (∀ i, L (θ i) = L i) ∧
    ∀ (i : Fin t) (j : ℕ) (hj : j < L i + 1), ∃ hj' : j < L (θ i) + 1,
      ρ (some ⟨i, ⟨j, hj⟩⟩) = some ⟨θ i, ⟨j, hj'⟩⟩ := by
  classical
  choose f hf0 hf using fun i ↦ arm_image ρ hρ h0 i 0 (Nat.zero_lt_succ _)
  have hall : ∀ (i : Fin t) (j : ℕ) (hj : j < L i + 1), ∃ hj' : j < L (f i) + 1,
      ρ (some ⟨i, ⟨j, hj⟩⟩) = some ⟨f i, ⟨j, hj'⟩⟩ := by
    intro i j hj
    obtain ⟨i', hj', he, hall⟩ := arm_image ρ hρ h0 i j hj
    obtain ⟨h0', h0''⟩ := hall 0 (Nat.zero_le _) (Nat.zero_lt_succ _)
    have hi' : i' = f i := by
      have := (h0''.symm.trans (hf i).1)
      simp only [Option.some.injEq, Sigma.mk.inj_iff] at this
      exact this.1
    subst hi'
    exact ⟨hj', he⟩
  let v0 : Fin t → StarV L := fun i ↦ some ⟨i, ⟨0, Nat.zero_lt_succ _⟩⟩
  have hinj : Function.Injective f := by
    intro i i' h
    have e1 : ρ (v0 i) = v0 (f i) := (hf i).1
    have e2 : ρ (v0 i') = v0 (f i') := (hf i').1
    have := ρ.injective ((e1.trans (congrArg v0 h)).trans e2.symm)
    simp only [v0, Option.some.injEq, Sigma.mk.inj_iff] at this
    exact this.1
  let θ : Equiv.Perm (Fin t) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hle : ∀ i, L i ≤ L (θ i) := by
    intro i
    obtain ⟨hj', -⟩ := hall i (L i) (Nat.lt_succ_self _)
    exact Nat.lt_succ_iff.1 hj'
  have hL : ∀ i, L (θ i) = L i := by
    have hsum : ∑ i, L i = ∑ i, L (θ i) := (Equiv.sum_comp θ L).symm
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ ↦ hle i)).1 hsum
    exact fun i ↦ (this i (Finset.mem_univ _)).symm
  exact ⟨θ, hL, hall⟩

end

end MultiplicativeBasisDeformations
