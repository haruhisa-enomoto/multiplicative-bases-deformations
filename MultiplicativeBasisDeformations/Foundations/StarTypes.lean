import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Three-armed stars with positive definite form

Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex`): a star with
three arms of `L i + 1` vertices and `∑ (L i + 1)/(L i + 2) < 2` is `D_n`
(two arms of one vertex) or `E_6, E_7, E_8` (arms of `1, 2, 2`, `1, 2, 3`,
`1, 2, 4` vertices).
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

theorem frac_ge_half (n : ℕ) : (1 : ℚ) / 2 ≤ ((n : ℚ) + 1) / (n + 2) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; linarith

theorem frac_ge_two_thirds {n : ℕ} (h : 1 ≤ n) : (2 : ℚ) / 3 ≤ ((n : ℚ) + 1) / (n + 2) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : (1 : ℚ) ≤ n := by exact_mod_cast h
  linarith

theorem frac_ge_three_quarters {n : ℕ} (h : 2 ≤ n) : (3 : ℚ) / 4 ≤ ((n : ℚ) + 1) / (n + 2) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : (2 : ℚ) ≤ n := by exact_mod_cast h
  linarith

theorem frac_ge_five_sixths {n : ℕ} (h : 4 ≤ n) : (5 : ℚ) / 6 ≤ ((n : ℚ) + 1) / (n + 2) := by
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : (4 : ℚ) ≤ n := by exact_mod_cast h
  linarith

/-- **The three-armed stars of Proposition 4.1**: `D` (two arms of one vertex) or
`E` (arms of one, two and at most four vertices). -/
theorem three_arm_types (L : Fin 3 → ℕ) (hs : ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2) :
    (∃ a b : Fin 3, a ≠ b ∧ L a = 0 ∧ L b = 0) ∨
      (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ L a = 0 ∧ L b = 1 ∧ 1 ≤ L c ∧ L c ≤ 3) := by
  rw [Fin.sum_univ_three] at hs
  have b0 := frac_ge_half (L 0)
  have b1 := frac_ge_half (L 1)
  have b2 := frac_ge_half (L 2)
  -- some arm has one vertex
  have key : ∀ (i j l : Fin 3), i ≠ j → i ≠ l → j ≠ l →
      ((L i : ℚ) + 1) / (L i + 2) + ((L j : ℚ) + 1) / (L j + 2) + ((L l : ℚ) + 1) / (L l + 2) < 2 →
      L i = 0 → (∃ a b : Fin 3, a ≠ b ∧ L a = 0 ∧ L b = 0) ∨
        (∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ L a = 0 ∧ L b = 1 ∧ 1 ≤ L c ∧ L c ≤ 3) := by
    intro i j l hij hil hjl hsum hi
    rw [hi] at hsum
    norm_num at hsum
    rcases Nat.eq_zero_or_pos (L j) with hj | hj
    · exact Or.inl ⟨i, j, hij, hi, hj⟩
    rcases Nat.eq_zero_or_pos (L l) with hl | hl
    · exact Or.inl ⟨i, l, hil, hi, hl⟩
    right
    rcases Nat.lt_or_ge (L j) 2 with hj2 | hj2
    · -- `L j = 1`
      refine ⟨i, j, l, hij, hil, hjl, hi, by omega, hl, ?_⟩
      by_contra hl4
      have := frac_ge_five_sixths (n := L l) (by omega)
      have := frac_ge_two_thirds (n := L j) hj
      linarith
    · rcases Nat.lt_or_ge (L l) 2 with hl2 | hl2
      · refine ⟨i, l, j, hil, hij, hjl.symm, hi, by omega, hj, ?_⟩
        by_contra hj4
        have := frac_ge_five_sixths (n := L j) (by omega)
        have := frac_ge_two_thirds (n := L l) hl
        linarith
      · exfalso
        have := frac_ge_three_quarters hj2
        have := frac_ge_three_quarters hl2
        linarith
  rcases Nat.eq_zero_or_pos (L 0) with h0 | h0
  · exact key 0 1 2 (by decide) (by decide) (by decide) hs h0
  rcases Nat.eq_zero_or_pos (L 1) with h1 | h1
  · exact key 1 0 2 (by decide) (by decide) (by decide) (by linarith) h1
  rcases Nat.eq_zero_or_pos (L 2) with h2 | h2
  · exact key 2 0 1 (by decide) (by decide) (by decide) (by linarith) h2
  exfalso
  have := frac_ge_two_thirds h0
  have := frac_ge_two_thirds h1
  have := frac_ge_two_thirds h2
  linarith

end MultiplicativeBasisDeformations
