import MultiplicativeBasisDeformations.Foundations.DynkinForm
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Forbidden configurations

Proof of Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex`):
"A vertex of degree at least four would contain a four-leaf star, and the
vector `z` with entries two at the centre and one at the leaves satisfies
`zᵀMz = 0` on it. Two trivalent vertices would contain their connecting path
and two extra edges at each end; weights two on the path and one on its four
leaves again give a nonzero vector `z` with `zᵀMz = 0`. Both contradict positive
definiteness of principal submatrices."

With the configuration bound (`qform_le_config`), the extra edges of the whole
graph only lower `zᵀMz`, so each configuration gives `zᵀMz ≤ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace MultiplicativeBasisDeformations

universe v

variable {D : Type v} [Fintype D] [DecidableEq D] (G : SimpleGraph D) [DecidableRel G.Adj]
  {n : D → ℚ} (hn : ∀ i, 0 < n i) (hMn : ∀ i, 0 < 2 * n i - ∑ j ∈ G.neighborFinset i, n j)

include hn hMn in
/-- A configuration with nonnegative, not all zero, weights and `∑ 2 w² ≤ ∑ w w`
over distinct adjacent pairs cannot occur. -/
theorem config_false {ι κ : Type*} [Fintype ι] [Fintype κ] {h : ι → D}
    (hh : Function.Injective h) (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (i₀ : ι) (hi₀ : w i₀ ≠ 0)
    (e : κ → ι × ι) (he : Function.Injective e) (hadj : ∀ c, G.Adj (h (e c).1) (h (e c).2))
    (hle : ∑ i, 2 * w i ^ 2 ≤ ∑ c, w (e c).1 * w (e c).2) : False := by
  have h1 := qform_le_config G hh w hw e he hadj
  have hz : zOf h w ≠ 0 := by
    intro h0
    have := congrFun h0 (h i₀)
    rw [zOf_apply hh] at this
    exact hi₀ this
  have h2 := qform_pos G n hn hMn hz
  linarith

include hn hMn in
/-- **No vertex of degree four.** -/
theorem degree_le_three (v : D) : G.degree v ≤ 3 := by
  by_contra hdeg
  push_neg at hdeg
  obtain ⟨f⟩ : Nonempty (Fin 4 ↪ G.neighborFinset v) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_fin, Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  let h : Fin 5 → D := Fin.cons v fun k ↦ (f k : D)
  have hh : Function.Injective h := by
    refine Fin.cons_injective_iff.2 ⟨?_, fun a b hab ↦ f.injective (Subtype.ext hab)⟩
    rintro ⟨k, hk⟩
    change (f k : D) = v at hk
    have := (SimpleGraph.mem_neighborFinset _ _ _).1 (f k).2
    rw [hk] at this
    exact G.irrefl this
  let w : Fin 5 → ℚ := ![2, 1, 1, 1, 1]
  let e : Fin 4 × Bool → Fin 5 × Fin 5 := fun c ↦
    if c.2 then (0, c.1.succ) else (c.1.succ, 0)
  refine config_false G hn hMn hh w (by intro i; fin_cases i <;> norm_num [w]) 0 (by norm_num [w])
    e ?_ ?_ ?_
  · rintro ⟨a, ba⟩ ⟨b, bb⟩ hab
    cases ba <;> cases bb <;> simp [e] at hab <;> simp [hab]
  · rintro ⟨k, b⟩
    have hk := (SimpleGraph.mem_neighborFinset _ _ _).1 (f k).2
    cases b
    · simpa [e, h] using hk.symm
    · simpa [e, h] using hk
  · simp [w, e, Fin.sum_univ_succ, Fintype.sum_prod_type]
    norm_num

include hn hMn in
/-- **No two trivalent vertices**: the configuration of a path `p₀ … p_m` with two
extra leaves at each end cannot occur. -/
theorem no_two_trivalent {m : ℕ} (p : Fin (m + 1) → D) (l : Fin 4 → D)
    (hinj : Function.Injective (Sum.elim p l))
    (hpath : ∀ k : Fin m, G.Adj (p k.castSucc) (p k.succ))
    (hl : ∀ j : Fin 4, G.Adj (if (j : ℕ) < 2 then p 0 else p (Fin.last m)) (l j)) : False := by
  let w : Fin (m + 1) ⊕ Fin 4 → ℚ := Sum.elim (fun _ ↦ 2) (fun _ ↦ 1)
  let att : Fin 4 → Fin (m + 1) ⊕ Fin 4 := fun j ↦
    if (j : ℕ) < 2 then Sum.inl 0 else Sum.inl (Fin.last m)
  let e : (Fin m × Bool) ⊕ (Fin 4 × Bool) → (Fin (m + 1) ⊕ Fin 4) × (Fin (m + 1) ⊕ Fin 4) :=
    Sum.elim (fun c ↦ if c.2 then (Sum.inl c.1.castSucc, Sum.inl c.1.succ)
        else (Sum.inl c.1.succ, Sum.inl c.1.castSucc))
      (fun c ↦ if c.2 then (att c.1, Sum.inr c.1) else (Sum.inr c.1, att c.1))
  refine config_false G hn hMn hinj w (by rintro (i | i) <;> norm_num [w]) (Sum.inr 0)
    (by norm_num [w]) e ?_ ?_ ?_
  · rintro ((⟨a, ba⟩ | ⟨a, ba⟩)) ((⟨b, bb⟩ | ⟨b, bb⟩)) hab <;>
      cases ba <;> cases bb <;> simp [e, att] at hab <;> (try split_ifs at hab) <;>
      simp_all [Fin.ext_iff] <;> omega
  · rintro ((⟨k, b⟩ | ⟨j, b⟩)) <;> cases b
    · simpa [e] using (hpath k).symm
    · simpa [e] using hpath k
    · have := (hl j).symm
      change G.Adj (l j) (Sum.elim p l (att j))
      by_cases hj : (j : ℕ) < 2
      · rw [show att j = Sum.inl 0 from if_pos hj]; rw [if_pos hj] at this; exact this
      · rw [show att j = Sum.inl (Fin.last m) from if_neg hj]; rw [if_neg hj] at this; exact this
    · have := hl j
      change G.Adj (Sum.elim p l (att j)) (l j)
      by_cases hj : (j : ℕ) < 2
      · rw [show att j = Sum.inl 0 from if_pos hj]; rw [if_pos hj] at this; exact this
      · rw [show att j = Sum.inl (Fin.last m) from if_neg hj]; rw [if_neg hj] at this; exact this
  · have hatt : ∀ j : Fin 4, w (att j) = 2 := fun j ↦ by
      simp only [att]; split_ifs <;> rfl
    simp only [e, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Sum.elim_inl,
      Sum.elim_inr, if_true, Bool.false_eq_true, if_false, hatt]
    simp [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring_nf
    rfl

/-- The sum identity behind the arm computation. -/
theorem arm_sum_aux (L : ℕ) :
    2 * ∑ j ∈ Finset.range (L + 1), ((j : ℚ) + 1) ^ 2 -
      2 * ∑ j ∈ Finset.range L, ((j : ℚ) + 1) * ((j : ℚ) + 2) = (L + 1) * (L + 2) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      rw [Finset.sum_range_succ (fun j : ℕ ↦ ((j : ℚ) + 1) ^ 2) (L + 1),
        Finset.sum_range_succ (fun j : ℕ ↦ ((j : ℚ) + 1) * ((j : ℚ) + 2)) L]
      push_cast at ih ⊢
      linear_combination ih

/-- **The arm computation** (the Schur complement at the centre): for one arm of
length `L + 1` with weights `(L + 1 - k)/(L + 2)`, its contribution is
`-(L+1)/(L+2)`. -/
theorem arm_contribution (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), 2 * (((L : ℚ) + 1 - k) / (L + 2)) ^ 2 -
      2 * (((L : ℚ) + 1) / (L + 2)) -
      ∑ k ∈ Finset.range L, 2 * ((((L : ℚ) + 1 - k) / (L + 2)) * (((L : ℚ) - k) / (L + 2))) =
      -(((L : ℚ) + 1) / (L + 2)) := by
  have hL' : (L : ℚ) + 2 ≠ 0 := by positivity
  have e1 : ∑ k ∈ Finset.range (L + 1), 2 * (((L : ℚ) + 1 - k) / (L + 2)) ^ 2 =
      2 / ((L : ℚ) + 2) ^ 2 * ∑ j ∈ Finset.range (L + 1), ((j : ℚ) + 1) ^ 2 := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have e2 : ∑ k ∈ Finset.range L, 2 * ((((L : ℚ) + 1 - k) / (L + 2)) * (((L : ℚ) - k) / (L + 2))) =
      2 / ((L : ℚ) + 2) ^ 2 * ∑ j ∈ Finset.range L, ((j : ℚ) + 1) * ((j : ℚ) + 2) := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rw [e1, e2]
  have := arm_sum_aux L
  field_simp
  linear_combination this

theorem sigma_fin_eq_iff {t : ℕ} {L : Fin t → ℕ} {a b : Fin t} {k : Fin (L a + 1)}
    {k' : Fin (L b + 1)} : (⟨a, k⟩ : Σ i, Fin (L i + 1)) = ⟨b, k'⟩ ↔ a = b ∧ (k : ℕ) = k' := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, h⟩; exact Sigma.ext rfl (heq_of_eq (Fin.ext h))

include hn hMn in
/-- **The arm inequality** (Schur complement at the centre,
`periodic-mesh-calculations.tex`): a centre with `t` arms of lengths
`L_i + 1` satisfies `∑_i (L_i + 1)/(L_i + 2) < 2`, i.e.
`2 - ∑ p_i/(p_i + 1) > 0` for arm lengths `p_i`. -/
theorem arm_inequality {t : ℕ} (L : Fin t → ℕ) (c : D) (a : ∀ i, Fin (L i + 1) → D)
    (hinj : Function.Injective (Sum.elim (fun _ : Unit ↦ c) (fun x : Σ i, Fin (L i + 1) ↦ a x.1 x.2)))
    (hc : ∀ i, G.Adj c (a i 0)) (ha : ∀ i (k : Fin (L i)), G.Adj (a i k.castSucc) (a i k.succ)) :
    ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2 := by
  by_contra hcon
  push_neg at hcon
  let w : Unit ⊕ (Σ i, Fin (L i + 1)) → ℚ :=
    Sum.elim (fun _ ↦ 1) (fun x ↦ ((L x.1 : ℚ) + 1 - x.2) / (L x.1 + 2))
  let e : (Fin t × Bool) ⊕ ((Σ i, Fin (L i)) × Bool) →
      (Unit ⊕ (Σ i, Fin (L i + 1))) × (Unit ⊕ (Σ i, Fin (L i + 1))) :=
    Sum.elim (fun x ↦ if x.2 then (Sum.inl (), Sum.inr ⟨x.1, 0⟩) else (Sum.inr ⟨x.1, 0⟩, Sum.inl ()))
      (fun x ↦ if x.2 then (Sum.inr ⟨x.1.1, x.1.2.castSucc⟩, Sum.inr ⟨x.1.1, x.1.2.succ⟩)
        else (Sum.inr ⟨x.1.1, x.1.2.succ⟩, Sum.inr ⟨x.1.1, x.1.2.castSucc⟩))
  refine config_false G hn hMn hinj w ?_ (Sum.inl ()) (by norm_num [w]) e ?_ ?_ ?_
  · rintro (u | ⟨i, k⟩)
    · norm_num [w]
    · simp only [w, Sum.elim_inr]
      have : (k : ℚ) ≤ L i := by exact_mod_cast Nat.lt_succ_iff.1 k.2
      apply div_nonneg <;> linarith
  · rintro ((⟨a, ba⟩ | ⟨⟨a, ka⟩, ba⟩)) ((⟨b, bb⟩ | ⟨⟨b, kb⟩, bb⟩)) hab <;>
      cases ba <;> cases bb <;> simp only [e, Sum.elim_inl, Sum.elim_inr, if_true,
        Bool.false_eq_true, if_false, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, false_and, and_false, sigma_fin_eq_iff, Fin.val_castSucc, Fin.val_succ,
        Fin.val_zero, true_and, and_true] at hab ⊢
    all_goals first
      | exact hab
      | (obtain ⟨⟨rfl, h1⟩, -⟩ := hab; exact Sigma.ext rfl (heq_of_eq (Fin.ext h1)))
      | (obtain ⟨⟨rfl, -⟩, -, h1⟩ := hab; exact Sigma.ext rfl (heq_of_eq (Fin.ext h1)))
      | (obtain ⟨⟨rfl, h1⟩, -, h2⟩ := hab; omega)
      | (obtain ⟨⟨-, h1⟩, -, h2⟩ := hab; omega)
      | skip
  · rintro ((⟨i, b⟩ | ⟨⟨i, k⟩, b⟩)) <;> cases b
    · simpa [e] using (hc i).symm
    · simpa [e] using hc i
    · simpa [e] using (ha i k).symm
    · simpa [e] using ha i k
  · have key : ∀ i : Fin t,
        ∑ k : Fin (L i + 1), 2 * w (Sum.inr ⟨i, k⟩) ^ 2 -
          2 * (w (Sum.inl ()) * w (Sum.inr ⟨i, 0⟩)) -
          ∑ k : Fin (L i), 2 * (w (Sum.inr ⟨i, k.castSucc⟩) * w (Sum.inr ⟨i, k.succ⟩)) =
        -(((L i : ℚ) + 1) / (L i + 2)) := by
      intro i
      have h := arm_contribution (L i)
      rw [← h]
      simp only [w, Sum.elim_inl, Sum.elim_inr, one_mul, Fin.val_zero, Nat.cast_zero, sub_zero,
        Fin.val_castSucc, Fin.val_succ]
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ 2 * (((L i : ℚ) + 1 - k) / (L i + 2)) ^ 2),
        Fin.sum_univ_eq_sum_range (fun k ↦ 2 * ((((L i : ℚ) + 1 - k) / (L i + 2)) *
          (((L i : ℚ) + 1 - (k + 1 : ℕ)) / (L i + 2))))]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast; ring
    have hsum : ∑ x, 2 * w x ^ 2 - ∑ c, w (e c).1 * w (e c).2 =
        2 + ∑ i : Fin t, (∑ k : Fin (L i + 1), 2 * w (Sum.inr ⟨i, k⟩) ^ 2 -
          2 * (w (Sum.inl ()) * w (Sum.inr ⟨i, 0⟩)) -
          ∑ k : Fin (L i), 2 * (w (Sum.inr ⟨i, k.castSucc⟩) * w (Sum.inr ⟨i, k.succ⟩))) := by
      have hw0 : w (Sum.inl ()) = 1 := rfl
      simp only [e, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_sigma,
        Bool.false_eq_true, ↓reduceIte, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib,
        Finset.univ_unique, Finset.sum_singleton, hw0]
      have e1 : ∑ x : Fin t, (1 * w (Sum.inr ⟨x, 0⟩) + w (Sum.inr ⟨x, 0⟩) * 1) =
          ∑ x : Fin t, 2 * (1 * w (Sum.inr ⟨x, 0⟩)) :=
        Finset.sum_congr rfl fun _ _ ↦ by ring
      have e2 : ∑ x : Fin t, ∑ k : Fin (L x),
          (w (Sum.inr ⟨x, k.castSucc⟩) * w (Sum.inr ⟨x, k.succ⟩) +
            w (Sum.inr ⟨x, k.succ⟩) * w (Sum.inr ⟨x, k.castSucc⟩)) =
          ∑ x : Fin t, ∑ k : Fin (L x),
            2 * (w (Sum.inr ⟨x, k.castSucc⟩) * w (Sum.inr ⟨x, k.succ⟩)) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_neg_distrib] at hsum
    linarith


end MultiplicativeBasisDeformations
