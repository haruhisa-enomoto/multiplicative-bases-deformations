import MultiplicativeBasisDeformations.Foundations.ZDeltaGauge
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Periodic scalar gauges (Lemma A.1)

`lem:periodic-scalar-gauges` (`periodic-mesh-calculations.tex:257–300`):
"The required coefficient ratios prescribe … equations
`μ_{a,j} μ_{b,j-1} = t_{v,j} η_{v,j}`, `μ_{a,j-1} μ_{b,j-1} = t_{u,j} η_{u,j}`.
Dividing the two equations gives a recurrence for `μ_a`. It closes around the
cycle exactly when [a product of the `η`] equals a prescribed number. Choose the
root product freely and assign the child products down the tree. Realize each
product by one factor, setting the other factors to one."

In height coordinates an edge line is indexed by `ℤ` and the equations read
`μ h μ (h+1) η' (h+2) = S h`, where `η'` is the relation scale at the child
endpoint when it sits at height `h + 2`, and the parent's scales are already
absorbed into `S`. A solution periodic of even period `P` exists after choosing
one factor of `η'` per period (`exists_periodic_line`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

variable {k : Type u} [CommRing k]

/-- The recurrence from `μ 0 = 1`. -/
def lineRec (R : ℤ → kˣ) : ℕ → kˣ
  | 0 => 1
  | n + 1 => R n * (lineRec R n)⁻¹

/-- The closing product of the recurrence over `[0, n)`. -/
theorem lineRec_eq (R : ℤ → kˣ) (n : ℕ) :
    lineRec R n = ∏ i ∈ Finset.range n, R i ^ ((-1 : ℤ) ^ (n - 1 - i)) := by
  induction n with
  | zero => simp [lineRec]
  | succ n ih =>
      rw [lineRec, ih, Finset.prod_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, zpow_one]
      rw [← Finset.prod_inv_distrib, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      rw [← zpow_neg, show n - i = (n - 1 - i) + 1 by omega, pow_succ, mul_neg_one]

/-- **A periodic solution of `μ h μ (h + 1) = R h`** for `R` of even period
`P`, when the alternating product over a period is one. -/
theorem exists_periodic_line (P : ℕ) (hP : 0 < P) (hPe : Even P) (R : ℤ → kˣ)
    (hR : ∀ h, R (h + P) = R h) (hprod : ∏ i ∈ Finset.range P, R i ^ ((-1 : ℤ) ^ i) = 1) :
    ∃ μ : ℤ → kˣ, (∀ h, μ (h + P) = μ h) ∧ ∀ h, μ h * μ (h + 1) = R h := by
  have hRmod : ∀ h, R h = R (h % P) := by
    intro h
    have : ∀ n : ℕ, ∀ h, R (h + n * P) = R h := by
      intro n; induction n with
      | zero => simp
      | succ n ih => intro h; rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hR, ih]
    conv_lhs => rw [← Int.emod_add_ediv_mul h P]
    obtain ⟨q, hq⟩ : ∃ q : ℤ, h / P = q := ⟨_, rfl⟩
    rcases le_or_gt 0 q with hq0 | hq0
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
      rw [hq, this]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -q := ⟨(-q).toNat, by omega⟩
      have := this n (h % P + q * P)
      rw [show h % P + q * P + n * P = h % P by rw [hn]; ring] at this
      rw [hq, this]
  -- the closing equation
  have hclose : lineRec R P = 1 := by
    rw [lineRec_eq]
    have e : ∀ i ∈ Finset.range P, R i ^ ((-1 : ℤ) ^ (P - 1 - i)) = (R i ^ ((-1 : ℤ) ^ i))⁻¹ := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hexp : ((-1 : ℤ) ^ (P - 1 - i)) = -((-1 : ℤ) ^ i) := by
        obtain ⟨r, hr⟩ := hPe
        rcases Nat.even_or_odd i with ⟨s, hs⟩ | ⟨s, hs⟩
        · rw [Odd.neg_one_pow ⟨r - s - 1, by omega⟩, Even.neg_one_pow ⟨s, hs⟩]
        · rw [Even.neg_one_pow ⟨r - s - 1, by omega⟩, Odd.neg_one_pow ⟨s, hs⟩, neg_neg]
      rw [hexp, zpow_neg]
    rw [Finset.prod_congr rfl e, Finset.prod_inv_distrib, hprod, inv_one]
  refine ⟨fun h ↦ lineRec R (h % P).toNat, fun h ↦ ?_, fun h ↦ ?_⟩
  · simp
  · show lineRec R (h % P).toNat * lineRec R ((h + 1) % P).toNat = R h
    have hP' : (0 : ℤ) < P := by exact_mod_cast hP
    have h0 : 0 ≤ h % P := Int.emod_nonneg _ hP'.ne'
    have h1 : h % P < P := Int.emod_lt_of_pos _ hP'
    have hstep : (h + 1) % P = if h % P = P - 1 then 0 else h % P + 1 := by
      have e1 : (h + 1) % P = (h % P + 1) % P := by
        conv_lhs => rw [← Int.emod_add_ediv_mul h P]
        rw [show h % P + h / P * P + 1 = h % P + 1 + h / P * P by ring, Int.add_mul_emod_self_right]
      rw [e1]
      split_ifs with hl
      · rw [hl, sub_add_cancel, Int.emod_self]
      · exact Int.emod_eq_of_lt (by omega) (by omega)
    by_cases hlast : h % P = P - 1
    · rw [hstep, if_pos hlast, hRmod h, hlast]
      obtain ⟨n, hn⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
      have e1 : ((P : ℤ) - 1).toNat = n := by omega
      have e2 : ((P : ℤ) - 1) = (n : ℤ) := by omega
      rw [e1, e2, Int.toNat_zero]
      rw [hn, lineRec, mul_inv_eq_one] at hclose
      rw [show lineRec R 0 = 1 from rfl, mul_one]
      exact hclose.symm
    · rw [hstep, if_neg hlast,
        show (h % P + 1).toNat = (h % P).toNat + 1 by omega, lineRec, hRmod h]
      rw [show ((h % P).toNat : ℤ) = h % P by omega, mul_comm (R _), ← mul_assoc,
        mul_inv_cancel, one_mul]

/-- **One relation scale per period closes the line**: for `S` of even period `P`
and a parity class `b` (the heights `h` at which the child endpoint sits at
`h + 2`), there are `P`-periodic `N` (relation scales of the child) and `M`
(arrow scales) with `M h M (h+1) N' h = S h`, where `N' h = N (h + 2)` in the
class `b` and `1` otherwise. -/
theorem exists_periodic_line_vertex (P : ℕ) (hP : 0 < P) (hPe : Even P) (S : ℤ → kˣ)
    (hS : ∀ h, S (h + P) = S h) (b : ZMod 2) :
    ∃ N M : ℤ → kˣ, (∀ h, N (h + P) = N h) ∧ (∀ h, M (h + P) = M h) ∧
      ∀ h, M h * M (h + 1) * (if (h : ZMod 2) = b then N (h + 2) else 1) = S h := by
  classical
  have hP2 : 2 ≤ P := by obtain ⟨r, hr⟩ := hPe; omega
  set n : ℕ := b.val
  have hn : n < 2 := ZMod.val_lt b
  have hnb : ((n : ℤ) : ZMod 2) = b := by simp [n]
  set A := ∏ i ∈ Finset.range P, S i ^ ((-1 : ℤ) ^ i)
  set lam : kˣ := A ^ ((-1 : ℤ) ^ n)
  let N : ℤ → kˣ := fun h ↦ if (h - (n + 2)) % P = 0 then lam else 1
  have hN : ∀ h, N (h + P) = N h := by
    intro h
    simp only [N, show h + P - (n + 2) = (h - (n + 2)) + P * 1 by ring, Int.add_mul_emod_self_left]
  let c : ℤ → kˣ := fun h ↦ if (h : ZMod 2) = b then N (h + 2) else 1
  let R : ℤ → kˣ := fun h ↦ S h * (c h)⁻¹
  have hc : ∀ h, c (h + P) = c h := by
    intro h
    have : ((h + P : ℤ) : ZMod 2) = (h : ZMod 2) := by
      obtain ⟨r, hr⟩ := hPe; push_cast; rw [hr]; push_cast
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
    simp only [c, this, show h + P + 2 = (h + 2) + P by ring, hN]
  have hR : ∀ h, R (h + P) = R h := fun h ↦ by simp only [R, hS, hc]
  have hcprod : ∏ i ∈ Finset.range P, (c i)⁻¹ ^ ((-1 : ℤ) ^ i) = lam⁻¹ ^ ((-1 : ℤ) ^ n) := by
    rw [Finset.prod_eq_single n]
    · have hcn : c n = lam := by
        simp only [c, hnb, if_true, N, show (n : ℤ) + 2 - (n + 2) = 0 by ring, Int.zero_emod]
      rw [hcn]
    · intro i hi hin
      rw [Finset.mem_range] at hi
      have hci : c i = 1 := by
        simp only [c, N]
        split_ifs with hib hN0
        · exfalso
          rw [show (i : ℤ) + 2 - (n + 2) = (i : ℤ) - n by ring] at hN0
          have hP' : (0 : ℤ) < P := by exact_mod_cast hP
          obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hN0
          rcases lt_trichotomy q 0 with hq0 | rfl | hq0
          · have : (P : ℤ) * q ≤ -P := by nlinarith
            omega
          · exact hin (by omega)
          · have : (P : ℤ) ≤ P * q := by nlinarith
            omega
        · rfl
        · rfl
      rw [hci, inv_one, one_zpow]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hprod : ∏ i ∈ Finset.range P, R i ^ ((-1 : ℤ) ^ i) = 1 := by
    simp only [R, mul_zpow, Finset.prod_mul_distrib]
    rw [hcprod]
    change A * lam⁻¹ ^ ((-1 : ℤ) ^ n) = 1
    simp only [lam]
    rw [← zpow_neg_one, ← zpow_mul, ← zpow_mul]
    have e : ((-1 : ℤ) ^ n * (-1 * (-1) ^ n)) = -1 := by
      rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] <;> norm_num
    rw [e, zpow_neg_one, mul_inv_cancel]
  obtain ⟨M, hMP, hM⟩ := exists_periodic_line P hP hPe R hR hprod
  refine ⟨N, M, hN, hMP, fun h ↦ ?_⟩
  rw [hM h]
  simp only [R, c, inv_mul_cancel_right]

end MultiplicativeBasisDeformations
