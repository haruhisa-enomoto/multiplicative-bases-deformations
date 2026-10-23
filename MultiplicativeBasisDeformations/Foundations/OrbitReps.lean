module

public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Representatives of the orbits of a permutation

For the periodic gauge (Lemma A.1) the arms of a star are permuted by the twist
`θ`; we solve the gauge equations on one arm of each orbit and transport them.
For a permutation `θ` of a finite linearly ordered type we fix the least element
`rep i` of the orbit of `i`, an exponent `ord i` with `θ^{ord i} (rep i) = i`, and
the minimal period `per i` of `rep i`; exponents reaching the same point differ
by a multiple of the period.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

namespace OrbitReps

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] (θ : Equiv.Perm α)

/-- The least element of the orbit. -/
def rep (i : α) : α := (Finset.univ.filter (θ.SameCycle i)).min'
  ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl θ i⟩⟩

theorem sameCycle_rep (i : α) : θ.SameCycle i (rep θ i) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ _)).2

theorem rep_eq_of_sameCycle {i i' : α} (h : θ.SameCycle i i') : rep θ i = rep θ i' := by
  unfold rep
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hj ↦ h.symm.trans hj, fun hj ↦ h.trans hj⟩

theorem rep_apply (i : α) : rep θ (θ i) = rep θ i :=
  (rep_eq_of_sameCycle θ (Equiv.Perm.SameCycle.refl θ i |>.apply_right)).symm

theorem exists_ord (i : α) : ∃ n : ℕ, (θ ^ n) (rep θ i) = i :=
  (sameCycle_rep θ i).symm.exists_nat_pow_eq

/-- An exponent reaching `i` from its representative. -/
noncomputable def ord (i : α) : ℕ := Nat.find (exists_ord θ i)

theorem pow_ord (i : α) : (θ ^ ord θ i) (rep θ i) = i := Nat.find_spec (exists_ord θ i)

/-- The period of the orbit. -/
noncomputable def per (i : α) : ℕ := Function.minimalPeriod θ (rep θ i)

theorem per_pos (i : α) : 0 < per θ i := by
  apply Function.minimalPeriod_pos_of_mem_periodicPts
  refine ⟨orderOf θ, orderOf_pos θ, ?_⟩
  change θ^[orderOf θ] (rep θ i) = rep θ i
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl

theorem pow_per (i : α) : (θ ^ per θ i) (rep θ i) = rep θ i := by
  rw [Equiv.Perm.coe_pow]; exact Function.iterate_minimalPeriod

theorem per_apply (i : α) : per θ (θ i) = per θ i := by
  unfold per; rw [rep_apply]

/-- Exponents reaching the same point differ by a multiple of the period. -/
theorem per_dvd_sub {i : α} {a b : ℕ} (h : (θ ^ a) (rep θ i) = (θ ^ b) (rep θ i)) :
    (per θ i : ℤ) ∣ (a : ℤ) - b := by
  wlog hab : b ≤ a generalizing a b
  · have := this h.symm (by omega)
    rw [show (a : ℤ) - b = -((b : ℤ) - a) by ring]
    exact (dvd_neg).2 this
  have h' : (θ ^ (a - b)) (rep θ i) = rep θ i := by
    have := congrArg (⇑((θ ^ b)⁻¹)) h
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
      at this
    have e : (θ ^ b)⁻¹ * θ ^ a = θ ^ (a - b) := by
      rw [show θ ^ a = θ ^ b * θ ^ (a - b) by rw [← pow_add, Nat.add_sub_cancel' hab],
        inv_mul_cancel_left]
    rwa [e] at this
  have hp : Function.IsPeriodicPt θ (a - b) (rep θ i) := by
    change θ^[a - b] (rep θ i) = rep θ i
    rw [← Equiv.Perm.coe_pow]; exact h'
  obtain ⟨q, hq⟩ := Function.isPeriodicPt_iff_minimalPeriod_dvd.1 hp
  exact ⟨q, by unfold per; push_cast [Nat.cast_sub hab]; rw [← Nat.cast_sub hab, hq]; push_cast; ring⟩

/-- The exponent of `θ i` is that of `i` plus one, up to the period. -/
theorem ord_apply (i : α) : (per θ i : ℤ) ∣ ((ord θ i : ℤ) + 1) - ord θ (θ i) := by
  apply per_dvd_sub
  rw [pow_succ', Equiv.Perm.mul_apply, pow_ord, ← rep_apply θ i, pow_ord]

theorem ord_rep (i : α) : ord θ (rep θ i) = 0 := by
  have h : (θ ^ 0) (rep θ (rep θ i)) = rep θ i := by
    rw [pow_zero, Equiv.Perm.one_apply, rep_eq_of_sameCycle θ (sameCycle_rep θ i).symm]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (exists_ord θ (rep θ i)) h)

theorem rep_rep (i : α) : rep θ (rep θ i) = rep θ i :=
  (rep_eq_of_sameCycle θ (sameCycle_rep θ i)).symm

end OrbitReps

end MultiplicativeBasisDeformations
