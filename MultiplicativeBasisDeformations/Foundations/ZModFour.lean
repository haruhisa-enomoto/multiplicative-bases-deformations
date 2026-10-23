module

public import Mathlib

/-!
# The coefficient ring `𝒪 = ℤ/4` (Section 10)

`integral-deformations.tex`: "Let `𝒪 = ℤ/4`. […] the coefficient sequence
`0 → 𝔽₂ → 𝒪 → 𝔽₂ → 0`."

The reduction `red : ℤ/4 → 𝔽₂`, the set-theoretic section `lift`, and the additive embedding
`tw : 𝔽₂ → 2𝒪`, `a ↦ 2ã`. Every statement is a finite check.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

/-- `𝔽₂`. -/
scoped notation "𝔽₂" => ZMod 2

instance : Fact (1 < 4) := ⟨by norm_num⟩

namespace Z4

/-- The reduction `𝒪 → 𝔽₂`. -/
def red : ZMod 4 →+* 𝔽₂ := ZMod.castHom (by norm_num : 2 ∣ 4) 𝔽₂

/-- The section `𝔽₂ → 𝒪` (not additive). -/
def lift (a : 𝔽₂) : ZMod 4 := (a.val : ZMod 4)

@[simp] theorem red_lift (a : 𝔽₂) : red (lift a) = a := by
  revert a; decide

theorem lift_zero : lift 0 = 0 := by decide

theorem four_eq_zero : (2 : ZMod 4) * 2 = 0 := by decide

theorem two_mul_two_mul (a : ZMod 4) : 2 * (2 * a) = 0 := by
  revert a; decide

/-- `2a` depends only on the reduction of `a`. -/
theorem two_mul_eq_of_red {a b : ZMod 4} (h : red a = red b) : 2 * a = 2 * b := by
  revert a b; decide

theorem two_ne_zero : (2 : ZMod 4) ≠ 0 := by decide

/-- The annihilator of `2` is the kernel of the reduction. -/
theorem two_mul_eq_zero_iff (a : ZMod 4) : 2 * a = 0 ↔ red a = 0 := by
  revert a; decide

/-- The kernel of the reduction is `2𝒪`. -/
theorem exists_two_mul_of_red {a : ZMod 4} (h : red a = 0) : ∃ b, a = 2 * b := by
  revert a; decide

/-- Two lifts of the same element differ by an element of `2𝒪`. -/
theorem exists_eq_add_two_mul {a b : ZMod 4} (h : red a = red b) : ∃ c, a = b + 2 * c := by
  revert a b; decide

/-- An element with nonzero reduction is a unit. -/
theorem isUnit_of_red_ne_zero {a : ZMod 4} (h : red a ≠ 0) : IsUnit a := by
  have : ∀ a : ZMod 4, red a ≠ 0 → ∃ b, a * b = 1 := by decide
  obtain ⟨b, hb⟩ := this a h
  exact IsUnit.of_mul_eq_one b hb

/-- The additive embedding `𝔽₂ → 2𝒪`, `a ↦ 2ã`. -/
def tw : 𝔽₂ →+ ZMod 4 where
  toFun a := 2 * lift a
  map_zero' := by decide
  map_add' := by decide

theorem tw_apply (a : 𝔽₂) : tw a = 2 * lift a := rfl

theorem tw_red (a : ZMod 4) : tw (red a) = 2 * a := by
  revert a; decide

theorem tw_injective : Function.Injective tw := by
  intro a b; revert a b; decide

theorem red_surjective : Function.Surjective red := fun a ↦ ⟨lift a, red_lift a⟩

theorem red_two : red 2 = 0 := by decide

end Z4

end MultiplicativeBasisDeformations
