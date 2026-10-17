import MultiplicativeBasisDeformations.Foundations.NormedBasis

/-!
# Sanity checks of the definitions

Small proved examples showing that the definitions are satisfiable in the
expected trivial cases.
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

universe u

variable (k : Type u) [Field k]

/-- The field `k` has a normed multiplicative basis, namely `{1}`. -/
theorem field_hasNormedMultiplicativeBasis : HasNormedMultiplicativeBasis k k := by
  refine ⟨PUnit.{u + 1}, Module.Basis.singleton PUnit.{u + 1} k, ?_⟩
  have hb : ∀ i, Module.Basis.singleton PUnit.{u + 1} k i = 1 := fun _ ↦ by simp
  have hrad : algebraRadical k k = ⊥ := by
    simp [algebraRadical, IsSemisimpleRing.jacobson_eq_bot]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact Or.inr ⟨i, by simp [hb]⟩
  · refine ⟨{PUnit.unit}, ?_, ?_⟩
    · refine ⟨⟨fun _ ↦ by simp [IsIdempotentElem], ?_⟩, ?_⟩
      · intro i j hij
        exact absurd (Subsingleton.elim i j) hij
      · simp [hb]
    · intro i _
      refine ⟨by simp [IsIdempotentElem], by simp [hb], ?_⟩
      intro f hf _ _
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp hf with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [hb, h])
  · intro n hn
    have hpow : algebraRadicalPow k k n = ⊥ := by
      rw [algebraRadicalPow, hrad, Submodule.bot_pow (by omega)]
    rw [hpow]
    simp [hpow]

end MultiplicativeBasisDeformations
