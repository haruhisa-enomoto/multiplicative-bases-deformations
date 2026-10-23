module

public import MultiplicativeBasisDeformations.Statement
public import MultiplicativeBasisDeformations.Statements.MainTheorems

/-!
# Theorem A in the independent vocabulary

The Mathlib-only notions of `Statement.lean` agree with those of the proof
library, so `theoremA` gives `Statement.TheoremA`.
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations.Statement

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- An independent complete family gives representation-finiteness in the
sense of the proof library. -/
theorem isRepresentationFinite_of (h : IsRepresentationFinite k A) :
    MultiplicativeBasisDeformations.IsRepresentationFinite k A := by
  obtain ⟨S⟩ := h
  exact ⟨S.size, S.obj, fun i ↦ ⟨S.finite i, S.indecomposable i⟩,
    fun M hM ↦ S.complete M hM.1 hM.2⟩

/-- A normed multiplicative basis of the proof library is one in the
independent sense. -/
theorem hasNormedMultiplicativeBasis_of
    (h : MultiplicativeBasisDeformations.HasNormedMultiplicativeBasis k A) :
    HasNormedMultiplicativeBasis k A := by
  obtain ⟨ι, b, hb⟩ := h
  exact ⟨ι, b, ⟨hb.multiplicative, hb.idempotents, hb.radicalPow⟩⟩

/-- **Theorem A** in the independent vocabulary. -/
theorem theoremA [IsAlgClosed k] [FiniteDimensional k A] : TheoremA k A := fun h ↦
  hasNormedMultiplicativeBasis_of k A
    (MultiplicativeBasisDeformations.theoremA k A (isRepresentationFinite_of k A h))

end MultiplicativeBasisDeformations.Statement
