module

public import MultiplicativeBasisDeformations.Independent.TheoremA
public import MultiplicativeBasisDeformations.Independent.Translate
public import MultiplicativeBasisDeformations.Independent.StandardComparison

/-!
# Theorem B in the independent vocabulary

The independent family is a skeleton of the proof library; its standardness
there (`theoremB`) transfers to the independent mesh category, because the
independent translate is the translation of `Γ_A` (`translateCompatible`) and
the coefficients of the mesh relations normalize to one (Lemma 4.4).
-/

@[expose] public section

set_option autoImplicit false

namespace MultiplicativeBasisDeformations.Statement

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- **Theorem B** in the independent vocabulary. -/
theorem theoremB [IsAlgClosed k] [FiniteDimensional k A] : TheoremB k A := by
  intro hbasic hrep hchar S
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  have hstd := MultiplicativeBasisDeformations.theoremB k A hbasic
    (isRepresentationFinite_of k A hrep) hchar
  exact isStandardFor_of (translateCompatible S) (hstd (toSkeleton S))

end MultiplicativeBasisDeformations.Statement
