import MultiplicativeBasisDeformations.Foundations.TreeRepetition
import MultiplicativeBasisDeformations.Foundations.StarModel

/-!
# The star model as an oriented tree

The star model with its two-colouring by depth and the orientation away from
the centre (`periodic-mesh-calculations.tex:179–185`: "For `D` and `E`, root the
tree at the trivalent vertex; for odd `A`, root it at its middle vertex ...
With the orientation away from the root ...").
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

/-- The star model as an oriented tree. -/
def starTree {t : ℕ} (L : Fin t → ℕ) : OrientedTree (StarV L) where
  G := starGraph L
  par x := (starDepth x : ZMod 2)
  par_adj {x y} h := by
    rcases starAdj_depth h with h' | h'
    · rw [h']; push_cast; rfl
    · rw [h']; push_cast
      rw [add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]
  orient := starOrient
  orient_adj h := h.1
  orient_or {x y} h := by
    constructor
    · rintro ⟨-, h1⟩ ⟨-, h2⟩; omega
    · intro hn
      refine ⟨h, ?_⟩
      rcases starAdj_depth h with h' | h'
      · exact h'
      · exact absurd ⟨(starGraph L).symm.symm _ _ h, h'⟩ hn

end MultiplicativeBasisDeformations
