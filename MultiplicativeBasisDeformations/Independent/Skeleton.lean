module

public import MultiplicativeBasisDeformations.Statement
public import MultiplicativeBasisDeformations.Foundations.ARQuiver

/-!
# Independent families and the skeletons of the proof library

An independent complete family of indecomposable right modules is an
`IndSkeleton` of the proof library with the same objects. The radical powers,
the spaces of irreducible maps and the Auslander–Reiten quivers agree.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations.Statement

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (S : IndecomposableFamily k A)

/-- The family as a skeleton of the proof library. -/
def toSkeleton : IndSkeleton k A where
  n := S.size
  obj := S.obj
  isFiniteIndecomposable i := ⟨S.finite i, S.indecomposable i⟩
  pairwise _ _ h := S.distinct h
  complete M hM := S.complete M hM.1 hM.2

theorem radPow_eq : ∀ (n : ℕ) (X Y : Ind S), radPow S n X Y = (toSkeleton S).radPow n X Y
  | 0, _, _ => rfl
  | n + 1, X, Y => by
      simp only [radPow, IndSkeleton.radPow, radPow_eq n]
      rfl

theorem finrank_irr_eq (X Y : Ind S) :
    Module.finrank k (Irr S X Y) = Module.finrank k ((toSkeleton S).Irr X Y) := by
  unfold Irr IndSkeleton.Irr IndSkeleton.layer
  rw [radPow_eq, radPow_eq]
  rfl

end MultiplicativeBasisDeformations.Statement
