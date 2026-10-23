module

public import MultiplicativeBasisDeformations.Foundations.MeshCategory

/-!
# Stable translation quivers

For a stable translation quiver (every vertex nonprojective and noninjective,
`TranslationQuiver.IsStable`) the translation is a permutation `τ` of the
vertices. The mate bijections give `y → x` iff `τ x → y`, and `τ` preserves
arrows. These facts are used throughout the proof of Proposition 4.1
(`periodic-mesh-calculations.tex`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}

theorem IsStable.mem_nonprojective (hQ : Q.IsStable) (v : V) : v ∈ Q.nonprojective := by rw [hQ.1]; trivial

theorem IsStable.mem_noninjective (hQ : Q.IsStable) (v : V) : v ∈ Q.noninjective := by rw [hQ.2]; trivial

/-- The translation of a stable translation quiver, as a permutation. -/
def IsStable.tauE (hQ : Q.IsStable) : Equiv.Perm V where
  toFun v := (Q.tau ⟨v, hQ.mem_nonprojective v⟩).1
  invFun v := (Q.tau.symm ⟨v, hQ.mem_noninjective v⟩).1
  left_inv v := by simp
  right_inv v := by simp

theorem IsStable.tauE_apply (hQ : Q.IsStable) (v : V) : hQ.tauE v = (Q.tau ⟨v, hQ.mem_nonprojective v⟩).1 := rfl

/-- Arrows into `x` correspond to arrows out of `τ x`. -/
theorem IsStable.nonempty_hom_iff (hQ : Q.IsStable) (x y : V) :
    Nonempty (y ⟶ x) ↔ Nonempty (hQ.tauE x ⟶ y) :=
  ⟨fun ⟨a⟩ ↦ ⟨Q.mate ⟨x, hQ.mem_nonprojective x⟩ y a⟩,
    fun ⟨b⟩ ↦ ⟨(Q.mate ⟨x, hQ.mem_nonprojective x⟩ y).symm b⟩⟩

/-- `τ` preserves arrows. -/
theorem IsStable.nonempty_hom_tau_iff (hQ : Q.IsStable) (u v : V) :
    Nonempty (hQ.tauE u ⟶ hQ.tauE v) ↔ Nonempty (u ⟶ v) := by
  rw [hQ.nonempty_hom_iff v u, hQ.nonempty_hom_iff u (hQ.tauE v)]

theorem IsStable.nonempty_hom_zpow_iff (hQ : Q.IsStable) (n : ℤ) (u v : V) :
    Nonempty ((hQ.tauE ^ n) u ⟶ (hQ.tauE ^ n) v) ↔ Nonempty (u ⟶ v) := by
  induction n using Int.induction_on generalizing u v with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hQ.nonempty_hom_tau_iff]
  | pred n ih =>
      have h1 : ∀ x, hQ.tauE (hQ.tauE⁻¹ x) = x := fun x ↦ by simp
      rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
        ← hQ.nonempty_hom_tau_iff, h1, h1]

end TranslationQuiver

end MultiplicativeBasisDeformations
