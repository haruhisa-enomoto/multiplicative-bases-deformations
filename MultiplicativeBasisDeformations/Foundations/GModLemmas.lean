import MultiplicativeBasisDeformations.Foundations.GradedExt

/-!
# Small lemmas on graded modules
-/

set_option autoImplicit false

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M : Type*} [AddCommGroup M] [Module R M]

theorem GMod.act_sum (MM : GMod GΛ M) {κ : Type*} (s : Finset κ) (f : κ → M) (b : Λ) :
    MM.act (∑ i ∈ s, f i) b = ∑ i ∈ s, MM.act (f i) b := by
  rw [map_sum, LinearMap.sum_apply]

theorem GMod.act_smul (MM : GMod GΛ M) (t : R) (m : M) (b : Λ) :
    MM.act (t • m) b = t • MM.act m b := by
  rw [map_smul, LinearMap.smul_apply]

end GExt

end MultiplicativeBasisDeformations
