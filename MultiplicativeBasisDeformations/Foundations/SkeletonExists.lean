module

public import MultiplicativeBasisDeformations.Foundations.RightModules

/-!
# Indecomposable skeletons exist

A representation-finite algebra has a complete irredundant list of its
finite-dimensional indecomposable modules: keep, in each isomorphism class of a
complete list, the representative of least index.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

/-- **A representation-finite algebra has an indecomposable skeleton.** -/
theorem exists_indSkeleton (hA : IsRepresentationFinite k A) : Nonempty (IndSkeleton k A) := by
  classical
  obtain ⟨n, X, hX, hcov⟩ := hA
  let cls : Fin n → Finset (Fin n) := fun i ↦ Finset.univ.filter fun j ↦ Nonempty (X j ≅ X i)
  have hne : ∀ i, (cls i).Nonempty := fun i ↦ ⟨i, by simp [cls]; exact ⟨Iso.refl _⟩⟩
  let r : Fin n → Fin n := fun i ↦ (cls i).min' (hne i)
  have hr : ∀ i, Nonempty (X (r i) ≅ X i) := fun i ↦ by
    have := (cls i).min'_mem (hne i)
    simpa [cls] using this
  have hcls : ∀ i j, Nonempty (X i ≅ X j) → cls i = cls j := by
    rintro i j ⟨φ⟩
    ext l
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨ψ⟩ ↦ ⟨ψ ≪≫ φ⟩, fun ⟨ψ⟩ ↦ ⟨ψ ≪≫ φ.symm⟩⟩
  have hrr : ∀ i j, Nonempty (X i ≅ X j) → r i = r j := fun i j h ↦ by
    simp only [r, hcls i j h]
  have hrr' : ∀ i, r (r i) = r i := fun i ↦ hrr _ _ (hr i)
  let T : Finset (Fin n) := Finset.univ.image r
  let eT : Fin T.card ≃ T := T.equivFin.symm
  refine ⟨{ n := T.card
            obj := fun t ↦ X (eT t).1
            isFiniteIndecomposable := fun t ↦ hX _
            pairwise := fun t t' ⟨φ⟩ ↦ ?_
            complete := fun M hM ↦ ?_ }⟩
  · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (eT t).2
    obtain ⟨a', -, ha'⟩ := Finset.mem_image.1 (eT t').2
    apply eT.injective
    apply Subtype.ext
    rw [← ha, ← ha'] at φ ⊢
    rw [← hrr' a, ← hrr' a']
    exact hrr _ _ ⟨φ⟩
  · obtain ⟨i, ⟨φ⟩⟩ := hcov M hM
    refine ⟨eT.symm ⟨r i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩, ⟨φ ≪≫ ?_⟩⟩
    rw [Equiv.apply_symm_apply]
    exact (hr i).some.symm

end MultiplicativeBasisDeformations
