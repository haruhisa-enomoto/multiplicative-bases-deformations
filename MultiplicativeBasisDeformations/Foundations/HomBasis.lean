import MultiplicativeBasisDeformations.Foundations.GradedExt

/-!
# Homogeneous bases of graded vector spaces

A finite-dimensional `ℤ`-graded vector space (`GExt.ZGr`) has a basis of homogeneous vectors
(`exists_homBasis`): it is the internal direct sum of its homogeneous components.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] (g : ZGr (R := k) M)

/-- The homogeneous component of degree `p`, indexed by the support. -/
abbrev homPart (p : g.supp) : Submodule k M := LinearMap.range (g.proj p)

theorem proj_homPart {p : ℤ} {q : g.supp} {x : M} (hx : x ∈ homPart g q) :
    g.proj p x = if (q : ℤ) = p then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [g.proj_proj]

theorem isInternal_homPart [DecidableEq g.supp] : DirectSum.IsInternal (homPart g) := by
  classical
  let inv : M →ₗ[k] DirectSum g.supp (fun p ↦ homPart g p) :=
    ∑ p : g.supp, (DirectSum.lof k g.supp (fun p ↦ homPart g p) p) ∘ₗ
      (g.proj p).rangeRestrict
  have hrr : ∀ (p : g.supp) (x : M), ((g.proj p).rangeRestrict x : M) = g.proj p x :=
    fun _ _ ↦ rfl
  have hr : ∀ x, DirectSum.coeLinearMap (homPart g) (inv x) = x := by
    intro x
    simp only [inv, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
      DirectSum.coeLinearMap_lof, hrr]
    conv_rhs => rw [g.sum x]
    rw [← Finset.sum_attach g.supp]
    rfl
  have hl : ∀ f, inv (DirectSum.coeLinearMap (homPart g) f) = f := by
    intro f
    induction f using DirectSum.induction_on with
    | zero => simp
    | of q y =>
        rw [DirectSum.coeLinearMap_of]
        simp only [inv, LinearMap.sum_apply, LinearMap.comp_apply]
        rw [Finset.sum_eq_single q]
        · rw [DirectSum.lof_eq_of]
          congr 1
          apply Subtype.ext
          rw [hrr, proj_homPart g y.2, if_pos rfl]
        · intro p _ hp
          have : (g.proj p).rangeRestrict y = 0 := by
            apply Subtype.ext
            rw [hrr, proj_homPart g y.2, if_neg (fun h ↦ hp (Subtype.ext h).symm)]
            rfl
          rw [this, map_zero]
        · intro h; exact absurd (Finset.mem_univ q) h
    | add f f' hf hf' => rw [map_add, map_add, hf, hf']
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

variable [FiniteDimensional k M]

/-- **Homogeneous bases.** -/
theorem exists_homBasis : ∃ (n : ℕ) (β : Module.Basis (Fin n) k M) (dβ : Fin n → ℤ),
    ∀ i, g.IsHom (dβ i) (β i) := by
  classical
  set B := (isInternal_homPart g).collectedBasis fun p ↦ Module.finBasis k (homPart g p)
  refine ⟨_, B.reindex (Fintype.equivFin _), fun i ↦ ((Fintype.equivFin _).symm i).1, fun i ↦ ?_⟩
  rw [Module.Basis.reindex_apply]
  have hm := (isInternal_homPart g).collectedBasis_mem
    (fun p ↦ Module.finBasis k (homPart g p)) ((Fintype.equivFin _).symm i)
  obtain ⟨y, hy⟩ := hm
  change g.proj _ _ = _
  rw [← hy, g.proj_proj, if_pos rfl]

end GExt

end MultiplicativeBasisDeformations
