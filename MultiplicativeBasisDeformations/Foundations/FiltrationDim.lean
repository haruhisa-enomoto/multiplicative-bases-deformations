import MultiplicativeBasisDeformations.Foundations.PositiveDeformation

/-!
# The dimension of a positive filtered deformation

A positive filtered deformation `B` of `Λ` (Definition 6.2) has `dim B = dim Λ`: each layer
`F^d/F^{d+1}` is identified with `Λ_d` by the leading-term map.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}

namespace LenGrading

/-- **A graded algebra is the sum of its components.** -/
theorem finrank_eq_sum [FiniteDimensional k Λ] (G : LenGrading k Λ) :
    Module.finrank k Λ = ∑ d : Fin G.N, Module.finrank k (LinearMap.range (G.proj d)) := by
  classical
  let e : Λ ≃ₗ[k] ((d : Fin G.N) → LinearMap.range (G.proj d)) :=
    { toFun := fun x d ↦ ⟨G.proj d x, LinearMap.mem_range_self _ _⟩
      map_add' := fun x y ↦ funext fun d ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun c x ↦ funext fun d ↦ Subtype.ext (map_smul _ _ _)
      invFun := fun y ↦ ∑ d, (y d : Λ)
      left_inv := fun x ↦ by
        simp only
        rw [Fin.sum_univ_eq_sum_range (fun d ↦ G.proj d x)]
        exact (G.sum x).symm
      right_inv := fun y ↦ funext fun d ↦ Subtype.ext (by
        simp only
        rw [map_sum, Finset.sum_eq_single d]
        · obtain ⟨z, hz⟩ := (y d).2
          rw [← hz, G.proj_proj, if_pos rfl]
        · intro e _ he
          obtain ⟨z, hz⟩ := (y e).2
          rw [← hz, G.proj_proj, if_neg (fun h ↦ he (Fin.ext h))]
        · simp) }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

end LenGrading

namespace PosFiltration

variable {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)

theorem finrank_step [FiniteDimensional k B] (d : ℕ) :
    Module.finrank k (P.F d) =
      Module.finrank k (P.F (d + 1)) + Module.finrank k (LinearMap.range (G.proj d)) := by
  set f : P.F d →ₗ[k] Λ := P.σ d ∘ₗ (P.F d).subtype
  have hr : LinearMap.range f = LinearMap.range (G.proj d) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨P.σ d a, P.σ_hom d a⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨a, ha, hax⟩ := P.σ_surj d _ (G.isHom_proj d y)
      exact ⟨⟨a, ha⟩, hax⟩
  have hk : LinearMap.ker f = (P.F (d + 1)).comap (P.F d).subtype := by
    ext ⟨a, ha⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    exact P.σ_ker d a ha
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe (P.F_succ_le d)).finrank_eq] at h
  omega

theorem finrank_F_zero [FiniteDimensional k B] (n : ℕ) :
    Module.finrank k (P.F 0) =
      Module.finrank k (P.F n) + ∑ d ∈ Finset.range n, Module.finrank k (LinearMap.range (G.proj d)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, P.finrank_step n, Finset.sum_range_succ]; ring

include P in
/-- **A positive filtered deformation has the dimension of `Λ`.** -/
theorem finrank_eq [FiniteDimensional k B] [FiniteDimensional k Λ] :
    Module.finrank k B = Module.finrank k Λ := by
  classical
  have h0 := P.finrank_F_zero (max P.M G.N)
  have hM : P.F (max P.M G.N) = ⊥ := by
    have : ∀ n, P.F (P.M + n) = ⊥ := by
      intro n
      induction n with
      | zero => exact P.F_M
      | succ n ih => exact le_bot_iff.1 (ih ▸ P.F_succ_le (P.M + n))
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (le_max_left P.M G.N)
    rw [hn, this]
  rw [hM, finrank_bot, zero_add, P.F_zero, finrank_top] at h0
  rw [h0, G.finrank_eq_sum, Fin.sum_univ_eq_sum_range (fun d ↦ Module.finrank k
    (LinearMap.range (G.proj d)))]
  refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun d _ hd ↦ ?_).symm
  rw [Finset.mem_range, not_lt] at hd
  rw [G.proj_ge d hd, LinearMap.range_zero, finrank_bot]

end PosFiltration

end MultiplicativeBasisDeformations
