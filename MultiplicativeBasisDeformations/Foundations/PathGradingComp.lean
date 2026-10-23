module

public import MultiplicativeBasisDeformations.Foundations.PathGrading

/-!
# Homogeneous components of composites in `kQ`

Composition with a homogeneous morphism of degree `m` shifts homogeneous
components by `m`. Together with the finiteness of the decomposition into
components, this reduces statements about the mesh sequences of `C(Q, c)` to
homogeneous families (`graded-category.tex`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.LinearPaths

universe u v w

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V]

theorem proj_comp_of_mem {m d : ℕ} {x y z : V} (F : obj (k := k) x ⟶ obj (k := k) y)
    {G : obj (k := k) y ⟶ obj (k := k) z} (hG : G ∈ degreePart (k := k) m y z) :
    proj (k := k) (d + m) x z (F ≫ G) = proj d x y F ≫ G := by
  induction F using induction_on with
  | h0 => simp
  | hadd F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Preadditive.add_comp]
  | hsingle p c =>
      rw [Linear.smul_comp, map_smul, map_smul, proj_path, Linear.smul_comp,
        proj_of_mem (comp_mem_degreePart (path_mem_degreePart p) hG)]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · simp

theorem proj_comp_of_mem_lt {m e : ℕ} {x y z : V} (F : obj (k := k) x ⟶ obj (k := k) y)
    {G : obj (k := k) y ⟶ obj (k := k) z} (hG : G ∈ degreePart (k := k) m y z) (he : e < m) :
    proj (k := k) e x z (F ≫ G) = 0 := by
  induction F using induction_on with
  | h0 => simp
  | hadd F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, add_zero]
  | hsingle p c =>
      rw [Linear.smul_comp, map_smul,
        proj_of_mem (comp_mem_degreePart (path_mem_degreePart p) hG), if_neg (by omega),
        smul_zero]

theorem proj_of_mem_comp {m d : ℕ} {x y z : V} {G : obj (k := k) x ⟶ obj (k := k) y}
    (hG : G ∈ degreePart (k := k) m x y) (F : obj (k := k) y ⟶ obj (k := k) z) :
    proj (k := k) (m + d) x z (G ≫ F) = G ≫ proj d y z F := by
  induction F using induction_on with
  | h0 => simp
  | hadd F₁ F₂ h₁ h₂ => rw [Preadditive.comp_add, map_add, h₁, h₂, map_add, Preadditive.comp_add]
  | hsingle p c =>
      rw [Linear.comp_smul, map_smul, map_smul, proj_path, Linear.comp_smul,
        proj_of_mem (comp_mem_degreePart hG (path_mem_degreePart p))]
      split_ifs with h1 h2 h2
      · rfl
      · omega
      · omega
      · simp

theorem proj_of_mem_comp_lt {m e : ℕ} {x y z : V} {G : obj (k := k) x ⟶ obj (k := k) y}
    (hG : G ∈ degreePart (k := k) m x y) (F : obj (k := k) y ⟶ obj (k := k) z) (he : e < m) :
    proj (k := k) e x z (G ≫ F) = 0 := by
  induction F using induction_on with
  | h0 => simp
  | hadd F₁ F₂ h₁ h₂ => rw [Preadditive.comp_add, map_add, h₁, h₂, add_zero]
  | hsingle p c =>
      rw [Linear.comp_smul, map_smul,
        proj_of_mem (comp_mem_degreePart hG (path_mem_degreePart p)), if_neg (by omega),
        smul_zero]

/-- The decomposition into homogeneous components may use any long enough
range of degrees. -/
theorem eq_sum_proj_of_le {x y : V} (f : obj (k := k) x ⟶ obj (k := k) y) :
    ∃ N : ℕ, ∀ M, N ≤ M → f = ∑ d ∈ Finset.range M, proj (k := k) d x y f := by
  obtain ⟨N, hN⟩ := eq_sum_proj (k := k) f
  refine ⟨N, fun M hM ↦ ?_⟩
  have hzero : ∀ d, N ≤ d → proj (k := k) d x y f = 0 := by
    intro d hd
    rw [hN, map_sum]
    refine Finset.sum_eq_zero fun e he ↦ ?_
    rw [proj_of_mem (proj_mem (d := e) f), if_neg]
    rw [Finset.mem_range] at he
    omega
  rw [← Finset.sum_range_add_sum_Ico _ hM, Finset.sum_eq_zero (s := Finset.Ico N M)
    (fun d hd ↦ hzero d (Finset.mem_Ico.1 hd).1), add_zero]
  exact hN

/-- A uniform range of degrees for a finite family. -/
theorem exists_sum_proj_family {α : Type*} [Fintype α] {x y : α → V}
    (f : ∀ a, obj (k := k) (x a) ⟶ obj (k := k) (y a)) :
    ∃ N : ℕ, ∀ a, f a = ∑ d ∈ Finset.range N, proj (k := k) d (x a) (y a) (f a) := by
  classical
  choose N hN using fun a ↦ eq_sum_proj_of_le (k := k) (f a)
  exact ⟨Finset.univ.sup N, fun a ↦ hN a _ (Finset.le_sup (Finset.mem_univ a))⟩

end MultiplicativeBasisDeformations.LinearPaths
