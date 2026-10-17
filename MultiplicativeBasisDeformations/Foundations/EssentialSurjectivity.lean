import MultiplicativeBasisDeformations.Foundations.GlobalDimension

/-!
# Evaluation at the projective labels: essential surjectivity

Lemma 2.9 (second part, `graded-category.tex:470–480`): "Given
`0 → X → I⁰ → I¹` over `Λ_e`, lift its injectives to projectives `Q⁰, Q¹` and
their map to `f : Q⁰ → Q¹`. Its kernel is a second syzygy and hence projective,
since `gl.dim Λ ≤ 2`. Exactness of `M ↦ Me` gives `X ≅ (ker f)e`."
Proposition 2.10 (`graded-category.tex:524–545`): the injective `A₀`-modules
`D(A₀ e_x)` are the evaluations of the injective labels `I_x`, by the socle
and a dimension count.

Here: the extension `ext : A₀ → Λ` by zero; the `e`-part of kernels; the dual
representables `J_p` and injective copresentations; `J_p ≅ ev(I_p)` from the
Hom-dimensions; essential surjectivity.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}
  {L : LocalFamily (k := k) F} (D : MeshData F L)

namespace MeshData

/-- Extension by zero `A₀ → Λ`. -/
def extA (a : Alg D.F0) : Alg F := fun y z ↦
  if h : D.proj y ∧ D.proj z then a ⟨y, h.1⟩ ⟨z, h.2⟩ else 0

theorem extA_mul (a b : Alg D.F0) : D.extA (a * b) = D.extA a * D.extA b := by
  ext y z
  simp only [extA, mul_apply]
  split_ifs with h
  · refine Eq.trans ?_ (D.sum_proj (fun t ↦ (if h : D.proj y ∧ D.proj t then
        a ⟨y, h.1⟩ ⟨t, h.2⟩ else (0 : F y ⟶ F t)) ≫
        (if h : D.proj t ∧ D.proj z then b ⟨t, h.1⟩ ⟨z, h.2⟩ else (0 : F t ⟶ F z)))
        (fun t ht ↦ by rw [dif_neg (fun h' ↦ ht h'.2), Limits.zero_comp])).symm
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [dif_pos ⟨h.1, t.2⟩, dif_pos ⟨t.2, h.2⟩]
  · symm
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    by_cases h1 : D.proj y ∧ D.proj t
    · have h2 : ¬ (D.proj t ∧ D.proj z) := fun h2 ↦ h ⟨h1.1, h2.2⟩
      rw [dif_neg h2, Limits.comp_zero]
    · rw [dif_neg h1, Limits.zero_comp]

theorem extA_add (a b : Alg D.F0) : D.extA (a + b) = D.extA a + D.extA b := by
  ext y z; simp only [extA, add_apply]; split_ifs <;> simp

theorem extA_rows (a : Alg D.F0) : ∀ y z, ¬ D.proj y → D.extA a y z = 0 := fun y z hy ↦ by
  simp only [extA]; rw [dif_neg (fun h ↦ hy h.1)]

theorem resAlg_extA (a : Alg D.F0) : D.resAlg (D.extA a) = a := by
  ext p q; simp [resAlg, extA, p.2, q.2]

theorem extA_smul_extZ {X : 𝒞} (a : Alg D.F0) (m : Rep D.F0 X) :
    D.extA a • D.extZ X m = D.extZ X (a • m) := by
  rw [D.smul_extZ _ (D.extA_rows a), resAlg_extA]

theorem restr_extA_smul {X : 𝒞} (a : Alg D.F0) (m : Rep F X) :
    D.restr X (D.extA a • m) = a • D.restr X m := by
  ext p
  rw [restr_apply, Rep.smul_apply, Rep.smul_apply,
    D.sum_proj (fun y ↦ D.extA a p.1 y ≫ m y) (fun y hy ↦ by
      simp only [extA]; rw [dif_neg (fun h ↦ hy h.2), Limits.zero_comp])]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp [extA, p.2, q.2]

theorem extA_one_smul {X : 𝒞} (m : Rep F X) : D.extA 1 • m = D.extZ X (D.restr X m) := by
  ext y
  rw [Rep.smul_apply, extZ_apply]
  split_ifs with hy
  · rw [Finset.sum_eq_single y]
    · simp [extA, hy, one_apply]
    · intro t _ ht
      simp only [extA, one_apply]
      split_ifs with h
      · rw [idTo_ne (fun e ↦ ht (congrArg Subtype.val e).symm), Limits.zero_comp]
      · rw [Limits.zero_comp]
    · simp
  · exact Finset.sum_eq_zero fun t _ ↦ by rw [D.extA_rows 1 y t hy, Limits.zero_comp]

section Families

variable {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- Restriction to the projective labels, componentwise. -/
def restrs (Z : κ → ι) : RZ F Z →ₗ[k] D.EZ Z :=
  LinearMap.pi fun j ↦ (D.restr (F (Z j))).comp (LinearMap.proj j)

theorem restrs_extZs (Z : κ → ι) (m : D.EZ Z) : D.restrs Z (D.extZs Z m) = m := by
  funext j; exact D.restr_extZ _ (m j)

theorem extA_one_smul_RZ (Z : κ → ι) (m : RZ F Z) :
    D.extA 1 • m = D.extZs Z (D.restrs Z m) := by
  funext j; exact D.extA_one_smul (m j)

theorem restrs_smul (Z : κ → ι) (a : Alg D.F0) (m : RZ F Z) :
    D.restrs Z (D.extA a • m) = a • D.restrs Z m := by
  funext j; exact D.restr_extA_smul a (m j)

theorem extZs_smul (Z : κ → ι) (a : Alg D.F0) (m : D.EZ Z) :
    D.extZs Z (a • m) = D.extA a • D.extZs Z m := by
  funext j; exact (D.extA_smul_extZ a (m j)).symm

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

/-- **The kernel of an evaluated matrix is the evaluation of a family.** -/
theorem ker_evMap_equiv {Z : κ → ι} {Z' : κ' → ι} (f : Mat F Z Z') :
    ∃ (μ : Type) (_ : Fintype μ) (_ : DecidableEq μ) (W : μ → ι),
      Nonempty (LinearMap.ker (D.evMap f) ≃ₗ[Alg D.F0] D.EZ W) := by
  obtain ⟨μ, _, _, W, ⟨ψ⟩⟩ := D.ker_bigMap_equiv f
  have hmem : ∀ m ∈ LinearMap.ker (D.evMap f), D.extZs Z m ∈ LinearMap.ker (bigMap (F := F) f) :=
    fun m hm ↦ by
      rw [LinearMap.mem_ker] at hm ⊢
      rw [bigMap_extZs, hm, map_zero]
  have hψe : ∀ y : LinearMap.ker (bigMap (F := F) f), D.extA 1 • ψ y = ψ (D.extA 1 • y) :=
    fun y ↦ (map_smul ψ _ _).symm
  have hepart : ∀ n : D.EZ W, D.extZs Z (D.restrs Z (ψ.symm (D.extZs W n) : RZ F Z)) =
      (ψ.symm (D.extZs W n) : RZ F Z) := by
    intro n
    rw [← extA_one_smul_RZ, ← Submodule.coe_smul, ← map_smul, ← extZs_smul, one_smul]
  refine ⟨μ, inferInstance, inferInstance, W, ⟨?_⟩⟩
  exact
    { toFun := fun m ↦ D.restrs W (ψ ⟨D.extZs Z m, hmem m m.2⟩)
      map_add' := fun m n ↦ by
        rw [← map_add]; congr 1; rw [← map_add]; congr 1
        apply Subtype.ext; simp
      map_smul' := fun a m ↦ by
        simp only [RingHom.id_apply]
        rw [← restrs_smul, ← map_smul]
        congr 2
        apply Subtype.ext
        simp [extZs_smul]
      invFun := fun n ↦ ⟨D.restrs Z (ψ.symm (D.extZs W n)), by
        rw [LinearMap.mem_ker]
        apply D.extZs_injective Z'
        rw [← bigMap_extZs, hepart, map_zero]
        exact (ψ.symm (D.extZs W n)).2⟩
      left_inv := fun m ↦ by
        apply Subtype.ext
        simp only
        have h1 : D.extZs W (D.restrs W (ψ ⟨D.extZs Z m, hmem m m.2⟩)) =
            ψ ⟨D.extZs Z m, hmem m m.2⟩ := by
          rw [← extA_one_smul_RZ, hψe]
          congr 1
          apply Subtype.ext
          simp [← extZs_smul]
        rw [h1, LinearEquiv.symm_apply_apply]
        exact D.restrs_extZs Z m
      right_inv := fun n ↦ by
        simp only
        have h1 : ∀ hp, (⟨D.extZs Z (D.restrs Z (ψ.symm (D.extZs W n) : RZ F Z)), hp⟩ :
            LinearMap.ker (bigMap (F := F) f)) = ψ.symm (D.extZs W n) :=
          fun _ ↦ Subtype.ext (hepart n)
        rw [h1, LinearEquiv.apply_symm_apply]
        exact D.restrs_extZs W n }

end Families

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
