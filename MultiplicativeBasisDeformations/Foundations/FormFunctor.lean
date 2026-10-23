module

public import MultiplicativeBasisDeformations.Foundations.BaseChange
public import MultiplicativeBasisDeformations.Foundations.GaugeTransfer

/-!
# The prime-field form of a scalar mesh category

`integral-deformations.tex`: "The all-one meshes […] define a graded category `C⁽²⁾`
with `k ⊗_{𝔽₂} C⁽²⁾ = C`." The coefficients of `C = C(Q, c)` are normalized to one by
Lemma 4.4 (a gauge `c_{x,a} = η_x μ_{σa} μ_a`), and the all-one category over the prime field
is a form of the all-one category over `k`.

Here: for coefficients `u` over a subfield `K` and a gauge `c = η · (ι ∘ u) · μ μ` over `k`,
the *form functor* `Fm = gauge ∘ redE : C(Q, u) → C(Q, c)` (`Fm`), with `Fm(a) = μ_a a` on
arrows, and for every `K`-linear `θ : k → K` the *retraction*
`Π θ = retE θ ∘ gauge⁻¹ : C(Q, c) → C(Q, u)`, a bimodule map over the image of `Fm`
(`Π_comp_Fm`, `Π_Fm_comp`) with `Π θ (t • Fm φ) = θ t • φ` (`Π_smul_Fm`). Hence `Fm` is injective
and the Hom spaces have equal dimensions (`finrank_Fm`).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

open LinearPaths

/-! ### The inverse gauge -/

section Gauge

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ) (c c' : MeshCoefficients k Q)
  (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
    c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a)

include h in
theorem gauge_inv_rel (x : Q.nonprojective) (y : V) (a : y ⟶ x.1) :
    c x y a = (η x)⁻¹ * c' x y a * (μ (Q.mate x y a))⁻¹ * (μ a)⁻¹ := by
  rw [h]; ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

/-- The inverse gauge functor `C(Q, c') → C(Q, c)`. -/
abbrev gaugeInv : ScalarMeshCategory k Q c' ⥤ ScalarMeshCategory k Q c :=
  gaugeQ (fun {_ _} a ↦ (μ a)⁻¹) (fun x ↦ (η x)⁻¹) c' c (gauge_inv_rel μ η c c' h)

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] in
theorem pathWt_inv {x : V} : ∀ {y : V} (p : Quiver.Path x y),
    pathWt (fun {_ _} a ↦ (μ a)⁻¹) p = (pathWt μ p)⁻¹
  | _, Quiver.Path.nil => by simp [pathWt]
  | _, Quiver.Path.cons p a => by
      simp only [pathWt]; rw [pathWt_inv p, mul_inv]

theorem gaugeInv_gaugeQ {x y : V} (φ : obj c x ⟶ obj c y) :
    (gaugeInv μ η c c' h).map ((gaugeQ μ η c c' h).map φ) = φ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ φ
  induction Φ using LinearPaths.induction_on with
  | h0 =>
      rw [Functor.map_zero, gaugeQ_map_zero, gaugeQ_map_zero]
  | hadd F G hF hG =>
      rw [Functor.map_add, gaugeQ_map_add, gaugeQ_map_add, hF, hG]
  | hsingle p t =>
      rw [Functor.map_smul, gaugeQ_map_smul, gaugeQ_map_smul]
      change t • (gaugeInv μ η c c' h).map ((gaugeQ μ η c c' h).map (pathMor c p)) = t • pathMor c p
      have e1 : (gaugeInv μ η c c' h).map (pathMor c' p) =
          (((pathWt μ p)⁻¹ : kˣ) : k) • pathMor c p := by
        rw [gaugeQ_pathMor, pathWt_inv]
      have e : (gaugeInv μ η c c' h).map ((gaugeQ μ η c c' h).map (pathMor c p)) = pathMor c p :=
        calc (gaugeInv μ η c c' h).map ((gaugeQ μ η c c' h).map (pathMor c p))
            = (gaugeInv μ η c c' h).map (((pathWt μ p : kˣ) : k) • pathMor c' p) := by
              rw [gaugeQ_pathMor]
          _ = ((pathWt μ p : kˣ) : k) • (gaugeInv μ η c c' h).map (pathMor c' p) :=
              gaugeQ_map_smul _ _ _ _ _ _ _
          _ = ((pathWt μ p : kˣ) : k) • ((((pathWt μ p)⁻¹ : kˣ) : k) • pathMor c p) := by rw [e1]
          _ = pathMor c p := by
              rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
      rw [e]

theorem gaugeQ_gaugeInv {x y : V} (ψ : obj c' x ⟶ obj c' y) :
    (gaugeQ μ η c c' h).map ((gaugeInv μ η c c' h).map ψ) = ψ := by
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) _ ψ
  induction Ψ using LinearPaths.induction_on with
  | h0 =>
      rw [Functor.map_zero, gaugeQ_map_zero, gaugeQ_map_zero]
  | hadd F G hF hG =>
      rw [Functor.map_add, gaugeQ_map_add, gaugeQ_map_add, hF, hG]
  | hsingle p t =>
      rw [Functor.map_smul, gaugeQ_map_smul, gaugeQ_map_smul]
      change t • (gaugeQ μ η c c' h).map ((gaugeInv μ η c c' h).map (pathMor c' p)) = t • pathMor c' p
      have e1 : (gaugeInv μ η c c' h).map (pathMor c' p) =
          (((pathWt μ p)⁻¹ : kˣ) : k) • pathMor c p := by
        rw [gaugeQ_pathMor, pathWt_inv]
      have e : (gaugeQ μ η c c' h).map ((gaugeInv μ η c c' h).map (pathMor c' p)) = pathMor c' p :=
        calc (gaugeQ μ η c c' h).map ((gaugeInv μ η c c' h).map (pathMor c' p))
            = (gaugeQ μ η c c' h).map ((((pathWt μ p)⁻¹ : kˣ) : k) • pathMor c p) := by rw [e1]
          _ = (((pathWt μ p)⁻¹ : kˣ) : k) • (gaugeQ μ η c c' h).map (pathMor c p) :=
              gaugeQ_map_smul _ _ _ _ _ _ _
          _ = (((pathWt μ p)⁻¹ : kˣ) : k) • (((pathWt μ p : kˣ) : k) • pathMor c' p) := by
              rw [gaugeQ_pathMor]
          _ = pathMor c' p := by
              rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      rw [e]

/-- The gauge, as a linear equivalence of Hom spaces. -/
def gaugeEquiv (x y : V) : (obj c x ⟶ obj c y) ≃ₗ[k] (obj c' x ⟶ obj c' y) where
  toFun φ := (gaugeQ μ η c c' h).map φ
  invFun ψ := (gaugeInv μ η c c' h).map ψ
  map_add' φ ψ := gaugeQ_map_add μ η c c' h φ ψ
  map_smul' t φ := gaugeQ_map_smul μ η c c' h t φ
  left_inv φ := gaugeInv_gaugeQ μ η c c' h φ
  right_inv ψ := gaugeQ_gaugeInv μ η c c' h ψ

end Gauge

/-! ### The form functor and its retractions -/

section Form

variable {K : Type} [Field K] {k : Type u} [Field k] [Algebra K k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (u : MeshCoefficients K Q) (c₁ c : MeshCoefficients k Q)
  (hred : ∀ x y a, algebraMap K k (u x y a : K) = (c₁ x y a : k))
  (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
  (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
    c x y a = η x * c₁ x y a * μ (Q.mate x y a) * μ a)

/-- **The form functor** `C(Q, u) → C(Q, c)` on morphisms. -/
def Fm {x y : V} (φ : obj u x ⟶ obj u y) : obj c x ⟶ obj c y :=
  (gaugeQ μ η c₁ c h).map (redE (algebraMap K k) u c₁ φ)

variable (θ : k →ₗ[K] K)

/-- **The retraction** `C(Q, c) → C(Q, u)` along `θ`. -/
def retF {x y : V} (ψ : obj c x ⟶ obj c y) : obj u x ⟶ obj u y :=
  retE u θ ((gaugeInv μ η c₁ c h).map ψ)

include hred

theorem Fm_comp {x y z : V} (φ : obj u x ⟶ obj u y) (φ' : obj u y ⟶ obj u z) :
    Fm u c₁ c μ η h (φ ≫ φ') = Fm u c₁ c μ η h φ ≫ Fm u c₁ c μ η h φ' := by
  rw [Fm, Fm, Fm, redE_comp hred, Functor.map_comp]

theorem Fm_add {x y : V} (φ φ' : obj u x ⟶ obj u y) :
    Fm u c₁ c μ η h (φ + φ') = Fm u c₁ c μ η h φ + Fm u c₁ c μ η h φ' := by
  rw [Fm, Fm, Fm, redE_add hred, gaugeQ_map_add]

theorem Fm_zero {x y : V} : Fm u c₁ c μ η h (0 : obj u x ⟶ obj u y) = 0 := by
  rw [Fm, redE_zero hred, gaugeQ_map_zero]

theorem Fm_smul {x y : V} (a : K) (φ : obj u x ⟶ obj u y) :
    Fm u c₁ c μ η h (a • φ) = algebraMap K k a • Fm u c₁ c μ η h φ := by
  rw [Fm, Fm, redE_smul hred, gaugeQ_map_smul]

theorem Fm_sub {x y : V} (φ φ' : obj u x ⟶ obj u y) :
    Fm u c₁ c μ η h (φ - φ') = Fm u c₁ c μ η h φ - Fm u c₁ c μ η h φ' := by
  rw [eq_sub_iff_add_eq, ← Fm_add u c₁ c hred, sub_add_cancel]

theorem Fm_sum {x y : V} {ι : Type*} (s : Finset ι) (φ : ι → (obj u x ⟶ obj u y)) :
    Fm u c₁ c μ η h (∑ i ∈ s, φ i) = ∑ i ∈ s, Fm u c₁ c μ η h (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Fm_zero u c₁ c hred]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Fm_add u c₁ c hred, ih]

theorem Fm_arrowMor {x y : V} (a : x ⟶ y) :
    Fm u c₁ c μ η h (arrowMor u a) = ((μ a : kˣ) : k) • arrowMor c a := by
  rw [Fm, redE_arrowMor hred, gaugeQ_arrowMor]

theorem Fm_id (x : V) : Fm u c₁ c μ η h (𝟙 (obj u x)) = 𝟙 (obj c x) := by
  have h1 : (𝟙 (obj u x)) = pathMor u (Quiver.Path.nil : Quiver.Path x x) := by
    unfold pathMor; exact (CategoryTheory.Functor.map_id _ _).symm
  have h2 : pathMor c (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (obj c x) := by
    unfold pathMor; exact CategoryTheory.Functor.map_id _ _
  rw [Fm, h1, redE_pathMor hred, gaugeQ_pathMor, h2]
  simp [pathWt]

theorem retF_add {x y : V} (ψ ψ' : obj c x ⟶ obj c y) :
    retF u c₁ c μ η h θ (ψ + ψ') = retF u c₁ c μ η h θ ψ + retF u c₁ c μ η h θ ψ' := by
  rw [retF, retF, retF, gaugeQ_map_add, retE_add hred]

theorem retF_zero {x y : V} : retF u c₁ c μ η h θ (0 : obj c x ⟶ obj c y) = 0 := by
  rw [retF, gaugeQ_map_zero, retE_zero hred]

theorem retF_sum {x y : V} {ι : Type*} (s : Finset ι) (ψ : ι → (obj c x ⟶ obj c y)) :
    retF u c₁ c μ η h θ (∑ i ∈ s, ψ i) = ∑ i ∈ s, retF u c₁ c μ η h θ (ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [retF_zero u c₁ c hred]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, retF_add u c₁ c hred, ih]

theorem retF_smul_Fm {x y : V} (t : k) (φ : obj u x ⟶ obj u y) :
    retF u c₁ c μ η h θ (t • Fm u c₁ c μ η h φ) = θ t • φ := by
  rw [retF, Fm, gaugeQ_map_smul, gaugeInv_gaugeQ, retE_smul_redE hred]

theorem retF_Fm (h1 : θ 1 = 1) {x y : V} (φ : obj u x ⟶ obj u y) :
    retF u c₁ c μ η h θ (Fm u c₁ c μ η h φ) = φ := by
  have := retF_smul_Fm u c₁ c hred μ η h θ 1 φ
  rwa [one_smul, h1, one_smul] at this

theorem retF_comp_Fm {x y z : V} (ψ : obj c x ⟶ obj c y) (φ : obj u y ⟶ obj u z) :
    retF u c₁ c μ η h θ (ψ ≫ Fm u c₁ c μ η h φ) = retF u c₁ c μ η h θ ψ ≫ φ := by
  rw [retF, Fm, Functor.map_comp, gaugeInv_gaugeQ, retE_comp_redE hred, retF]

theorem retF_Fm_comp {x y z : V} (φ : obj u x ⟶ obj u y) (ψ : obj c y ⟶ obj c z) :
    retF u c₁ c μ η h θ (Fm u c₁ c μ η h φ ≫ ψ) = φ ≫ retF u c₁ c μ η h θ ψ := by
  rw [retF, Fm, Functor.map_comp, gaugeInv_gaugeQ, retE_redE_comp hred, retF]

theorem Fm_injective {x y : V} :
    Function.Injective (Fm u c₁ c μ η h : (obj u x ⟶ obj u y) → (obj c x ⟶ obj c y)) := by
  intro φ φ' e
  rw [Fm, Fm] at e
  exact redE_injective hred ((gaugeEquiv μ η c₁ c h x y).injective e)

omit θ in
include h in
/-- **Equal dimensions.** -/
theorem finiteDimensional_finrank_Fm {x y : V} [FiniteDimensional k (obj c x ⟶ obj c y)] :
    FiniteDimensional K (obj u x ⟶ obj u y) ∧
      Module.finrank K (obj u x ⟶ obj u y) = Module.finrank k (obj c x ⟶ obj c y) := by
  have : FiniteDimensional k (obj c₁ x ⟶ obj c₁ y) :=
    LinearEquiv.finiteDimensional (gaugeEquiv μ η c₁ c h x y).symm
  obtain ⟨h₁, h₂⟩ := finiteDimensional_finrank_redE (k := k) hred (X := x) (Y := y)
  exact ⟨h₁, h₂.trans (gaugeEquiv μ η c₁ c h x y).finrank_eq⟩

end Form

end ScalarMeshCategory

end MultiplicativeBasisDeformations
