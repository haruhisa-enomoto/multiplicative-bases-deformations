import MultiplicativeBasisDeformations.Foundations.A0Normed
import MultiplicativeBasisDeformations.Foundations.A0Graded
import MultiplicativeBasisDeformations.Foundations.GradedLocal

/-!
# The radical of a finite scalar mesh category is its positive part

For a finite-dimensional scalar mesh category `C(Q, c)`, the morphisms of degree at least `m`
(`Ge m`) are closed under composition with degrees adding (`ge_comp`), vanish for `m` large
(`exists_ge_eq_zero`), and a morphism is radical (`1 - fg` invertible for all `g`) exactly when
its degree-zero part vanishes (`radical_iff`). This is the input `gr_J C = C` of the proof of
Corollary 4.15 (`scalar-normalization.tex`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

/-- Morphisms of degree at least `m`. -/
def Ge (m : ℕ) {x y : V} (f : obj c x ⟶ obj c y) : Prop := ∀ d < m, degProj c d x y f = 0

variable {c}

theorem ge_zero {x y : V} (f : obj c x ⟶ obj c y) : Ge c 0 f := fun d hd ↦ absurd hd (by omega)

theorem ge_of_mem {d m : ℕ} {x y : V} {f : obj c x ⟶ obj c y} (hf : f ∈ degreePart c d x y)
    (hd : m ≤ d) : Ge c m f := fun e he ↦ by
  rw [degProj_of_mem c hf, if_neg (by omega)]

theorem Ge.mono {m m' : ℕ} {x y : V} {f : obj c x ⟶ obj c y} (hf : Ge c m f) (h : m' ≤ m) :
    Ge c m' f := fun d hd ↦ hf d (by omega)

theorem Ge.add {m : ℕ} {x y : V} {f g : obj c x ⟶ obj c y} (hf : Ge c m f) (hg : Ge c m g) :
    Ge c m (f + g) := fun d hd ↦ by rw [map_add, hf d hd, hg d hd, add_zero]

theorem Ge.sub {m : ℕ} {x y : V} {f g : obj c x ⟶ obj c y} (hf : Ge c m f) (hg : Ge c m g) :
    Ge c m (f - g) := fun d hd ↦ by rw [map_sub, hf d hd, hg d hd, sub_zero]

theorem Ge.smul {m : ℕ} {x y : V} (t : k) {f : obj c x ⟶ obj c y} (hf : Ge c m f) :
    Ge c m (t • f) := fun d hd ↦ by rw [map_smul, hf d hd, smul_zero]

theorem Ge.neg {m : ℕ} {x y : V} {f : obj c x ⟶ obj c y} (hf : Ge c m f) : Ge c m (-f) :=
  fun d hd ↦ by rw [map_neg, hf d hd, neg_zero]

theorem ge_zero_mor (m : ℕ) {x y : V} : Ge c m (0 : obj c x ⟶ obj c y) := fun d _ ↦ map_zero _

theorem ge_sum (m : ℕ) {x y : V} {ι : Type*} (s : Finset ι) {f : ι → (obj c x ⟶ obj c y)}
    (hf : ∀ i ∈ s, Ge c m (f i)) : Ge c m (∑ i ∈ s, f i) := fun d hd ↦ by
  rw [map_sum]; exact Finset.sum_eq_zero fun i hi ↦ hf i hi d hd

theorem degProj_eq_of_ge {m : ℕ} {x y : V} {f : obj c x ⟶ obj c y} (hf : Ge c m f) {d : ℕ}
    (hd : d < m) : degProj c d x y f = 0 := hf d hd

variable [Finite V] (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

include hfin in
/-- **Composition adds degrees.** -/
theorem ge_comp {m m' : ℕ} {x y z : V} {f : obj c x ⟶ obj c y} {g : obj c y ⟶ obj c z}
    (hf : Ge c m f) (hg : Ge c m' g) : Ge c (m + m') (f ≫ g) := by
  obtain ⟨N, hN⟩ := exists_degreePart_eq_bot c hfin
  intro d' hd'
  rw [eq_sum_degProj c hN f, eq_sum_degProj c hN g, Preadditive.sum_comp, map_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rw [Preadditive.comp_sum, map_sum]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [degProj_of_mem c (comp_mem_degreePart' c (degProj_mem c d f) (degProj_mem c e g))]
  split_ifs with h
  · rcases lt_or_ge d m with hdm | hdm
    · rw [hf d hdm, Limits.zero_comp]
    · rw [hg e (by omega), Limits.comp_zero]
  · rfl

include hfin in
theorem exists_ge_eq_zero : ∃ N : ℕ, ∀ (x y : V) (f : obj c x ⟶ obj c y), Ge c N f → f = 0 := by
  obtain ⟨N, hN⟩ := exists_degreePart_eq_bot c hfin
  refine ⟨N, fun x y f hf ↦ ?_⟩
  rw [eq_sum_degProj c hN f]
  exact Finset.sum_eq_zero fun d hd ↦ hf d (Finset.mem_range.1 hd)

theorem degProj_id (x : V) : degProj c 0 x x (𝟙 (obj c x)) = 𝟙 (obj c x) := by
  rw [← pathMor_nil, degProj_of_mem c (pathMor_mem_degreePart c _)]
  exact if_pos rfl

theorem id_ne_zero (x : V) : 𝟙 (obj c x) ≠ 0 := by
  rw [← pathMor_nil]; exact pathMor_nil_ne_zero c x

include hfin in
theorem isNilpotent_of_ge {x : V} (f : End (obj c x)) (hf : Ge c 1 f) : IsNilpotent f := by
  obtain ⟨N, hN⟩ := exists_ge_eq_zero hfin (c := c)
  have hpow : ∀ n : ℕ, Ge c n (f ^ n) := by
    intro n
    induction n with
    | zero => exact ge_zero _
    | succ n ih =>
      rw [pow_succ, End.mul_def]
      exact (ge_comp hfin hf ih).mono (by omega)
  exact ⟨N, hN x x _ (hpow N)⟩

include hfin in
theorem isIso_id_sub {x : V} (f : obj c x ⟶ obj c x) (hf : Ge c 1 f) :
    IsIso (𝟙 (obj c x) - f) := by
  have := (isNilpotent_of_ge hfin (f : End (obj c x)) hf).isUnit_one_sub
  exact (isUnit_iff_isIso (𝟙 (obj c x) - f)).1 this

include hfin in
theorem not_isIso_of_ge {x : V} (f : obj c x ⟶ obj c x) (hf : Ge c 1 f) : ¬ IsIso f := by
  intro hi
  let f' : End (obj c x) := f
  have hu : IsUnit f' := (isUnit_iff_isIso f').2 hi
  obtain ⟨n, hn⟩ := isNilpotent_of_ge hfin f' hf
  have : IsUnit (f' ^ n) := hu.pow n
  rw [hn] at this
  haveI : Nontrivial (End (obj c x)) := ⟨⟨1, 0, id_ne_zero x⟩⟩
  exact not_isUnit_zero ‹IsUnit (0 : End (obj c x))›

include hfin in
/-- **The radical of `C(Q, c)` is its positive part.** -/
theorem radical_iff {x y : V} (f : obj c x ⟶ obj c y) :
    (∀ g : obj c y ⟶ obj c x, IsIso (𝟙 (obj c x) - f ≫ g)) ↔ degProj c 0 x y f = 0 := by
  constructor
  · intro h
    by_contra h0
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨t, ht⟩ := degreePart_zero_eq c (degProj_mem c 0 f)
      have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact h0 ht
      have hge : Ge c 1 (f - t • 𝟙 (obj c x)) := fun d hd ↦ by
        obtain rfl : d = 0 := by omega
        rw [map_sub, map_smul, degProj_id, ht, sub_self]
      apply not_isIso_of_ge hfin _ (hge.smul (-t⁻¹))
      convert h (t⁻¹ • 𝟙 (obj c x)) using 1
      have e : (-t⁻¹) * t = -1 := by field_simp
      rw [Linear.comp_smul, Category.comp_id, smul_sub, smul_smul, e, neg_one_smul, neg_smul]
      abel
    · exact h0 (degreePart_zero_ne hxy (degProj_mem c 0 f))
  · intro h g
    refine isIso_id_sub hfin _ ?_
    have h1 : Ge c 1 f := fun d hd ↦ by
      obtain rfl : d = 0 := by omega
      exact h
    simpa using ge_comp hfin h1 (ge_zero g)

include hfin in
/-- **Distinct vertices are not isomorphic.** -/
theorem eq_of_comp_eq_id {x y : V} (f : obj c x ⟶ obj c y) (g : obj c y ⟶ obj c x)
    (h : f ≫ g = 𝟙 (obj c x)) : x = y := by
  by_contra hxy
  have hf : Ge c 1 f := fun d hd ↦ by
    obtain rfl : d = 0 := by omega
    exact degreePart_zero_ne hxy (degProj_mem c 0 f)
  have := (ge_comp hfin hf (ge_zero g)) 0 (by omega)
  rw [h, degProj_id] at this
  exact id_ne_zero x this

end MeshWalk

end MultiplicativeBasisDeformations
