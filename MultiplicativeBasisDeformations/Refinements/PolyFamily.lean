import Mathlib

/-!
# Polynomial families of vectors (toward Proposition 12.8)

A family `t ↦ f t` of vectors indexed by parameter values `t : I → k` is *polynomial*
(`IsPoly`) if it is a finite sum `Σ_j t^{e_j} v_j` of monomials with vector coefficients. These
are the specializations of the `k[t_i]`-valued data of `deformation-refinements.tex:375–400`.
Polynomial families are closed under sums, linear and bilinear maps; over an infinite field a
polynomial family vanishing on the torus `t_i ≠ 0` vanishes identically
(`IsPoly.eq_zero_of_torus`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

variable {k : Type*} [Field k] {I : Type} [Fintype I] [DecidableEq I]

/-- The monomial `t^n = Π_i t_i^{n_i}`. -/
def mono (n : I → ℕ) (t : I → k) : k := ∏ i, t i ^ n i

theorem mono_add (n n' : I → ℕ) (t : I → k) : mono (n + n') t = mono n t * mono n' t := by
  simp only [mono, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mono_zero (t : I → k) : mono 0 t = 1 := by simp [mono]

theorem mono_one (n : I → ℕ) : mono n (fun _ ↦ (1 : k)) = 1 := by simp [mono]

variable {V W X : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]

/-- **A polynomial family**: a finite sum of monomials with vector coefficients. -/
def IsPoly (f : (I → k) → V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → I → ℕ) (v : ι → V), ∀ t, f t = ∑ j, mono (e j) t • v j

namespace IsPoly

theorem const (v : V) : IsPoly (fun _ : I → k ↦ v) :=
  ⟨Unit, inferInstance, fun _ ↦ 0, fun _ ↦ v, fun t ↦ by simp [mono_zero]⟩

theorem monomial (n : I → ℕ) (v : V) : IsPoly (fun t : I → k ↦ mono n t • v) :=
  ⟨Unit, inferInstance, fun _ ↦ n, fun _ ↦ v, fun t ↦ by simp⟩

theorem add {f g : (I → k) → V} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun t ↦ f t + g t) := by
  obtain ⟨ι, _, e, v, hf⟩ := hf
  obtain ⟨ι', _, e', v', hg⟩ := hg
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim e e', Sum.elim v v', fun t ↦ by
    beta_reduce; rw [hf, hg, Fintype.sum_sum_type]; rfl⟩

theorem zero : IsPoly (fun _ : I → k ↦ (0 : V)) := by simpa using const (k := k) (I := I) (0 : V)

theorem map (g : V →ₗ[k] W) {f : (I → k) → V} (hf : IsPoly f) : IsPoly (fun t ↦ g (f t)) := by
  obtain ⟨ι, _, e, v, hf⟩ := hf
  exact ⟨ι, inferInstance, e, fun j ↦ g (v j), fun t ↦ by
    beta_reduce; rw [hf, map_sum]; simp only [map_smul]⟩

theorem neg {f : (I → k) → V} (hf : IsPoly f) : IsPoly (fun t ↦ -f t) := by
  simpa using map (-LinearMap.id) hf

theorem sub {f g : (I → k) → V} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun t ↦ f t - g t) := by
  simpa [sub_eq_add_neg] using add hf hg.neg

theorem smul (c : k) {f : (I → k) → V} (hf : IsPoly f) : IsPoly (fun t ↦ c • f t) :=
  map (c • LinearMap.id) hf

theorem sum {κ : Type*} (s : Finset κ) {f : κ → (I → k) → V} (hf : ∀ j ∈ s, IsPoly (f j)) :
    IsPoly (fun t ↦ ∑ j ∈ s, f j t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact add (hf a (Finset.mem_insert_self a s))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem bilin (B : V →ₗ[k] W →ₗ[k] X) {f : (I → k) → V} {g : (I → k) → W} (hf : IsPoly f)
    (hg : IsPoly g) : IsPoly (fun t ↦ B (f t) (g t)) := by
  obtain ⟨ι, _, e, v, hf⟩ := hf
  obtain ⟨ι', _, e', v', hg⟩ := hg
  refine ⟨ι × ι', inferInstance, fun j ↦ e j.1 + e' j.2, fun j ↦ B (v j.1) (v' j.2), fun t ↦ ?_⟩
  beta_reduce
  rw [hf, hg, Fintype.sum_prod_type]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, mono_add, mul_smul]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦
    smul_comm (mono (e' j') t) (mono (e j) t) (B (v j) (v' j'))

/-- **Polynomial identities extend from the torus.** -/
theorem eq_zero_of_torus [Infinite k] {f : (I → k) → V} (hf : IsPoly f)
    (h : ∀ t : I → k, (∀ i, t i ≠ 0) → f t = 0) (t : I → k) : f t = 0 := by
  classical
  obtain ⟨ι, _, e, v, hf⟩ := hf
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  let mon : ι → MvPolynomial I k := fun j ↦
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (e j)) (φ (v j))
  let P : MvPolynomial I k := ∑ j, mon j
  have hev : ∀ s : I → k, MvPolynomial.eval s P = φ (f s) := by
    intro s
    rw [hf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [mon, MvPolynomial.eval_monomial, map_smul, smul_eq_mul]
    rw [Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, mono]
    ring
  have hP : P * ∏ i, MvPolynomial.X i = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul, map_zero, map_prod, hev]
    simp only [MvPolynomial.eval_X]
    by_cases hs : ∀ i, s i ≠ 0
    · rw [h s hs, map_zero, zero_mul]
    · push Not at hs
      obtain ⟨i, hi⟩ := hs
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
  have hX : (∏ i, MvPolynomial.X i : MvPolynomial I k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ MvPolynomial.X_ne_zero i
  rw [← hev, (mul_eq_zero.1 hP).resolve_right hX, map_zero]

end IsPoly

end MultiplicativeBasisDeformations
