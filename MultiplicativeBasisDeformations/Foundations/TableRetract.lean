import MultiplicativeBasisDeformations.Foundations.TableCover

/-!
# Retractions of ray tables (Lemma 8.9 at ray level)

`lem:representation-transfer`: a table `S` embedded in a table `T` by a unital morphism that
is injective on rays, such that a ray of `T` whose product with an embedded ray is embedded is
itself embedded (on either side). The projection of `kT` onto the embedded rays is then an
`S`-bimodule retraction, and Lemma 4.6 shows that `kS` is representation-finite when `kT`
is.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

variable {V R V' R' : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  [Fintype V'] [DecidableEq V'] [Fintype R'] [DecidableEq R']

namespace Mor

variable {S : Mult V R} {T : Mult V' R'} (m : Mor S T) (g : R → R') (hg : ∀ r, m.f r = some (g r))
  (hginj : Function.Injective g)
  (hL : ∀ s t t', T.mul (g s) t = some (g t') → ∃ s', g s' = t)
  (hR : ∀ s t t', T.mul t (g s) = some (g t') → ∃ s', g s' = t)
  (k : Type u) [Field k]

variable (S T) in
/-- The projection onto the embedded rays. -/
def retr : T.Lin k →ₗ[k] S.Lin k :=
  (T.basis k).constr k fun t ↦ if h : ∃ s, g s = t then S.b k h.choose else 0

variable (S T) in
theorem retr_b (t : R') : retr S T g k (T.b k t) = if h : ∃ s, g s = t then S.b k h.choose else 0 := by
  rw [retr, ← Mult.basis_apply, Module.Basis.constr_basis]

variable (S T) in
include hginj in
theorem retr_b_g (s : R) : retr S T g k (T.b k (g s)) = S.b k s := by
  rw [retr_b, dif_pos ⟨s, rfl⟩]
  congr 1
  exact hginj (Exists.choose_spec (⟨s, rfl⟩ : ∃ s', g s' = g s))

variable (S T) in
theorem retr_b_not (t : R') (h : ¬ ∃ s, g s = t) : retr S T g k (T.b k t) = 0 := by
  rw [retr_b, dif_neg h]

include hg in
theorem alg_b_g (s : R) : m.alg k (S.b k s) = T.b k (g s) := by
  rw [alg_b, hg]; rfl

include hg in
theorem mul_g (s s' : R) : T.mul (g s) (g s') = (S.mul s s').map g := by
  have := m.hmul s s'
  rw [hg, hg] at this
  simp only [Option.bind_some] at this
  rw [this]
  cases S.mul s s' with
  | none => rfl
  | some w => rw [Option.bind_some, hg]; rfl

include hg hginj in
theorem retr_alg (x : S.Lin k) : retr S T g k (m.alg k x) = x := by
  have : (retr S T g k).comp (m.alg k).toLinearMap = LinearMap.id := by
    refine (S.basis k).ext fun s ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, Mult.basis_apply,
      AlgHom.toLinearMap_apply, m.alg_b_g g hg, retr_b_g S T g hginj k]
  exact congrArg (fun f ↦ f x) this

include hg hginj hL in
theorem retr_left (d : S.Lin k) (x : T.Lin k) :
    retr S T g k (m.alg k d * x) = d * retr S T g k x := by
  have h : ((LinearMap.mul k _).compl₁₂ (m.alg k).toLinearMap LinearMap.id).compr₂ (retr S T g k) =
      (LinearMap.mul k _).compl₁₂ LinearMap.id (retr S T g k) := by
    refine LinearMap.ext_basis (S.basis k) (T.basis k) fun s t ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, Mult.basis_apply, m.alg_b_g g hg]
    by_cases ht : ∃ s', g s' = t
    · obtain ⟨s', rfl⟩ := ht
      rw [retr_b_g S T g hginj k, Mult.b_mul, Mult.b_mul, m.mul_g g hg]
      cases S.mul s s' with
      | none => simp
      | some w => simp [retr_b_g S T g hginj k]
    · rw [retr_b_not S T g k t ht, mul_zero, Mult.b_mul]
      cases hm : T.mul (g s) t with
      | none => simp
      | some w =>
        simp only [Option.elim_some]
        apply retr_b_not S T g k w
        rintro ⟨s', rfl⟩
        exact ht (hL s t s' hm)
  exact congrArg (fun B ↦ B d x) h

include hg hginj hR in
theorem retr_right (x : T.Lin k) (d : S.Lin k) :
    retr S T g k (x * m.alg k d) = retr S T g k x * d := by
  have h : ((LinearMap.mul k _).compl₁₂ LinearMap.id (m.alg k).toLinearMap).compr₂ (retr S T g k) =
      (LinearMap.mul k _).compl₁₂ (retr S T g k) LinearMap.id := by
    refine LinearMap.ext_basis (T.basis k) (S.basis k) fun t s ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, Mult.basis_apply, m.alg_b_g g hg]
    by_cases ht : ∃ s', g s' = t
    · obtain ⟨s', rfl⟩ := ht
      rw [retr_b_g S T g hginj k, Mult.b_mul, Mult.b_mul, m.mul_g g hg]
      cases S.mul s' s with
      | none => simp
      | some w => simp [retr_b_g S T g hginj k]
    · rw [retr_b_not S T g k t ht, zero_mul, Mult.b_mul]
      cases hm : T.mul t (g s) with
      | none => simp
      | some w =>
        simp only [Option.elim_some]
        apply retr_b_not S T g k w
        rintro ⟨s', rfl⟩
        exact ht (hR s t s' hm)
  exact congrArg (fun B ↦ B x d) h

include hg hginj in
theorem alg_injective : Function.Injective (m.alg k) := fun x y h ↦ by
  rw [← m.retr_alg g hg hginj k x, h, m.retr_alg g hg hginj k]

include hg hginj hL hR in
/-- **Lemma 8.9 for ray tables** (`lem:representation-transfer`). -/
theorem retract_isRepresentationFinite (h : IsRepresentationFinite k (T.Lin k)) :
    IsRepresentationFinite k (S.Lin k) := by
  set α := m.alg k
  let e := AlgEquiv.ofInjective α (m.alg_injective g hg hginj k)
  refine splitRepresentationTransfer_of (C := α.range) (q := e.symm.toAlgHom)
    (retr S T g k) (fun c c' b ↦ ?_) e.symm.surjective (fun c ↦ ?_) h
  · obtain ⟨_, d, rfl⟩ := c
    obtain ⟨_, d', rfl⟩ := c'
    have h1 : e.symm ⟨α d, d, rfl⟩ = d := by rw [AlgEquiv.symm_apply_eq]; rfl
    have h2 : e.symm ⟨α d', d', rfl⟩ = d' := by rw [AlgEquiv.symm_apply_eq]; rfl
    change retr S T g k (α d * b * α d') = e.symm ⟨α d, d, rfl⟩ * retr S T g k b * e.symm ⟨α d', d', rfl⟩
    rw [h1, h2, m.retr_right g hg hginj hR, m.retr_left g hg hginj hL]
  · obtain ⟨_, d, rfl⟩ := c
    have h1 : e.symm ⟨α d, d, rfl⟩ = d := by rw [AlgEquiv.symm_apply_eq]; rfl
    change retr S T g k (α d) = e.symm ⟨α d, d, rfl⟩
    rw [h1, m.retr_alg g hg hginj]

end Mor

end RaySys

end MultiplicativeBasisDeformations
