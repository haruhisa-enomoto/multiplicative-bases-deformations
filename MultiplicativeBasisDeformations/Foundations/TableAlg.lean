import MultiplicativeBasisDeformations.Foundations.RayTable
import MultiplicativeBasisDeformations.Foundations.SplitTransfer

/-!
# The linearization `kP` of a ray table

`kP` has basis the rays, with products given by the table (`set:projective-companion`). We
realize it inside `Matrix R R k` through the left regular representation, so that it is a
`Subalgebra` with basis `b r` and `b r * b s = b (rs)` or `0`.

A *table morphism* `P → P'` sends rays to rays or zero, compatibly with products, and sends
the identities onto the identities, each hit once. It induces an algebra map `kP → kP'`,
surjective when every ray is hit; representation-finiteness passes along such maps
(`isRepresentationFinite_of_surjective`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

/-- Representation-finiteness passes to quotient algebras. -/
theorem isRepresentationFinite_of_surjective {k : Type u} [Field k] {A B : Type u} [Ring A]
    [Algebra k A] [Ring B] [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
    (φ : A →ₐ[k] B) (hφ : Function.Surjective φ) (hA : IsRepresentationFinite k A) :
    IsRepresentationFinite k B :=
  splitRepresentationTransfer_of (C := ⊤) (q := φ.comp (Subalgebra.val ⊤))
    φ.toLinearMap (fun c c' b ↦ by simp [map_mul]) (fun d ↦ by
      obtain ⟨a, rfl⟩ := hφ d; exact ⟨⟨a, trivial⟩, rfl⟩) (fun c ↦ rfl) hA

namespace RaySys

namespace Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  (P : Mult V R) (k : Type u) [CommRing k] [Nontrivial k]

/-- The left regular action of a ray. -/
def rho (r : R) : Matrix R R k := fun t s ↦ if P.mul r s = some t then 1 else 0

theorem rho_apply (r t s : R) : P.rho k r t s = if P.mul r s = some t then 1 else 0 := rfl

theorem rho_mul (r r' : R) : P.rho k r * P.rho k r' = (P.mul r r').elim 0 (P.rho k) := by
  ext t s
  rw [Matrix.mul_apply]
  simp only [rho_apply, mul_ite, mul_one, mul_zero]
  have h := P.assoc r r' s
  -- `∑ u, [r' s = u] [r u = t]`
  rw [Finset.sum_eq_single_of_mem (a := (P.mul r' s).getD r) (Finset.mem_univ _)]
  · cases hrr : P.mul r r' with
    | none =>
      rw [hrr] at h
      simp only [Option.bind_none] at h
      simp only [Option.elim_none, Matrix.zero_apply]
      cases hs : P.mul r' s with
      | none => simp
      | some w =>
        rw [hs] at h
        simp only [Option.bind_some] at h
        simp [← h]
    | some m =>
      rw [hrr] at h
      simp only [Option.bind_some] at h
      simp only [Option.elim_some, rho_apply, h]
      cases hs : P.mul r' s with
      | none => simp
      | some w => simp
  · intro u _ hu
    split_ifs with h1 h2
    · exfalso; apply hu; rw [h1]; rfl
    · rfl
    · rfl

theorem sum_rho_e : ∑ x, P.rho k (P.e x) = 1 := by
  ext t s
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [rho_apply]
  rw [Finset.sum_eq_single (P.src s)]
  · rw [P.e_mul s]
    by_cases h : s = t
    · simp [h]
    · simp [h, Ne.symm h]
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (by have := P.mul_mid _ _ _ h; rwa [P.tgt_e] at this)
  · simp

/-- The span of the rays. -/
def linSpan : Submodule k (Matrix R R k) := Submodule.span k (Set.range (P.rho k))

theorem rho_mem (r : R) : P.rho k r ∈ P.linSpan k := Submodule.subset_span ⟨r, rfl⟩

theorem one_mem_linSpan : (1 : Matrix R R k) ∈ P.linSpan k := by
  rw [← P.sum_rho_e k]
  exact Submodule.sum_mem _ fun x _ ↦ P.rho_mem k _

theorem mul_mem_linSpan (a b : Matrix R R k) (ha : a ∈ P.linSpan k) (hb : b ∈ P.linSpan k) :
    a * b ∈ P.linSpan k := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r', rfl⟩ := hy
      rw [rho_mul]
      cases P.mul r r' with
      | none => exact Submodule.zero_mem _
      | some m => exact P.rho_mem k m
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- **The linearization `kP`.** -/
def Lin : Subalgebra k (Matrix R R k) :=
  (P.linSpan k).toSubalgebra (P.one_mem_linSpan k) (P.mul_mem_linSpan k)

/-- The basis vector of a ray. -/
def b (r : R) : P.Lin k := ⟨P.rho k r, P.rho_mem k r⟩

theorem b_mul (r s : R) : P.b k r * P.b k s = (P.mul r s).elim 0 (P.b k) := by
  apply Subtype.ext
  change P.rho k r * P.rho k s = _
  rw [rho_mul]
  cases P.mul r s <;> rfl

theorem b_mul_of_some {r s t : R} (h : P.mul r s = some t) : P.b k r * P.b k s = P.b k t := by
  rw [b_mul, h]; rfl

theorem b_mul_of_none {r s : R} (h : P.mul r s = none) : P.b k r * P.b k s = 0 := by
  rw [b_mul, h]; rfl

theorem sum_b_e : ∑ x, P.b k (P.e x) = 1 := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum]
  exact P.sum_rho_e k

/-- The coordinate of a matrix at a ray: its entry at `(r, e (tgt r))`. -/
theorem rho_apply_e (r r' : R) : P.rho k r' r (P.e (P.tgt r)) = if r' = r then 1 else 0 := by
  rw [rho_apply]
  by_cases h : r' = r
  · subst h; rw [P.mul_e]; simp
  · rw [if_neg h, if_neg]
    intro h'
    have h2 := P.mul_mid _ _ _ h'
    rw [P.src_e] at h2
    have := P.mul_e r'
    rw [h2, h'] at this
    exact h (Option.some_injective _ this).symm

theorem linearIndependent_b : LinearIndependent k (P.b k) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have := congrArg (fun a : P.Lin k ↦ (a : Matrix R R k) i (P.e (P.tgt i))) hc
  simp only [AddSubmonoidClass.coe_finset_sum, Matrix.sum_apply, ZeroMemClass.coe_zero,
    Matrix.zero_apply] at this
  change ∑ x ∈ s, c x * P.rho k x i (P.e (P.tgt i)) = 0 at this
  simp only [rho_apply_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', if_pos hi] at this
  exact this

theorem span_b : Submodule.span k (Set.range (P.b k)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, ha⟩ -
  change a ∈ Submodule.span k (Set.range (P.rho k)) at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    exact Submodule.subset_span ⟨r, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have : (⟨x + y, Submodule.add_mem _ hx hy⟩ : P.Lin k) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    have : (⟨c • x, Submodule.smul_mem _ c hx⟩ : P.Lin k) = c • ⟨x, hx⟩ := rfl
    rw [this]; exact Submodule.smul_mem _ c ih

/-- **The ray basis of `kP`.** -/
def basis : Module.Basis R k (P.Lin k) :=
  Module.Basis.mk (P.linearIndependent_b k) (P.span_b k).ge

theorem basis_apply (r : R) : P.basis k r = P.b k r := by
  simp [basis]

instance : Module.Finite k (P.Lin k) := Module.Finite.of_basis (P.basis k)

theorem mul_e_none {x : V} {r : R} (h : x ≠ P.src r) : P.mul (P.e x) r = none := by
  cases h' : P.mul (P.e x) r with
  | none => rfl
  | some t => exact absurd (by have := P.mul_mid _ _ _ h'; rwa [P.tgt_e] at this) h

theorem mul_none_e {x : V} {r : R} (h : x ≠ P.tgt r) : P.mul r (P.e x) = none := by
  cases h' : P.mul r (P.e x) with
  | none => rfl
  | some t => exact absurd (by have := P.mul_mid _ _ _ h'; rwa [P.src_e, eq_comm] at this) h

theorem b_e_mul (x : V) (r : R) : P.b k (P.e x) * P.b k r = if x = P.src r then P.b k r else 0 := by
  split_ifs with h
  · subst h; exact P.b_mul_of_some k (P.e_mul r)
  · exact P.b_mul_of_none k (P.mul_e_none h)

theorem b_mul_e (r : R) (x : V) : P.b k r * P.b k (P.e x) = if x = P.tgt r then P.b k r else 0 := by
  split_ifs with h
  · subst h; exact P.b_mul_of_some k (P.mul_e r)
  · exact P.b_mul_of_none k (P.mul_none_e h)

theorem b_ne_zero (r : R) : P.b k r ≠ 0 := by
  rw [← basis_apply]; exact (P.basis k).ne_zero r

theorem basis_repr_b (r r' : R) : (P.basis k).repr (P.b k r) r' = if r = r' then 1 else 0 := by
  rw [← basis_apply, Module.Basis.repr_self, Finsupp.single_apply]

end Mult

/-! ### Table morphisms -/

variable {V R V' R' : Type} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R] [Fintype V'] [DecidableEq V'] [Fintype R'] [DecidableEq R']

/-- A (not necessarily unital) morphism of tables: rays go to rays or zero, compatibly with
products, and identities go to identities or zero. -/
structure NMor (P : Mult V R) (P' : Mult V' R') where
  f : R → Option R'
  hmul : ∀ r s, (f r).bind (fun a ↦ (f s).bind (fun c ↦ P'.mul a c)) = (P.mul r s).bind f
  hid : ∀ x, f (P.e x) = none ∨ ∃ x', f (P.e x) = some (P'.e x')

/-- A morphism of tables: the identities go onto the identities, each hit once. -/
structure Mor (P : Mult V R) (P' : Mult V' R') extends NMor P P' where
  hid' : ∀ x', ∃! x, f (P.e x) = some (P'.e x')

namespace NMor

variable {P : Mult V R} {P' : Mult V' R'} (m : NMor P P') (k : Type u) [CommRing k] [Nontrivial k]

/-- The induced linear map. -/
def lin : P.Lin k →ₗ[k] P'.Lin k := (P.basis k).constr k fun r ↦ (m.f r).elim 0 (P'.b k)

theorem lin_b (r : R) : m.lin k (P.b k r) = (m.f r).elim 0 (P'.b k) := by
  rw [lin, ← Mult.basis_apply, Module.Basis.constr_basis]

theorem lin_mul (x y : P.Lin k) : m.lin k (x * y) = m.lin k x * m.lin k y := by
  have h : (LinearMap.mul k (P.Lin k)).compr₂ (m.lin k) =
      (LinearMap.mul k (P'.Lin k)).compl₁₂ (m.lin k) (m.lin k) := by
    refine LinearMap.ext_basis (P.basis k) (P.basis k) fun r s ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      Mult.basis_apply, Mult.b_mul, lin_b]
    have hm := m.hmul r s
    cases hrs : P.mul r s with
    | none =>
      rw [hrs] at hm
      simp only [Option.elim_none, map_zero]
      cases hr : m.f r with
      | none => simp
      | some a =>
        rw [hr] at hm
        cases hs : m.f s with
        | none => simp
        | some c =>
          rw [hs] at hm
          simp only [Option.bind_some, Option.bind_none] at hm
          simp [Mult.b_mul, hm]
    | some t =>
      rw [hrs] at hm
      simp only [Option.elim_some, lin_b, Option.bind_some] at hm ⊢
      cases hr : m.f r with
      | none => rw [hr] at hm; simp only [Option.bind_none] at hm; rw [← hm]; simp
      | some a =>
        rw [hr] at hm
        cases hs : m.f s with
        | none => rw [hs] at hm; simp only [Option.bind_some, Option.bind_none] at hm; rw [← hm]; simp
        | some c =>
          rw [hs] at hm
          simp only [Option.bind_some] at hm
          simp [Mult.b_mul, hm]
  exact congrArg (fun B ↦ B x y) h


end NMor

namespace Mor

variable {P : Mult V R} {P' : Mult V' R'} (m : Mor P P') (k : Type u) [CommRing k] [Nontrivial k]

theorem lin_one : m.lin k 1 = 1 := by
  rw [← P.sum_b_e k, map_sum, ← P'.sum_b_e k]
  simp only [NMor.lin_b]
  choose σ hσ hσu using m.hid'
  symm
  refine Finset.sum_bij_ne_zero (fun x' _ _ ↦ σ x') (fun _ _ _ ↦ Finset.mem_univ _)
    (fun a _ _ b _ _ h ↦ ?_) (fun x _ hx ↦ ?_) (fun x' _ _ ↦ by rw [hσ x']; rfl)
  · have h1 := hσ a
    rw [h, hσ b] at h1
    have := Option.some_injective _ h1
    have := congrArg P'.src this
    rwa [P'.src_e, P'.src_e, eq_comm] at this
  · rcases m.hid x with h | ⟨x', hx'⟩
    · rw [h] at hx; exact absurd rfl hx
    · refine ⟨x', Finset.mem_univ _, ?_, ?_⟩
      · exact P'.b_ne_zero k _
      · exact (hσu x' x hx').symm

/-- **The algebra map of a table morphism.** -/
def alg : P.Lin k →ₐ[k] P'.Lin k :=
  AlgHom.ofLinearMap (m.lin k) (m.lin_one k) (m.toNMor.lin_mul k)

theorem alg_b (r : R) : m.alg k (P.b k r) = (m.f r).elim 0 (P'.b k) := m.toNMor.lin_b k r

theorem alg_surjective (hs : ∀ r', ∃ r, m.f r = some r') : Function.Surjective (m.alg k) := by
  intro y
  have : y ∈ Submodule.span k (Set.range (P'.b k)) := by rw [P'.span_b k]; trivial
  induction this using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r', rfl⟩ := hx
    obtain ⟨r, hr⟩ := hs r'
    exact ⟨P.b k r, by rw [alg_b, hr]; rfl⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨c, rfl⟩ := hy; exact ⟨a + c, map_add _ _ _⟩
  | smul c x _ hx => obtain ⟨a, rfl⟩ := hx; exact ⟨c • a, map_smul _ _ _⟩

end Mor

/-- **Representation-finiteness passes along surjective table morphisms.** -/
theorem Mor.isRepresentationFinite {P : Mult V R} {P' : Mult V' R'} (m : Mor P P') (k : Type u)
    [Field k] (hs : ∀ r', ∃ r, m.f r = some r')
    (h : IsRepresentationFinite k (P.Lin k)) : IsRepresentationFinite k (P'.Lin k) :=
  isRepresentationFinite_of_surjective (m.alg k) (m.alg_surjective k hs) h

end RaySys

end MultiplicativeBasisDeformations
