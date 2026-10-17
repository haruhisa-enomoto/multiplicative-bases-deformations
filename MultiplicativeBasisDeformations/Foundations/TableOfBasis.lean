import MultiplicativeBasisDeformations.Foundations.TableAlg
import MultiplicativeBasisDeformations.Foundations.NormedBasis

/-!
# The multiplication table of a multiplicative basis

For an algebra `Λ` with a multiplicative basis `b` containing a complete set of orthogonal
idempotents `b (E v)`, every basis vector lying in one corner, the products of basis vectors
define a ray table (`multOfBasis`): the table of Construction 3.? / Definition 3.9(2) read
off from the basis (`projective-rays.tex:276–305`, "`b_r b_s = b_{rs}` or `0`"). Its
associativity comes from that of `Λ`, and its linearization is isomorphic to `Λ`
(`linEquiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace OfBasis

variable {k : Type u} [Field k] {Λ : Type u} [Ring Λ] [Algebra k Λ]
  {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  (b : Module.Basis R k Λ) (hmul : IsMultiplicativeBasis b) (E : V → R)
  (hE : CompleteOrthogonalIdempotents fun v ↦ b (E v)) (src tgt : R → V)
  (hcor : ∀ r, b (E (src r)) * b r * b (E (tgt r)) = b r)
  (hEs : ∀ v, src (E v) = v) (hEt : ∀ v, tgt (E v) = v)

open Classical in
/-- The product of two basis indices. -/
def mulB (r s : R) : Option R := if h : ∃ t, b r * b s = b t then some h.choose else none

include hmul in
theorem b_mul_b (r s : R) : b r * b s = (mulB b r s).elim 0 b := by
  classical
  unfold mulB
  split_ifs with h
  · exact h.choose_spec
  · exact (hmul r s).resolve_right h

theorem mulB_eq_some {r s t : R} : mulB b r s = some t ↔ b r * b s = b t := by
  classical
  unfold mulB
  split_ifs with h
  · rw [Option.some_inj]
    exact ⟨fun e ↦ e ▸ h.choose_spec, fun e ↦ b.injective (h.choose_spec.symm.trans e)⟩
  · simp only [reduceCtorEq, false_iff]
    exact fun e ↦ h ⟨t, e⟩

include hcor hE in
theorem e_mul_b (r : R) : b (E (src r)) * b r = b r := by
  conv_lhs => rw [← hcor r]
  rw [← mul_assoc, ← mul_assoc, (hE.idem (src r)).eq, hcor]

include hcor hE in
theorem b_mul_e (r : R) : b r * b (E (tgt r)) = b r := by
  conv_lhs => rw [← hcor r]
  rw [mul_assoc, (hE.idem (tgt r)).eq, hcor]

include hcor hE in
theorem src_of_mul {r s t : R} (h : b r * b s = b t) : src t = src r := by
  by_contra hne
  apply b.ne_zero t
  calc b t = b (E (src t)) * b t := (e_mul_b b E hE src tgt hcor t).symm
    _ = b (E (src t)) * (b (E (src r)) * b r * b s) := by rw [e_mul_b b E hE src tgt hcor r, h]
    _ = 0 := by rw [← mul_assoc, ← mul_assoc, hE.ortho hne, zero_mul, zero_mul]

include hcor hE in
theorem tgt_of_mul {r s t : R} (h : b r * b s = b t) : tgt t = tgt s := by
  by_contra hne
  apply b.ne_zero t
  rw [← b_mul_e b E hE src tgt hcor t, ← h, mul_assoc, ← b_mul_e b E hE src tgt hcor s, mul_assoc,
    hE.ortho (Ne.symm hne), mul_zero, mul_zero]

include hcor hE in
theorem mid_of_mul {r s t : R} (h : b r * b s = b t) : tgt r = src s := by
  by_contra hne
  apply b.ne_zero t
  rw [← h, ← b_mul_e b E hE src tgt hcor r, ← e_mul_b b E hE src tgt hcor s, mul_assoc,
    ← mul_assoc (b (E (tgt r))), hE.ortho hne, zero_mul, mul_zero]

include hmul in
theorem elim_mul (o : Option R) (u : R) :
    o.elim 0 b * b u = (o.bind fun t ↦ mulB b t u).elim 0 b := by
  cases o with
  | none => simp
  | some t => simp only [Option.elim_some, Option.bind_some]; exact b_mul_b b hmul t u

include hmul in
theorem mul_elim (r : R) (o : Option R) :
    b r * o.elim 0 b = (o.bind fun t ↦ mulB b r t).elim 0 b := by
  cases o with
  | none => simp
  | some t => simp only [Option.elim_some, Option.bind_some]; exact b_mul_b b hmul r t

theorem elim_injective {o o' : Option R} (h : o.elim 0 b = o'.elim (0 : Λ) b) : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some t => exact absurd h.symm (b.ne_zero t)
  | some t =>
    cases o' with
    | none => exact absurd h (b.ne_zero t)
    | some t' => exact congrArg some (b.injective h)

include hmul in
theorem assocB (r s u : R) :
    (mulB b r s).bind (fun t ↦ mulB b t u) = (mulB b s u).bind (fun t ↦ mulB b r t) := by
  apply elim_injective b
  rw [← elim_mul b hmul, ← mul_elim b hmul, ← b_mul_b b hmul, ← b_mul_b b hmul, mul_assoc]

/-- **The multiplication table of the basis.** -/
def multOfBasis : Mult V R where
  src := src
  tgt := tgt
  e := E
  src_e := hEs
  tgt_e := hEt
  mul := mulB b
  mul_src _ _ _ h := src_of_mul b E hE src tgt hcor ((mulB_eq_some b).1 h)
  mul_tgt _ _ _ h := tgt_of_mul b E hE src tgt hcor ((mulB_eq_some b).1 h)
  mul_mid _ _ _ h := mid_of_mul b E hE src tgt hcor ((mulB_eq_some b).1 h)
  e_mul r := (mulB_eq_some b).2 (e_mul_b b E hE src tgt hcor r)
  mul_e r := (mulB_eq_some b).2 (b_mul_e b E hE src tgt hcor r)
  assoc := assocB b hmul

/-- The basis equivalence `kP ≃ Λ`. -/
def linLin : (multOfBasis b hmul E hE src tgt hcor hEs hEt).Lin k ≃ₗ[k] Λ :=
  ((multOfBasis b hmul E hE src tgt hcor hEs hEt).basis k).equiv b (Equiv.refl R)

theorem linLin_b (r : R) :
    linLin b hmul E hE src tgt hcor hEs hEt ((multOfBasis b hmul E hE src tgt hcor hEs hEt).b k r) =
      b r := by
  rw [linLin, ← Mult.basis_apply, Module.Basis.equiv_apply, Equiv.refl_apply]

theorem linLin_mul (x y : (multOfBasis b hmul E hE src tgt hcor hEs hEt).Lin k) :
    linLin b hmul E hE src tgt hcor hEs hEt (x * y) =
      linLin b hmul E hE src tgt hcor hEs hEt x * linLin b hmul E hE src tgt hcor hEs hEt y := by
  have key : ∀ r s, linLin b hmul E hE src tgt hcor hEs hEt
      ((multOfBasis b hmul E hE src tgt hcor hEs hEt).b k r *
        (multOfBasis b hmul E hE src tgt hcor hEs hEt).b k s) =
      b r * b s := by
    intro r s
    rw [Mult.b_mul, b_mul_b b hmul]
    show linLin b hmul E hE src tgt hcor hEs hEt ((mulB b r s).elim 0
      ((multOfBasis b hmul E hE src tgt hcor hEs hEt).b k)) = (mulB b r s).elim 0 b
    cases mulB b r s with
    | none => simp
    | some t => simp only [Option.elim_some, linLin_b]
  have hspan : ∀ z : (multOfBasis b hmul E hE src tgt hcor hEs hEt).Lin k,
      z ∈ Submodule.span k (Set.range ((multOfBasis b hmul E hE src tgt hcor hEs hEt).b k)) :=
    fun z ↦ by rw [Mult.span_b]; trivial
  have hy : ∀ r, linLin b hmul E hE src tgt hcor hEs hEt
      ((multOfBasis b hmul E hE src tgt hcor hEs hEt).b k r * y) =
      b r * linLin b hmul E hE src tgt hcor hEs hEt y := by
    intro r
    induction hspan y using Submodule.span_induction with
    | mem z hz => obtain ⟨s, rfl⟩ := hz; rw [key, linLin_b]
    | zero => simp
    | add z z' _ _ h1 h2 => rw [mul_add, map_add, h1, h2, map_add, mul_add]
    | smul t z _ h => rw [mul_smul_comm, map_smul, h, map_smul, mul_smul_comm]
  induction hspan x using Submodule.span_induction with
  | mem z hz => obtain ⟨r, rfl⟩ := hz; rw [hy, linLin_b]
  | zero => simp
  | add z z' _ _ h1 h2 => rw [add_mul, map_add, h1, h2, map_add, add_mul]
  | smul t z _ h => rw [smul_mul_assoc, map_smul, h, map_smul, smul_mul_assoc]

/-- **The linearization of the table is `Λ`.** -/
def linEquiv : (multOfBasis b hmul E hE src tgt hcor hEs hEt).Lin k ≃ₐ[k] Λ :=
  AlgEquiv.ofLinearEquiv (linLin b hmul E hE src tgt hcor hEs hEt) (by
      rw [← Mult.sum_b_e, map_sum, ← hE.complete]
      exact Finset.sum_congr rfl fun v _ ↦ linLin_b b hmul E hE src tgt hcor hEs hEt _)
    (linLin_mul b hmul E hE src tgt hcor hEs hEt)

theorem linEquiv_b (r : R) :
    linEquiv b hmul E hE src tgt hcor hEs hEt
      ((multOfBasis b hmul E hE src tgt hcor hEs hEt).b k r) = b r :=
  linLin_b b hmul E hE src tgt hcor hEs hEt r

end OfBasis


end RaySys

end MultiplicativeBasisDeformations
