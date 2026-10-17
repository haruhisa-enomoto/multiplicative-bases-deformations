import MultiplicativeBasisDeformations.Foundations.RaySetting
import MultiplicativeBasisDeformations.Foundations.OppositeRepFinite

/-!
# The opposite ray system

The paper proves many statements together with "the dual assertion", obtained "by passing to
the opposite algebra". `Tab.op` reverses rays and products; its linearization is the opposite
algebra of `kP` (`linOpEquiv`), so it is representation-finite when `kP` is
(`isRepresentationFinite_op`); `Sys.op` carries Setting 8.4 over.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

variable {V R L : Type} [AddCommGroup L]

namespace Tab

/-- **The opposite ray table.** -/
def op (P : Tab V R L) : Tab V R L where
  src := P.tgt
  tgt := P.src
  e := P.e
  src_e := P.tgt_e
  tgt_e := P.src_e
  mul r s := P.mul s r
  mul_src r s t h := P.mul_tgt s r t h
  mul_tgt r s t h := P.mul_src s r t h
  mul_mid r s t h := (P.mul_mid s r t h).symm
  e_mul r := P.mul_e r
  mul_e r := P.e_mul r
  assoc r s u := (P.assoc u s r).symm
  wt := P.wt
  wt_mul r s t h := by rw [P.wt_mul s r t h, add_comm]
  deg := P.deg
  deg_pos r h := P.deg_pos r fun h' ↦ h (by
    change r = P.e (P.tgt r)
    rw [h', P.tgt_e])
  sep r r' h1 h2 h3 := P.sep r r' h2 h1 h3

variable (P : Tab V R L)

@[simp] theorem op_src : P.op.src = P.tgt := rfl
@[simp] theorem op_tgt : P.op.tgt = P.src := rfl
@[simp] theorem op_e : P.op.e = P.e := rfl
@[simp] theorem op_mul (r s : R) : P.op.mul r s = P.mul s r := rfl
@[simp] theorem op_wt : P.op.wt = P.wt := rfl
@[simp] theorem op_deg : P.op.deg = P.deg := rfl

theorem op_emul (a b : Elt R) : P.op.toMult.emul a b = P.toMult.emul b a := by
  cases a with
  | one => cases b <;> rfl
  | zero => cases b <;> rfl
  | ray r =>
    cases b with
    | one => rfl
    | zero => rfl
    | ray s => rw [Mult.emul_ray, Mult.emul_ray]; rfl

/-- Elements of the monoid with zero of the opposite table. -/
def toOp (a : M P.toMult) : M P.op.toMult := (a : Elt R)

theorem toOp_mul (a b : M P.toMult) : P.toOp (a * b) = P.toOp b * P.toOp a :=
  (P.op_emul b a).symm

theorem toOp_one : P.toOp 1 = 1 := rfl

theorem toOp_zero : P.toOp 0 = 0 := rfl

theorem toOp_rr (r : R) : P.toOp (P.rr r) = P.op.rr r := rfl

theorem toOp_injective : Function.Injective P.toOp := fun _ _ h ↦ h

theorem toOp_pow (a : M P.toMult) (n : ℕ) : P.toOp (a ^ n) = P.toOp a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, toOp_mul, ih, ← pow_succ']

theorem toOp_eq_zero {a : M P.toMult} : P.toOp a = 0 ↔ a = 0 := Iff.rfl

end Tab

namespace Tab

variable [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] (P : Tab V R L)
  (k : Type u) [Field k]

/-- The linear identification of `k(P^op)` with `kP`. -/
def linOpL : P.op.Lin k ≃ₗ[k] (P.Lin k)ᵐᵒᵖ :=
  ((P.op.toMult.basis k).equiv (P.toMult.basis k) (Equiv.refl R)).trans
    (MulOpposite.opLinearEquiv k)

theorem linOpL_b (r : R) : P.linOpL k (P.op.b k r) = MulOpposite.op (P.b k r) := by
  simp [linOpL, ← Mult.basis_apply, Module.Basis.equiv_apply]

theorem linOpL_mul (x y : P.op.Lin k) : P.linOpL k (x * y) = P.linOpL k x * P.linOpL k y := by
  have h : (LinearMap.mul k _).compr₂ (P.linOpL k).toLinearMap =
      (LinearMap.mul k _).compl₁₂ (P.linOpL k).toLinearMap (P.linOpL k).toLinearMap := by
    refine LinearMap.ext_basis (P.op.toMult.basis k) (P.op.toMult.basis k) fun r s ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe, Mult.basis_apply, linOpL_b, Mult.b_mul, ← MulOpposite.op_mul]
    change P.linOpL k ((P.mul s r).elim 0 (P.op.b k)) = MulOpposite.op ((P.mul s r).elim 0 (P.b k))
    cases P.mul s r with
    | none => simp
    | some t => simp [linOpL_b]
  exact congrArg (fun B ↦ B x y) h

theorem linOpL_one : P.linOpL k 1 = 1 := by
  rw [← P.op.sum_b_e k, map_sum]
  simp only [linOpL_b]
  have := map_sum (MulOpposite.opAddEquiv : P.Lin k ≃+ (P.Lin k)ᵐᵒᵖ) (fun x ↦ P.b k (P.e x))
    Finset.univ
  simp only [MulOpposite.opAddEquiv_apply] at this
  change ∑ x, MulOpposite.op (P.b k (P.e x)) = 1
  rw [← this, P.sum_b_e k]; rfl

/-- **The linearization of the opposite table is the opposite algebra.** -/
def linOpEquiv : P.op.Lin k ≃ₐ[k] (P.Lin k)ᵐᵒᵖ :=
  AlgEquiv.ofLinearEquiv (P.linOpL k) (P.linOpL_one k) (P.linOpL_mul k)

/-- **The opposite table is representation-finite with `kP`.** -/
theorem op_isRepresentationFinite (h : IsRepresentationFinite k (P.Lin k)) :
    IsRepresentationFinite k (P.op.Lin k) :=
  isRepresentationFinite_of_algEquiv (P.linOpEquiv k).symm (isRepresentationFinite_op h)

end Tab

namespace Sys

variable [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]

theorem toOp_mul3 (P : Tab V R L) (a b c : M P.toMult) :
    P.toOp (a * b * c) = P.toOp c * P.toOp b * P.toOp a := by
  rw [Tab.toOp_mul, Tab.toOp_mul, mul_assoc]

/-- **The opposite ray system** (Setting 8.4 for `A₀ᵒᵖ`). -/
@[reducible] def op (S : Sys V R L) : Sys V R L where
  P := S.P.op
  q x := S.P.toOp (S.q x)
  q_cases x := by
    rcases S.q_cases x with h | ⟨g, hg, h1, h2, h3⟩
    · left; rw [h]; rfl
    · right; exact ⟨g, by rw [hg]; rfl, h2, h1, h3⟩
  q_pow r h := by
    obtain ⟨j, hj⟩ := S.q_pow r h.symm
    refine ⟨j, ?_⟩
    change S.P.toOp (S.q (S.P.tgt r)) ^ j * S.P.toOp (S.P.rr (S.P.e (S.P.tgt r))) = S.P.toOp (S.P.rr r)
    have h' : S.P.tgt r = S.P.src r := h
    rw [← Tab.toOp_pow, ← Tab.toOp_mul, h', ← S.qpow_comm_e, hj]
  cyc r := by
    rcases S.cyc r with h | h
    · right
      intro i j hne
      have hne' : S.q (S.P.src r) ^ j * S.P.rr r * S.q (S.P.tgt r) ^ i ≠ 0 := by
        intro h0; apply hne
        change S.P.toOp (S.q (S.P.tgt r)) ^ i * S.P.toOp (S.P.rr r) *
          S.P.toOp (S.q (S.P.src r)) ^ j = 0
        rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3, h0]; rfl
      obtain ⟨i', hi'⟩ := h j i hne'
      refine ⟨i', ?_⟩
      change S.P.toOp (S.q (S.P.tgt r)) ^ i * S.P.toOp (S.P.rr r) * S.P.toOp (S.q (S.P.src r)) ^ j =
        S.P.toOp (S.P.rr r) * S.P.toOp (S.q (S.P.src r)) ^ i'
      rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3, ← Tab.toOp_mul, hi']
    · left
      intro i j hne
      have hne' : S.q (S.P.src r) ^ j * S.P.rr r * S.q (S.P.tgt r) ^ i ≠ 0 := by
        intro h0; apply hne
        change S.P.toOp (S.q (S.P.tgt r)) ^ i * S.P.toOp (S.P.rr r) *
          S.P.toOp (S.q (S.P.src r)) ^ j = 0
        rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3, h0]; rfl
      obtain ⟨j', hj'⟩ := h j i hne'
      refine ⟨j', ?_⟩
      change S.P.toOp (S.q (S.P.tgt r)) ^ i * S.P.toOp (S.P.rr r) * S.P.toOp (S.q (S.P.src r)) ^ j =
        S.P.toOp (S.q (S.P.tgt r)) ^ j' * S.P.toOp (S.P.rr r)
      rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3, ← Tab.toOp_mul, hj']
  chain r s h1 h2 := by
    rcases S.chain r s h2 h1 with ⟨i, j, h⟩ | ⟨i, j, h⟩
    · left
      refine ⟨j, i, ?_⟩
      change S.P.toOp (S.P.rr r) = S.P.toOp (S.q (S.P.tgt r)) ^ j * S.P.toOp (S.P.rr s) *
        S.P.toOp (S.q (S.P.src r)) ^ i
      rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3, h]
    · right
      refine ⟨j, i, ?_⟩
      change S.P.toOp (S.P.rr s) = S.P.toOp (S.q (S.P.tgt r)) ^ j * S.P.toOp (S.P.rr r) *
        S.P.toOp (S.q (S.P.src r)) ^ i
      rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3, h]

variable (S : Sys V R L)

theorem op_rr (r : R) : S.op.rr r = S.P.toOp (S.rr r) := rfl

theorem op_q (x : V) : S.op.q x = S.P.toOp (S.q x) := rfl

theorem op_P : S.op.P = S.P.op := rfl

theorem op_wtM (a : M S.P.toMult) : S.op.wtM (S.P.toOp a) = S.wtM a := by
  cases a <;> rfl

theorem op_χ (x : V) : S.op.χ x = S.χ x := S.op_wtM (S.q x)

theorem op_cycL_iff (f : R) : S.op.CycL f ↔ S.CycR f := by
  constructor
  · intro h s h1 h2
    obtain ⟨i, hi⟩ := h s h2 h1
    refine ⟨i, ?_⟩
    apply S.P.toOp_injective
    change S.op.rr s = _ at hi
    rw [op_rr, op_q] at hi
    rw [Tab.toOp_mul, Tab.toOp_pow, hi]; rfl
  · intro h s h1 h2
    obtain ⟨j, hj⟩ := h s h2 h1
    refine ⟨j, ?_⟩
    show S.P.toOp (S.rr s) = S.P.toOp (S.q (S.P.tgt f)) ^ j * S.P.toOp (S.rr f)
    rw [← Tab.toOp_pow, ← Tab.toOp_mul]
    exact congrArg S.P.toOp hj

theorem op_cycR_iff (f : R) : S.op.CycR f ↔ S.CycL f := by
  constructor
  · intro h s h1 h2
    obtain ⟨j, hj⟩ := h s h2 h1
    refine ⟨j, ?_⟩
    apply S.P.toOp_injective
    change S.op.rr s = _ at hj
    rw [op_rr, op_q] at hj
    rw [Tab.toOp_mul, Tab.toOp_pow, hj]; rfl
  · intro h s h1 h2
    obtain ⟨i, hi⟩ := h s h2 h1
    refine ⟨i, ?_⟩
    show S.P.toOp (S.rr s) = S.P.toOp (S.rr f) * S.P.toOp (S.q (S.P.src f)) ^ i
    rw [← Tab.toOp_pow, ← Tab.toOp_mul]
    exact congrArg S.P.toOp hi

theorem op_inU_iff (s r : R) : S.op.InU s r ↔ S.InU s r := by
  constructor
  · rintro ⟨i, j, h⟩
    refine ⟨j, i, S.P.toOp_injective ?_⟩
    change S.op.rr s = S.op.q (S.P.op.src r) ^ i * S.op.rr r * S.op.q (S.P.op.tgt r) ^ j at h
    rw [op_rr, op_rr, op_q, op_q] at h
    rw [toOp_mul3, Tab.toOp_pow, Tab.toOp_pow, h]; rfl
  · rintro ⟨i, j, h⟩
    refine ⟨j, i, ?_⟩
    show S.P.toOp (S.rr s) = S.P.toOp (S.q (S.P.tgt r)) ^ j * S.P.toOp (S.rr r) *
      S.P.toOp (S.q (S.P.src r)) ^ i
    rw [← Tab.toOp_pow, ← Tab.toOp_pow, ← toOp_mul3]
    exact congrArg S.P.toOp h

theorem op_isGen_iff (f : R) : S.op.IsGen f ↔ S.IsGen f := by
  constructor
  · intro h s h1 h2; exact (S.op_inU_iff s f).1 (h s h2 h1)
  · intro h s h1 h2; exact (S.op_inU_iff s f).2 (h s h2 h1)

theorem op_rf_iff (r s : R) : S.P.op.RF r s ↔ S.P.LF s r := Iff.rfl

theorem op_lf_iff (r s : R) : S.P.op.LF r s ↔ S.P.RF s r := Iff.rfl

end Sys

end RaySys

end MultiplicativeBasisDeformations
