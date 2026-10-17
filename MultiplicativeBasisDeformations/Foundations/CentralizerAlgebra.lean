import MultiplicativeBasisDeformations.Foundations.TableInduction

/-!
# Lemma 9.2 as stated: `B_χ = C_χ/𝔞_χ ≅ kQ_χ`

`integral-partial-lifts.tex:52–113` (`lem:centralizer-ray-algebra`). Put `q̂ = ∑_x q̂_x`,
`C_χ = Cent_{A₀}(q̂)`, `𝔞_χ = {c ∈ C_χ : q̂c = 0}` and `B_χ = C_χ/𝔞_χ`. "The algebra `B_χ` is
basic and representation-finite. Its basis consists of the supporting identities and the
two-sided rays of `A₀`, and its products define a weighted multiplication table `Q_χ` ...
Thus `B_χ = kQ_χ`. If `B_χ ≠ 0`, it has strictly fewer nonzero basis labels than `P`."

`CentralizerTable.lean` builds the tables `Tc` and `Q_χ` and proves the representation
finiteness and the count. Here the algebras themselves: `q̂ b_r = b_{r⁺}` or `0`, and likewise
on the right (`qhat_mul_b_cases`, `b_mul_qhat_cases`), so the commutator of `q̂` with a ray is
`±b_{r⁺}` exactly for one-sided rays (`comm_b`); successors of distinct rays are distinct
(`succ_inj`). Hence `C_χ` is spanned by the identities, two-sided and unshiftable rays
(`mem_Cχ_iff`, `Cχ_eq_range`), `𝔞_χ` by the unshiftable nonidentity rays and the identities at
`q̂_x = 0` (`mem_aχ_iff`), and the quotient map `C_χ → kQ_χ` induces `B_χ ≅ kQ_χ`
(`Bχ_equiv`, `centralizerRayAlgebra`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

/-- Basic algebras are invariant under ring isomorphisms. -/
theorem IsBasicAlgebra.of_ringEquiv {A B : Type*} [Ring A] [Ring B] (f : A ≃+* B)
    (h : IsBasicAlgebra A) : IsBasicAlgebra B := by
  obtain ⟨n, e, hc, hp, hiso⟩ := h
  refine ⟨n, f ∘ e, hc.map (f : A →+* B), fun i ↦ ?_, fun i j ⟨x, y, h1, h2, h3, h4⟩ ↦ ?_⟩
  · obtain ⟨hi, hne, hmin⟩ := hp i
    refine ⟨hi.map f, by simpa using hne, fun g hg h1 h2 ↦ ?_⟩
    have hg' : IsIdempotentElem (f.symm g) := hg.map f.symm
    rcases hmin (f.symm g) hg' (f.injective (by simpa using h1))
      (f.injective (by simpa using h2)) with h | h
    · left; simpa using congrArg f h
    · right; simpa using congrArg f h
  · apply hiso i j
    refine ⟨f.symm x, f.symm y, f.injective ?_, f.injective ?_, f.injective ?_, f.injective ?_⟩ <;>
      simpa using ‹_›

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

variable {χ : L}

/-! ### Successors -/

/-- A ray with the endpoints of `r` and weight `ℓ(r) + χ` exists. -/
def HasSucc (χ : L) (r : R) : Prop :=
  ∃ r', S.P.src r' = S.P.src r ∧ S.P.tgt r' = S.P.tgt r ∧ S.P.wt r' = S.P.wt r + χ

theorem succ_spec' {r : R} (h : S.HasSucc χ r) : S.P.src (S.succ χ r) = S.P.src r ∧
    S.P.tgt (S.succ χ r) = S.P.tgt r ∧ S.P.wt (S.succ χ r) = S.P.wt r + χ := by
  classical
  have h' : ∃ r', S.P.src r' = S.P.src r ∧ S.P.tgt r' = S.P.tgt r ∧ S.P.wt r' = S.P.wt r + χ := h
  rw [succ, dif_pos h']
  exact h'.choose_spec

/-- **Distinct rays have distinct successors.** -/
theorem succ_inj {r r' : R} (h : S.HasSucc χ r) (h' : S.HasSucc χ r')
    (e : S.succ χ r = S.succ χ r') : r = r' := by
  obtain ⟨a1, a2, a3⟩ := S.succ_spec' h
  obtain ⟨b1, b2, b3⟩ := S.succ_spec' h'
  rw [e] at a1 a2 a3
  exact S.P.sep _ _ (a1.symm.trans b1) (a2.symm.trans b2)
    (add_right_cancel (a3.symm.trans b3))

theorem qh_loop (x : V) :
    S.qh χ x = 0 ∨ ∃ g, S.qh χ x = ⌜g⌝ ∧ S.P.src g = x ∧ S.P.tgt g = x ∧ S.P.wt g = χ := by
  classical
  by_cases hs : S.Supp χ x
  · rw [S.qh_of_supp χ hs]
    rcases S.q_cases x with h | ⟨g, hg, h1, h2, -⟩
    · exact Or.inl h
    · refine Or.inr ⟨g, hg, h1, h2, ?_⟩
      have := hs.2
      change S.wtM (S.q x) = χ at this
      rw [hg] at this
      exact this
  · exact Or.inl (S.qh_of_not_supp χ hs)

theorem qh_mul_of_ne {x : V} {r : R} (h : x ≠ S.P.src r) : S.qh χ x * ⌜r⌝ = 0 := by
  rcases S.qh_loop x with h0 | ⟨g, hg, -, h2, -⟩
  · rw [h0, zero_mul]
  · rw [hg]; exact S.P.rr_mul_rr_eq_zero_of_ne (by rw [h2]; exact h)

theorem mul_qh_of_ne {x : V} {r : R} (h : x ≠ S.P.tgt r) : ⌜r⌝ * S.qh χ x = 0 := by
  rcases S.qh_loop x with h0 | ⟨g, hg, h1, -, -⟩
  · rw [h0, mul_zero]
  · rw [hg]; exact S.P.rr_mul_rr_eq_zero_of_ne (by rw [h1]; exact Ne.symm h)

/-- `q̂_x r` is zero or the successor of `r`. -/
theorem qh_mul_eq (r : R) : S.qh χ (S.P.src r) * ⌜r⌝ = 0 ∨
    (S.HasSucc χ r ∧ S.qh χ (S.P.src r) * ⌜r⌝ = ⌜S.succ χ r⌝) := by
  by_cases h0 : S.qh χ (S.P.src r) * ⌜r⌝ = 0
  · exact Or.inl h0
  right
  rcases S.qh_loop (S.P.src r) with hq | ⟨g, hg, g1, g2, g3⟩
  · exact absurd (by rw [hq, zero_mul]) h0
  rw [hg] at h0 ⊢
  obtain ⟨t, ht⟩ := S.ray_of_mul_ne h0
  obtain ⟨t1, t2, -, t4⟩ := S.prod_of ht
  have hs : S.HasSucc χ r := ⟨t, by rw [t1, g1], t2, by rw [t4, g3, add_comm]⟩
  obtain ⟨e1, e2, e3⟩ := S.succ_spec' hs
  refine ⟨hs, ?_⟩
  rw [ht, S.P.sep t (S.succ χ r) (by rw [t1, g1, e1]) (by rw [t2, e2])
    (by rw [t4, g3, e3, add_comm])]

/-- `r q̂_y` is zero or the successor of `r`. -/
theorem mul_qh_eq (r : R) : ⌜r⌝ * S.qh χ (S.P.tgt r) = 0 ∨
    (S.HasSucc χ r ∧ ⌜r⌝ * S.qh χ (S.P.tgt r) = ⌜S.succ χ r⌝) := by
  by_cases h0 : ⌜r⌝ * S.qh χ (S.P.tgt r) = 0
  · exact Or.inl h0
  right
  rcases S.qh_loop (S.P.tgt r) with hq | ⟨g, hg, g1, g2, g3⟩
  · exact absurd (by rw [hq, mul_zero]) h0
  rw [hg] at h0 ⊢
  obtain ⟨t, ht⟩ := S.ray_of_mul_ne h0
  obtain ⟨t1, t2, -, t4⟩ := S.prod_of ht
  have hs : S.HasSucc χ r := ⟨t, t1, by rw [t2, g2], by rw [t4, g3]⟩
  obtain ⟨e1, e2, e3⟩ := S.succ_spec' hs
  refine ⟨hs, ?_⟩
  rw [ht, S.P.sep t (S.succ χ r) (by rw [t1, e1]) (by rw [t2, g2, e2]) (by rw [t4, g3, e3])]

/-! ### The actions of `q̂` on rays -/

/-- The left action of `q̂` survives on `r`. -/
def Lq (χ : L) (r : R) : Prop := S.qh χ (S.P.src r) * ⌜r⌝ ≠ 0

/-- The right action of `q̂` survives on `r`. -/
def Rq (χ : L) (r : R) : Prop := ⌜r⌝ * S.qh χ (S.P.tgt r) ≠ 0

theorem e_mul_qh (x : V) : ⌜S.P.e x⌝ * S.qh χ x = S.qh χ x := by
  rcases S.qh_loop x with h | ⟨g, hg, g1, -, -⟩
  · rw [h, mul_zero]
  · rw [hg]; exact S.e_mul_rr' g g1

theorem qh_mul_e (x : V) : S.qh χ x * ⌜S.P.e x⌝ = S.qh χ x := by
  rcases S.qh_loop x with h | ⟨g, hg, -, g2, -⟩
  · rw [h, zero_mul]
  · rw [hg, ← g2]; exact S.rr_mul_e g

/-- **Both actions agree on the centralizer rays, and differ on the others.** -/
theorem lq_iff_rq (hχ : 0 < S.P.deg χ) (hprim : Prim χ) (r : R) :
    S.InC χ r ↔ (S.Lq χ r ↔ S.Rq χ r) := by
  constructor
  · rintro (hB | hn)
    · exact ⟨fun _ ↦ hB.2.2, fun _ ↦ hB.2.1⟩
    · by_cases he : r = S.P.e (S.P.src r)
      · unfold Lq Rq
        rw [he, S.P.src_e, S.P.tgt_e, S.e_mul_qh, S.qh_mul_e]
      · have hL : ¬ S.Lq χ r := fun h ↦ hn (S.shift_of_qh_mul he h).1
        have hR : ¬ S.Rq χ r := fun h ↦ hn (S.shift_of_mul_qh he h).1
        exact ⟨fun h ↦ absurd h hL, fun h ↦ absurd h hR⟩
  · intro h
    by_cases hs : S.Shift χ r
    · rcases S.types_of_shift hχ hprim hs with hT | hT | hT
      · exact absurd ((h.1 hT.2.1)) (not_not.2 hT.2.2)
      · exact absurd ((h.2 hT.2.2)) (not_not.2 hT.2.1)
      · exact Or.inl hT
    · exact Or.inr hs

/-- On the centralizer rays, the left action survives exactly on the rays of `Q_χ`. -/
theorem lq_iff_inQ {r : R} (hr : S.InC χ r) : S.Lq χ r ↔ S.InQ χ r := by
  constructor
  · intro hL
    rcases hr with hB | hn
    · exact Or.inl hB
    · by_cases he : r = S.P.e (S.P.src r)
      · refine Or.inr ⟨he, S.supp_of_qh hL⟩
      · exact absurd (S.shift_of_qh_mul he hL).1 hn
  · rintro (hB | ⟨he, hs⟩)
    · exact hB.2.1
    · unfold Lq
      rw [he, S.P.src_e, S.qh_mul_e, S.qh_of_supp χ hs]
      exact hs.1

variable (k : Type u) [Field k]

/-! ### Elements of `kP` -/

/-- Elements of the monoid with zero as elements of `kP`. -/
def toLin : M S.P.toMult → S.P.Lin k
  | Elt.one => 1
  | Elt.zero => 0
  | Elt.ray r => S.P.b k r

@[simp] theorem toLin_one : S.toLin k 1 = 1 := rfl
@[simp] theorem toLin_zero : S.toLin k 0 = 0 := rfl
@[simp] theorem toLin_rr (r : R) : S.toLin k ⌜r⌝ = S.P.b k r := rfl

theorem toLin_mul (a b : M S.P.toMult) : S.toLin k (a * b) = S.toLin k a * S.toLin k b := by
  rcases S.elt_cases a with rfl | rfl | ⟨r, rfl⟩
  · rw [one_mul, toLin_one, one_mul]
  · rw [zero_mul, toLin_zero, zero_mul]
  rcases S.elt_cases b with rfl | rfl | ⟨s, rfl⟩
  · rw [mul_one, toLin_one, mul_one]
  · rw [mul_zero, toLin_zero, mul_zero]
  rw [toLin_rr, toLin_rr, Mult.b_mul]
  rcases S.rr_mul_rr_cases r s with h | ⟨t, h⟩
  · have h' : S.P.mul r s = none := by
      by_contra hn
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hn
      exact S.rr_ne t ((S.P.rr_mul_rr_eq_rr.2 ht).symm.trans h)
    rw [h, h']; rfl
  · rw [h, S.P.rr_mul_rr_eq_rr.1 h]; rfl

/-- `q̂ = ∑_x q̂_x`. -/
def qhat (χ : L) : S.P.Lin k := ∑ x, S.toLin k (S.qh χ x)

theorem qhat_mul_b (r : R) : S.qhat k χ * S.P.b k r = S.toLin k (S.qh χ (S.P.src r) * ⌜r⌝) := by
  rw [qhat, Finset.sum_mul, Finset.sum_eq_single (S.P.src r)]
  · rw [toLin_mul]; rfl
  · intro x _ hx; rw [← toLin_rr, ← toLin_mul, S.qh_mul_of_ne hx, toLin_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem b_mul_qhat (r : R) : S.P.b k r * S.qhat k χ = S.toLin k (⌜r⌝ * S.qh χ (S.P.tgt r)) := by
  rw [qhat, Finset.mul_sum, Finset.sum_eq_single (S.P.tgt r)]
  · rw [toLin_mul]; rfl
  · intro x _ hx; rw [← toLin_rr, ← toLin_mul, S.mul_qh_of_ne hx, toLin_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

open Classical in
theorem qhat_mul_b' (r : R) :
    S.qhat k χ * S.P.b k r = if S.Lq χ r then S.P.b k (S.succ χ r) else 0 := by
  rw [qhat_mul_b]
  rcases S.qh_mul_eq r with h | ⟨-, h⟩
  · rw [h, if_neg (show ¬ S.Lq χ r from not_not.2 h)]; rfl
  · rw [h, if_pos (by unfold Lq; rw [h]; exact S.rr_ne _)]; rfl

open Classical in
theorem b_mul_qhat' (r : R) :
    S.P.b k r * S.qhat k χ = if S.Rq χ r then S.P.b k (S.succ χ r) else 0 := by
  rw [b_mul_qhat]
  rcases S.mul_qh_eq r with h | ⟨-, h⟩
  · rw [h, if_neg (show ¬ S.Rq χ r from not_not.2 h)]; rfl
  · rw [h, if_pos (by unfold Rq; rw [h]; exact S.rr_ne _)]; rfl

theorem hasSucc_of_lq {r : R} (h : S.Lq χ r) : S.HasSucc χ r :=
  ((S.qh_mul_eq r).resolve_left h).1

theorem hasSucc_of_rq {r : R} (h : S.Rq χ r) : S.HasSucc χ r :=
  ((S.mul_qh_eq r).resolve_left h).1

/-- **Coefficients of a combination of successors.** -/
theorem sum_succ_eq_zero_iff (p : R → Prop) [DecidablePred p] (hp : ∀ r, p r → S.HasSucc χ r) (a : R → k) :
    ∑ r, (if p r then a r • S.P.b k (S.succ χ r) else 0) = 0 ↔ ∀ r, p r → a r = 0 := by
  constructor
  · intro h r0 hr0
    have := congrArg (fun z ↦ (S.P.basis k).repr z (S.succ χ r0)) h
    simp only [map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.finsetSum_apply] at this
    rw [Finset.sum_eq_single r0] at this
    · rw [if_pos hr0, map_smul, Finsupp.smul_apply, Mult.basis_repr_b, if_pos rfl,
        smul_eq_mul, mul_one] at this
      exact this
    · intro r _ hr
      split_ifs with hpr
      · rw [map_smul, Finsupp.smul_apply, Mult.basis_repr_b,
          if_neg (fun e ↦ hr (S.succ_inj (hp r hpr) (hp r0 hr0) e)), smul_zero]
      · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro h
    exact Finset.sum_eq_zero fun r _ ↦ by
      split_ifs with hpr
      · rw [h r hpr, zero_smul]
      · rfl

/-! ### The centralizer and the ideal -/

/-- `C_χ = Cent_{A₀}(q̂)`. -/
def Cχ (χ : L) : Subalgebra k (S.P.Lin k) := Subalgebra.centralizer k {S.qhat k χ}

/-- A shortcut: instance search through the matrix algebra is slow. -/
instance (χ : L) : Ring (S.Cχ k χ) := Subalgebra.toRing _

theorem mem_Cχ (c : S.P.Lin k) : c ∈ S.Cχ k χ ↔ S.qhat k χ * c = c * S.qhat k χ := by
  rw [Cχ, Subalgebra.mem_centralizer_iff]
  simp

theorem sum_repr (c : S.P.Lin k) : ∑ r, (S.P.basis k).repr c r • S.P.b k r = c := by
  conv_rhs => rw [← (S.P.basis k).sum_repr c]
  simp only [Mult.basis_apply]

/-- **`C_χ` is spanned by the identities, the two-sided rays and the unshiftable rays.** -/
theorem mem_Cχ_iff (hχ : 0 < S.P.deg χ) (hprim : Prim χ) (c : S.P.Lin k) :
    c ∈ S.Cχ k χ ↔ ∀ r, ¬ S.InC χ r → (S.P.basis k).repr c r = 0 := by
  classical
  rw [mem_Cχ, ← sub_eq_zero]
  set a := fun r ↦ (S.P.basis k).repr c r
  have key : S.qhat k χ * c - c * S.qhat k χ =
      ∑ r, (if ¬ S.InC χ r then (if S.Lq χ r then a r else -a r) • S.P.b k (S.succ χ r)
        else 0) := by
    conv_lhs => rw [← S.sum_repr k c]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, qhat_mul_b', b_mul_qhat']
    have hc := S.lq_iff_rq hχ hprim r
    by_cases hL : S.Lq χ r <;> by_cases hR : S.Rq χ r
    · rw [if_pos hL, if_pos hR, sub_self, smul_zero, if_neg (not_not.2 (hc.2 (iff_of_true hL hR)))]
    · rw [if_pos hL, if_neg hR, sub_zero, if_pos (fun h ↦ hR ((hc.1 h).1 hL)), if_pos hL]
    · rw [if_neg hL, if_pos hR, zero_sub, if_pos (fun h ↦ hL ((hc.1 h).2 hR)), if_neg hL,
        smul_neg, neg_smul]
    · rw [if_neg hL, if_neg hR, sub_zero, smul_zero,
        if_neg (not_not.2 (hc.2 (iff_of_false hL hR)))]
  rw [key, S.sum_succ_eq_zero_iff k (fun r ↦ ¬ S.InC χ r) (fun r hr ↦ ?_)]
  · refine forall_congr' fun r ↦ forall_congr' fun _ ↦ ?_
    split_ifs
    · exact Iff.rfl
    · exact neg_eq_zero
  · rw [S.lq_iff_rq hχ hprim] at hr
    by_cases hL : S.Lq χ r
    · exact S.hasSucc_of_lq hL
    · by_cases hR : S.Rq χ r
      · exact S.hasSucc_of_rq hR
      · exact absurd (iff_of_false hL hR) hr

variable (hχ : 0 < S.P.deg χ) (hprim : Prim χ)

open Classical

/-- The coefficients of an element of the centralizer table. -/
theorem repr_incl (x : (S.Tc hχ hprim).Lin k) (r : R) :
    (S.P.basis k).repr ((S.incl hχ hprim).alg k x) r =
      if h : S.InC χ r then ((S.Tc hχ hprim).basis k).repr x ⟨r, h⟩ else 0 := by
  classical
  have key : (Finsupp.lapply r).comp ((S.P.basis k).repr.toLinearMap.comp
      ((S.incl hχ hprim).alg k).toLinearMap) =
      if h : S.InC χ r then (Finsupp.lapply (⟨r, h⟩ : {r // (S.cData hχ hprim).pR r})).comp
        ((S.Tc hχ hprim).basis k).repr.toLinearMap else 0 := by
    refine ((S.Tc hχ hprim).basis k).ext fun r' ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Mult.basis_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply]
    rw [S.incl_b, Mult.basis_repr_b]
    split_ifs with h1 h2 h2
    · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        Finsupp.lapply_apply, Mult.basis_repr_b]
      rw [if_pos (Subtype.ext h1)]
    · exact absurd (h1 ▸ r'.2) h2
    · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        Finsupp.lapply_apply, Mult.basis_repr_b]
      rw [if_neg (fun e ↦ h1 (congrArg Subtype.val e))]
    · rfl
  have := congrArg (fun F ↦ F x) key
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearEquiv.coe_coe, Finsupp.lapply_apply] at this
  rw [this]
  split_ifs <;> rfl

/-- The image of the centralizer table: coefficients vanish off the centralizer rays. -/
theorem mem_range_incl (c : S.P.Lin k) :
    c ∈ ((S.incl hχ hprim).alg k).range ↔ ∀ r, ¬ S.InC χ r → (S.P.basis k).repr c r = 0 := by
  classical
  constructor
  · rintro ⟨x, hx⟩ r hr
    rw [← hx]
    change (S.P.basis k).repr ((S.incl hχ hprim).alg k x) r = 0
    rw [repr_incl, dif_neg hr]
  · intro h
    refine ⟨∑ r' : {r // (S.cData hχ hprim).pR r}, (S.P.basis k).repr c r'.1 •
      (S.Tc hχ hprim).b k r', ?_⟩
    change (S.incl hχ hprim).alg k _ = c
    rw [map_sum]
    simp only [map_smul, S.incl_b]
    conv_rhs => rw [← S.sum_repr k c]
    rw [← Finset.sum_subtype (Finset.univ.filter fun r ↦ S.InC χ r)
      (fun x ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl)
      (fun r ↦ (S.P.basis k).repr c r • S.P.b k r), Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    split_ifs with hr
    · rfl
    · rw [h r hr, zero_smul]

/-- **`C_χ` is the image of the centralizer table.** -/
theorem Cχ_eq_range : S.Cχ k χ = ((S.incl hχ hprim).alg k).range := by
  ext c
  rw [S.mem_Cχ_iff k hχ hprim, mem_range_incl]

/-- `𝔞_χ = {c ∈ C_χ : q̂c = 0}`. -/
def aχ (χ : L) : Ideal (S.Cχ k χ) where
  carrier := {c | S.qhat k χ * c = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, mul_add] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' a b hb := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul] at *
    rw [← mul_assoc, (S.mem_Cχ k a).1 a.2, mul_assoc, hb, mul_zero]

instance (χ : L) : (S.aχ k χ).IsTwoSided where
  mul_mem_of_left b ha := by
    change S.qhat k χ * ((_ : S.P.Lin k) * _) = 0
    change S.qhat k χ * _ = 0 at ha
    rw [← mul_assoc, ha, zero_mul]

include hχ hprim in
/-- **`𝔞_χ` is spanned by the unshiftable nonidentity rays and the identities at `q̂_x = 0`**:
an element of `C_χ` lies in `𝔞_χ` exactly when its coefficients at the rays of `Q_χ`
vanish. -/
theorem mem_aχ_iff (c : S.Cχ k χ) :
    c ∈ S.aχ k χ ↔ ∀ r, S.InQ χ r → (S.P.basis k).repr c r = 0 := by
  classical
  change S.qhat k χ * (c : S.P.Lin k) = 0 ↔ _
  have hC := (S.mem_Cχ_iff k hχ hprim c).1 c.2
  have key : S.qhat k χ * (c : S.P.Lin k) = ∑ r, (if S.Lq χ r then
      (S.P.basis k).repr c r • S.P.b k (S.succ χ r) else 0) := by
    conv_lhs => rw [← S.sum_repr k c]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [mul_smul_comm, qhat_mul_b']
    split_ifs <;> simp
  rw [key, S.sum_succ_eq_zero_iff k (S.Lq χ) (fun r h ↦ S.hasSucc_of_lq h)]
  refine forall_congr' fun r ↦ ?_
  by_cases hr : S.InC χ r
  · rw [S.lq_iff_inQ hr]
  · exact ⟨fun _ _ ↦ hC r hr, fun _ _ ↦ hC r hr⟩

/-- The identification `C_χ ≃ kT_c`. -/
def eC : S.Cχ k χ ≃ₐ[k] (S.Tc hχ hprim).Lin k :=
  (Subalgebra.equivOfEq _ _ (S.Cχ_eq_range k hχ hprim)).trans
    (AlgEquiv.ofInjective _ (S.incl_injective hχ hprim k)).symm

theorem incl_eC (c : S.Cχ k χ) : (S.incl hχ hprim).alg k (S.eC k hχ hprim c) = c := by
  have := (AlgEquiv.ofInjective _ (S.incl_injective hχ hprim k)).apply_symm_apply
    ((Subalgebra.equivOfEq _ _ (S.Cχ_eq_range k hχ hprim)) c)
  exact congrArg Subtype.val this

theorem proj_incl (x : (S.Tc hχ hprim).Lin k) :
    S.proj hχ hprim k ((S.incl hχ hprim).alg k x) = (S.quot hχ hprim).alg k x := by
  have key : (S.proj hχ hprim k).comp ((S.incl hχ hprim).alg k).toLinearMap =
      ((S.quot hχ hprim).alg k).toLinearMap := by
    refine ((S.Tc hχ hprim).basis k).ext fun r ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Mult.basis_apply]
    rw [S.incl_b, S.proj_b, S.quot_b]
  exact congrArg (fun F ↦ F x) key

/-- The quotient map `C_χ → kQ_χ`. -/
def φχ : S.Cχ k χ →ₐ[k] (S.Qχ hχ hprim).Lin k :=
  ((S.quot hχ hprim).alg k).comp (S.eC k hχ hprim).toAlgHom

theorem φχ_apply (c : S.Cχ k χ) : S.φχ k hχ hprim c = S.proj hχ hprim k c := by
  change (S.quot hχ hprim).alg k (S.eC k hχ hprim c) = _
  rw [← S.proj_incl, S.incl_eC]

theorem φχ_surjective : Function.Surjective (S.φχ k hχ hprim) := by
  intro y
  obtain ⟨x, hx⟩ := Mor.alg_surjective (S.quot hχ hprim) k (fun r' ↦
    ⟨⟨r'.1, S.inQ_inC r'.2⟩, by
      dsimp only [quot]
      rw [dif_pos (show S.InQ χ r'.1 from r'.2)]⟩) y
  refine ⟨(S.eC k hχ hprim).symm x, ?_⟩
  change (S.quot hχ hprim).alg k (S.eC k hχ hprim ((S.eC k hχ hprim).symm x)) = y
  rw [AlgEquiv.apply_symm_apply, hx]

/-- `π(c) = 0` exactly when the coefficients of `c` at the rays of `Q_χ` vanish. -/
theorem proj_eq_zero_iff (c : S.P.Lin k) :
    S.proj hχ hprim k c = 0 ↔ ∀ r, S.InQ χ r → (S.P.basis k).repr c r = 0 := by
  classical
  have key : S.proj hχ hprim k c = ∑ r, (S.P.basis k).repr c r •
      (if h : S.InQ χ r then (S.Qχ hχ hprim).b k ⟨r, h⟩ else 0) := by
    conv_lhs => rw [← S.sum_repr k c]
    rw [map_sum]
    simp only [map_smul, S.proj_b]
  rw [key]
  constructor
  · intro h r0 hr0
    have := congrArg (fun z ↦ ((S.Qχ hχ hprim).basis k).repr z ⟨r0, hr0⟩) h
    simp only [map_sum, map_smul, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.finsetSum_apply, Finsupp.smul_apply] at this
    rw [Finset.sum_eq_single r0] at this
    · rw [dif_pos hr0, Mult.basis_repr_b, if_pos rfl, smul_eq_mul, mul_one] at this
      exact this
    · intro r _ hr
      split_ifs with h
      · rw [Mult.basis_repr_b, if_neg (fun e ↦ hr (congrArg Subtype.val e)), smul_zero]
      · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro h
    exact Finset.sum_eq_zero fun r _ ↦ by
      split_ifs with hr
      · rw [h r hr, zero_smul]
      · rw [smul_zero]

/-- **`𝔞_χ` is the kernel of `C_χ → kQ_χ`.** -/
theorem aχ_eq_ker : S.aχ k χ = RingHom.ker (S.φχ k hχ hprim) := by
  ext c
  rw [S.mem_aχ_iff k hχ hprim, RingHom.mem_ker, φχ_apply, proj_eq_zero_iff]


/-- `B_χ = C_χ/𝔞_χ`. -/
abbrev Bχ (χ : L) : Type u := (S.Cχ k χ) ⧸ (S.aχ k χ)

/-- **`B_χ ≅ kQ_χ`.** -/
def Bχ_equiv : S.Bχ k χ ≃ₐ[k] (S.Qχ hχ hprim).Lin k :=
  (Ideal.quotientEquivAlgOfEq k (S.aχ_eq_ker k hχ hprim)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (S.φχ_surjective k hχ hprim))

theorem Bχ_equiv_mk (c : S.Cχ k χ) :
    S.Bχ_equiv k hχ hprim (Ideal.Quotient.mk _ c) = S.proj hχ hprim k c := by
  rw [Bχ_equiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk, φχ_apply]

include hχ hprim in
theorem b_mem_Cχ {r : R} (h : S.InC χ r) : S.P.b k r ∈ S.Cχ k χ := by
  rw [S.Cχ_eq_range k hχ hprim]
  exact ⟨(S.Tc hχ hprim).b k ⟨r, h⟩, S.incl_b hχ hprim k _⟩

/-- The class in `B_χ` of a ray of `Q_χ` is its basis vector of `kQ_χ`. -/
theorem Bχ_equiv_b {r : R} (h : S.InQ χ r) :
    S.Bχ_equiv k hχ hprim (Ideal.Quotient.mk _ ⟨S.P.b k r, S.b_mem_Cχ k hχ hprim (S.inQ_inC h)⟩) =
      (S.Qχ hχ hprim).b k ⟨r, h⟩ := by
  rw [Bχ_equiv_mk]
  exact (S.proj_b hχ hprim k r).trans (dif_pos h)

instance (χ : L) : FiniteDimensional k (S.Cχ k χ) :=
  Module.Finite.of_injective (S.Cχ k χ).val.toLinearMap Subtype.val_injective

instance (χ : L) : FiniteDimensional k (S.Bχ k χ) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (S.aχ k χ)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective k _)

/-- **Lemma 9.2** (`lem:centralizer-ray-algebra`), as stated: `B_χ = C_χ/𝔞_χ` is basic and
representation-finite; the classes of the supporting identities and the two-sided rays form a
basis, whose products are those of the table `Q_χ` (`B_χ ≅ kQ_χ`, the class of a ray going to
its basis vector); `Q_χ` has fewer rays than `P` when `B_χ ≠ 0`. Here `C_χ = Cent_{A₀}(q̂)` and
`𝔞_χ = {c ∈ C_χ : q̂c = 0}`. -/
theorem centralizerRayAlgebra [IsAlgClosed k] (hfin : IsRepresentationFinite k (S.P.Lin k)) :
    IsBasicAlgebra (S.Bχ k χ) ∧ IsRepresentationFinite k (S.Bχ k χ) ∧
    (∃ e : S.Bχ k χ ≃ₐ[k] (S.Qχ hχ hprim).Lin k, ∀ (r : R) (h : S.InQ χ r),
      e (Ideal.Quotient.mk _ ⟨S.P.b k r, S.b_mem_Cχ k hχ hprim (S.inQ_inC h)⟩) =
        (S.Qχ hχ hprim).b k ⟨r, h⟩) ∧
    (Nontrivial (S.Bχ k χ) → Fintype.card {r // (S.qData hχ hprim).pR r} < Fintype.card R) := by
  refine ⟨IsBasicAlgebra.of_ringEquiv (S.Bχ_equiv k hχ hprim).symm.toRingEquiv
      ((S.Qχ hχ hprim).isBasic_lin k),
    isRepresentationFinite_of_surjective (S.Bχ_equiv k hχ hprim).symm.toAlgHom
      (S.Bχ_equiv k hχ hprim).symm.surjective (S.Qχ_isRepresentationFinite hχ hprim k hfin),
    ⟨S.Bχ_equiv k hχ hprim, fun r h ↦ S.Bχ_equiv_b k hχ hprim h⟩, fun hn ↦ ?_⟩
  apply S.card_Qχ_lt hχ hprim
  by_contra hx
  push Not at hx
  have : IsEmpty {r // (S.qData hχ hprim).pR r} :=
    ⟨fun r ↦ hx _ ((S.qData hχ hprim).src_mem r.1 r.2)⟩
  have : Subsingleton ((S.Qχ hχ hprim).Lin k) := by
    refine ⟨fun a b ↦ ?_⟩
    rw [← ((S.Qχ hχ hprim).basis k).sum_repr a, ← ((S.Qχ hχ hprim).basis k).sum_repr b]
    simp
  exact not_subsingleton _ ((S.Bχ_equiv k hχ hprim).toEquiv.subsingleton)

end Sys

end RaySys

end MultiplicativeBasisDeformations
