import MultiplicativeBasisDeformations.Foundations.CentralizerTable
import MultiplicativeBasisDeformations.Foundations.HochschildCochains

/-!
# Indicator cocycles on zero products (Section 11)

`lem:two-associative-tables`, `prop:indicator-cocycles` and the associativity part of
`prop:zero-product-family` (`binary-families.tex`), for `A₀ = kP`.

The correction `ε(r, s) = r * s` on pairs with `rs = 0` (and `0` otherwise) is the difference
of the stem product (associative, Prop 8.12) and the ray product. The identity `dε = 0` of
the proof of Lemma 11.1 is proved here in the monoid with zero `M P`, case by case on the
table of that proof; nested insertions vanish by Cor 8.11.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L)

local notation:max "⌜" r "⌝" => Sys.rr S r

open Classical in
/-- The correction `ε(r, s)`: the stem product on zero pairs, zero otherwise. -/
def eps (u v : R) : M S.P.toMult := if ⌜u⌝ * ⌜v⌝ = 0 then S.stem u v else 0

theorem eps_cases (u v : R) : S.eps u v = 0 ∨ ∃ w, S.eps u v = ⌜w⌝ := by
  classical
  unfold eps
  split_ifs
  · exact S.stem_cases u v
  · exact Or.inl rfl

theorem eps_of_mul_ne {u v : R} (h : ⌜u⌝ * ⌜v⌝ ≠ 0) : S.eps u v = 0 := by
  classical
  rw [eps, if_neg h]

theorem eps_of_mul_eq {u v : R} (h : ⌜u⌝ * ⌜v⌝ = 0) : S.eps u v = S.stem u v := by
  classical
  rw [eps, if_pos h]

/-- The stem product with a ray killed by its target radical is the ray product. -/
theorem stem_of_killed_tgt {t w : R} (h : ⌜t⌝ * S.q (S.P.tgt t) = 0) :
    S.stem t w = ⌜t⌝ * ⌜w⌝ := by
  classical
  by_cases h0 : ⌜t⌝ * ⌜w⌝ = 0
  · rw [h0]
    unfold stem
    rw [dif_neg]
    push Not
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [pow_zero, mul_one]; exact h0
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
      rw [show 0 + m + 1 = 1 + m by omega, pow_add, pow_one, ← mul_assoc, h, zero_mul, zero_mul]
  · exact S.stem_of_mul_ne h0

/-- A positive local power at a vertex other than the source of a ray kills it. -/
theorem qpow_mul_of_ne {y : V} {t : R} (hy : y ≠ S.P.src t) {n : ℕ} (hn : 1 ≤ n) :
    S.q y ^ n * ⌜t⌝ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, pow_succ, mul_assoc]
  rcases S.q_cases y with h | ⟨g, hg, g1, g2, -⟩
  · rw [h, zero_mul, mul_zero]
  · rw [hg]
    rw [S.P.rr_mul_rr_eq_zero_of_ne (by rw [g2]; exact hy), mul_zero]

/-- The stem product with a ray killed by its source radical is the ray product. -/
theorem stem_of_killed_src {t w : R} (h : S.q (S.P.src t) * ⌜t⌝ = 0) :
    S.stem w t = ⌜w⌝ * ⌜t⌝ := by
  classical
  by_cases h0 : ⌜w⌝ * ⌜t⌝ = 0
  · rw [h0]
    unfold stem
    rw [dif_neg]
    push Not
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [pow_zero, mul_one]; exact h0
    · by_cases hwt : S.P.tgt w = S.P.src t
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
        rw [show 0 + m + 1 = m + 1 by omega, pow_succ, mul_assoc, mul_assoc, hwt, h, mul_zero,
          mul_zero]
      · rw [mul_assoc, S.qpow_mul_of_ne hwt (n := n) hn, mul_zero]
  · exact S.stem_of_mul_ne h0

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **A correction value is killed by both endpoint radicals** (Cor 8.13). -/
theorem eps_killed (hfin : IsRepresentationFinite k (S.P.Lin k)) {u v t : R}
    (h : S.eps u v = ⌜t⌝) : ⌜t⌝ * S.q (S.P.tgt t) = 0 ∧ S.q (S.P.src t) * ⌜t⌝ = 0 := by
  have huv : ⌜u⌝ * ⌜v⌝ = 0 := by
    by_contra h0; rw [S.eps_of_mul_ne h0] at h; exact S.rr_ne t h.symm
  rw [S.eps_of_mul_eq huv] at h
  obtain ⟨-, -, h1, h2, h3⟩ := S.active_zero k hfin huv (by rw [h]; exact S.rr_ne t)
  rw [h1] at h
  rw [h] at h2 h3
  have hqv : S.q (S.P.tgt u) * ⌜v⌝ ≠ 0 := by
    intro h0; apply S.rr_ne t; rw [← h, mul_assoc, h0, mul_zero]
  obtain ⟨v', hv'⟩ := S.mul_right_ray hqv
  obtain ⟨e1, e2⟩ := S.qpow_mul_endpoints (n := 1) (by rw [pow_one]; exact hv')
  have huv' : ⌜u⌝ * ⌜v'⌝ = ⌜t⌝ := by rw [← hv', ← mul_assoc, h]
  obtain ⟨t1, t2, -, -⟩ := S.prod_of huv'
  refine ⟨by rw [t2, e2]; exact h3, by rw [t1]; exact h2⟩

/-- The stem product of a correction value with a ray. -/
theorem stemL_eps (hfin : IsRepresentationFinite k (S.P.Lin k)) (u v w : R) :
    S.stemL (S.eps u v) w = S.eps u v * ⌜w⌝ := by
  classical
  rcases S.eps_cases u v with h | ⟨t, ht⟩
  · rw [h, zero_mul]; unfold stemL; rw [dif_neg]; rintro ⟨w', hw'⟩; exact S.rr_ne w' hw'.symm
  · rw [ht, S.stemL_rr, S.stem_of_killed_tgt (S.eps_killed k hfin ht).1]

/-- The stem product of a ray with a correction value. -/
theorem stemR_eps (hfin : IsRepresentationFinite k (S.P.Lin k)) (u v w : R) :
    S.stemR u (S.eps v w) = ⌜u⌝ * S.eps v w := by
  classical
  rcases S.eps_cases v w with h | ⟨t, ht⟩
  · rw [h, mul_zero]; unfold stemR; rw [dif_neg]; rintro ⟨w', hw'⟩; exact S.rr_ne w' hw'.symm
  · rw [ht, S.stemR_rr, S.stem_of_killed_src (S.eps_killed k hfin ht).2]

/-- **`dε = 0`** (proof of Lemma 11.1), the four cases of its table. -/
theorem deps_zero (hfin : IsRepresentationFinite k (S.P.Lin k)) (u v w : R) :
    (⌜u⌝ * ⌜v⌝ = 0 → ⌜v⌝ * ⌜w⌝ = 0 → S.eps u v * ⌜w⌝ = ⌜u⌝ * S.eps v w) ∧
    (∀ t', ⌜u⌝ * ⌜v⌝ = 0 → ⌜v⌝ * ⌜w⌝ = ⌜t'⌝ → S.eps u v * ⌜w⌝ = S.eps u t') ∧
    (∀ t, ⌜u⌝ * ⌜v⌝ = ⌜t⌝ → ⌜v⌝ * ⌜w⌝ = 0 → S.eps t w = ⌜u⌝ * S.eps v w) ∧
    (∀ t t', ⌜u⌝ * ⌜v⌝ = ⌜t⌝ → ⌜v⌝ * ⌜w⌝ = ⌜t'⌝ → S.eps t w = S.eps u t') := by
  have hA := S.stem_assoc u v w
  refine ⟨fun h1 h2 ↦ ?_, fun t' h1 h2 ↦ ?_, fun t h1 h2 ↦ ?_, fun t t' h1 h2 ↦ ?_⟩
  · rw [← S.eps_of_mul_eq h1, ← S.eps_of_mul_eq h2] at hA
    rw [← S.stemL_eps k hfin, hA, S.stemR_eps k hfin]
  · rw [← S.eps_of_mul_eq h1, S.stem_of_mul_ne (r := v) (s := w) (by rw [h2]; exact S.rr_ne t'),
      h2, S.stemR_rr] at hA
    have hut : ⌜u⌝ * ⌜t'⌝ = 0 := by rw [← h2, ← mul_assoc, h1, zero_mul]
    rw [← S.stemL_eps k hfin, hA, S.eps_of_mul_eq hut]
  · rw [S.stem_of_mul_ne (r := u) (s := v) (by rw [h1]; exact S.rr_ne t), h1, S.stemL_rr,
      ← S.eps_of_mul_eq h2] at hA
    have htw : ⌜t⌝ * ⌜w⌝ = 0 := by rw [← h1, mul_assoc, h2, mul_zero]
    rw [S.eps_of_mul_eq htw, hA, S.stemR_eps k hfin]
  · rw [S.stem_of_mul_ne (r := u) (s := v) (by rw [h1]; exact S.rr_ne t), h1, S.stemL_rr,
      S.stem_of_mul_ne (r := v) (s := w) (by rw [h2]; exact S.rr_ne t'), h2, S.stemR_rr] at hA
    have e : ⌜t⌝ * ⌜w⌝ = ⌜u⌝ * ⌜t'⌝ := by rw [← h1, ← h2, mul_assoc]
    by_cases h0 : ⌜t⌝ * ⌜w⌝ = 0
    · rw [S.eps_of_mul_eq h0, S.eps_of_mul_eq (e ▸ h0), hA]
    · rw [S.eps_of_mul_ne h0, S.eps_of_mul_ne (e ▸ h0)]

/-- **Nested insertions vanish** (Prop 11.2(3)). -/
theorem eps_nested (hfin : IsRepresentationFinite k (S.P.Lin k)) {u v t : R}
    (h : S.eps u v = ⌜t⌝) (w : R) : S.eps t w = 0 ∧ S.eps w t = 0 := by
  obtain ⟨h1, h2⟩ := S.eps_killed k hfin h
  constructor
  · by_cases h0 : ⌜t⌝ * ⌜w⌝ = 0
    · rw [S.eps_of_mul_eq h0, S.stem_of_killed_tgt h1, h0]
    · exact S.eps_of_mul_ne h0
  · by_cases h0 : ⌜w⌝ * ⌜t⌝ = 0
    · rw [S.eps_of_mul_eq h0, S.stem_of_killed_src h2, h0]
    · exact S.eps_of_mul_ne h0

/-- A nonzero correction is `r q_y s` on a composable zero pair of generating rays. -/
theorem eps_ne_zero_spec (hfin : IsRepresentationFinite k (S.P.Lin k)) {u v : R}
    (h : S.eps u v ≠ 0) : ⌜u⌝ * ⌜v⌝ = 0 ∧ S.IsGen u ∧ S.IsGen v ∧ S.P.tgt u = S.P.src v ∧
      S.eps u v = ⌜u⌝ * S.q (S.P.tgt u) * ⌜v⌝ := by
  have huv : ⌜u⌝ * ⌜v⌝ = 0 := by
    by_contra h0; exact h (S.eps_of_mul_ne h0)
  rw [S.eps_of_mul_eq huv] at h ⊢
  obtain ⟨g1, g2, h1, -, -⟩ := S.active_zero k hfin huv h
  refine ⟨huv, g1, g2, ?_, h1⟩
  by_contra hne
  apply h
  have h2 := S.qpow_mul_of_ne (y := S.P.tgt u) (t := v) hne (n := 1) le_rfl
  rw [pow_one] at h2
  rw [h1, mul_assoc, h2, mul_zero]

/-- **Corrections vanish on local left inputs** (proof of Prop 11.3(3)). -/
theorem eps_local_left (hfin : IsRepresentationFinite k (S.P.Lin k)) {u : R}
    (hu : S.P.src u = S.P.tgt u) (v : R) : S.eps u v = 0 := by
  by_contra h
  obtain ⟨h0, g1, -, hm, -⟩ := S.eps_ne_zero_spec k hfin h
  have he := S.gen_loop g1 hu
  rw [he, S.P.tgt_e] at hm
  rw [he, S.e_mul_rr' v hm.symm] at h0
  exact S.rr_ne v h0

/-- **Corrections vanish on local right inputs.** -/
theorem eps_local_right (hfin : IsRepresentationFinite k (S.P.Lin k)) (u : R) {v : R}
    (hv : S.P.src v = S.P.tgt v) : S.eps u v = 0 := by
  by_contra h
  obtain ⟨h0, -, g2, hm, -⟩ := S.eps_ne_zero_spec k hfin h
  have he := S.gen_loop g2 hv
  rw [he, S.P.src_e] at hm
  rw [he] at h0
  have : ⌜u⌝ * ⌜S.P.e (S.P.tgt u)⌝ = ⌜u⌝ := S.rr_mul_e u
  rw [← hm] at h0
  exact S.rr_ne u (this.symm.trans h0)

/-! ### Cochains supported on zero pairs -/

variable (K : Type u) [Field K]

/-- The basis vector of a ray, and zero. -/
def vecM (x : M S.P.toMult) : S.P.Lin K := Elt.rec 0 0 (fun r ↦ S.P.b K r) x

omit [IsAlgClosed k] in
theorem vecM_rr (r : R) : S.vecM K ⌜r⌝ = S.P.b K r := rfl

omit [IsAlgClosed k] in
theorem vecM_zero : S.vecM K 0 = 0 := rfl

omit [IsAlgClosed k] in
theorem b_mul_b (u v : R) : S.P.b K u * S.P.b K v = S.vecM K (⌜u⌝ * ⌜v⌝) := by
  rw [Mult.b_mul, Mult.rr_mul_rr]
  cases S.P.mul u v <;> rfl

omit [IsAlgClosed k] in
theorem b_mul_vecM (u : R) {x : M S.P.toMult} (hx : x = 0 ∨ ∃ w, x = ⌜w⌝) :
    S.P.b K u * S.vecM K x = S.vecM K (⌜u⌝ * x) := by
  rcases hx with rfl | ⟨w, rfl⟩
  · rw [mul_zero, vecM_zero, mul_zero]
  · rw [vecM_rr, b_mul_b]

omit [IsAlgClosed k] in
theorem vecM_mul_b (w : R) {x : M S.P.toMult} (hx : x = 0 ∨ ∃ u, x = ⌜u⌝) :
    S.vecM K x * S.P.b K w = S.vecM K (x * ⌜w⌝) := by
  rcases hx with rfl | ⟨u, rfl⟩
  · rw [zero_mul, vecM_zero, zero_mul]
  · rw [vecM_rr, b_mul_b]

/-- The cochain `Σ a_z ε_z` with coefficients `a : R → R → K` (supported on zero pairs). -/
def coch (a : R → R → K) : S.P.Lin K →ₗ[K] S.P.Lin K →ₗ[K] S.P.Lin K :=
  (S.P.basis K).constr K fun u ↦ (S.P.basis K).constr K fun v ↦ a u v • S.vecM K (S.eps u v)

omit [IsAlgClosed k] in
theorem coch_b (a : R → R → K) (u v : R) :
    S.coch K a (S.P.b K u) (S.P.b K v) = a u v • S.vecM K (S.eps u v) := by
  rw [coch, ← Mult.basis_apply, Module.Basis.constr_basis, ← Mult.basis_apply,
    Module.Basis.constr_basis]

omit [IsAlgClosed k] in
theorem coch_vecM (a : R → R → K) {x : M S.P.toMult} (hx : x = 0 ∨ ∃ u, x = ⌜u⌝) (w : R) :
    S.coch K a (S.vecM K x) (S.P.b K w) =
      match x with
      | Elt.ray u => a u w • S.vecM K (S.eps u w)
      | _ => 0 := by
  rcases hx with rfl | ⟨u, rfl⟩
  · rw [vecM_zero, map_zero, LinearMap.zero_apply]
  · rw [vecM_rr, coch_b]; rfl

/-- The pair carrying the positive term of the cocycle equation at `(u, v, w)`. -/
def posP (u v w : R) : R × R := match S.P.mul v w with
  | none => (v, w)
  | some t' => (u, t')

/-- The pair carrying the negative term. -/
def negP (u v w : R) : R × R := match S.P.mul u v with
  | none => (u, v)
  | some t => (t, w)

/-- The common value of the two terms. -/
def Xv (u v w : R) : M S.P.toMult := match S.P.mul u v with
  | none => S.eps u v * ⌜w⌝
  | some t => S.eps t w

omit [IsAlgClosed k] in
theorem Xv_cases (u v w : R) : S.Xv u v w = 0 ∨ ∃ t, S.Xv u v w = ⌜t⌝ := by
  unfold Xv
  cases S.P.mul u v with
  | none =>
    rcases S.eps_cases u v with h | ⟨t, ht⟩
    · left; rw [h, zero_mul]
    · rcases S.rr_mul_rr_cases t w with h0 | ⟨s, hs⟩
      · left; rw [ht, h0]
      · right; exact ⟨s, by rw [ht, hs]⟩
  | some t => exact S.eps_cases t w

omit [IsAlgClosed k] in
/-- A function linear in each of three arguments vanishes if it vanishes on basis triples. -/
theorem eq_zero_of_basis3 {N : Type*} [AddCommGroup N] [Module K N]
    (E : S.P.Lin K → S.P.Lin K → S.P.Lin K → N)
    (h1 : ∀ a a' b c, E (a + a') b c = E a b c + E a' b c)
    (h1' : ∀ (t : K) a b c, E (t • a) b c = t • E a b c)
    (h2 : ∀ a b b' c, E a (b + b') c = E a b c + E a b' c)
    (h2' : ∀ (t : K) a b c, E a (t • b) c = t • E a b c)
    (h3 : ∀ a b c c', E a b (c + c') = E a b c + E a b c')
    (h3' : ∀ (t : K) a b c, E a b (t • c) = t • E a b c)
    (hh : ∀ u v w, E (S.P.b K u) (S.P.b K v) (S.P.b K w) = 0) (a b c : S.P.Lin K) :
    E a b c = 0 := by
  have hspan : ∀ x : S.P.Lin K, x ∈ Submodule.span K (Set.range (S.P.b K)) := fun x ↦ by
    rw [S.P.span_b K]; trivial
  have s3 : ∀ u v z, E (S.P.b K u) (S.P.b K v) z = 0 := by
    intro u v z
    induction hspan z using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hh u v w
    | zero => have := h3' 0 (S.P.b K u) (S.P.b K v) 0; rw [zero_smul, zero_smul] at this; exact this
    | add x y _ _ hx hy => rw [h3, hx, hy, add_zero]
    | smul t x _ hx => rw [h3', hx, smul_zero]
  have s2 : ∀ u y z, E (S.P.b K u) y z = 0 := by
    intro u y z
    induction hspan y using Submodule.span_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact s3 u v z
    | zero => have := h2' 0 (S.P.b K u) 0 z; rw [zero_smul, zero_smul] at this; exact this
    | add x y _ _ hx hy => rw [h2, hx, hy, add_zero]
    | smul t x _ hx => rw [h2', hx, smul_zero]
  induction hspan a using Submodule.span_induction with
  | mem x hx => obtain ⟨u, rfl⟩ := hx; exact s2 u b c
  | zero => have := h1' 0 0 b c; rw [zero_smul, zero_smul] at this; exact this
  | add x y _ _ hx hy => rw [h1, hx, hy, add_zero]
  | smul t x _ hx => rw [h1', hx, smul_zero]

/-- **The cocycle equation on a basis triple** (proof of Lemma 11.1): one positive and one
negative term, with the same value. -/
theorem coch_expr (hfin : IsRepresentationFinite k (S.P.Lin k)) (a : R → R → K) (u v w : R) :
    S.P.b K u * S.coch K a (S.P.b K v) (S.P.b K w) - S.coch K a (S.P.b K u * S.P.b K v) (S.P.b K w)
      + S.coch K a (S.P.b K u) (S.P.b K v * S.P.b K w) - S.coch K a (S.P.b K u) (S.P.b K v) * S.P.b K w
      = (a (S.posP u v w).1 (S.posP u v w).2 - a (S.negP u v w).1 (S.negP u v w).2) •
          S.vecM K (S.Xv u v w) := by
  have hd := S.deps_zero k hfin u v w
  rw [coch_b, coch_b, Mult.b_mul, Mult.b_mul, mul_smul_comm, smul_mul_assoc,
    S.b_mul_vecM K u (S.eps_cases v w), S.vecM_mul_b K w (S.eps_cases u v)]
  have huv := S.P.rr_mul_rr u v
  have hvw := S.P.rr_mul_rr v w
  unfold posP negP Xv
  cases h1 : S.P.mul u v with
  | none =>
    rw [h1, Option.elim_none] at huv
    cases h2 : S.P.mul v w with
    | none =>
      rw [h2, Option.elim_none] at hvw
      simp only [Option.elim_none, map_zero, LinearMap.zero_apply, sub_zero, add_zero]
      rw [hd.1 huv hvw, sub_smul]
    | some t' =>
      rw [h2, Option.elim_some] at hvw
      simp only [Option.elim_none, Option.elim_some, map_zero, LinearMap.zero_apply, sub_zero,
        coch_b, S.eps_of_mul_ne (show ⌜v⌝ * ⌜w⌝ ≠ 0 by rw [hvw]; exact S.rr_ne t'), mul_zero,
        vecM_zero, smul_zero, zero_add]
      rw [hd.2.1 t' huv hvw, sub_smul]
  | some t =>
    rw [h1, Option.elim_some] at huv
    cases h2 : S.P.mul v w with
    | none =>
      rw [h2, Option.elim_none] at hvw
      simp only [Option.elim_none, Option.elim_some, map_zero, add_zero, coch_b,
        S.eps_of_mul_ne (show ⌜u⌝ * ⌜v⌝ ≠ 0 by rw [huv]; exact S.rr_ne t), zero_mul, vecM_zero,
        smul_zero, sub_zero]
      rw [hd.2.2.1 t huv hvw, sub_smul]
    | some t' =>
      rw [h2, Option.elim_some] at hvw
      simp only [Option.elim_some, coch_b,
        S.eps_of_mul_ne (show ⌜u⌝ * ⌜v⌝ ≠ 0 by rw [huv]; exact S.rr_ne t),
        S.eps_of_mul_ne (show ⌜v⌝ * ⌜w⌝ ≠ 0 by rw [hvw]; exact S.rr_ne t'), zero_mul, mul_zero,
        vecM_zero, smul_zero, zero_sub, sub_zero]
      rw [hd.2.2.2 t t' huv hvw, sub_smul]; abel

/-- The coefficient condition: equal coefficients on the two terms of every equation. -/
def EdgeOK (a : R → R → K) : Prop :=
  ∀ u v w, S.Xv u v w ≠ 0 → a (S.posP u v w).1 (S.posP u v w).2 = a (S.negP u v w).1 (S.negP u v w).2

/-- **Prop 11.2(1)**: the supported cochain is a cocycle iff its coefficients satisfy the
equalities. -/
theorem coch_isCocycle_iff (hfin : IsRepresentationFinite k (S.P.Lin k)) (a : R → R → K) :
    LenGrading.IsCocycle₂ (S.coch K a) ↔ S.EdgeOK K a := by
  constructor
  · intro h u v w hX
    have e := h (S.P.b K u) (S.P.b K v) (S.P.b K w)
    rw [S.coch_expr k K hfin] at e
    by_contra hne
    apply hX
    rcases S.Xv_cases u v w with h0 | ⟨t, ht⟩
    · exact h0
    · exfalso
      rw [ht, vecM_rr] at e
      exact sub_ne_zero.2 hne (smul_eq_zero.1 e |>.resolve_right (S.P.b_ne_zero K t))
  · intro h x y z
    refine S.eq_zero_of_basis3 K (fun x y z ↦ x * S.coch K a y z - S.coch K a (x * y) z +
      S.coch K a x (y * z) - S.coch K a x y * z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ x y z
    · intro x x' y z; simp only [add_mul, map_add, LinearMap.add_apply]; abel
    · intro t x y z; simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply, smul_sub,
        smul_add]
    · intro x y y' z; simp only [mul_add, add_mul, map_add, LinearMap.add_apply]; abel
    · intro t x y z; simp only [smul_mul_assoc, mul_smul_comm, map_smul, LinearMap.smul_apply,
        smul_sub, smul_add]
    · intro x y z z'; simp only [mul_add, map_add, LinearMap.add_apply]; abel
    · intro t x y z; simp only [mul_smul_comm, map_smul, LinearMap.smul_apply, smul_sub,
        smul_add]
    · intro u v w
      rw [S.coch_expr k K hfin]
      by_cases hX : S.Xv u v w = 0
      · rw [hX, vecM_zero, smul_zero]
      · rw [h u v w hX, sub_self, zero_smul]

omit [IsAlgClosed k] in
theorem coch_add (a a' : R → R → K) : S.coch K (a + a') = S.coch K a + S.coch K a' := by
  refine (S.P.basis K).ext fun u ↦ (S.P.basis K).ext fun v ↦ ?_
  simp only [Mult.basis_apply, LinearMap.add_apply, coch_b, Pi.add_apply, add_smul]

omit [IsAlgClosed k] in
theorem coch_smul (t : K) (a : R → R → K) : S.coch K (t • a) = t • S.coch K a := by
  refine (S.P.basis K).ext fun u ↦ (S.P.basis K).ext fun v ↦ ?_
  simp only [Mult.basis_apply, LinearMap.smul_apply, coch_b, Pi.smul_apply, smul_eq_mul,
    mul_smul]

omit [IsAlgClosed k] in
theorem coch_sum {ι : Type*} (s : Finset ι) (a : ι → R → R → K) :
    S.coch K (∑ i ∈ s, a i) = ∑ i ∈ s, S.coch K (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine (S.P.basis K).ext fun u ↦ (S.P.basis K).ext fun v ↦ ?_
    rw [Mult.basis_apply, Mult.basis_apply, coch_b]; simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, coch_add, ih]

/-- **Mixed insertions vanish** (`eq:mixed-insertions-zero`). -/
theorem coch_nested (hfin : IsRepresentationFinite k (S.P.Lin k)) (a b : R → R → K)
    (x y z : S.P.Lin K) :
    S.coch K a (S.coch K b x y) z = 0 ∧ S.coch K a x (S.coch K b y z) = 0 := by
  constructor
  · refine S.eq_zero_of_basis3 K (fun x y z ↦ S.coch K a (S.coch K b x y) z) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ x y z
    · intro x x' y z; simp only [map_add, LinearMap.add_apply]
    · intro t x y z; simp only [map_smul, LinearMap.smul_apply]
    · intro x y y' z; simp only [map_add, LinearMap.add_apply]
    · intro t x y z; simp only [map_smul, LinearMap.smul_apply]
    · intro x y z z'; simp only [map_add]
    · intro t x y z; simp only [map_smul]
    · intro u v w
      rw [coch_b, map_smul, LinearMap.smul_apply]
      rcases S.eps_cases u v with h | ⟨t, ht⟩
      · rw [h, vecM_zero, map_zero, LinearMap.zero_apply, smul_zero]
      · rw [ht, vecM_rr, coch_b, (S.eps_nested k hfin ht w).1, vecM_zero, smul_zero, smul_zero]
  · refine S.eq_zero_of_basis3 K (fun x y z ↦ S.coch K a x (S.coch K b y z)) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ x y z
    · intro x x' y z; simp only [map_add, LinearMap.add_apply]
    · intro t x y z; simp only [map_smul, LinearMap.smul_apply]
    · intro x y y' z; simp only [map_add, LinearMap.add_apply]
    · intro t x y z; simp only [map_smul, LinearMap.smul_apply]
    · intro x y z z'; simp only [map_add]
    · intro t x y z; simp only [map_smul]
    · intro u v w
      rw [coch_b, map_smul]
      rcases S.eps_cases v w with h | ⟨t, ht⟩
      · rw [h, vecM_zero, map_zero, smul_zero]
      · rw [ht, vecM_rr, coch_b, (S.eps_nested k hfin ht u).2, vecM_zero, smul_zero, smul_zero]

/-- **Prop 11.3(1)**: `m + Σ a_z ε_z` is associative when the coefficients satisfy the
equalities. -/
theorem family_assoc (hfin : IsRepresentationFinite k (S.P.Lin k)) {a : R → R → K}
    (ha : S.EdgeOK K a) (x y z : S.P.Lin K) :
    (x * y + S.coch K a x y) * z + S.coch K a (x * y + S.coch K a x y) z =
      x * (y * z + S.coch K a y z) + S.coch K a x (y * z + S.coch K a y z) := by
  have hc := (S.coch_isCocycle_iff k K hfin a).2 ha x y z
  have n1 := (S.coch_nested k K hfin a a x y z).1
  have n2 := (S.coch_nested k K hfin a a x y z).2
  simp only [map_add, LinearMap.add_apply, add_mul, mul_add, n1, n2, add_zero]
  rw [← sub_eq_zero]
  have e : x * y * z + S.coch K a x y * z + S.coch K a (x * y) z -
      (x * (y * z) + x * S.coch K a y z + S.coch K a x (y * z)) =
      -(x * S.coch K a y z - S.coch K a (x * y) z + S.coch K a x (y * z) - S.coch K a x y * z) := by
    noncomm_ring
  rw [e, hc, neg_zero]

/-! ### Indicator classes (Prop 11.2(2)) -/

/-- Two pairs carry the two terms of one cocycle equation. -/
def Edge (z z' : R × R) : Prop :=
  ∃ u v w, S.Xv u v w ≠ 0 ∧ S.posP u v w = z ∧ S.negP u v w = z'

/-- The equivalence relation generated by the cocycle equations. -/
def pairSetoid : Setoid (R × R) := Relation.EqvGen.setoid S.Edge

open Classical in
/-- The indicator coefficients of a class. -/
def ind (c : Quotient S.pairSetoid) : R → R → K := fun u v ↦
  if (⟦(u, v)⟧ : Quotient S.pairSetoid) = c then 1 else 0

/-- **The indicator cocycle `μ_E`** (`eq:indicator-cocycles`). -/
def muE (c : Quotient S.pairSetoid) : S.P.Lin K →ₗ[K] S.P.Lin K →ₗ[K] S.P.Lin K :=
  S.coch K (S.ind K c)

omit [IsAlgClosed k] in
theorem edgeOK_ind (c : Quotient S.pairSetoid) : S.EdgeOK K (S.ind K c) := by
  intro u v w hX
  have h : (⟦S.posP u v w⟧ : Quotient S.pairSetoid) = ⟦S.negP u v w⟧ :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨u, v, w, hX, rfl, rfl⟩)
  unfold ind
  rw [Prod.mk.eta, Prod.mk.eta, h]

omit [IsAlgClosed k] in
/-- Coefficients satisfying the equalities are constant on classes. -/
theorem const_of_edgeOK {a : R → R → K} (ha : S.EdgeOK K a) {z z' : R × R}
    (h : (⟦z⟧ : Quotient S.pairSetoid) = ⟦z'⟧) : a z.1 z.2 = a z'.1 z'.2 := by
  have h' : Relation.EqvGen S.Edge z z' := Quotient.exact h
  clear h
  induction h' with
  | rel x y hxy =>
    obtain ⟨u, v, w, hX, rfl, rfl⟩ := hxy
    exact ha u v w hX
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Prop 11.2(2)**: a supported cocycle is a combination of indicator cocycles. -/
theorem coch_eq_sum_muE (hfin : IsRepresentationFinite k (S.P.Lin k)) {a : R → R → K}
    (ha : LenGrading.IsCocycle₂ (S.coch K a)) [Fintype (Quotient S.pairSetoid)] :
    S.coch K a = ∑ c : Quotient S.pairSetoid,
      (a (Quotient.out c).1 (Quotient.out c).2) • S.muE K c := by
  have hok := (S.coch_isCocycle_iff k K hfin a).1 ha
  have hdec : a = ∑ c : Quotient S.pairSetoid, (a (Quotient.out c).1 (Quotient.out c).2) • S.ind K c := by
    funext u v
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ind]
    rw [Finset.sum_eq_single (⟦(u, v)⟧ : Quotient S.pairSetoid)]
    · rw [if_pos rfl, mul_one]
      exact (S.const_of_edgeOK K hok (z := Quotient.out (⟦(u, v)⟧ : Quotient S.pairSetoid))
        (z' := (u, v)) (Quotient.out_eq _)).symm
    · intro c _ hc
      rw [if_neg (fun h ↦ hc (Eq.symm h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  conv_lhs => rw [hdec]
  rw [S.coch_sum]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [S.coch_smul]; rfl

end Sys

end RaySys

end MultiplicativeBasisDeformations
