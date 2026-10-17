import MultiplicativeBasisDeformations.Foundations.IntegralLifting
import MultiplicativeBasisDeformations.Foundations.IndicatorRel
import MultiplicativeBasisDeformations.Foundations.SquareZero

/-!
# The Hochschild complex of `OP` in one character

`integral-deformations.tex`: "We put `A^{(2)} = 𝔽₂P` and `A^{(4)} = 𝒪P`; all cochains are
normalized relative to the vertex identities and respect the categorical grading and the
integer ray weights."

For a ray system with weights and a character `χ`, a normalized relative cochain of character
`χ` on the linearization `OP` (any commutative ring `O`) sends a composable pair of
nonidentity rays `(u, v)` to a multiple of the ray `w₂(u, v)` with the endpoints of `uv` and
weight `ℓ(u) + ℓ(v) + χ` (unique by `sep`). Such cochains are coefficient functions on the
pairs for which `w₂` exists (`C2`); one-cochains are coefficient functions on the shiftable
rays (`C1`). Their realizations `Φ₁`, `Φ₂` as linear and bilinear maps of `OP`, and the
coboundary `d₁` in coefficients (`d1`), with `hcobdry (Φ₁ f) = Φ₂ (d₁ f)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u u'

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (χ : L)

local notation:max "⌜" r "⌝" => Sys.rr S r

open Classical in
/-- The ray with the endpoints of `uv` and weight `ℓ(u) + ℓ(v) + χ`, if any. -/
def w2 (u v : R) : Option R :=
  if h : ∃ t, S.P.src t = S.P.src u ∧ S.P.tgt t = S.P.tgt v ∧ S.P.wt t = S.P.wt u + S.P.wt v + χ
  then some h.choose else none

theorem w2_eq_some {u v t : R} :
    S.w2 χ u v = some t ↔
      S.P.src t = S.P.src u ∧ S.P.tgt t = S.P.tgt v ∧ S.P.wt t = S.P.wt u + S.P.wt v + χ := by
  classical
  unfold w2
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro ht
      obtain ⟨a1, a2, a3⟩ := h.choose_spec
      exact S.P.sep _ _ (a1.trans ht.1.symm) (a2.trans ht.2.1.symm) (a3.trans ht.2.2.symm)
  · simp only [reduceCtorEq, false_iff]
    exact fun ht ↦ h ⟨t, ht⟩

/-- The index set of normalized relative two-cochains of character `χ`. -/
def I2 (p : R × R) : Prop :=
  S.P.tgt p.1 = S.P.src p.2 ∧ p.1 ≠ S.P.e (S.P.src p.1) ∧ p.2 ≠ S.P.e (S.P.src p.2) ∧
    (S.w2 χ p.1 p.2).isSome

/-- Coefficient one-cochains: functions on the shiftable rays. -/
abbrev C1 (O : Type u) := {r // S.Shift χ r} → O

/-- Coefficient two-cochains: functions on the composable nonidentity pairs with a target. -/
abbrev C2 (O : Type u) := {p : R × R // S.I2 χ p} → O

variable (O : Type u) [CommRing O] [Nontrivial O]

/-- The vector of a ray, or zero. -/
def vecW (o : Option R) : S.P.Lin O := o.elim 0 (S.P.b O)

open Classical in
/-- **The realization of a one-cochain** as a linear map of `OP`. -/
def Φ1 (f : S.C1 χ O) : S.P.Lin O →ₗ[O] S.P.Lin O :=
  (S.P.basis O).constr O fun r ↦ if h : S.Shift χ r then f ⟨r, h⟩ • S.P.b O (S.succ χ r) else 0

open Classical in
theorem Φ1_b (f : S.C1 χ O) (r : R) :
    S.Φ1 χ O f (S.P.b O r) = if h : S.Shift χ r then f ⟨r, h⟩ • S.P.b O (S.succ χ r) else 0 := by
  rw [Φ1, ← Mult.basis_apply, Module.Basis.constr_basis]

open Classical in
/-- **The realization of a two-cochain** as a bilinear map of `OP`. -/
def Φ2 (c : S.C2 χ O) : S.P.Lin O →ₗ[O] S.P.Lin O →ₗ[O] S.P.Lin O :=
  (S.P.basis O).constr O fun u ↦ (S.P.basis O).constr O fun v ↦
    if h : S.I2 χ (u, v) then c ⟨(u, v), h⟩ • S.vecW O (S.w2 χ u v) else 0

open Classical in
theorem Φ2_b (c : S.C2 χ O) (u v : R) :
    S.Φ2 χ O c (S.P.b O u) (S.P.b O v) =
      if h : S.I2 χ (u, v) then c ⟨(u, v), h⟩ • S.vecW O (S.w2 χ u v) else 0 := by
  rw [Φ2, ← Mult.basis_apply, Module.Basis.constr_basis, ← Mult.basis_apply,
    Module.Basis.constr_basis]

theorem b_mul_b_opt (u v : R) : S.P.b O u * S.P.b O v = S.vecW O (S.P.mul u v) :=
  Mult.b_mul _ O u v

theorem vecW_none : S.vecW O none = 0 := rfl

theorem vecW_some (t : R) : S.vecW O (some t) = S.P.b O t := rfl

variable {χ}

/-- A product of a ray with a successor lands on `w₂`. -/
theorem w2_of_mul_succ_right {u v t : R} (hv : S.Shift χ v) (h : S.P.mul u (S.succ χ v) = some t) :
    S.w2 χ u v = some t := by
  obtain ⟨s1, s2, s3⟩ := S.succ_spec χ hv
  rw [w2_eq_some]
  refine ⟨S.P.mul_src _ _ _ h, by rw [S.P.mul_tgt _ _ _ h, s2], ?_⟩
  rw [S.P.wt_mul _ _ _ h, s3]; abel

theorem w2_of_mul_succ_left {u v t : R} (hu : S.Shift χ u) (h : S.P.mul (S.succ χ u) v = some t) :
    S.w2 χ u v = some t := by
  obtain ⟨s1, s2, s3⟩ := S.succ_spec χ hu
  rw [w2_eq_some]
  refine ⟨by rw [S.P.mul_src _ _ _ h, s1], S.P.mul_tgt _ _ _ h, ?_⟩
  rw [S.P.wt_mul _ _ _ h, s3]; abel

theorem w2_of_mul {u v t : R} (h : S.P.mul u v = some t) (ht : S.Shift χ t) :
    S.w2 χ u v = some (S.succ χ t) := by
  obtain ⟨s1, s2, s3⟩ := S.succ_spec χ ht
  rw [w2_eq_some]
  refine ⟨by rw [s1, S.P.mul_src _ _ _ h], by rw [s2, S.P.mul_tgt _ _ _ h], ?_⟩
  rw [s3, S.P.wt_mul _ _ _ h]

variable (χ)

open Classical in
/-- The coboundary of a one-cochain, in coefficients (three substitution terms). -/
def d1raw (f : S.C1 χ O) (u v : R) : O :=
  (if h : S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome then f ⟨v, h.1⟩ else 0) -
    (match S.P.mul u v with
      | some t => if ht : S.Shift χ t then f ⟨t, ht⟩ else 0
      | none => 0) +
    (if h : S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome then f ⟨u, h.1⟩ else 0)

/-- **The coboundary `d₁` in coefficients.** -/
def d1 (f : S.C1 χ O) : S.C2 χ O := fun p ↦ S.d1raw χ O f p.1.1 p.1.2

open Classical in
theorem term1 (f : S.C1 χ O) (u v : R) :
    S.P.b O u * S.Φ1 χ O f (S.P.b O v) =
      (if h : S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome then f ⟨v, h.1⟩ else 0) •
        S.vecW O (S.w2 χ u v) := by
  rw [Φ1_b]
  by_cases hv : S.Shift χ v
  · rw [dif_pos hv, mul_smul_comm, b_mul_b_opt]
    cases h : S.P.mul u (S.succ χ v) with
    | none => simp [vecW_none]
    | some t =>
      rw [dif_pos ⟨hv, by simp [h]⟩, S.w2_of_mul_succ_right hv h]
  · rw [dif_neg hv, mul_zero, dif_neg (fun h ↦ hv h.1), zero_smul]

open Classical in
theorem term3 (f : S.C1 χ O) (u v : R) :
    S.Φ1 χ O f (S.P.b O u) * S.P.b O v =
      (if h : S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome then f ⟨u, h.1⟩ else 0) •
        S.vecW O (S.w2 χ u v) := by
  rw [Φ1_b]
  by_cases hu : S.Shift χ u
  · rw [dif_pos hu, smul_mul_assoc, b_mul_b_opt]
    cases h : S.P.mul (S.succ χ u) v with
    | none => simp [vecW_none]
    | some t =>
      rw [dif_pos ⟨hu, by simp [h]⟩, S.w2_of_mul_succ_left hu h]
  · rw [dif_neg hu, zero_mul, dif_neg (fun h ↦ hu h.1), zero_smul]

open Classical in
theorem term2 (f : S.C1 χ O) (u v : R) :
    S.Φ1 χ O f (S.P.b O u * S.P.b O v) =
      (match S.P.mul u v with
        | some t => if ht : S.Shift χ t then f ⟨t, ht⟩ else 0
        | none => 0) • S.vecW O (S.w2 χ u v) := by
  rw [b_mul_b_opt]
  cases h : S.P.mul u v with
  | none => simp [vecW_none]
  | some t =>
    simp only [vecW_some, Φ1_b]
    by_cases ht : S.Shift χ t
    · rw [dif_pos ht, dif_pos ht, S.w2_of_mul h ht]; rfl
    · rw [dif_neg ht, dif_neg ht, zero_smul]

theorem not_shift_e (x : V) : ¬ S.Shift χ (S.P.e x) := fun h ↦ h.1 (by rw [S.P.src_e])

theorem not_shift_of_eq_e {r : R} (h : r = S.P.e (S.P.src r)) : ¬ S.Shift χ r := fun hs ↦ hs.1 h

theorem d1raw_eq_zero_of_not (f : S.C1 χ O) {u v : R} (h : ¬ S.I2 χ (u, v))
    (hw : (S.w2 χ u v).isSome) : S.d1raw χ O f u v = 0 := by
  classical
  unfold d1raw
  by_cases hmid : S.P.tgt u = S.P.src v
  · have h' : u = S.P.e (S.P.src u) ∨ v = S.P.e (S.P.src v) := by
      by_contra hc
      push Not at hc
      exact h ⟨hmid, hc.1, hc.2, hw⟩
    rcases h' with hu | hv
    · -- `u` is an identity
      have hx : S.P.src v = S.P.src u := by
        rw [← hmid]; conv_lhs => rw [hu]
        rw [S.P.tgt_e]
      have hmul : S.P.mul u v = some v := by
        rw [hu, ← hx]; exact S.P.e_mul v
      have h3 : ¬ (S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome) :=
        fun h0 ↦ S.not_shift_of_eq_e χ hu h0.1
      simp only [hmul, dif_neg h3, add_zero]
      by_cases hv : S.Shift χ v
      · have hm1 : S.P.mul u (S.succ χ v) = some (S.succ χ v) := by
          rw [hu, ← hx, ← (S.succ_spec χ hv).1]; exact S.P.e_mul _
        have hs : (S.P.mul u (S.succ χ v)).isSome := by rw [hm1]; rfl
        rw [dif_pos hv, dif_pos ⟨hv, hs⟩, sub_self]
      · rw [dif_neg hv, dif_neg (fun h0 : S.Shift χ v ∧ _ ↦ hv h0.1), sub_self]
    · -- `v` is an identity
      have hmul : S.P.mul u v = some u := by
        rw [hv, ← hmid]; exact S.P.mul_e u
      have h1 : ¬ (S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome) :=
        fun h0 ↦ S.not_shift_of_eq_e χ hv h0.1
      simp only [hmul, dif_neg h1, zero_sub]
      by_cases hu : S.Shift χ u
      · have hm3 : S.P.mul (S.succ χ u) v = some (S.succ χ u) := by
          rw [hv, ← hmid, ← (S.succ_spec χ hu).2.1]; exact S.P.mul_e _
        have hs : (S.P.mul (S.succ χ u) v).isSome := by rw [hm3]; rfl
        rw [dif_pos hu, dif_pos ⟨hu, hs⟩, neg_add_cancel]
      · rw [dif_neg hu, dif_neg (fun h0 : S.Shift χ u ∧ _ ↦ hu h0.1), neg_zero, add_zero]
  · -- not composable: every substitution vanishes
    have hm2 : S.P.mul u v = none := by
      cases hm : S.P.mul u v with
      | none => rfl
      | some t => exact absurd (S.P.mul_mid _ _ _ hm) hmid
    have h1 : ¬ (S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome) := by
      rintro ⟨hv, hs⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
      apply hmid
      rw [← (S.succ_spec χ hv).1]; exact S.P.mul_mid _ _ _ ht
    have h3 : ¬ (S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome) := by
      rintro ⟨hu, hs⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
      apply hmid
      rw [← (S.succ_spec χ hu).2.1]; exact S.P.mul_mid _ _ _ ht
    simp only [hm2, dif_neg h1, dif_neg h3, sub_zero, add_zero]

/-- **`d(Φ₁ f) = Φ₂(d₁ f)`.** -/
theorem hcobdry_Φ1 (f : S.C1 χ O) : GExt.hcobdry (S.Φ1 χ O f) = S.Φ2 χ O (S.d1 χ O f) := by
  classical
  refine (S.P.basis O).ext fun u ↦ (S.P.basis O).ext fun v ↦ ?_
  simp only [Mult.basis_apply]
  rw [GExt.hcobdry_apply, term1, term2, term3, Φ2_b, ← sub_smul, ← add_smul]
  change S.d1raw χ O f u v • _ = _
  by_cases h : S.I2 χ (u, v)
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    cases hw : S.w2 χ u v with
    | none => rw [vecW_none, smul_zero]
    | some t => rw [S.d1raw_eq_zero_of_not χ O f h (by rw [hw]; rfl), zero_smul]

/-! ### The cocycle condition in coefficients -/

open Classical in
/-- The ray with the endpoints of `uvw` and weight `ℓ(u) + ℓ(v) + ℓ(w) + χ`, if any. -/
def w3 (u v w : R) : Option R :=
  if h : ∃ t, S.P.src t = S.P.src u ∧ S.P.tgt t = S.P.tgt w ∧
      S.P.wt t = S.P.wt u + S.P.wt v + S.P.wt w + χ
  then some h.choose else none

theorem w3_eq_some {u v w t : R} :
    S.w3 χ u v w = some t ↔ S.P.src t = S.P.src u ∧ S.P.tgt t = S.P.tgt w ∧
      S.P.wt t = S.P.wt u + S.P.wt v + S.P.wt w + χ := by
  classical
  unfold w3
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro ht
      obtain ⟨a1, a2, a3⟩ := h.choose_spec
      exact S.P.sep _ _ (a1.trans ht.1.symm) (a2.trans ht.2.1.symm) (a3.trans ht.2.2.symm)
  · simp only [reduceCtorEq, false_iff]
    exact fun ht ↦ h ⟨t, ht⟩

open Classical in
/-- The Hochschild coboundary of a two-cochain, in coefficients (four terms). -/
def d2raw (c : S.C2 χ O) (u v w : R) : O :=
  (if h : S.I2 χ (v, w) ∧ (S.P.mul u ((S.w2 χ v w).getD u)).isSome then c ⟨(v, w), h.1⟩ else 0) -
    (match S.P.mul u v with
      | some t => if h : S.I2 χ (t, w) then c ⟨(t, w), h⟩ else 0
      | none => 0) +
    (match S.P.mul v w with
      | some t => if h : S.I2 χ (u, t) then c ⟨(u, t), h⟩ else 0
      | none => 0) -
    (if h : S.I2 χ (u, v) ∧ (S.P.mul ((S.w2 χ u v).getD u) w).isSome then c ⟨(u, v), h.1⟩
      else 0)

variable {χ}

theorem w3_of_left {u v w t t₁ : R} (ht : S.w2 χ v w = some t) (h : S.P.mul u t = some t₁) :
    S.w3 χ u v w = some t₁ := by
  obtain ⟨a1, a2, a3⟩ := (S.w2_eq_some χ).1 ht
  rw [w3_eq_some]
  refine ⟨S.P.mul_src _ _ _ h, by rw [S.P.mul_tgt _ _ _ h, a2], ?_⟩
  rw [S.P.wt_mul _ _ _ h, a3]; abel

theorem w3_of_mulL {u v w t t₁ : R} (ht : S.P.mul u v = some t) (h : S.w2 χ t w = some t₁) :
    S.w3 χ u v w = some t₁ := by
  obtain ⟨a1, a2, a3⟩ := (S.w2_eq_some χ).1 h
  rw [w3_eq_some]
  refine ⟨by rw [a1, S.P.mul_src _ _ _ ht], a2, ?_⟩
  rw [a3, S.P.wt_mul _ _ _ ht]

theorem w3_of_mulR {u v w t t₁ : R} (ht : S.P.mul v w = some t) (h : S.w2 χ u t = some t₁) :
    S.w3 χ u v w = some t₁ := by
  obtain ⟨a1, a2, a3⟩ := (S.w2_eq_some χ).1 h
  rw [w3_eq_some]
  refine ⟨a1, by rw [a2, S.P.mul_tgt _ _ _ ht], ?_⟩
  rw [a3, S.P.wt_mul _ _ _ ht]; abel

theorem w3_of_right {u v w t t₁ : R} (ht : S.w2 χ u v = some t) (h : S.P.mul t w = some t₁) :
    S.w3 χ u v w = some t₁ := by
  obtain ⟨a1, a2, a3⟩ := (S.w2_eq_some χ).1 ht
  rw [w3_eq_some]
  refine ⟨by rw [S.P.mul_src _ _ _ h, a1], S.P.mul_tgt _ _ _ h, ?_⟩
  rw [S.P.wt_mul _ _ _ h, a3]; abel

variable (χ)

theorem I2_isSome {p : R × R} (h : S.I2 χ p) : ∃ t, S.w2 χ p.1 p.2 = some t :=
  Option.isSome_iff_exists.1 h.2.2.2

open Classical in
/-- **The Hochschild coboundary of `Φ₂ c` on basis triples.** -/
theorem hoch_b (c : S.C2 χ O) (u v w : R) :
    S.P.b O u * S.Φ2 χ O c (S.P.b O v) (S.P.b O w) - S.Φ2 χ O c (S.P.b O u * S.P.b O v) (S.P.b O w)
      + S.Φ2 χ O c (S.P.b O u) (S.P.b O v * S.P.b O w) - S.Φ2 χ O c (S.P.b O u) (S.P.b O v) * S.P.b O w
      = S.d2raw χ O c u v w • S.vecW O (S.w3 χ u v w) := by
  have tA : S.P.b O u * S.Φ2 χ O c (S.P.b O v) (S.P.b O w) =
      (if h : S.I2 χ (v, w) ∧ (S.P.mul u ((S.w2 χ v w).getD u)).isSome then c ⟨(v, w), h.1⟩
        else 0) • S.vecW O (S.w3 χ u v w) := by
    rw [Φ2_b]
    by_cases hI : S.I2 χ (v, w)
    · obtain ⟨t, ht⟩ := S.I2_isSome χ hI
      rw [dif_pos hI, mul_smul_comm, ht, vecW_some, b_mul_b_opt]
      simp only [Option.getD_some]
      by_cases hs : (S.P.mul u t).isSome
      · obtain ⟨t₁, hm⟩ := Option.isSome_iff_exists.1 hs
        rw [dif_pos ⟨hI, hs⟩, show S.vecW O (S.P.mul u t) = S.P.b O t₁ by rw [hm]; rfl,
          S.w3_of_left ht hm]
        rfl
      · have hm : S.P.mul u t = none := Option.not_isSome_iff_eq_none.1 hs
        rw [dif_neg (fun h0 ↦ hs h0.2), show S.vecW O (S.P.mul u t) = 0 by rw [hm]; rfl,
          smul_zero, zero_smul]
    · rw [dif_neg hI, mul_zero, dif_neg (fun h0 ↦ hI h0.1), zero_smul]
  have tD : S.Φ2 χ O c (S.P.b O u) (S.P.b O v) * S.P.b O w =
      (if h : S.I2 χ (u, v) ∧ (S.P.mul ((S.w2 χ u v).getD u) w).isSome then c ⟨(u, v), h.1⟩
        else 0) • S.vecW O (S.w3 χ u v w) := by
    rw [Φ2_b]
    by_cases hI : S.I2 χ (u, v)
    · obtain ⟨t, ht⟩ := S.I2_isSome χ hI
      rw [dif_pos hI, smul_mul_assoc, ht, vecW_some, b_mul_b_opt]
      simp only [Option.getD_some]
      by_cases hs : (S.P.mul t w).isSome
      · obtain ⟨t₁, hm⟩ := Option.isSome_iff_exists.1 hs
        rw [dif_pos ⟨hI, hs⟩, show S.vecW O (S.P.mul t w) = S.P.b O t₁ by rw [hm]; rfl,
          S.w3_of_right ht hm]
        rfl
      · have hm : S.P.mul t w = none := Option.not_isSome_iff_eq_none.1 hs
        rw [dif_neg (fun h0 ↦ hs h0.2), show S.vecW O (S.P.mul t w) = 0 by rw [hm]; rfl,
          smul_zero, zero_smul]
    · rw [dif_neg hI, zero_mul, dif_neg (fun h0 ↦ hI h0.1), zero_smul]
  have tB : S.Φ2 χ O c (S.P.b O u * S.P.b O v) (S.P.b O w) =
      (match S.P.mul u v with
        | some t => if h : S.I2 χ (t, w) then c ⟨(t, w), h⟩ else 0
        | none => 0) • S.vecW O (S.w3 χ u v w) := by
    rw [b_mul_b_opt]
    cases hm : S.P.mul u v with
    | none => simp [vecW_none]
    | some t =>
      simp only [vecW_some, Φ2_b]
      by_cases hI : S.I2 χ (t, w)
      · obtain ⟨t₁, ht₁⟩ := S.I2_isSome χ hI
        rw [dif_pos hI, dif_pos hI, ht₁, S.w3_of_mulL hm ht₁]
      · rw [dif_neg hI, dif_neg hI, zero_smul]
  have tC : S.Φ2 χ O c (S.P.b O u) (S.P.b O v * S.P.b O w) =
      (match S.P.mul v w with
        | some t => if h : S.I2 χ (u, t) then c ⟨(u, t), h⟩ else 0
        | none => 0) • S.vecW O (S.w3 χ u v w) := by
    rw [b_mul_b_opt]
    cases hm : S.P.mul v w with
    | none => simp [vecW_none]
    | some t =>
      simp only [vecW_some, Φ2_b]
      by_cases hI : S.I2 χ (u, t)
      · obtain ⟨t₁, ht₁⟩ := S.I2_isSome χ hI
        rw [dif_pos hI, dif_pos hI, ht₁, S.w3_of_mulR hm ht₁]
      · rw [dif_neg hI, dif_neg hI, zero_smul]
  rw [tA, tB, tC, tD, ← sub_smul, ← add_smul, ← sub_smul]
  rfl

omit [DecidableEq L] in
/-- A function linear in each of three arguments of `OP` vanishes if it vanishes on basis
triples. -/
theorem eq_zero_of_basis3' {N : Type*} [AddCommGroup N] [Module O N]
    (E : S.P.Lin O → S.P.Lin O → S.P.Lin O → N)
    (h1 : ∀ a a' b c, E (a + a') b c = E a b c + E a' b c)
    (h1' : ∀ (t : O) a b c, E (t • a) b c = t • E a b c)
    (h2 : ∀ a b b' c, E a (b + b') c = E a b c + E a b' c)
    (h2' : ∀ (t : O) a b c, E a (t • b) c = t • E a b c)
    (h3 : ∀ a b c c', E a b (c + c') = E a b c + E a b c')
    (h3' : ∀ (t : O) a b c, E a b (t • c) = t • E a b c)
    (hh : ∀ u v w, E (S.P.b O u) (S.P.b O v) (S.P.b O w) = 0) (a b c : S.P.Lin O) :
    E a b c = 0 := by
  have hspan : ∀ x : S.P.Lin O, x ∈ Submodule.span O (Set.range (S.P.b O)) := fun x ↦ by
    rw [Mult.span_b]; trivial
  have s3 : ∀ u v z, E (S.P.b O u) (S.P.b O v) z = 0 := by
    intro u v z
    induction hspan z using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hh u v w
    | zero => have := h3' 0 (S.P.b O u) (S.P.b O v) 0; rw [zero_smul, zero_smul] at this; exact this
    | add x y _ _ hx hy => rw [h3, hx, hy, add_zero]
    | smul t x _ hx => rw [h3', hx, smul_zero]
  have s2 : ∀ u y z, E (S.P.b O u) y z = 0 := by
    intro u y z
    induction hspan y using Submodule.span_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact s3 u v z
    | zero => have := h2' 0 (S.P.b O u) 0 z; rw [zero_smul, zero_smul] at this; exact this
    | add x y _ _ hx hy => rw [h2, hx, hy, add_zero]
    | smul t x _ hx => rw [h2', hx, smul_zero]
  induction hspan a using Submodule.span_induction with
  | mem x hx => obtain ⟨u, rfl⟩ := hx; exact s2 u b c
  | zero => have := h1' 0 0 b c; rw [zero_smul, zero_smul] at this; exact this
  | add x y _ _ hx hy => rw [h1, hx, hy, add_zero]
  | smul t x _ hx => rw [h1', hx, smul_zero]

/-- **The cocycle condition in coefficients.** -/
theorem isHCocycle_Φ2_iff (c : S.C2 χ O) :
    GExt.IsHCocycle (S.Φ2 χ O c) ↔ ∀ u v w, (S.w3 χ u v w).isSome → S.d2raw χ O c u v w = 0 := by
  constructor
  · intro h u v w hw
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hw
    have := h (S.P.b O u) (S.P.b O v) (S.P.b O w)
    rw [S.hoch_b χ O c, ht, vecW_some] at this
    have h' := congrArg (fun z ↦ (S.P.basis O).repr z t) this
    simp only [map_smul, ← Mult.basis_apply, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h'
    exact h'
  · intro h a b c'
    refine S.eq_zero_of_basis3' O (fun a b c' ↦ a * S.Φ2 χ O c b c' - S.Φ2 χ O c (a * b) c' +
      S.Φ2 χ O c a (b * c') - S.Φ2 χ O c a b * c') ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b c'
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
      rw [S.hoch_b χ O c]
      cases hw : S.w3 χ u v w with
      | none => rw [vecW_none, smul_zero]
      | some t => rw [h u v w (by rw [hw]; rfl), zero_smul]

/-! ### Naturality in the coefficients -/

section Natural

variable {O' : Type u'} [CommRing O'] [Nontrivial O']

/-- **`d₁` commutes with additive maps of coefficients.** -/
theorem d1_map (φ : O →+ O') (f : S.C1 χ O) : S.d1 χ O' (φ ∘ f) = φ ∘ S.d1 χ O f := by
  classical
  funext p
  simp only [Function.comp, d1, d1raw]
  rw [map_add, map_sub]
  congr 1
  · congr 1
    · split_ifs <;> simp
    · cases S.P.mul p.1.1 p.1.2 with
      | none => simp
      | some t => simp only; split_ifs <;> simp
  · split_ifs <;> simp

/-- **The cocycle formula commutes with additive maps of coefficients.** -/
theorem d2raw_map (φ : O →+ O') (c : S.C2 χ O) (u v w : R) :
    S.d2raw χ O' (φ ∘ c) u v w = φ (S.d2raw χ O c u v w) := by
  classical
  simp only [d2raw, Function.comp, map_add, map_sub]
  congr 1
  · congr 1
    · congr 1
      · split_ifs <;> simp
      · cases S.P.mul u v with
        | none => simp
        | some t => simp only; split_ifs <;> simp
    · cases S.P.mul v w with
      | none => simp
      | some t => simp only; split_ifs <;> simp
  · split_ifs <;> simp

theorem d1_add (f g : S.C1 χ O) : S.d1 χ O (f + g) = S.d1 χ O f + S.d1 χ O g := by
  classical
  funext p
  simp only [d1, d1raw, Pi.add_apply]
  cases S.P.mul p.1.1 p.1.2 with
  | none => simp only; split_ifs <;> (try simp) <;> ring
  | some t => simp only; split_ifs <;> (try simp) <;> ring

theorem d1_smul (a : O) (f : S.C1 χ O) : S.d1 χ O (a • f) = a • S.d1 χ O f := by
  classical
  funext p
  simp only [d1, d1raw, Pi.smul_apply, smul_eq_mul]
  cases S.P.mul p.1.1 p.1.2 with
  | none => simp only; split_ifs <;> (try simp) <;> ring
  | some t => simp only; split_ifs <;> (try simp) <;> ring

theorem d1_sum {ι : Type*} (s : Finset ι) (f : ι → S.C1 χ O) :
    S.d1 χ O (∑ i ∈ s, f i) = ∑ i ∈ s, S.d1 χ O (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext p; simp only [Finset.sum_empty, d1, d1raw, Pi.zero_apply]
    cases S.P.mul p.1.1 p.1.2 with
    | none => simp
    | some t => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, d1_add, ih]

theorem d2raw_add (c c' : S.C2 χ O) (u v w : R) :
    S.d2raw χ O (c + c') u v w = S.d2raw χ O c u v w + S.d2raw χ O c' u v w := by
  classical
  simp only [d2raw, Pi.add_apply]
  cases S.P.mul u v <;> cases S.P.mul v w <;> simp only <;> split_ifs <;> (try simp) <;> ring

theorem d2raw_smul (a : O) (c : S.C2 χ O) (u v w : R) :
    S.d2raw χ O (a • c) u v w = a * S.d2raw χ O c u v w := by
  classical
  simp only [d2raw, Pi.smul_apply, smul_eq_mul]
  cases S.P.mul u v <;> cases S.P.mul v w <;> simp only <;> split_ifs <;> (try simp) <;> ring

end Natural

end Sys

end RaySys

end MultiplicativeBasisDeformations
