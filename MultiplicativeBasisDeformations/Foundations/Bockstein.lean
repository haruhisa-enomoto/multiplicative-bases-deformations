import MultiplicativeBasisDeformations.Foundations.CharComplex
import MultiplicativeBasisDeformations.Foundations.ZModFour
import MultiplicativeBasisDeformations.Foundations.BaseChange
import MultiplicativeBasisDeformations.Foundations.SupportedBockstein
import MultiplicativeBasisDeformations.Foundations.CentralizerTable
import MultiplicativeBasisDeformations.Foundations.IndicatorRel

/-!
# Supported representatives through the connecting map (Corollary 10.5, coefficient form)

`cor:zero-supported-coverage` (`integral-deformations.tex`) on the coefficient complexes
of `CharComplex`, with `𝒪 = ℤ/4` and the sequence `0 → 𝔽₂ → 𝒪 → 𝔽₂ → 0`: Lemma 10.4
(`supported_bockstein`) applies to `C¹ → C² → C³` of character `χ` with `U` the pairs `(u, v)`
with `uv = 0` whose stem product is the ray `w₂(u, v)`. Condition (2) is Theorem 9.1(3): a
derivation modulo two has nonzero-product Leibniz coefficients (`IsSol`), which lift to `ℤ`
by `integral_lifting`; the lifted coboundary vanishes on nonzero products and lands in the stem
lines at zero products (`d1_isSol_mem_U`). Condition (1) is Proposition 10.3 (`IStar`). This
gives the corollary over `𝔽₂` (`cor105_coeff₂`); "It may be chosen over `𝔽₂` and then extended
to `k`": a class over `k` has a coordinate class over `𝔽₂` which is not a coboundary, and a
retraction `k → 𝔽₂` shows that its supported representative stays a non-coboundary over `k`
(`cor105_coeff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]

/-- A coboundary is a cocycle. -/
theorem isHCocycle_hcobdry (h : Λ →ₗ[R] Λ) : IsHCocycle (hcobdry h) := by
  intro a b c
  simp only [hcobdry_apply, map_add, map_sub, mul_add, mul_sub, add_mul, sub_mul, mul_assoc]
  abel

end GExt

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (χ : L)

local notation:max "⌜" r "⌝" => Sys.rr S r

/-! ### The complex as linear maps -/

section Lin

variable (O : Type u) [CommRing O] [Nontrivial O]

/-- The index set of three-cochain coefficients. -/
abbrev T3 := {t : R × R × R // (S.w3 χ t.1 t.2.1 t.2.2).isSome}

/-- `d₁` as a linear map. -/
def d1L : S.C1 χ O →ₗ[O] S.C2 χ O where
  toFun := S.d1 χ O
  map_add' := S.d1_add χ O
  map_smul' := S.d1_smul χ O

/-- `d₂` as a linear map. -/
def d2L : S.C2 χ O →ₗ[O] (S.T3 χ → O) where
  toFun c t := S.d2raw χ O c t.1.1 t.1.2.1 t.1.2.2
  map_add' c c' := funext fun t ↦ S.d2raw_add χ O c c' _ _ _
  map_smul' a c := funext fun t ↦ S.d2raw_smul χ O a c _ _ _

theorem d1L_apply (f : S.C1 χ O) : S.d1L χ O f = S.d1 χ O f := rfl

theorem d2L_apply (c : S.C2 χ O) (t : S.T3 χ) :
    S.d2L χ O c t = S.d2raw χ O c t.1.1 t.1.2.1 t.1.2.2 := rfl

theorem d2L_d1L (f : S.C1 χ O) : S.d2L χ O (S.d1L χ O f) = 0 := by
  have h := (S.isHCocycle_Φ2_iff χ O (S.d1 χ O f)).1
    (by rw [← S.hcobdry_Φ1 χ O f]; exact GExt.isHCocycle_hcobdry _)
  funext t
  exact h _ _ _ t.2

/-- The coordinates of `U`: zero products whose stem product is the ray `w₂`. -/
def UC (p : R × R) : Prop :=
  ⌜p.1⌝ * ⌜p.2⌝ = 0 ∧ ∃ t, S.w2 χ p.1 p.2 = some t ∧ S.eps p.1 p.2 = ⌜t⌝

/-- **The supported cochains.** -/
def Usub : Submodule O (S.C2 χ O) where
  carrier := {c | ∀ p, ¬ S.UC χ p.1 → c p = 0}
  add_mem' ha hb p hp := by rw [Pi.add_apply, ha p hp, hb p hp, add_zero]
  zero_mem' p _ := rfl
  smul_mem' a c hc p hp := by rw [Pi.smul_apply, hc p hp, smul_zero]

end Lin

/-! ### Solutions of the Leibniz equations -/

section Sol

variable {χ}

theorem IsSol.map {M N : Type*} [AddCommGroup M] [AddCommGroup N] {d : R → M}
    (hd : S.IsSol χ d) (φ : M →+ N) : S.IsSol χ (φ ∘ d) := by
  classical
  refine ⟨fun r hr ↦ by simp [hd.1 r hr], fun r s t h ht ↦ ?_⟩
  simp only [Function.comp, hd.2 r s t h ht, map_add]
  congr 1 <;> split_ifs <;> simp

theorem IsSol.add {M : Type*} [AddCommGroup M] {d d' : R → M} (hd : S.IsSol χ d)
    (hd' : S.IsSol χ d') : S.IsSol χ (d + d') := by
  classical
  refine ⟨fun r hr ↦ by simp [hd.1 r hr, hd'.1 r hr], fun r s t h ht ↦ ?_⟩
  simp only [Pi.add_apply, hd.2 r s t h ht, hd'.2 r s t h ht]
  split_ifs <;> abel

theorem IsSol.zero {M : Type*} [AddCommGroup M] : S.IsSol χ (0 : R → M) :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ ↦ by simp⟩

theorem IsSol.sum {M : Type*} [AddCommGroup M] {ι : Type*} (s : Finset ι) {d : ι → R → M}
    (hd : ∀ i ∈ s, S.IsSol χ (d i)) : S.IsSol χ (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact IsSol.zero S
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hd i (Finset.mem_insert_self _ _)).add S (ih fun j hj ↦ hd j (Finset.mem_insert_of_mem hj))

end Sol

/-! ### The lifted coboundary is supported on stem lines -/

section Support

variable {χ}

theorem stem_eq_of_q {r s : R} (h0 : ⌜r⌝ * ⌜s⌝ = 0) (h1 : ⌜r⌝ * S.q (S.P.tgt r) * ⌜s⌝ ≠ 0) :
    S.stem r s = ⌜r⌝ * S.q (S.P.tgt r) * ⌜s⌝ := by
  classical
  have hex : ∃ n : ℕ, ⌜r⌝ * S.q (S.P.tgt r) ^ n * ⌜s⌝ ≠ 0 := ⟨1, by rwa [pow_one]⟩
  have hf : Nat.find hex = 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨by rwa [pow_one], fun n hn ↦ ?_⟩
    obtain rfl : n = 0 := by omega
    simp [h0]
  rw [stem, dif_pos hex, hf, pow_one]

/-- A nonzero substitution `u v⁺` at a zero product lies on the stem line. -/
theorem UC_of_right (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {u v t : R} (hmid : S.P.tgt u = S.P.src v)
    (h0 : ⌜u⌝ * ⌜v⌝ = 0) (hv : S.Shift χ v) (ht : S.P.mul u (S.succ χ v) = some t) :
    S.UC χ (u, v) := by
  classical
  have ht' : ⌜u⌝ * ⌜S.succ χ v⌝ = ⌜t⌝ := S.P.rr_mul_rr_eq_rr.2 ht
  refine ⟨h0, t, S.w2_of_mul_succ_right hv ht, ?_⟩
  rcases S.succ_by_gen hχ hprim hv with h | h
  · -- `v⁺ = q̂ v`
    have hs : S.Supp χ (S.P.src v) := by
      by_contra hs
      rw [S.qh_of_not_supp χ hs, zero_mul] at h
      exact S.rr_ne _ h.symm
    rw [S.qh_of_supp χ hs] at h
    have hq : ⌜u⌝ * S.q (S.P.tgt u) * ⌜v⌝ = ⌜t⌝ := by rw [hmid, mul_assoc, h, ht']
    show (if ⌜u⌝ * ⌜v⌝ = 0 then S.stem u v else 0) = _
    rw [if_pos h0, S.stem_eq_of_q h0 (by rw [hq]; exact S.rr_ne t), hq]
  · -- `v⁺ = v q̂`: then `u v⁺ = 0`
    exfalso
    have : ⌜u⌝ * ⌜S.succ χ v⌝ = 0 := by rw [← h, ← mul_assoc, h0, zero_mul]
    rw [ht'] at this
    exact S.rr_ne t this

/-- A nonzero substitution `u⁺ v` at a zero product lies on the stem line. -/
theorem UC_of_left (hχ : 0 < S.P.deg χ) (hprim : Prim χ) {u v t : R}
    (h0 : ⌜u⌝ * ⌜v⌝ = 0) (hu : S.Shift χ u) (ht : S.P.mul (S.succ χ u) v = some t) :
    S.UC χ (u, v) := by
  classical
  have ht' : ⌜S.succ χ u⌝ * ⌜v⌝ = ⌜t⌝ := S.P.rr_mul_rr_eq_rr.2 ht
  refine ⟨h0, t, S.w2_of_mul_succ_left hu ht, ?_⟩
  rcases S.succ_by_gen hχ hprim hu with h | h
  · exfalso
    have : ⌜S.succ χ u⌝ * ⌜v⌝ = 0 := by rw [← h, mul_assoc, h0, mul_zero]
    rw [ht'] at this
    exact S.rr_ne t this
  · have hs : S.Supp χ (S.P.tgt u) := by
      by_contra hs
      rw [S.qh_of_not_supp χ hs, mul_zero] at h
      exact S.rr_ne _ h.symm
    rw [S.qh_of_supp χ hs] at h
    have hq : ⌜u⌝ * S.q (S.P.tgt u) * ⌜v⌝ = ⌜t⌝ := by rw [h, ht']
    show (if ⌜u⌝ * ⌜v⌝ = 0 then S.stem u v else 0) = _
    rw [if_pos h0, S.stem_eq_of_q h0 (by rw [hq]; exact S.rr_ne t), hq]

/-- **The coboundary of a solution of the nonzero-product Leibniz equations is supported on the
stem lines of zero products** (`cor:zero-supported-coverage`, proof). -/
theorem d1_isSol_mem_U (hχ : 0 < S.P.deg χ) (hprim : Prim χ) (O : Type u) [CommRing O]
    [Nontrivial O] {δ : R → O} (hδ : S.IsSol χ δ) :
    S.d1 χ O (fun r ↦ δ r.1) ∈ S.Usub χ O := by
  classical
  intro p
  obtain ⟨⟨u, v⟩, hI⟩ := p
  intro hU
  have hmid := hI.1
  have hu0 := hI.2.1
  change S.d1raw χ O (fun r ↦ δ r.1) u v = 0
  unfold d1raw
  change ¬ S.UC χ (u, v) at hU
  cases hm : S.P.mul u v with
  | none =>
    have h0 : ⌜u⌝ * ⌜v⌝ = 0 := S.P.rr_mul_rr_eq_zero.2 hm
    rw [dif_neg, dif_neg]
    · simp
    · rintro ⟨hu, hs⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
      exact hU (S.UC_of_left hχ hprim h0 hu ht)
    · rintro ⟨hv, hs⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
      exact hU (S.UC_of_right hχ hprim hmid h0 hv ht)
  | some t =>
    have hp : ⌜u⌝ * ⌜v⌝ = ⌜t⌝ := S.P.rr_mul_rr_eq_rr.2 hm
    simp only
    by_cases ht : S.Shift χ t
    · rw [dif_pos ht, hδ.2 u v t hp ht]
      have hL : (S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome) ↔ S.EL χ u v t := by
        constructor
        · rintro ⟨hu, hs⟩
          obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
          refine ⟨hu, ?_⟩
          rcases S.subst_left hu hp with h | ⟨-, h⟩
          · exact absurd (h.symm.trans (S.P.rr_mul_rr_eq_rr.2 hs)) (S.rr_ne s).symm
          · exact h
        · rintro ⟨hu, h⟩
          exact ⟨hu, Option.isSome_iff_exists.2 ⟨_, S.P.rr_mul_rr_eq_rr.1 h⟩⟩
      have hR : (S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome) ↔ S.ER χ u v t := by
        constructor
        · rintro ⟨hv, hs⟩
          obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
          refine ⟨hv, ?_⟩
          rcases S.subst_right hu0 hv hp with h | ⟨-, h⟩
          · exact absurd (h.symm.trans (S.P.rr_mul_rr_eq_rr.2 hs)) (S.rr_ne s).symm
          · exact h
        · rintro ⟨hv, h⟩
          exact ⟨hv, Option.isSome_iff_exists.2 ⟨_, S.P.rr_mul_rr_eq_rr.1 h⟩⟩
      have eA : (if h : S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome then
          (fun r : {r // S.Shift χ r} ↦ δ r.1) ⟨v, h.1⟩ else 0) =
          if S.ER χ u v t then δ v else 0 := by
        by_cases a : S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome
        · rw [dif_pos a, if_pos (hR.1 a)]
        · rw [dif_neg a, if_neg (fun b ↦ a (hR.2 b))]
      have eC : (if h : S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome then
          (fun r : {r // S.Shift χ r} ↦ δ r.1) ⟨u, h.1⟩ else 0) =
          if S.EL χ u v t then δ u else 0 := by
        by_cases a : S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome
        · rw [dif_pos a, if_pos (hL.1 a)]
        · rw [dif_neg a, if_neg (fun b ↦ a (hL.2 b))]
      rw [eA, eC]; abel
    · rw [dif_neg ht, dif_neg, dif_neg]
      · simp
      · rintro ⟨hu, hs⟩
        obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
        rcases S.subst_left hu hp with h | ⟨h, -⟩
        · exact S.rr_ne s ((S.P.rr_mul_rr_eq_rr.2 hs).symm.trans h)
        · exact ht h
      · rintro ⟨hv, hs⟩
        obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
        rcases S.subst_right hu0 hv hp with h | ⟨h, -⟩
        · exact S.rr_ne s ((S.P.rr_mul_rr_eq_rr.2 hs).symm.trans h)
        · exact ht h

theorem shift_succ_iff {u v t : R} (hp : ⌜u⌝ * ⌜v⌝ = ⌜t⌝) :
    (S.Shift χ u ∧ (S.P.mul (S.succ χ u) v).isSome) ↔ S.EL χ u v t := by
  constructor
  · rintro ⟨hu, hs⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨hu, ?_⟩
    rcases S.subst_left hu hp with h | ⟨-, h⟩
    · exact absurd (h.symm.trans (S.P.rr_mul_rr_eq_rr.2 hs)) (S.rr_ne s).symm
    · exact h
  · rintro ⟨hu, h⟩
    exact ⟨hu, Option.isSome_iff_exists.2 ⟨_, S.P.rr_mul_rr_eq_rr.1 h⟩⟩

theorem shift_succ_iff' {u v t : R} (hu0 : u ≠ S.P.e (S.P.src u)) (hp : ⌜u⌝ * ⌜v⌝ = ⌜t⌝) :
    (S.Shift χ v ∧ (S.P.mul u (S.succ χ v)).isSome) ↔ S.ER χ u v t := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨hv, ?_⟩
    rcases S.subst_right hu0 hv hp with h | ⟨-, h⟩
    · exact absurd (h.symm.trans (S.P.rr_mul_rr_eq_rr.2 hs)) (S.rr_ne s).symm
    · exact h
  · rintro ⟨hv, h⟩
    exact ⟨hv, Option.isSome_iff_exists.2 ⟨_, S.P.rr_mul_rr_eq_rr.1 h⟩⟩

variable (χ) in
open Classical in
/-- A one-cochain as a function on all rays (zero on unshiftable rays). -/
def ext1 {O : Type u} [Zero O] (f : {r // S.Shift χ r} → O) (r : R) : O :=
  if h : S.Shift χ r then f ⟨r, h⟩ else 0

/-- **A one-cocycle gives a solution of the nonzero-product Leibniz equations.** -/
theorem isSol_of_d1 (O : Type u) [CommRing O] [Nontrivial O] (f : S.C1 χ O)
    (hf : S.d1 χ O f = 0) : S.IsSol χ (S.ext1 χ f) := by
  classical
  refine ⟨fun r hr ↦ by rw [ext1, dif_neg hr], fun r s t hp ht ↦ ?_⟩
  by_cases hr0 : r = S.P.e (S.P.src r)
  · -- `r` is an identity, so `t = s`
    have hre : ⌜r⌝ = ⌜S.P.e (S.P.src r)⌝ := congrArg _ hr0
    have hsx : S.P.src s = S.P.src r := by
      rw [← (S.prod_of hp).2.2.1]; conv_lhs => rw [hr0]
      rw [S.P.tgt_e]
    have hst : t = s := by
      rw [hre, S.e_mul_rr' s hsx] at hp
      exact (S.rr_inj hp).symm
    subst hst
    have hEL : ¬ S.EL χ r t t := fun h ↦ h.1.1 hr0
    have hER : S.ER χ r t t := ⟨ht, by
      rw [hre, S.e_mul_rr' _ (by rw [(S.succ_spec χ ht).1, hsx])]⟩
    rw [if_neg hEL, if_pos hER, zero_add]
  by_cases hs0 : s = S.P.e (S.P.src s)
  · have hse : ⌜s⌝ = ⌜S.P.e (S.P.tgt r)⌝ := by
      rw [(S.prod_of hp).2.2.1]; exact congrArg _ hs0
    have hrt : t = r := by
      rw [hse, S.rr_mul_e] at hp
      exact (S.rr_inj hp).symm
    subst hrt
    have hER : ¬ S.ER χ t s t := fun h ↦ h.1.1 hs0
    have hEL : S.EL χ t s t := ⟨ht, by
      rw [hse, ← (S.succ_spec χ ht).2.1, S.rr_mul_e]⟩
    rw [if_pos hEL, if_neg hER, add_zero]
  -- both are nonidentities: the coboundary equation at `(r, s)`
  have hm : S.P.mul r s = some t := S.P.rr_mul_rr_eq_rr.1 hp
  have hI : S.I2 χ (r, s) := ⟨(S.prod_of hp).2.2.1, hr0, hs0, by
    rw [S.w2_of_mul hm ht]; rfl⟩
  have h0 := congrFun hf ⟨(r, s), hI⟩
  change S.d1raw χ O f r s = 0 at h0
  unfold d1raw at h0
  rw [hm] at h0
  simp only [dif_pos ht] at h0
  have eA : (if h : S.Shift χ s ∧ (S.P.mul r (S.succ χ s)).isSome then f ⟨s, h.1⟩ else 0) =
      if S.ER χ r s t then S.ext1 χ f s else 0 := by
    by_cases a : S.Shift χ s ∧ (S.P.mul r (S.succ χ s)).isSome
    · rw [dif_pos a, if_pos ((S.shift_succ_iff' hr0 hp).1 a), ext1, dif_pos a.1]
    · rw [dif_neg a, if_neg (fun b ↦ a ((S.shift_succ_iff' hr0 hp).2 b))]
  have eC : (if h : S.Shift χ r ∧ (S.P.mul (S.succ χ r) s).isSome then f ⟨r, h.1⟩ else 0) =
      if S.EL χ r s t then S.ext1 χ f r else 0 := by
    by_cases a : S.Shift χ r ∧ (S.P.mul (S.succ χ r) s).isSome
    · rw [dif_pos a, if_pos ((S.shift_succ_iff hp).1 a), ext1, dif_pos a.1]
    · rw [dif_neg a, if_neg (fun b ↦ a ((S.shift_succ_iff hp).2 b))]
  rw [eA, eC] at h0
  rw [ext1, dif_pos ht]
  linear_combination -h0

end Support

/-! ### Condition (2): lifting derivations to `ℤ/4` -/

section Lift

variable (k : Type u) [Field k] [IsAlgClosed k]

variable {χ}

/-- **Solutions with values in `𝔽₂` lift to `𝒪 = ℤ/4`**: Theorem 9.1(3). -/
theorem exists_Z4_isSol (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hW : ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r)
    {d : R → 𝔽₂} (hd : S.IsSol χ d) :
    ∃ D : R → ZMod 4, S.IsSol χ D ∧ ∀ r, Z4.red (D r) = d r := by
  obtain ⟨ω, hω, hωd⟩ := S.integral_lifting k hfin hχ hprim hW hd
  exact ⟨_, hω.map S (Int.castAddHom (ZMod 4)), fun r ↦ by
    simp only [Function.comp, Int.coe_castAddHom, map_intCast]; exact hωd r⟩

variable (χ) in
/-- **Condition (2) of Lemma 10.4.** -/
theorem cond2 (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hW : ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r)
    (δ : S.C1 χ (ZMod 4)) (hδ : ∃ m, S.d1L χ (ZMod 4) δ = (2 : ZMod 4) • m) :
    ∃ ε, S.d1L χ (ZMod 4) (δ + (2 : ZMod 4) • ε) ∈ S.Usub χ (ZMod 4) := by
  classical
  obtain ⟨m, hm⟩ := hδ
  -- the reduction of `δ` is a cocycle
  have hred : S.d1 χ 𝔽₂ (Z4.red.toAddMonoidHom ∘ δ) = 0 := by
    rw [S.d1_map χ (ZMod 4) Z4.red.toAddMonoidHom δ]
    funext p
    have := congrFun hm p
    simp only [d1L_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Function.comp, this, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      map_mul, Pi.zero_apply, Z4.red_two, zero_mul]
  obtain ⟨D, hD, hDr⟩ := S.exists_Z4_isSol k hfin hχ hprim hW (S.isSol_of_d1 𝔽₂ _ hred)
  have hlift : ∀ r : {r // S.Shift χ r}, Z4.red (D r.1) = Z4.red (δ r) := fun r ↦ by
    rw [hDr, ext1, dif_pos r.2]; rfl
  choose ε hε using fun r ↦ Z4.exists_eq_add_two_mul (hlift r)
  refine ⟨ε, ?_⟩
  have : δ + (2 : ZMod 4) • ε = fun r ↦ D r.1 := funext fun r ↦ by
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hε r]
  rw [this, d1L_apply]
  exact S.d1_isSol_mem_U hχ hprim (ZMod 4) hD

variable (χ) in
/-- **Proposition 10.3 in coefficients** (`prop:integral-bockstein`, `i_* = 0`): twice a
cochain over `𝒪 = ℤ/4` whose reduction is a cocycle is a coboundary. -/
def IStar : Prop :=
  ∀ z : S.C2 χ (ZMod 4), (∃ w, S.d2L χ (ZMod 4) z = (2 : ZMod 4) • w) →
    ∃ δ, (2 : ZMod 4) • z = S.d1L χ (ZMod 4) δ

variable (χ) in
/-- **Proposition 10.3, surjectivity of the connecting map** (`prop:integral-bockstein`): every
two-cocycle `c` over `𝔽₂` of character `χ` is `β` of a derivation: there is a one-cochain `δ`
over `𝒪 = ℤ/4` with `dδ = 2c̃` whose reduction is a cocycle, i.e. `c = (dδ)/2`. -/
theorem beta_surjective (hI : S.IStar χ) (c : S.C2 χ 𝔽₂) (hc : S.d2L χ 𝔽₂ c = 0) :
    ∃ δ : S.C1 χ (ZMod 4), S.d1L χ (ZMod 4) δ = (2 : ZMod 4) • (Z4.lift ∘ c) ∧
      S.d1 χ 𝔽₂ (Z4.red ∘ δ) = 0 := by
  classical
  set rd : ZMod 4 →+ 𝔽₂ := Z4.red.toAddMonoidHom
  set z : S.C2 χ (ZMod 4) := Z4.lift ∘ c
  have hz : rd ∘ z = c := funext fun p ↦ Z4.red_lift (c p)
  have hdz : ∃ w, S.d2L χ (ZMod 4) z = (2 : ZMod 4) • w := by
    have : ∀ t, Z4.red (S.d2L χ (ZMod 4) z t) = 0 := fun t ↦ by
      rw [show Z4.red (S.d2L χ (ZMod 4) z t) = rd (S.d2L χ (ZMod 4) z t) from rfl, d2L_apply,
        ← S.d2raw_map χ (ZMod 4) rd z, hz]
      exact congrFun hc t
    choose w hw using fun t ↦ Z4.exists_two_mul_of_red (this t)
    exact ⟨w, funext fun t ↦ hw t⟩
  obtain ⟨δ, hδ⟩ := hI z hdz
  refine ⟨δ, hδ.symm, ?_⟩
  have := S.d1_map χ (ZMod 4) rd δ
  change S.d1 χ 𝔽₂ (rd ∘ δ) = 0
  rw [this, ← d1L_apply, ← hδ]
  funext p
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul, rd, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, map_mul, Z4.red_two, zero_mul, Pi.zero_apply]

theorem ann_two {ι : Type*} (m : ι → ZMod 4) (h : (2 : ZMod 4) • m = 0) :
    ∃ m', m = (2 : ZMod 4) • m' := by
  choose m' hm' using fun i ↦ Z4.exists_two_mul_of_red
    ((Z4.two_mul_eq_zero_iff (m i)).1 (congrFun h i))
  exact ⟨m', funext fun i ↦ hm' i⟩

variable (χ) in
/-- **Corollary 10.5 over `𝔽₂`** (`cor:zero-supported-coverage`): given Proposition 10.3, a
cocycle of character `χ` which is not a coboundary yields one supported on the stem lines of
zero products which is not a coboundary. -/
theorem cor105_coeff₂ (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hW : ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r)
    (hI : S.IStar χ) (c : S.C2 χ 𝔽₂) (hc : S.d2L χ 𝔽₂ c = 0) (hnc : ¬ ∃ f, c = S.d1 χ 𝔽₂ f) :
    ∃ u : S.C2 χ 𝔽₂, u ∈ S.Usub χ 𝔽₂ ∧ S.d2L χ 𝔽₂ u = 0 ∧ ¬ ∃ f, u = S.d1 χ 𝔽₂ f := by
  classical
  set rd : ZMod 4 →+ 𝔽₂ := Z4.red.toAddMonoidHom
  have hrd : ∀ a, rd a = Z4.red a := fun _ ↦ rfl
  set z : S.C2 χ (ZMod 4) := fun p ↦ Z4.lift (c p)
  have hz : rd ∘ z = c := funext fun p ↦ Z4.red_lift (c p)
  have hdz : ∃ w, S.d2L χ (ZMod 4) z = (2 : ZMod 4) • w := by
    have : ∀ t, Z4.red (S.d2L χ (ZMod 4) z t) = 0 := fun t ↦ by
      rw [← hrd, d2L_apply, ← S.d2raw_map χ (ZMod 4) rd z, hz]
      exact congrFun hc t
    choose w hw using fun t ↦ Z4.exists_two_mul_of_red (this t)
    exact ⟨w, funext fun t ↦ hw t⟩
  obtain ⟨u, hu, ⟨w, hw⟩, δ, m, hzu⟩ := supported_bockstein (2 : ZMod 4) (S.d1L χ (ZMod 4))
    (S.d2L χ (ZMod 4)) (S.d2L_d1L χ (ZMod 4)) (S.Usub χ (ZMod 4)) ann_two ann_two
    (fun m hm ↦ ⟨fun p ↦ if S.UC χ p.1 then m p else 0, fun p hp ↦ by
      show (if S.UC χ p.1 then m p else 0) = 0
      rw [if_neg hp],
      funext fun p ↦ by
        by_cases hp : S.UC χ p.1
        · simp [hp]
        · have := hm p hp
          simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
          rw [this, if_neg hp, mul_zero]⟩)
    hI (S.cond2 χ k hfin hχ hprim hW) z hdz
  refine ⟨rd ∘ u, fun p hp ↦ by simp [hu p hp], ?_, ?_⟩
  · funext t
    have := congrFun hw t
    rw [d2L_apply] at this ⊢
    rw [S.d2raw_map χ (ZMod 4) rd u, hrd, this, Pi.smul_apply, smul_eq_mul, map_mul, Z4.red_two,
      zero_mul]
    rfl
  · rintro ⟨f, hf⟩
    apply hnc
    refine ⟨f + rd ∘ δ, ?_⟩
    have h1 : rd ∘ (z - u) = rd ∘ (S.d1L χ (ZMod 4) δ + (2 : ZMod 4) • m) := by rw [hzu]
    have h2 : rd ∘ ((2 : ZMod 4) • m) = 0 := funext fun p ↦ by
      simp only [Function.comp, Pi.smul_apply, smul_eq_mul, hrd, map_mul, Pi.zero_apply,
        Z4.red_two, zero_mul]
    have e1 : rd ∘ (z - u) = c - rd ∘ u := by
      rw [← hz]; funext p; simp
    have e2 : rd ∘ (S.d1L χ (ZMod 4) δ + (2 : ZMod 4) • m) = S.d1 χ 𝔽₂ (rd ∘ δ) := by
      have : rd ∘ (S.d1L χ (ZMod 4) δ + (2 : ZMod 4) • m) =
          rd ∘ S.d1L χ (ZMod 4) δ + rd ∘ ((2 : ZMod 4) • m) := funext fun p ↦ by simp
      rw [this, h2, add_zero, d1L_apply, S.d1_map]
    rw [e1, e2, hf] at h1
    rw [S.d1_add, ← h1]; abel

variable [CharP k 2]

variable (χ) in
/-- **Corollary 10.5 in coefficients** (`cor:zero-supported-coverage`), over `k`: the
corollary over `𝔽₂`, extended to `k`. -/
theorem cor105_coeff (hfin : IsRepresentationFinite k (S.P.Lin k)) (hχ : 0 < S.P.deg χ)
    (hprim : Prim χ)
    (hW : ∀ w : R → ZMod 2,
      (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ → w t = w r + w s) →
      ∃ ω : R → ℤ, (∀ r s t, S.TB χ r → S.TB χ s → S.TB χ t → ⌜r⌝ * ⌜s⌝ = ⌜t⌝ →
        ω t = ω r + ω s) ∧ ∀ r, S.TB χ r → (ω r : ZMod 2) = w r)
    (hI : S.IStar χ) (c : S.C2 χ k) (hc : S.d2L χ k c = 0) (hnc : ¬ ∃ f, c = S.d1 χ k f) :
    ∃ u : S.C2 χ k, u ∈ S.Usub χ k ∧ S.d2L χ k u = 0 ∧ ¬ ∃ f, u = S.d1 χ k f := by
  classical
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  set B := Module.Basis.ofVectorSpace (ZMod 2) k
  -- the coordinate cochains over `𝔽₂`
  set cj : _ → S.C2 χ 𝔽₂ := fun j p ↦ B.repr (c p) j
  have hcj : ∀ j, S.d2L χ 𝔽₂ (cj j) = 0 := fun j ↦ funext fun t ↦ by
    rw [d2L_apply]
    have := S.d2raw_map χ k (B.coord j).toAddMonoidHom c t.1.1 t.1.2.1 t.1.2.2
    change S.d2raw χ 𝔽₂ (cj j) _ _ _ = _ at this
    rw [this, ← d2L_apply, hc]; simp
  -- some coordinate is not a coboundary
  obtain ⟨j, hj⟩ : ∃ j, ¬ ∃ f, cj j = S.d1 χ 𝔽₂ f := by
    by_contra hall
    push Not at hall
    apply hnc
    choose f hf using hall
    set T : Finset _ := Finset.univ.biUnion fun p ↦ (B.repr (c p)).support
    refine ⟨∑ j ∈ T, (LinearMap.toSpanSingleton (ZMod 2) k (B j)).toAddMonoidHom ∘ f j, ?_⟩
    rw [S.d1_sum]
    funext p
    rw [Finset.sum_apply]
    have hp : c p = ∑ j ∈ T, B.repr (c p) j • B j := by
      have key : ∑ j ∈ (B.repr (c p)).support, B.repr (c p) j • B j = c p := by
        have := B.linearCombination_repr (c p)
        rwa [Finsupp.linearCombination_apply, Finsupp.sum] at this
      conv_lhs => rw [← key]
      exact Finset.sum_subset (fun j hj ↦ Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, hj⟩)
        fun j _ hj ↦ by rw [Finsupp.notMem_support_iff.1 hj, zero_smul]
    rw [hp]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [S.d1_map, Function.comp_apply, ← hf j]
    rfl
  obtain ⟨u, hu, hu2, hnu⟩ := S.cor105_coeff₂ χ k hfin hχ hprim hW hI (cj j) (hcj j) hj
  set ι : 𝔽₂ →+ k := (algebraMap (ZMod 2) k).toAddMonoidHom
  refine ⟨ι ∘ u, fun p hp ↦ by simp [hu p hp], ?_, ?_⟩
  · funext t
    rw [d2L_apply, S.d2raw_map χ 𝔽₂ ι u, ← d2L_apply, hu2]; simp
  · rintro ⟨f, hf⟩
    obtain ⟨θ, h1⟩ := ScalarMeshCategory.exists_retraction (K := ZMod 2) (k := k)
    apply hnu
    refine ⟨θ.toAddMonoidHom ∘ f, ?_⟩
    rw [S.d1_map, ← hf]
    funext p
    simp only [Function.comp, ι, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      LinearMap.toAddMonoidHom_coe, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul,
      mul_one]

end Lift

end Sys

end RaySys

end MultiplicativeBasisDeformations
