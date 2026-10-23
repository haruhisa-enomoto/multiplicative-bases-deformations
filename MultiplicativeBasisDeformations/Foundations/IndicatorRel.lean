module

public import MultiplicativeBasisDeformations.Foundations.IndicatorCocycles

/-!
# Indicator cochains: relativity and characters

Two facts used in the proofs of Propositions 11.2 and 11.3 (`binary-families.tex`):

* the supported cochains are normalized `S`-relative (their values vanish on identity inputs
  and they commute with the vertex idempotents);
* "Every indicator has a single positive character `c_E = ℓ(r*s) − ℓ(r) − ℓ(s) = ℓ(q_y)`.
  All pairs in one class `E` have the same character, since each equation `a_z = a_{z'}`
  comes from a homogeneous cocycle equation." (`pairChar_edge`)
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  (hfin : IsRepresentationFinite k (S.P.Lin k))

local notation:max "⌜" r "⌝" => Sys.rr S r

include hfin in
/-- **A nonzero correction has the endpoints of its pair.** -/
theorem eps_endpoints {u v t : R} (h : S.eps u v = ⌜t⌝) :
    S.P.src t = S.P.src u ∧ S.P.tgt t = S.P.tgt v := by
  have hne : S.eps u v ≠ 0 := by rw [h]; exact S.rr_ne t
  obtain ⟨-, -, -, -, he⟩ := S.eps_ne_zero_spec k hfin hne
  rw [he] at h
  rcases S.q_cases (S.P.tgt u) with hq | ⟨g, hg, -, -, -⟩
  · rw [hq, mul_zero, zero_mul] at h; exact absurd h.symm (S.rr_ne t)
  rw [hg] at h
  rcases S.rr_mul_rr_cases u g with h0 | ⟨u', hu'⟩
  · rw [h0, zero_mul] at h; exact absurd h.symm (S.rr_ne t)
  rw [hu'] at h
  obtain ⟨e1, e2, -⟩ := S.prod_of h
  obtain ⟨e1', -⟩ := S.prod_of hu'
  exact ⟨e1.trans e1', e2⟩

/-- The character of a pair: `ℓ(r*s) − ℓ(r) − ℓ(s)`. -/
def pairChar (z : R × R) : L := S.wtM (S.eps z.1 z.2) - S.P.wt z.1 - S.P.wt z.2

theorem wtM_vecM_ne {x : M S.P.toMult} (hx : x ≠ 0) (hx' : x = 0 ∨ ∃ t, x = ⌜t⌝) :
    ∃ t, x = ⌜t⌝ := hx'.resolve_left hx

include hfin in
/-- **The two pairs of a cocycle equation have nonzero corrections and the same
character.** -/
theorem pairChar_edge {z z' : R × R} (h : S.Edge z z') :
    S.eps z.1 z.2 ≠ 0 ∧ S.eps z'.1 z'.2 ≠ 0 ∧ S.pairChar z = S.pairChar z' := by
  obtain ⟨u, v, w, hX, rfl, rfl⟩ := h
  have hd := S.deps_zero k hfin u v w
  have huv := S.P.rr_mul_rr u v
  have hvw := S.P.rr_mul_rr v w
  unfold posP negP pairChar
  unfold Xv at hX
  cases h1 : S.P.mul u v with
  | none =>
    rw [h1, Option.elim_none] at huv
    rw [h1] at hX
    cases h2 : S.P.mul v w with
    | none =>
      rw [h2, Option.elim_none] at hvw
      simp only
      have e := hd.1 huv hvw
      have hX' : ⌜u⌝ * S.eps v w ≠ 0 := e ▸ hX
      have h1' : S.eps u v ≠ 0 := fun h0 ↦ hX (by rw [h0, zero_mul])
      have h2' : S.eps v w ≠ 0 := fun h0 ↦ hX' (by rw [h0, mul_zero])
      refine ⟨h2', h1', ?_⟩
      have w1 := S.wtM_mul _ _ hX
      have w2 := S.wtM_mul _ _ hX'
      rw [e] at w1
      rw [w1, wtM_rr] at w2
      rw [wtM_rr] at w2
      rw [show S.wtM (S.eps v w) = S.wtM (S.eps u v) + S.P.wt w - S.P.wt u by
        rw [w2]; abel]
      abel
    | some t' =>
      rw [h2, Option.elim_some] at hvw
      simp only
      have e := hd.2.1 t' huv hvw
      have h1' : S.eps u v ≠ 0 := fun h0 ↦ hX (by rw [h0, zero_mul])
      have h2' : S.eps u t' ≠ 0 := e ▸ hX
      refine ⟨h2', h1', ?_⟩
      have w1 := S.wtM_mul _ _ hX
      rw [e] at w1
      have wt' := S.P.wt_of_mul hvw
      rw [w1, wtM_rr, wt']
      abel
  | some t =>
    rw [h1, Option.elim_some] at huv
    rw [h1] at hX
    cases h2 : S.P.mul v w with
    | none =>
      rw [h2, Option.elim_none] at hvw
      simp only
      have e := hd.2.2.1 t huv hvw
      have h1' : S.eps t w ≠ 0 := hX
      have hX' : ⌜u⌝ * S.eps v w ≠ 0 := e ▸ hX
      have h2' : S.eps v w ≠ 0 := fun h0 ↦ hX' (by rw [h0, mul_zero])
      refine ⟨h2', h1', ?_⟩
      have w2 := S.wtM_mul _ _ hX'
      rw [← e, wtM_rr] at w2
      have wt' := S.P.wt_of_mul huv
      rw [w2, wt']
      abel
    | some t' =>
      rw [h2, Option.elim_some] at hvw
      simp only
      have e := hd.2.2.2 t t' huv hvw
      have h1' : S.eps t w ≠ 0 := hX
      have h2' : S.eps u t' ≠ 0 := e ▸ hX
      refine ⟨h2', h1', ?_⟩
      rw [e, S.P.wt_of_mul huv, S.P.wt_of_mul hvw]
      abel

include hfin in
/-- **Pairs of one class with nonzero corrections have the same character.** -/
theorem pairChar_class {z z' : R × R} (h : (⟦z⟧ : Quotient S.pairSetoid) = ⟦z'⟧)
    (hz : S.eps z.1 z.2 ≠ 0) : S.eps z'.1 z'.2 ≠ 0 ∧ S.pairChar z = S.pairChar z' := by
  have h' : Relation.EqvGen S.Edge z z' := Quotient.exact h
  have key : ∀ {a b : R × R}, Relation.EqvGen S.Edge a b →
      (S.eps a.1 a.2 ≠ 0 ↔ S.eps b.1 b.2 ≠ 0) ∧
        (S.eps a.1 a.2 ≠ 0 → S.pairChar a = S.pairChar b) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      obtain ⟨h1, h2, h3⟩ := S.pairChar_edge k hfin hxy
      exact ⟨⟨fun _ ↦ h2, fun _ ↦ h1⟩, fun _ ↦ h3⟩
    | refl => exact ⟨Iff.rfl, fun _ ↦ rfl⟩
    | symm x y _ ih => exact ⟨ih.1.symm, fun hy ↦ (ih.2 (ih.1.2 hy)).symm⟩
    | trans x y w _ _ ih1 ih2 =>
      exact ⟨ih1.1.trans ih2.1, fun hx ↦ (ih1.2 hx).trans (ih2.2 (ih1.1.1 hx))⟩
  obtain ⟨h1, h2⟩ := key h'
  exact ⟨h1.1 hz, h2 hz⟩

/-! ### The supported cochains are relative -/

variable (c : R → R → k)

theorem bilin_ext {f g : S.P.Lin k →ₗ[k] S.P.Lin k →ₗ[k] S.P.Lin k}
    (h : ∀ u v, f (S.P.b k u) (S.P.b k v) = g (S.P.b k u) (S.P.b k v)) : f = g :=
  (S.P.basis k).ext fun u ↦ (S.P.basis k).ext fun v ↦ by
    simp only [Mult.basis_apply]; exact h u v

include hfin in
theorem coch_e_mul (x : V) (a z : S.P.Lin k) :
    S.coch k c (S.P.b k (S.P.e x) * a) z = S.P.b k (S.P.e x) * S.coch k c a z := by
  have := S.bilin_ext k (f := (S.coch k c).comp (LinearMap.mulLeft k (S.P.b k (S.P.e x))))
    (g := (S.coch k c).compr₂ (LinearMap.mulLeft k (S.P.b k (S.P.e x)))) fun u v ↦ by
      simp only [LinearMap.comp_apply, LinearMap.compr₂_apply, LinearMap.mulLeft_apply]
      rw [Mult.b_e_mul, coch_b, mul_smul_comm]
      rcases S.eps_cases u v with h0 | ⟨t, ht⟩
      · split_ifs <;> simp [h0, vecM_zero, coch_b]
      · rw [ht, vecM_rr, Mult.b_e_mul]
        obtain ⟨e1, -⟩ := S.eps_endpoints k hfin ht
        split_ifs with h1 h2 h2
        · rw [coch_b, ht, vecM_rr]
        · exact absurd (h1.trans e1.symm) h2
        · exact absurd (h2.trans e1) h1
        · simp
  exact congrArg (fun φ ↦ φ a z) this

include hfin in
theorem coch_mul_e (x : V) (a z : S.P.Lin k) :
    S.coch k c (a * S.P.b k (S.P.e x)) z = S.coch k c a (S.P.b k (S.P.e x) * z) := by
  have := S.bilin_ext k (f := (S.coch k c).comp (LinearMap.mulRight k (S.P.b k (S.P.e x))))
    (g := (S.coch k c).compl₂ (LinearMap.mulLeft k (S.P.b k (S.P.e x)))) fun u v ↦ by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply]
      rw [Mult.b_mul_e, Mult.b_e_mul]
      by_cases h0 : S.eps u v = 0
      · split_ifs <;> simp [coch_b, h0, vecM_zero]
      · obtain ⟨-, -, -, hm, -⟩ := S.eps_ne_zero_spec k hfin h0
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (h1.trans hm) h2
        · exact absurd (h2.trans hm.symm) h1
        · simp
  exact congrArg (fun φ ↦ φ a z) this

include hfin in
theorem coch_mul_e_right (x : V) (a z : S.P.Lin k) :
    S.coch k c a (z * S.P.b k (S.P.e x)) = S.coch k c a z * S.P.b k (S.P.e x) := by
  have := S.bilin_ext k (f := (S.coch k c).compl₂ (LinearMap.mulRight k (S.P.b k (S.P.e x))))
    (g := (S.coch k c).compr₂ (LinearMap.mulRight k (S.P.b k (S.P.e x)))) fun u v ↦ by
      simp only [LinearMap.compl₂_apply, LinearMap.compr₂_apply, LinearMap.mulRight_apply]
      rw [Mult.b_mul_e, coch_b, smul_mul_assoc]
      rcases S.eps_cases u v with h0 | ⟨t, ht⟩
      · split_ifs <;> simp [h0, vecM_zero, coch_b]
      · rw [ht, vecM_rr, Mult.b_mul_e]
        obtain ⟨-, e2⟩ := S.eps_endpoints k hfin ht
        split_ifs with h1 h2 h2
        · rw [coch_b, ht, vecM_rr]
        · exact absurd (h1.trans e2.symm) h2
        · exact absurd (h2.trans e2) h1
        · simp
  exact congrArg (fun φ ↦ φ a z) this

include hfin in
theorem coch_e_left (x : V) (z : S.P.Lin k) : S.coch k c (S.P.b k (S.P.e x)) z = 0 := by
  have : S.coch k c (S.P.b k (S.P.e x)) = 0 := (S.P.basis k).ext fun v ↦ by
    rw [Mult.basis_apply, coch_b, S.eps_local_left k hfin (by rw [S.P.src_e, S.P.tgt_e]),
      vecM_zero, smul_zero, LinearMap.zero_apply]
  rw [this, LinearMap.zero_apply]

include hfin in
theorem coch_e_right (x : V) (a : S.P.Lin k) : S.coch k c a (S.P.b k (S.P.e x)) = 0 := by
  have : (S.coch k c).flip (S.P.b k (S.P.e x)) = 0 := (S.P.basis k).ext fun u ↦ by
    rw [LinearMap.flip_apply, Mult.basis_apply, coch_b,
      S.eps_local_right k hfin u (by rw [S.P.src_e, S.P.tgt_e]), vecM_zero, smul_zero,
      LinearMap.zero_apply]
  rw [← LinearMap.flip_apply, this, LinearMap.zero_apply]

/-! ### Values of the indicator cocycles -/

open Classical in
theorem muE_b (E : Quotient S.pairSetoid) (u v : R) :
    S.muE k E (S.P.b k u) (S.P.b k v) =
      if (⟦(u, v)⟧ : Quotient S.pairSetoid) = E then S.vecM k (S.eps u v) else 0 := by
  classical
  rw [muE, coch_b, ind]
  split_ifs <;> simp

include hfin in
/-- **An indicator of a class of character `χ` shifts weights by `χ`.** -/
theorem muE_value {E : Quotient S.pairSetoid} {χ : L}
    (hE : ∀ z : R × R, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ)
    (u v : R) : S.muE k E (S.P.b k u) (S.P.b k v) = 0 ∨
      ∃ t, S.muE k E (S.P.b k u) (S.P.b k v) = S.P.b k t ∧
        S.P.wt t = S.P.wt u + S.P.wt v + χ ∧ S.P.src t = S.P.src u ∧ S.P.tgt t = S.P.tgt v := by
  classical
  rw [muE_b]
  split_ifs with h
  · rcases S.eps_cases u v with h0 | ⟨t, ht⟩
    · left; rw [h0, vecM_zero]
    · right
      have hc := hE (u, v) h (by rw [ht]; exact S.rr_ne t)
      obtain ⟨e1, e2⟩ := S.eps_endpoints k hfin ht
      refine ⟨t, by rw [ht, vecM_rr], ?_, e1, e2⟩
      have : S.pairChar (u, v) = S.P.wt t - S.P.wt u - S.P.wt v := by
        simp only [pairChar, ht, wtM_rr]
      rw [hc] at this
      rw [this]; abel
  · left; rfl

end Sys

end RaySys

end MultiplicativeBasisDeformations
